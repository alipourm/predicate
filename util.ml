open Cil
module H = Hashtbl
module A = Alpha

(* [weimer] Sun May  5 12:25:24 PDT 2002
 * This code was pulled from ext/switch.ml because it looks like we really
 * want it to be part of CIL. 
 *
 * Here is the magic handling to
 *  (1) replace switch statements with if/goto
 *  (2) remove "break"
 *  (3) remove "default"
 *  (4) remove "continue"
 *)

(* This alphaTable is used to prevent collision of label names when
   transforming switch statements and loops. It uses a *unit*
   alphaTableData ref because there isn't any information we need to
   carry around. *)
let labelAlphaTable : (string, unit A.alphaTableData ref) H.t =
  H.create 11

let freshLabel (base:string) =
  fst (A.newAlphaName labelAlphaTable None base ())

let rec xform_switch_stmt s break_dest cont_dest = begin
  s.labels <- Util.list_map (fun lab -> match lab with
    Label _ -> lab
  | Case(e,l) ->
      let suffix =
	match getInteger e with
	| Some value -> 
	    if compare_cilint value zero_cilint < 0 then
	      "neg_" ^ string_of_cilint (neg_cilint value)
	    else
	      string_of_cilint value
	| None ->
	    "exp"
      in
      let str = "case_" ^ suffix in
      Label(freshLabel str,l,false)
  | Default(l) -> Label(freshLabel "switch_default",l,false)
  ) s.labels ; 
  match s.skind with
  | Instr _ | Return _ | Goto _ -> ()
  | Break(l) -> begin try 
                  s.skind <- Goto(break_dest (),l)
                with e ->
                  ignore (error "prepareCFG: break: %a@!" d_stmt s) ;
                  raise e
                end
  | Continue(l) -> begin try
                  s.skind <- Goto(cont_dest (),l)
                with e ->
                  ignore (error "prepareCFG: continue: %a@!" d_stmt s) ;
                  raise e
                end
  | If(e,b1,b2,l) -> xform_switch_block b1 break_dest cont_dest ;
                     xform_switch_block b2 break_dest cont_dest
  | Switch(e,b,sl,l) ->
      (* change
       * switch (se) {
       *   case 0: s0 ;
       *   case 1: s1 ; break;
       *   ...
       * }
       *
       * into:
       *
       * if (se == 0) goto label_0;
       * if (se == 1) goto label_1;
       * ...
       * goto label_default; // If there is a [Default]
       * goto label_break; // If there is no [Default]
       * label_0: s0;
       * label_1: s1; goto label_break;
       * ...
       * label_break: ; // break_stmt
       *
       * The default case, if present, must be used only if *all*
       * non-default cases fail [ISO/IEC 9899:1999, §6.8.4.2, ¶5]. As
       * a result, we test all cases first, and hit 'default' only if
       * no case matches. However, we do not reorder the switch's
       * body, so fall-through still works as expected.
       *
       *)

      let break_stmt = mkStmt (Instr []) in
      break_stmt.labels <- [Label(freshLabel "switch_break",l,false)] ;

      (* To be changed into goto default if there if a [Default] *)
      let goto_break = mkStmt (Goto (ref break_stmt, l)) in

      (* Return a list of [If] statements, equivalent to the cases of [stmt].
       * Use a single [If] and || operators if useLogicalOperators is true.
       * If [stmt] is a [Default], update goto label_break into goto
       * label_default.
       *)
      let xform_choice stmt =
        let cases = List.filter (function Label _ -> false | _ -> true ) stmt.labels in
        try (* is this the default case? *)
          match List.find (function Default _ -> true | _ -> false) cases with
          | Default dl ->
              (* We found a [Default], update the fallthrough goto *)
              goto_break.skind <- Goto(ref stmt, dl);
              []
          | _ -> E.s (bug "Unexpected pattern-matching failure")
        with
        Not_found -> (* this is a list of specific cases *)
          match cases with
          | Case (ce,cl) :: lab_tl ->
              (* assume that integer promotion and type conversion of cases is
               * performed by cabs2cil. *)
              let make_eq exp =  BinOp(Eq, e, exp, typeOf e) in
              let make_or_from_cases =
                List.fold_left
                    (fun pred label -> match label with
                           Case (exp, _) -> BinOp(LOr, pred, make_eq exp, intType)
                         | _ -> E.s (bug "Unexpected pattern-matching failure"))
                    (make_eq ce)
            in
            let make_if_stmt pred cl =
              let then_block = mkBlock [ mkStmt (Goto(ref stmt,cl)) ] in
              let else_block = mkBlock [] in
              mkStmt(If(pred,then_block,else_block,cl)) in
            if !useLogicalOperators then
              [make_if_stmt (make_or_from_cases lab_tl) cl]
            else
              List.map
                (function Case (ce,cl) -> make_if_stmt (make_eq ce) cl
                         | _ -> E.s (bug "Unexpected pattern-matching failure"))
                cases
          | Default _ :: _ | Label _ :: _ ->
              E.s (bug "Unexpected pattern-matching failure")
          | [] -> E.s (bug "Block missing 'case' and 'default' in switch statement")
      in
      b.bstmts <-
        (List.flatten (List.map xform_choice sl)) @
        [goto_break] @
        b.bstmts @
        [break_stmt];
      s.skind <- Block b;
      xform_switch_block b (fun () -> ref break_stmt) cont_dest
  | Loop(b,l,_,_) -> 
          let break_stmt = mkStmt (Instr []) in
          break_stmt.labels <- [Label(freshLabel "while_break",l,false)] ;
          let cont_stmt = mkStmt (Instr []) in
          cont_stmt.labels <- [Label(freshLabel "while_continue",l,false)] ;
          b.bstmts <- cont_stmt :: b.bstmts ;
          let this_stmt = mkStmt 
            (Loop(b,l,Some(cont_stmt),Some(break_stmt))) in 
          let break_dest () = ref break_stmt in
          let cont_dest () = ref cont_stmt in 
          xform_switch_block b break_dest cont_dest ;
          break_stmt.succs <- s.succs ; 
          let new_block = mkBlock [ this_stmt ; break_stmt ] in
          s.skind <- Block new_block
  | Block(b) -> xform_switch_block b break_dest cont_dest

  | TryExcept _ | TryFinally _ -> 
      failwith "xform_switch_statement: structured exception handling not implemented"

end and xform_switch_block b break_dest cont_dest =
  try 
    let rec link_succs sl = match sl with
    | [] -> ()
    | hd :: tl -> (if hd.succs = [] then hd.succs <- tl) ; link_succs tl
    in 
    link_succs b.bstmts ;
    List.iter (fun stmt -> 
      xform_switch_stmt stmt break_dest cont_dest) b.bstmts ;
  with e ->
    List.iter (fun stmt -> ignore
      (warn "prepareCFG: %a@!" d_stmt stmt)) b.bstmts ;
    raise e

(* Enter all the labels in a function into an alpha renaming table to
   prevent duplicate labels when transforming loops and switch
   statements. *)
class registerLabelsVisitor : cilVisitor = object
  inherit nopCilVisitor
  method vstmt { labels = labels } = begin
    List.iter
      (function
           Label (name,_,_) -> A.registerAlphaName labelAlphaTable None name ()
         | _ -> ())
      labels;
    DoChildren
  end
  method vexpr _ = SkipChildren
  method vtype _ = SkipChildren
  method vinst _ = SkipChildren
end

(* prepare a function for computeCFGInfo by removing break, continue,
 * default and switch statements/labels and replacing them with Ifs and
 * Gotos. *)
let prepareCFG (fd : fundec) : unit =
  (* Labels are local to a function, so start with a clean slate by
     clearing labelAlphaTable. Then register all labels. *)
  H.clear labelAlphaTable;
  ignore (visitCilFunction (new registerLabelsVisitor) fd);
  xform_switch_block fd.sbody 
      (fun () -> failwith "prepareCFG: break with no enclosing loop") 
      (fun () -> failwith "prepareCFG: continue with no enclosing loop")
