module PredStmt = 
struct 
  open Pretty
  open Cil
  open Printf
  open Common
module H = Hashtbl
module F = Frontc
module E = Errormsg


module StringSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = string
  end )

let writeStr2File fname content = 
  (let chan = open_out_gen [Open_creat;Open_append] 33188 fname in
  begin
    ignore(fprintf chan "%s" content);
    close_out chan;
  end  )

let gcurrFunc = ref ""
let blockid = ref (-1)
let stmttable : (stmt ref, stmt ref) H.t = H.create 10000
let globtable : (varinfo, int) H.t = H.create 100

let preddone = ref (StringSet.empty)

let globid = ref (-1)

let predlist = ref ([])

let passdone = ref false

let getNextGlobId () =
  (globid := (!globid)+1; !globid)

let getNextBlockId () =
  (blockid := (!blockid)+1; !blockid)
    
let expToStr e =
  (Pretty.sprint 4096 (Pretty.dprintf "%a" d_exp e))  
    
let predid = ref (-1)
let getNextPredId () = ((predid := !predid + 1); !predid)
    
let curFile =  ref ""
    
let callCilAddPredValue args = 
    let fdec = emptyFunction "__cil_add_pred_value" in
    fdec.svar.vtype <- TFun(voidType, Some [("id",intType,[]);("pretty",charPtrType,[]);("value",intType,[])], false, []);
    Call(None, Lval(Var(fdec.svar),NoOffset),args, locUnknown)

let callCilBeginPredValues args = 
    let fdec = emptyFunction "__cil_begin_pred_values" in
    fdec.svar.vtype <- TFun(voidType, Some [("id",intType,[]);("srcname", charPtrType,[]);("fname",charPtrType,[])], false, []);
    Call(None, Lval(Var(fdec.svar),NoOffset),args, locUnknown)
    
let mkInstrsStmts sl =
  List.flatten (List.map (fun i -> 
    (match i.skind with 
      Instr il -> il
    | _ -> [])) sl)

let stmtToStr e =
  (Pretty.sprint 4096 (Pretty.dprintf "%a" d_stmt e))  

let prependIl il1 il2 =
  List.flatten (List.map (fun i -> il1 @ [i]) il2)
                
type check = PtrRef of exp | ArrRef of lval

let rec case2if  curfun exp cases =
  match cases with 
  |[] -> ()
  | hl::tl->
      ( let a = List.hd hl.labels  in
      match a  with
  
      | Case (e,l) ->  print_string "case\n"; 
	  predlist :=((curfun,  BinOp(Eq, exp , e, Cil.intType)):: (!predlist));
      | Label (_,_,_) -> print_string "label\n";
	  ()
      |	Default (l) -> print_string "default\n";
	  ()

	  );
      case2if curfun exp tl



let rec collectPointersLhost lhost l =
  match lhost with
  | Var v -> l
  | Mem e -> collectPointers e (PtrRef(e)::l)

and collectPointersOffset offset l =
  match offset with
  | NoOffset -> l
  | Index(e,offset1) -> collectPointers e  (collectPointersOffset offset1 l)
  | Field(f,offset1) -> collectPointersOffset offset1 l
    
and collectPointersLval lval l =
    match lval with
    | (lhost,Index(e2,offset1)) ->
    collectPointersLhost lhost (ArrRef(lval)::(collectPointersOffset offset1 l))
    | (lhost,offset) ->
    collectPointersLhost lhost (collectPointersOffset offset l)
    
and collectPointers e l =
  match e with
  | Const(c) -> l
  | Lval(lval) -> collectPointersLval lval l
  | SizeOf(t) -> l
  | SizeOfE(e1) -> l
  | SizeOfStr(s) -> l
  | AlignOf(t) -> l
  | AlignOfE(e1) -> l
  | UnOp(u,e1,t) -> collectPointers e1 l
  | BinOp(u,e1,e2,t) -> collectPointers e1 (collectPointers e2 l)
  | CastE(t,e1) -> collectPointers e1 l
  | AddrOf(lval) -> collectPointersLval lval l
  | StartOf(lval) -> collectPointersLval lval l
    
let rec makeChecks l =
  match l with 
  | [(PtrRef h)] -> BinOp(Ne, h, integer(0), Cil.intType)
  | (PtrRef h)::t -> BinOp(LAnd,BinOp(Ne, h, integer(0), Cil.intType),makeChecks t, Cil.intType)
  | [(ArrRef h)] -> one
(*
      (match h with 
      | (lhost,Index(e2,offset)) ->
      (Printf.printf "ARRAY = %s\n" (expToStr (Lval(lhost,NoOffset)));
       try 
        (let s = lenOfArray (Some (Lval(lhost,NoOffset))) in
        (Printf.printf "2ARR e = %s length = %d\n" (expToStr (Lval(lhost,NoOffset))) s;
         BinOp(Lt, e2, integer s, Cil.intType)))
      with LenOfArray -> (Printf.printf "2BOMB\n"; zero))
      |     _ -> one)
*)
  | (ArrRef h)::t -> makeChecks t
  | [] -> one
    
    
let rec inScopeLhost lhost cf =
  match lhost with
  | Var v -> inScopeVarinfo v cf
  | Mem e -> false (* inScope e cf *)
    
and inScopeVarinfo v (f, cf) =
  ((v.vglob && ((H.find globtable v) <= !globid)) || (cf == f))
    
and inScopeOffset offset cf =
  match offset with
  | NoOffset -> true
  | Index(e,offset1) -> false (* (inScope e cf) && (inScopeOffset offset1 cf) *)
  | Field(f,offset1) -> false (* inScopeOffset offset1 cf *)
    
and inScopeLval (lhost,offset) cf =
  (inScopeLhost lhost cf) && (inScopeOffset offset cf)
    
and inScope e cf =
  match e with
  | Const(c) -> true
  | Lval(lval) -> inScopeLval lval cf
  | SizeOf(t) -> true
  | SizeOfE(e1) -> inScope e1 cf
  | SizeOfStr(s) -> true
  | AlignOf(t) -> true
  | AlignOfE(e1) -> inScope e1 cf
  | UnOp(u,e1,t) -> inScope e1 cf
  | BinOp(u,e1,e2,t) -> (inScope e1 cf) && (inScope e2 cf)
  | CastE(t,e1) -> inScope e1 cf
  | AddrOf(lval) -> inScopeLval lval cf 
  | StartOf(lval) -> inScopeLval lval cf
    
let rec mapPredCalls (bc, cf, l) =
  match l with
  | (f, p)::t ->
      if (inScope p (f, cf) && (not (StringSet.mem (expToStr p) (!preddone)))) then
    inScopeCalls (bc, cf, p, t)
      else mapPredCalls (bc, cf, t)
  | [] -> []
    
and inScopeCalls (bc, cf, p, t) =
  let h =
    (let cv = collectPointers p [] in
    (if cv == [] then
      (preddone := (StringSet.add (expToStr p) (!preddone));
       mkStmtOneInstr( callCilAddPredValue [integer (getNextPredId()); mkString(expToStr p); p ]))
    else 
      let safe = (makeChecks cv) in
      let safes = mkStmtOneInstr (callCilAddPredValue [integer (getNextPredId()); mkString(expToStr p); p ]) in
      let nsafes = mkStmtOneInstr (callCilAddPredValue [integer (getNextPredId()); mkString(expToStr p); p ]) in
      let b1 = mkBlock [safes] in
      let b2 = mkBlock [nsafes] in
      (preddone := (StringSet.add (expToStr p) (!preddone));
       mkStmt (If (safe, b1, b2, locUnknown))))) in
         h:: mapPredCalls(bc, cf, t)
      
let rec checkOffset cf e =
()
(*
  match e with 
  | (Lval(lhost,Index(e2,offset))) ->
      (try
    (let s = lenOfArray (Some e) in
    (Printf.printf "ARR e = %s length = %d\n" (expToStr e) s;
     predlist := (cf, BinOp(Lt, e2, integer s, Cil.intType))::(!predlist)))
      with LenOfArray -> (Printf.printf ("BOMB\n")))
  | _ -> ()
*)
  
class viFinderClass br = object(self)
      inherit nopCilVisitor
      
      method vvrbl vi' = 
      (br := true;
      SkipChildren)
      
end
      
let expContainsVi e  =
     let br = ref false in
     let vis = new viFinderClass  br in
     ignore(visitCilExpr vis e);
     !br
     
let rec print_predlist p = 
  match p with
  | [] -> ();
  | hd::tl -> print_string (fst hd);print_string " ";print_string (expToStr(snd hd)); print_string "\n";print_predlist tl
  

let mkPredCalls bc cf l =
  (preddone := StringSet.empty;
   print_string "startedPredCalls-----\n";
   print_int bc;
   print_string cf;
   print_string "\n";
   print_predlist l;
   print_string "\n";
   
   mkStmtOneInstr (callCilBeginPredValues [integer(bc); mkString(!curFile); mkString(cf) ]))::mapPredCalls(bc, cf, l)


let callArg args = 
    let fdec = emptyFunction "__cil_update_input1" in
  (*fdec.svar.vtype <- TFun(voidType, Some [("id",intType,[]);("pretty",charPtrType,[]);("value",intType,[])], false, []);*)
    Call(None, Lval(Var(fdec.svar),NoOffset),args, locUnknown)



let mkArgAssignmentCall f=
  print_string (f.svar.vname);
 
  let  args = f.sformals in
  match args with
  | [] -> print_string("\nError: main function does not have any arguments! "); dummyStmt
  | hd::snd::tail -> 
      let fdec = emptyFunction "__cil_update_input2" in
      (*fdec.svar.vtype <- TFun(voidType, Some [("id",intType,[]);("pretty",charPtrType,[]);("value",intType,[])], false, []);*)
      let call = Call(None, Lval(Var(fdec.svar),NoOffset),
		      [Lval(Var(hd),NoOffset);Lval(Var(snd),NoOffset)], locUnknown)
      in
      mkStmt (Instr [call])
  | hd::tail -> let  
  	argname = hd.vname in
   (*    Call(None, Lval(Var(f.svar),NoOffset),args, locUnknown)*)

        mkStmt (Instr [callArg [Lval(Var(hd),NoOffset)]]) 
          

let addmap bs news = 
  match bs with
  | [] -> ()
  | x::xs -> match x.labels with
              | [] -> ()
              | _ -> H.add stmttable (ref x) (ref (List.hd news)); (List.hd news).labels <- x.labels
              
              
let prependStmtListToBody sl b =
  (*let isl = mkInstrsStmts sl in*)

  b.bstmts <- (List.flatten (List.map (fun i -> 
    (match i.skind with
      Instr il -> let kk = mkStmt (Instr (List.flatten (List.map (fun j ->
	(mkInstrsStmts (mkPredCalls (getNextBlockId()) !gcurrFunc !predlist)) @ [j] ) il))) 
        in kk.labels <- i.labels; [kk]
    | _ -> (mkPredCalls (getNextBlockId()) !gcurrFunc !predlist) @ [i])) b.bstmts))

class fixGotoVisitor = object (self) inherit nopCilVisitor 
  method vstmt(s) = 
    (match s.skind with
      | Goto (t,p) -> (try 
                         let v = H.find stmttable t in
                         ChangeTo (mkStmt (Goto (v, p)) )
                      with _ -> SkipChildren )
      | _ -> DoChildren
    )
end

class preMainVisitor = object(self) inherit nopCilVisitor
  method vfunc(f) =
    if ((compare f.svar.vname  "main") == 0) then 
      	(f.sbody.bstmts <- 
	   (mkArgAssignmentCall f)::f.sbody.bstmts) 
    else ();
    DoChildren
end

class fixGoto1Visitor = object (self) inherit nopCilVisitor 
  method vstmt(s) = 
    match s.labels with
      | [] -> DoChildren
      | _  -> ( try 
                let v = H.find stmttable (ref s) in
                  s.labels <- [];
                  DoChildren
                with _ -> DoChildren  
              ) 
end
    
class predStmtCovVisitor = object (self) inherit nopCilVisitor   

  val mutable curFunc: string = ""
      
  method vfunc (f ) = 
    curFunc <- f.svar.vname;
    gcurrFunc := f.svar.vname;
    DoChildren 
      
  method vglob (g) =
    ((match g with
    | GVarDecl (v, l) ->  (H.add globtable v (getNextGlobId()))
    | GVar (v, i, l) -> (H.add globtable v (getNextGlobId()))
    | _ -> ());
     DoChildren)
      
(*  method vexpr e =
    (Printf.printf "EXP: %s  " (expToStr (e));
     (try
       (let s = lenOfArray (Some (e))
       in Printf.printf "Size: %d\n" s)
     with LenOfArray -> Printf.printf "No length\n");
     DoChildren)
*)

  method vexpr(e) =
    ((match e with
    | (Lval(Mem e1, offset)) -> (predlist := (curFunc, BinOp(Ne, e1, integer 0, Cil.intType))::(!predlist);
                 checkOffset curFunc e)
    | (Lval(e1,offset)) -> checkOffset curFunc e
    | _ -> ());
     DoChildren)
      
  method vstmt(s) =
    ((if (not (!passdone)) then
      (match s.skind with
      | If(e,b1,b2,loc) ->
          (predlist := (curFunc,e)::(!predlist))
(**      | Return ( eo, loc) ->
 *	  
 *	  let (e, b) = (isConditional eo) in
 *	  if (b)
 *	  then 
 *	    (predlist := (curFunc,e)::(!predlist))
 *	  else
 *	    ()
 *)	    
      |	Switch (exp, b, labels, loc) ->
	  case2if curFunc exp labels


      | _ -> ()

)
    else ()); 
     DoChildren)
      
  method vblock(b) = 
    if ((!passdone) || (hasAttribute "predCover" b.battrs) ) then
      (if List.length b.bstmts > 0 then begin
        (match b.bstmts with
        | s::t ->
            (match s.skind with
            | Instr [Call(None,f,_,_)] ->
                (match f with
                | Lval(Var(fdecsvar),NoOffset) -> 
            if ((compare fdecsvar.vname "__cil_add_pred_value") == 0) then ()
            else prependStmtListToBody 0 b
        | _ -> prependStmtListToBody 0 b)
            | _ -> prependStmtListToBody 0 b)
        | _ -> prependStmtListToBody 0 b) end
      else (); )

    else ();
    DoChildren
      
end


let rec dumpPreds predFile pred_list ord =
  match pred_list with
  | [] ->()
  | hd::tl -> output_string predFile ((string_of_int ord)^"%%");  output_string predFile ((fst hd)^"%%");
      output_string predFile (expToStr (snd hd)^"%%\n"); dumpPreds predFile tl (ord+1);;


let instStPred f =
  let lwVisitor = new predStmtCovVisitor in
      begin 
	curFile := f.fileName;
	visitCilFileSameGlobals (lwVisitor :> cilVisitor) f;
	
	predlist := List.filter (fun e -> expContainsVi (snd e) ) !predlist;
	passdone := true;
	globid := ( -1 );
	visitCilFileSameGlobals (lwVisitor :> cilVisitor) f
      end;
  let gotoVisitor = new fixGotoVisitor in
  visitCilFileSameGlobals (gotoVisitor :> cilVisitor) f;
  let goto1Visitor = new fixGoto1Visitor in
       visitCilFileSameGlobals (goto1Visitor :> cilVisitor) f;
  print_string "applying preMain";
  let vis = new preMainVisitor in
  visitCilFileSameGlobals (vis :> cilVisitor) f;
  let f = open_out "stmtpredcount" in
  output_string f (string_of_int(!predid+1));
  (close_out f);
  let predfile = open_out "__predicates" in
  dumpPreds predfile !predlist 0; 
  (close_out predfile);;



let parseOneFile (fname: string) : Cil.file =
  let cabs, cil = F.parse_with_cabs fname () in
  Rmtmps.removeUnusedTemps cil;
  print_string cil.fileName;
  print_string "in parse predStmt\n";
  instStPred cil;
  cil
;;
    


(*let outFile : string ref = ref "t.c.cc"*)

let outputFile (f : Cil.file) : unit =
 (* if !O.outFile <> "" then*)
  try
    let c = open_out !Common.outFile in
    
    Cil.print_CIL_Input := false;
    Stats.time "printCIL" 
      (Cil.dumpFile (!Cil.printerForMaincil) c !Common.outFile) f;
    close_out c
  with _ ->
    E.s (E.error "Couldn't open file %s" !Common.outFile)





end;;




(**
 *let feature : featureDescr = 
 *  { fd_name = "predStmtCov";
 *   fd_enabled = ref false;
 *   fd_description = "generation of code to produce predicate\
   coverage at state ment level";
 *   fd_extraopt = [];
 *   fd_doit = 
 *   (function (f: file) ->
 *     let lwVisitor = new predStmtCovVisitor in
 *     ( 
 *     curFile := f.fileName;
 *     visitCilFileSameGlobals (lwVisitor :> cilVisitor) f;
      
 *     predlist := List.filter (fun e -> expContainsVi (snd e) ) !predlist;
            
 *     passdone := true;
 *     globid := ( -1 );
 *     visitCilFileSameGlobals (lwVisitor :> cilVisitor) f);
 *     let gotoVisitor = new fixGotoVisitor in
 *      visitCilFileSameGlobals (gotoVisitor :> cilVisitor) f;
 *     let goto1Visitor = new fixGoto1Visitor in
 *      visitCilFileSameGlobals (goto1Visitor :> cilVisitor) f;
 *      
 *     let f = open_out "stmtpredcount" in
 *         output_string f (string_of_int(!predid+1));
 *       (close_out f);
 *   );
 *   fd_post_check = true;
 *  } 
*)
