open Pretty
open Cil
open Printf

module C = Cil
module F = Frontc
module E = Errormsg

module S = String
module H = Hashtbl

module StringSet = Set.Make( 
  struct
    let compare = Pervasives.compare
    type t = string
  end )

let writeStr2File fname content = 
  (let chan = open_out_gen [Open_creat;Open_wronly; Open_append; Open_text] 33188 fname in
  begin
    ignore(fprintf chan "%s" content);
    close_out chan;
  end  )
  
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

let digitToStr d =
  match d with
  | 0 -> "0"
  | 1 -> "1"
  | 2 -> "2"
  | 3 -> "3"
  | 4 -> "4"
  | 5 -> "5"
  | 6 -> "6"
  | 7 -> "7"
  | 8 -> "8"
  | 9 -> "9"
  | _->  "Error"

let rec intToStr n =
  match n/10 with
  | 0 -> digitToStr (n mod 10)
  | _ -> (intToStr (n/10))^( digitToStr (n mod 10))
    
let curFile =  ref ""
    
(* create a statement to call function fname 
 * with types argType and arguments args *)
let callCilAddPredValue args = 
    let fdec = emptyFunction "__cil_add_pred_value" in
    fdec.svar.vtype <- TFun(voidType, Some [("id",intType,[]);("pretty",charPtrType,[]);("value",intType,[])], false, []);
    Call(None, Lval(Var(fdec.svar),NoOffset),args, locUnknown)

let callCilBeginPredValues args = 
    let fdec = emptyFunction "__cil_begin_pred_values" in
    fdec.svar.vtype <- TFun(voidType, Some [("id",intType,[]);("srcname", charPtrType,[]);("fname",charPtrType,[])], false, []);
    Call(None, Lval(Var(fdec.svar),NoOffset),args, locUnknown)

let addmap bs news = 
  match bs with
  | [] -> ()
  | x::xs -> match x.labels with
              | [] -> ()
              | _ -> H.add stmttable (ref x) (ref (List.hd news)); (List.hd news).labels <- x.labels
              
let prependStmtListToBody il b =
  (addmap b.bstmts il;
  List.iter (fun i -> b.bstmts <- i :: b.bstmts) 
    (List.rev il) )   
    
type check = PtrRef of exp | ArrRef of lval

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
  | Question(e1, e2, e3, t) -> collectPointers e1 (collectPointers e2 (collectPointers e3 l))
   
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
      |    _ -> one)
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
  | Question(e1, e2, e3, t) -> (inScope e1 cf) && (inScope e2 cf) && (inScope e3 cf)
    
   
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

      
let mkPredCalls bc cf l =
  (preddone := StringSet.empty;
   mkStmtOneInstr (callCilBeginPredValues [integer(bc); mkString(!curFile); mkString(cf) ]))::mapPredCalls(bc, cf, l)
(* unused*)
let processLetter l =
  match l with
  | '.' -> '_'
  | '\\' -> '_'
  | _-> l



 
let locToStr loc = "l" ^"_"^ ( intToStr( loc.line)) 



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



 
class fixSwitchVisitor = object (self) inherit nopCilVisitor
 
   method vstmt s =
      match s.skind with
      |	Switch (e, body, cases, l) ->
	 (*case2if e cases 0;*)
	 
	  SkipChildren
      |	_ -> DoChildren
	  
	  (*ChangeTo (mkStmt (If (e, body,)))*)
(*	  xform_switch_stmt s break_dest cont_dest*)
     
end

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
   
let isConditional e =
match e with 
| BinOp (op, _,_,_)
    -> ( match op  with
    | Lt                                  (** <  (arithmetic comparison) *)
    | Gt                                  (** >  (arithmetic comparison) *)  
    | Le                                  (** <= (arithmetic comparison) *)
    | Ge                                  (** >=  (arithmetic comparison) *)
    | Eq                                  (** == (arithmetic comparison) *)
    | Ne                                  (** != (arithmetic comparison) *)           -> true
    | _ -> false 
	  ) 
  | _ -> false


let isConditional eo =
match eo with
| None -> zero,false
| Some e -> e ,( isConditional e)

(**
 *module A = Alpha

 *let labelAlphaTable : (string, unit A.alphaTableData ref) H.t =
 * H.create 11


 *let freshLabel (base:string) =
  *fst (A.newAlphaName labelAlphaTable None base ())

 *xform_switch_stmt s break_dest cont_dest
**)
class predCovVisitor = object (self) inherit nopCilVisitor
    
  val mutable curFunc: string = ""
      
  method vfunc (f ) = 
    curFunc <- f.svar.vname;
    DoChildren 
      
  method vglob (g) =
    ((match g with
    | GVarDecl (v, l) ->  (H.add globtable v (getNextGlobId()))
    | GVar (v, i, l) -> (H.add globtable v (getNextGlobId()))
    | _ -> ());
     DoChildren)
      
(*  method vexpr e =
 *   (Printf.printf "EXP: %s  " (expToStr (e));
 *    (try
 *      (let s = lenOfArray (Some (e))
 *      in Printf.printf "Size: %d\n" s)
 *    with LenOfArray -> Printf.printf "No length\n");
 *    DoChildren)
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
      | Return ( eo, loc) ->
	  
	  let (e, b) = (isConditional eo) in
	  if (b)
	  then 
	    (predlist := (curFunc,e)::(!predlist))
	  else
	    ()
	    
      |	Switch (exp, b, labels, loc) ->
	  case2if curFunc exp labels
      |	_ -> ()
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
		    else prependStmtListToBody (mkPredCalls (getNextBlockId()) curFunc !predlist) b
		| _ -> prependStmtListToBody (mkPredCalls (getNextBlockId()) curFunc !predlist) b)
            | _ -> prependStmtListToBody (mkPredCalls (getNextBlockId()) curFunc !predlist) b)
        | _ -> prependStmtListToBody (mkPredCalls (getNextBlockId()) curFunc !predlist) b) end
      else (); )
    else ();
    DoChildren
  end

let rec print_list l = 
    match l with
  | []-> print_string "Nothing\n";();
  | head:: tail -> print_string "SOME\n";  print_string (expToStr (snd  head)); print_list tail

let inst_for_pred f =
(*  function (f: file) ->*)
  print_string "in\n";
  let lwVisitor = new predCovVisitor in
  (
  print_string "I'm here";
  curFile := f.fileName;
  visitCilFileSameGlobals (lwVisitor :> cilVisitor) f;
  predlist := List.filter (fun e -> expContainsVi (snd e) ) !predlist;
  print_list !predlist;
  let fp=open_out "blockdiffpred" in
  output_string fp (string_of_int(List.length !predlist));
  (close_out fp);
   
  passdone := true;
  globid := ( -1 );
  visitCilFileSameGlobals (lwVisitor :> cilVisitor) f);   
  let switchVisitor = new fixSwitchVisitor in 
   visitCilFileSameGlobals (switchVisitor :> cilVisitor) f;
  let gotoVisitor = new fixGotoVisitor in
  visitCilFileSameGlobals (gotoVisitor :> cilVisitor) f;
  let goto1Visitor = new fixGoto1Visitor in
  visitCilFileSameGlobals (goto1Visitor :> cilVisitor) f;
  let f = open_out "blockpredcount" in
  output_string f (string_of_int(!predid+1));
  (close_out f)



let outFile : string ref = ref "t.c.cc"


let parseOneFile (fname: string) : Cil.file =
  let cabs, cil = F.parse_with_cabs fname () in
 
  Rmtmps.removeUnusedTemps cil;
  print_string cil.fileName;
  print_string "in parse\n";
  print_string ("outfile =   "^ !outFile);
  inst_for_pred cil;
  cil
 
  
 

let outputFile  (f : Cil.file) : unit =
 (* if !O.outFile <> "" then*)
  try
    let c = open_out !outFile in
    
    Cil.print_CIL_Input := false;
    Stats.time "printCIL" 
      (Cil.dumpFile (!Cil.printerForMaincil) c !outFile) f;
    close_out c
  with _ ->
    E.s (E.error "Couldn't open file %s" !outFile)


let non_fun s  =
  print_string "wrong argument!"

let main =
 (* outputFile (parseOneFile "t.c");*)
  print_string "done\n";
  let argDescr =  [ "-instPr", Arg.String (fun x -> outputFile (parseOneFile x)),
		    " instruments <file> for predicate coverage.";
		    "-instStPr", Arg.String (fun x -> outputFile (parseOneFile x)),
		    " instruments <file> for statement predicate coverage. INACTIVE";
		    "-instBranch", Arg.String (fun x -> outputFile (parseOneFile x)),
		    " instruments <arg> for branch coverage. INACTIVE";
		    "-o", Arg.String (fun x -> outFile :=  x),
		    " determines the output file." 
		  ] 
  in
  Arg.parse (Arg.align argDescr) non_fun "this is a tool for instumenting c programs."
  ;;

main;;







(**
 *   
 *
 * let feature : featureDescr = 
 *  { fd_name = "predCov";
 *   fd_enabled = ref false;
 *   fd_description = "generation of code to produce predicate coverage at block level";
 *   fd_extraopt = [];
 *   fd_doit = 
 *   (function (f: file) ->
 *     let lwVisitor = new predCovVisitor in
 *     ( 
 *     curFile := f.fileName;
 *
 *     visitCilFileSameGlobals (lwVisitor :> cilVisitor) f;
 *     
 *     predlist := List.filter (fun e -> expContainsVi (snd e) ) !predlist;
 *     let fp=open_out "blockdiffpred" in
 *     output_string fp (string_of_int(List.length !predlist));
 *     (close_out fp);

 *     passdone := true;
 *     globid := ( -1 );
     
 *     visitCilFileSameGlobals (lwVisitor :> cilVisitor) f);   
      
 *     let gotoVisitor = new fixGotoVisitor in
 *     visitCilFileSameGlobals (gotoVisitor :> cilVisitor) f;
 *     let goto1Visitor = new fixGoto1Visitor in
 *     visitCilFileSameGlobals (goto1Visitor :> cilVisitor) f;
       
  *    let f = open_out "blockpredcount" in
  *    output_string f (string_of_int(!predid+1));
  *    (close_out f);
  *  );       
      
  *  fd_post_check = true;
  *} 
 **)
