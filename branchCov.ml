module BranchCov =
struct  
open Pretty
open Cil
open Common
open Cfg
module E = Errormsg

open PredStmt
module F = Frontc
  
module H = Hashtbl

let globtable : (stmt ref, stmt ref) H.t = H.create 10000

let branchid = ref (-1)

let getNextBranchId () =
  (branchid := (!branchid)+1; !branchid)

let callCilHitBranch args = 
    let fdec = emptyFunction "__cil_hit_branch" in
    fdec.svar.vtype <- TFun(voidType, Some [("srcname", charPtrType,[]);("fname",charPtrType,[]);("bid", intType,[])], false, []);
    Call(None, Lval(Var(fdec.svar),NoOffset),args, locUnknown)

let addmap bs news = 
  match bs with
  | [] -> ()
  | x::xs -> match x.labels with
              | [] -> ()
              | _ -> H.add globtable (ref x) (ref news); news.labels <- x.labels
              
let prependInstrToBlk il b =
  (b.bstmts <- let news = (mkStmtOneInstr il) in addmap b.bstmts news; news:: b.bstmts)

let writeStr2File fname content = 
  (let chan = open_out_gen [Open_creat;Open_wronly] 33188 fname in
    begin
      ignore(fprintf chan "%s" content);
      close_out chan;
    end  )

let curFile =  ref ""
    
class branchCovVisitor = object (self) inherit nopCilVisitor

  val mutable curFunc: string = "" 
    

    method vfunc (f ) = 
    ( curFunc <- f.svar.vname;
      (*ChangeTo (Cfg.cfgFun f);*)
     DoChildren;)
      
  method vstmt(s) =
    ((match s.skind with
    | If(e,b1,b2,loc) ->
  ((prependInstrToBlk 
      (callCilHitBranch [(mkString !curFile); (mkString curFunc); (integer(getNextBranchId()))]) b1);
   (prependInstrToBlk 
      (callCilHitBranch [(mkString !curFile); (mkString curFunc); (integer(getNextBranchId()))]) b2);
   ); 

    | _ -> ()); 
    
  DoChildren)

end

class fixGotoVisitor = object (self) inherit nopCilVisitor 
  method vstmt(s) = 
    (match s.skind with
      | Goto (t,p) -> (try 
                         let v = H.find globtable t in
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
(*                let v = H.find globtable (ref s) in *)
                  s.labels <- [];
                  DoChildren
                with _ -> DoChildren  
              ) 
end


let inst_branch f =
  let lwVisitor = new branchCovVisitor in
      begin 
	curFile := f.fileName;
	visitCilFileSameGlobals (lwVisitor :> cilVisitor) f;
      end;
  let gotoVisitor = new fixGotoVisitor in
  visitCilFileSameGlobals (gotoVisitor :> cilVisitor) f;
  let goto1Visitor = new fixGoto1Visitor in
       visitCilFileSameGlobals (goto1Visitor :> cilVisitor) f;
  print_string "applying preMain";
  let vis = new PredStmt.preMainVisitor in
  visitCilFileSameGlobals (vis :> cilVisitor) f;;



let parseOneFile (fname: string) : Cil.file =
  let cabs, cil = F.parse_with_cabs fname () in
  Rmtmps.removeUnusedTemps cil;
  print_string cil.fileName;
  print_string "In parse branchCov\n";
 (* !Cfg.computeFileCFG cil;*)
  inst_branch(cil);
  cil
;;
    
    
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

(*
let feature : featureDescr = 
  { fd_name = "branchCov";
    fd_enabled = ref false;
    fd_description = "generation of code to produce branch coverage";
    fd_extraopt = [];
  fd_doit = 
    (function (f: file) ->
     let lwVisitor = new branchCovVisitor in
     ( 
     curFile := f.fileName;   
     visitCilFileSameGlobals (lwVisitor :> cilVisitor) f;
     let gotoVisitor = new fixGotoVisitor in
       visitCilFileSameGlobals (gotoVisitor :> cilVisitor) f;
     let goto1Visitor = new fixGoto1Visitor in
       visitCilFileSameGlobals (goto1Visitor :> cilVisitor) f;
     
     writeStr2File "branchcount" (string_of_int((!branchid)+1));
      ));
    fd_post_check = true;
  } 

*)
