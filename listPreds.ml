
open Pretty
open Cil
open Printf
module E = Errormsg
module F = Frontc


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
  
let expToStr e =
  (Pretty.sprint 4096 (Pretty.dprintf "%a" d_exp e))  

let blockid = ref (-1)
let stmttable : (stmt ref, stmt ref) H.t = H.create 10000
let globtable : (varinfo, int) H.t = H.create 100

let preddone = ref (StringSet.empty)

let curFile2 = ref ("")


let rec print_list l = match l with  
[] -> ()
| e::l -> print_string e ; print_string " " ; print_list l




let rec condIn_St (st : stmt) =
  match stmt.stkind with
  | If(cond, b1,b2,loc) -> 
 (**     E.log "cond \n " ;
  *    Printf.printf "***Exp= %s***\n" (expToStr(cond));
  *    extractConditionals b1.bstmts; extractConditionals b2.bstmts;
  *)    
 |Block _
  |Loop (_, _, _, _)
  |Switch (_, _, _, _)
  |Continue _
  |Break _
  |Goto (_, _)
  |Return (_, _)
  |Instr _
  |TryExcept (_, _, _, _)
  |TryFinally (_, _, _) -> ()
	;;
	


let condInBlock (b:block) =
  
  




let rec condIn_St_List (st_list: stmt list) =
  match st_list  with
  | [] -> ()
  | head::tail -> condIn_st head;
    	  (** If(cond, b1,b2,loc) ->
	   * E.log "cond \n " ;
	   * Printf.printf "***Exp= %s***\n" (expToStr(cond));
	   * condIn_block b1; condIn_block b2;
	   *)
     
      condIn_St_List tail;      
;;

(* process individual*) 
let processg i =
  match i with  
  |   GFun (f, l) -> print_string ("function found " ^ f.svar.vname ^ "\n"); extractConditionals f.sbody.bstmts;
  | _ -> ();;







let rec processIt gl = 
  match gl with 
  |  [] -> ()
  | e::l -> processg e; processIt l;;


let parseOneFile (fname: string) : Cil.file =
  let cabs, cil = F.parse_with_cabs fname () in
(*Rmtmps.removeUnusedTemps cil;*)
  E.log  "Mordi?!\n";
  print_string cil.fileName;
  let k = cil.globals in processIt k;
 
  cil;;

parseOneFile ("t.c");;
