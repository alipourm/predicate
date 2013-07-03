(*
 *
 * Copyright (c) 2011-2012,
 *  Alex Groce          <agroce@gmail.com>
 *  Chaoqiang Zhang     <zhangch@eecs.oregonstate.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)
 
open Pretty
open Cil
open Cfg
open Usedef
open Printf
open String

module E=Errormsg
module H = Hashtbl

let globtable : (stmt ref, stmt ref) H.t = H.create 10000

let sidbase = ref (-1)
let sidnextbase = ref(-1)

let cfginfofile = "cfginfofile"
let blkcountfile = "blockcount"

let nodeid = ref (-1)
let getNextNodeId () = ((nodeid := !nodeid + 1); !nodeid)


let callCilHitCFGNode args = 
    let fdec = emptyFunction "__cil_hit_cfgnode" in
    fdec.svar.vtype <- TFun(voidType, Some [("srcname", charPtrType,[]);("fname",charPtrType,[]);("nid", intType,[]);("stage",intType,[])], false, []);
    Call(None, Lval(Var(fdec.svar),NoOffset),args, locUnknown)
    
let addmap bs news = 
  match bs with
  | [] -> ()
  | x::xs -> match x.labels with
              | [] -> ()
              | _ -> H.add globtable (ref x) (ref news); news.labels <- x.labels
              
let prependInstrToBlk il b =
  (b.bstmts <- let news = (mkStmtOneInstr il) in addmap b.bstmts news; news:: b.bstmts)
   
(* in a CFG, given a statement, if it's the begin node of the CFG, return -1, if it's the end node, return 1, otherwise, return 0*)
let statStatement (s:stmt) = 
    ( match s.preds with
    | [] -> (match s.succs with 
                | [] -> 2
                | _  -> -1 )
    | _  -> (match s.succs with 
                | [] -> 1
                | _  -> 0 )
    )            

let hasLoopFollow(s:stmt) = 
    ( match s.succs with 
        | h::t -> ( let flag = statStatement(h) in (match h.skind with 
                        | Loop(_,_,_,_) -> [h.sid; statStatement(h)]
                        | _ -> [] ) )
        | _ -> []    
    )    
    
let writeStr2File fname content = 
    (let chan = open_out_gen [Open_creat;Open_append] 33188 fname in
        begin
            ignore(fprintf chan "%s" content);
            close_out chan;
        end    )

(*************************************************)

(* print control flow graph (in dot form) for fundec to channel *)
let rec forallStmts (todo) (fd : fundec) = 
  begin
    fasBlock todo fd.sbody;
  end

and fasBlock (todo) (b : block) =
  List.iter (fasStmt todo) b.bstmts

and fasStmt (todo) (s : stmt) =
  begin
    (todo s);
    (*writeStr2File "log.txt" (d_cfgnodelabel s);*)
    match s.skind with
      | Block b -> ((*writeStr2File "log.txt" "a block\n";*) fasBlock todo b)
      | If (_, tb, fb, _) -> 
      ( (*writeStr2File "log.txt" (sprintf "length = %d;" (List.length tb.bstmts) );*) fasBlock todo tb; fasBlock todo fb)
      | Switch (_, b, _, _) -> fasBlock todo b
      | Loop (b, _, _, _) -> fasBlock todo b
      | (Return _ | Break _ | Continue _ | Goto _ | Instr _) -> ()
      | TryExcept _ | TryFinally _ -> E.s (E.unimp "try/except/finally")
  end
;;


(* print out cfg *)
let d_cfgnodename (s : stmt) =
  sprintf "%d" s.sid
let d_cfgedge (src) (dest) =
  sprintf "%s->%s;" (d_cfgnodename src) (d_cfgnodename dest)

let d_cfgnode (s : stmt) =
  sprintf "%s;" (d_cfgnodename s)

let d_cfgnode1tmp (s) (l) =
    String.concat "" (List.map (fun x -> (sprintf "%s" (d_cfgedge s x)) )l)
  
let d_cfgnode1 (s: stmt) =
    d_cfgnode1tmp s s.succs
        
(*let d_var() (s:stmt)*)
let firstnode = ref false
let funcparameters: VS.t ref = ref VS.empty


    
    
let d_node_du (s:stmt) = 
  begin  
    let varUsed, varDefs = Usedef.computeUseDefStmtKind ~acc_used:VS.empty ~acc_defs:VS.empty s.skind in 
    if( (!firstnode) == false ) 
    then 
        begin
            sprintf "%s(%s,|,%s);"
              (d_cfgnodename s)
              (VS.fold (fun x y -> let dd = sprintf "%s," x.vname in String.concat "" [dd;y]) varUsed "")
              (VS.fold (fun x y -> let dd = sprintf "%s," x.vname in String.concat "" [dd;y]) varDefs "")
        end
    else
        begin
        firstnode := false;
        let fulldefs = VS.union varDefs !funcparameters in
        sprintf "%s(%s,|,%s);"
          (d_cfgnodename s)
          (VS.fold (fun x y -> let dd = sprintf "%s," x.vname in String.concat "" [dd;y]) varUsed "")
          (VS.fold (fun x y -> let dd = sprintf "%s," x.vname in String.concat "" [dd;y]) fulldefs "")
        end
  end
  
let printCfgChannel (chan : out_channel) (fd : fundec) =
  let pnode (s:stmt) = fprintf chan "%s" (d_cfgnode s) in
  let pedge (s:stmt) = fprintf chan "%s" (d_cfgnode1 s) in
  let pdu (s:stmt) = fprintf chan "%s" (d_node_du s) in
    begin 
      ignore(fprintf chan "nodes: ");    
      forallStmts pnode fd;
      ignore(fprintf chan "\nedges: ");
      forallStmts pedge fd;  
      ignore(fprintf chan "\nduinfo: ");
      forallStmts pdu fd;
      ignore(fprintf chan "\n");
    end


(*************************************************)
        
let curFile =  ref ""
class pathCovVisitor = object (self) inherit nopCilVisitor

  val mutable curFunc: string = ""

  method vfunc (f ) = 
     sidbase := !sidnextbase+1;
    ( Cil.prepareCFG(f);
      Cil.computeCFGInfo f false;
      curFunc <- f.svar.vname;
      firstnode:=true;
      funcparameters := VS.empty;
      List.iter (fun arg -> funcparameters := VS.add arg !funcparameters) f.sformals;
      
      writeStr2File cfginfofile ("\nfunname: " ^ curFunc ^ "\n");    
      (* export nodes:a;b;c \n edges: a->b; b->c; *)
      let chan = open_out_gen [Open_creat;Open_append] 33188 cfginfofile in
        begin
          printCfgChannel chan f;
          close_out chan;
        end;
        
      DoChildren)
  
  method vstmt(s:stmt) =  
     ( match s.skind with
        | Instr (b) ->
            (if (s.sid >= 0) then
            (let l = ( callCilHitCFGNode [ mkString(!curFile); mkString(curFunc); integer(s.sid); integer( statStatement(s) ) ] )
            in (let smt = mkStmt(Instr(l::b) ) in (smt.labels <- s.labels; ChangeTo smt) )   ) 
            else (let smt = mkStmt(Instr(b)) in ( smt.labels<-s.labels; ChangeTo smt))  );
       | Block( b ) -> 
        (    let extra = hasLoopFollow(s) in 
                begin
                    match extra with
                        | [loopid;loopfollower] -> (prependInstrToBlk
                                                    ( callCilHitCFGNode [ mkString(!curFile); mkString(curFunc); integer(loopid); integer( statStatement(s) ) ]) b )
                        | _ -> ()
                end    ;
            (prependInstrToBlk
            ( callCilHitCFGNode [ mkString(!curFile); mkString(curFunc); integer(s.sid); integer( statStatement(s) ) ]) b ); );  
           DoChildren
       | Loop (b,_,_,_) ->  DoChildren
       | If (_,_,_,_)
       | Return(_,_) 
       | Goto(_,_)        
       ->       
       (if true then (self#queueInstr[callCilHitCFGNode [ mkString(!curFile); mkString(curFunc); integer(s.sid); integer( statStatement(s) ) ]]) else () )    
       ; DoChildren
        
        | _ -> DoChildren          
      )
    (*DoChildren *)
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
                let v = H.find globtable (ref s) in
                  s.labels <- [];
                  DoChildren
                with _ -> DoChildren  
              ) 
end

let feature : featureDescr = 
  { fd_name = "pathCov";
    fd_enabled = ref false;
    fd_description = "generation of code to produce path coverage";
    fd_extraopt = [];
    fd_doit = 
    (function (f: file) ->
     let lwVisitor = new pathCovVisitor in
     ( 
      curFile := f.fileName;
      visitCilFileSameGlobals (lwVisitor :> cilVisitor) f;
      let gotoVisitor = new fixGotoVisitor in
       visitCilFileSameGlobals (gotoVisitor :> cilVisitor) f;
      let goto1Visitor = new fixGoto1Visitor in
       visitCilFileSameGlobals (goto1Visitor :> cilVisitor) f;
       
      ));
    fd_post_check = true;
  } 

