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
open Printf
module H = Hashtbl

let globtable : (stmt ref, stmt ref) H.t = H.create 10000

let blockid = ref (-1)

let getNextBlockId () =
  (blockid := (!blockid)+1; !blockid)

let callCilHitBlock args = 
    let fdec = emptyFunction "__cil_hit_block" in
    fdec.svar.vtype <- TFun(voidType, Some [("srcname", charPtrType,[]);("fname",charPtrType,[]);("bid", intType,[])], false, []);
    Call(None, Lval(Var(fdec.svar),NoOffset),args, locUnknown)

let addmap bs news = 
  match bs with
  | [] -> ()
  | x::xs -> match x.labels with
              | [] -> ()
              | _ -> H.add globtable (ref x) (ref news); news.labels <- x.labels

(*let prependInstrListToBody il b =
  List.iter (fun i -> b.bstmts <- let news = (mkStmtOneInstr i) in addmap b.bstmts news; news:: b.bstmts) 
    (List.rev il)*)
    
let prependInstrToBlk il b =
  (b.bstmts <- let news = (mkStmtOneInstr il) in addmap b.bstmts news; news:: b.bstmts)

let writeStr2File fname content = 
  (let chan = open_out_gen [Open_creat;Open_wronly] 33188 fname in
    begin
      ignore(fprintf chan "%s" content);
      close_out chan;
    end  )
  
let curFile =  ref ""
class blockCovVisitor = object (self) inherit nopCilVisitor

  val mutable curFunc: string = ""
  
  method vfunc (f ) = 
    ( curFunc <- f.svar.vname;   
      DoChildren)
      
  method vblock(b) = 
      (if List.length b.bstmts > 0 then begin
           prependInstrToBlk
          ( callCilHitBlock [(mkString !curFile); (mkString curFunc); (integer(getNextBlockId()))] ) b ; end
      else (); );

  DoChildren

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
  { fd_name = "blockCov";
    fd_enabled = ref false;
    fd_description = "generation of code to produce block coverage";
    fd_extraopt = [];
  fd_doit = 
    (function (f: file) ->
     let lwVisitor = new blockCovVisitor in
     ( 
    curFile := f.fileName;

    visitCilFileSameGlobals (lwVisitor :> cilVisitor) f;
    
    let gotoVisitor = new fixGotoVisitor in
     visitCilFileSameGlobals (gotoVisitor :> cilVisitor) f;
    let goto1Visitor = new fixGoto1Visitor in
     visitCilFileSameGlobals (goto1Visitor :> cilVisitor) f;
     
    writeStr2File "blockcount" (string_of_int((!blockid)+1));
      ));
    fd_post_check = true;
  } 

