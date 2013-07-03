
CIL=/usr/local/lib/ocaml/3.12.1/cil
common: common.ml
	ocamlopt -c  common.ml

pred: predCov.ml
	echo Compiling pred
	ocamlopt -c -I $(CIL) predCov.ml
	echo Compiled!
	echo Liking pred
	ocamlopt -ccopt -L$(CIL) -o mainPred  common.cmx  unix.cmxa str.cmxa nums.cmxa   $(CIL)/cil.cmxa predCov.cmx
echo File Made!


predStmtCov:

	echo Compiling predSt
	ocamlopt -c -I $(CIL) predStmtCov.ml
	echo Compiled!
	echo Linking predSt
	ocamlopt -ccopt -L$(CIL) -o predSt common.cmx  unix.cmxa str.cmxa nums.cmxa   $(CIL)/cil.cmxa predStmtCov.cmx
	echo File Made!

predStmt:
	echo Compiling predStmt
	ocamlopt -c -I $(CIL) predStmt.ml
	echo Compiled!

	echo Linking predStmt
	ocamlopt -ccopt -L$(CIL) -o predSt common.cmx  unix.cmxa str.cmxa nums.cmxa   $(CIL)/cil.cmxa predStmt.cmx
	echo File Made!

branchStmt:
	echo Compiling branchStmt
	ocamlopt -c -I $(CIL) branchCov.ml
	echo Compiled!

	echo Linking predStmt
	ocamlopt -ccopt -L$(CIL) -o branchCov common.cmx  unix.cmxa str.cmxa nums.cmxa   $(CIL)/cil.cmxa predStmt.cmx
	echo File Made!



all:
	echo Compiling Main
	ocamlopt -c -I $(CIL)   main.ml

	echo Linking Main
	ocamlopt -ccopt -L$(CIL) -o inst_osu common.cmx  unix.cmxa str.cmxa nums.cmxa   $(CIL)/cil.cmxa predStmt.cmx branchCov.cmx main.cmx 
	echo File Made!






