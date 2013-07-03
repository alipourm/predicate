open PredStmt
open BranchCov
open Common

let non_fun s  =
  print_string "Wrong argument!"

let main =
 (* outputFile (parseOneFile "t.c");*)
   let argDescr =  [
(* "-instPr", Arg.String (fun x -> outputFile (parseOneFile x)),
		    " instruments <file> for predicate coverage.";
*)		 
   "-instStPr", Arg.String (fun x -> PredStmt.outputFile (PredStmt.parseOneFile x)),
		    " instruments <file> for statement predicate coverage. INACTIVE";

		    "-instBranch", Arg.String (fun x -> BranchCov.outputFile (BranchCov.parseOneFile x)),
		    " instruments <arg> for branch coverage. INACTIVE";

		    "-o", Arg.String (fun x -> Common.outFile :=  x),
		    " determines the output file." 
	  ] 
  in
  Arg.parse (Arg.align argDescr) non_fun "this is a tool for instumenting c programs."
  ;;

main;;
