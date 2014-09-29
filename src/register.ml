open Vcgen
open Slicing
open Gs_printer



  (* Main function *)
  let run () =

     Ast.compute (); 
     if (Ast.is_computed()) then Towhy3.Self.result "AST computed.\n"; 	
     let c_file = Ast.get () in
     Cfg.clearFileCFG c_file;
     computeCfg ();
     let vcgen_results = calculus () in
     let slicing_results = slicing Post_slicing (removeReturnStatement vcgen_results) [Alt_ergo;CVC3;CVC4;Yices] in
     print_slice_results slicing_results


     
let () = Db.Main.extend run 