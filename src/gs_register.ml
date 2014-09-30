open Gs_options
open Slicing
open Gs_printer




(* Computes cfg for all functions and fills in info information on fundec (smaxstmid and sallsmts) *)
let computeCfg () =
    Globals.Functions.iter_on_fundecs
    (
      fun fundec -> 
        Cfg.prepareCFG fundec;
        Cfg.computeCFGInfo fundec false  
    )

  (* Main function *)
  let run () =

     Ast.compute (); 
     if (Ast.is_computed()) then Gs_options.Self.result "AST computed.\n"; 	
     let c_file = Ast.get () in
     Cfg.clearFileCFG c_file;
     computeCfg ();
     let vcgen_results = Vcgen.calculus () in
     let slicing_results = slicing Post_slicing (Vcgen.removeReturnStatement vcgen_results) [Alt_ergo;CVC3;CVC4;Yices] in
     print_slice_results slicing_results


     
let () = Db.Main.extend run 