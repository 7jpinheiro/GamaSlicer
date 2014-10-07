open Gs_options
open Vcgen
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
     let vcgen_results = calculus Sp in
     let slice_g = Slicegraph.createSliceGraph vcgen_results in 
     print_vertex slice_g
     (*let slicing_results = slicing Post_slicing (removeReturnStatement vcgen_results) [Alt_ergo;CVC3;CVC4;Yices] in
     print_slice_results slicing_results
     List.iter (fun x -> print_predicate x.predicate) vcgen_results  *)


     
let () = Db.Main.extend run 