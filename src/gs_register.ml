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
     let vcgen_results = calculus Wp in
     let vcl = removeReturnStatement vcgen_results in
     let slice_g = Slicegraph.createSliceGraph vcl in 
     let slicing_results = slicing Post_slicing  vcl [Alt_ergo;CVC3;CVC4;Yices] in
     let n_slice_g = Slicegraph.addSlicedEdges slicing_results slice_g in 
     print_slice_results slicing_results; 
     print_edges slice_g

let () = Db.Main.extend run 