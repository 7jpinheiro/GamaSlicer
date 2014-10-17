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
     let vcl = removeReturnStatement vcgen_results in
     let slice_g = Slicegraph.create_slice_graph vcl in 
     let slicing_results = slicing Post_slicing  vcl [Alt_ergo;CVC3;CVC4;Yices] in
     let n_slice_g = Slicegraph.add_sliced_edges slicing_results slice_g in 
     let sliced_path = Slicegraph.slice n_slice_g vcl in
     print_slice_results slicing_results;
     List.iter(fun x -> print_statement x.statement) vcl;
     print_vertex slice_g;
     print_edges slice_g;
     print_path sliced_path
     
let () = Db.Main.extend run     