open Cil_types
open Gs_options
open Vcgen
open Slicing
open Gs_printer
open Provers



let parse_slice_type str =
   if (str = "post") then Post_slicing else
   begin
       if(str = "prec") then Prec_slicing else
       begin
           if(str = "spec") then Spec_slicing else
           Gs_options.Self.fatal "Not a type of slice.\n"; 
       end
   end

let get_list_kf () =
    let kf_list = 
       Globals.Functions.fold
       (
          fun kf acc -> kf :: acc  
       ) []
    in
    List.filter Kernel_function.is_definition kf_list 


(* Computes cfg for all functions and fills in info information on fundec (smaxstmid and sallsmts) *)
let computeCfg () =
    Globals.Functions.iter_on_fundecs
    (
      fun fundec -> 
        Cfg.prepareCFG fundec;
        Cfg.computeCFGInfo fundec false  
    )

let slice_fun vc_type fun_dec provers_list =
    let post_condt = fun_dec.post_condition in
    let pre_condt = fun_dec.pre_condition in
    let vcg_wp = fun_dec.vcgen_result_wp in
    let vcg_sp = fun_dec.vcgen_result_sp in
    let sliced_path = 
         begin
            match vc_type with
            | Post_slicing -> 
                            let slice_g = Slicegraph.create_slice_graph vcg_wp in 
                            let slicing_results = slicing vc_type vcg_wp provers_list in
                            let n_slice_g = Slicegraph.add_sliced_edges slicing_results slice_g in 
                            let sliced_path = Slicegraph.slice n_slice_g vcg_wp in
                            List.iter(fun x -> print_why3_term x.po.proof_obligation) vcg_wp;
                            print_slice_results slicing_results;
                            print_vertex slice_g;
                            print_edges slice_g;
                            sliced_path
            | Prec_slicing -> 
                            let slice_g = Slicegraph.create_slice_graph vcg_sp in 
                            let slicing_results = slicing vc_type vcg_sp provers_list in
                            let n_slice_g = Slicegraph.add_sliced_edges slicing_results slice_g in
                            let sliced_path = Slicegraph.slice n_slice_g vcg_sp in
                            List.iter(fun x -> print_why3_term x.po.proof_obligation) vcg_wp;
                            print_slice_results slicing_results;
                            print_vertex slice_g;
                            print_edges slice_g;
                            sliced_path
             | Spec_slicing -> raise (Invalid_argument "Not yet implemented")
    end
    in
    print_path sliced_path


  (* Main function *)
  let run () =

     Ast.compute (); 
     if (Ast.is_computed()) then Gs_options.Self.result "AST computed.\n"; 	
     let c_file = Ast.get () in
     Cfg.clearFileCFG c_file;
     computeCfg ();
     calculus ();
     let provers_list = [Alt_ergo;CVC3;CVC4;Yices] in
     let slice_type = parse_slice_type (Gs_options.SliceType.get()) in
     let kf_list = get_list_kf () in 
     List.iter
     (
       fun kf -> let fun_name = Ast_info.Function.get_name kf.fundec in
                Gs_options.Self.result "Slicing %s\n" fun_name;
                slice_fun slice_type (get_fun kf) provers_list
     ) kf_list
     
     
let () = Db.Main.extend run     