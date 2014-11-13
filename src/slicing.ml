open Cil_types
open Vcgen
open Provers
open Why3

type assert_slicing_type =
| Post_slicing (* Postcondition-based Slicing *)
| Prec_slicing (* Precondition-based Slicing *)
| Spec_slicing (* Specification-based Slicing *)

type slicing_result =
{
  mutable stmt_1 : stmt ;
  mutable stmt_2 : stmt ;                       (* The statement  *)
  mutable formula : Term.term;                  (* The statement is LoopS, if contains a Loop with one block *)
  mutable prover_result: prover_result list ;   (* The statement is LoopS, if contains a Loop with one block *)
  mutable slicing_type: assert_slicing_type;    (* The statement is LoopS, if contains a Loop with one block *)
}


let comp_wp = Hashtbl.create 257

let add_comp_wp stmt vcgen =
  Hashtbl.add comp_wp stmt.sid vcgen

let get_comp_wp stmt  =
  try
    Hashtbl.find comp_wp stmt.sid
  with Not_found ->
    Gs_options.Self.fatal "Comp wp not found" 


let print_why3_term_aux term =
  Gs_options.Self.result "Why3 Formula: %a\n" Pretty.print_term term

let print_aux stmt1 stmt2 = 
 Gs_options.Self.result "%d -> %d\n" stmt1.sid stmt2.sid


let my_tail l =
  match l with
  | [] -> []
  | x::y -> y


let my_head l =
  match l with
  | [] -> []
  | x::y -> x
  

let is_not_simple_type vcgen_result =
  match vcgen_result.stype with
  | SimpleS -> false
  | _ -> true

let build_imp slicing_type elem1 elem2 =
     match slicing_type with
      |Post_slicing -> let po1 = get_po elem1 in
                       let po2 = get_po elem2 in
                       let form = Term.t_implies po1 po2 in
                       Towhy3.bound_vars Term.t_forall_close_simp form 
      |Prec_slicing -> let po1 = get_po elem1 in
                       let po2 = get_po elem2 in
                       let form = Term.t_implies po1 po2 in
                       Towhy3.bound_vars Term.t_exists_close_simp form
      |Spec_slicing -> let po1 = get_po elem1 in
                       let po2 = get_po elem2 in
                       let form = Term.t_implies po1 po2 in
                       Towhy3.bound_vars Term.t_forall_close_simp form

let build_slicing_result statement1 statement2 form prover_result slicing_type = 
  {
   stmt_1 = statement1;
   stmt_2 = statement2;
   formula = form;
   slicing_type = slicing_type;
   prover_result = prover_result;
  }

let rec isValid prover_result =
  match prover_result with
  | [] -> false
  | x::t -> if ((String.compare x.result "Valid")=0) then true else isValid t


let rec fail_prover formula prov tv = 
  Gs_options.Self.result"Why3 tvsymbol not found %a\n" Pretty.print_vs tv;
  let nf = Term.t_forall_close_simp [tv] [] formula in   
  print_why3_term_aux nf; 
  try_prover nf prov


and try_prover formula prov = 
   try
     send_to_prover formula prov
   with Decl.UnboundVar tv -> fail_prover formula prov tv

let rec apply_slicing slicing_type elem vcgen_results provers_list =
  match vcgen_results with
  | [] -> []
  | h :: t -> 
        let formula = build_imp slicing_type elem h in
        let prl = List.map (fun prov -> 
                                   try
                                     try_prover formula prov
                                   with
                                   | Decl.UnboundVar tv -> fail_prover formula prov tv
                                                              
                            ) provers_list in  
        (build_slicing_result elem.statement h.statement formula prl slicing_type) :: (apply_slicing slicing_type elem t provers_list)


let rec apply_and_remove slice_fun slicing_type elem vcgen_results provers_list  =
  match vcgen_results with
  | [] -> if (is_not_simple_type elem) then (statement_kind apply_slicing slice_fun elem vcgen_results provers_list slicing_type) else []
  | h :: t -> (statement_kind apply_slicing slice_fun elem vcgen_results provers_list slicing_type) @ (apply_and_remove slice_fun slicing_type h t provers_list)

and statement_kind func slice_fun elem vcgen_results provers_list slicing_type =
  match elem.stype with
  | StartS -> func slicing_type elem vcgen_results provers_list
  | EndS -> []
  | SimpleS -> func slicing_type elem vcgen_results provers_list
  | IfS (vcl1,vcl2) -> (func slicing_type elem vcgen_results provers_list) @ (apply_kind slice_fun slicing_type vcl1 provers_list) @ (apply_kind slice_fun slicing_type vcl2 provers_list)
  | BlockS vclb -> (func slicing_type elem vcgen_results provers_list) @ (apply_kind slice_fun slicing_type vclb provers_list) 
  | LoopS vcll -> (func slicing_type elem vcgen_results provers_list) @ (apply_kind slice_fun slicing_type vcll provers_list) 


and apply_kind slice_fun slice_type vcgen_results provers_list = 
  match vcgen_results with
  | [] -> []
  | x::t -> slice_fun slice_type vcgen_results provers_list

and slicing slice_type vcgen_results provers_list = 
  match slice_type with
  | Post_slicing -> apply_and_remove slicing Post_slicing (List.hd vcgen_results) (my_tail vcgen_results) provers_list 
  | Prec_slicing -> apply_and_remove slicing Prec_slicing (List.hd vcgen_results) (my_tail vcgen_results) provers_list 
  | Spec_slicing -> raise (Invalid_argument "Specification-based slicing not to be invoked in function slicing (1)")


let equal_stmt statement1 statement2 =
  print_aux statement1 statement2;
  Cil_datatype.Stmt.equal statement1 statement2

let rec get_complex_type branch vc_sp vc_wp =
  match vc_wp.stype with 
  | IfS (vcl1,vcl2) -> begin
                        try  
                         find_vcgen branch vc_sp vcl1
                         with
                        |Not_found ->  find_vcgen branch vc_sp vcl2
                      end
  | BlockS vclb -> find_vcgen branch vc_sp vclb                 
  | LoopS  vcll -> find_vcgen branch vc_sp vcll                 
  | SimpleS -> raise Not_found
  | StartS -> raise Not_found
  | EndS -> raise Not_found


and find_complex_type branch vcgen_result_sp vcgen_wp = 
  match vcgen_wp with
  | [] -> raise (Invalid_argument " Wp not found") 
  | x::t -> try
            get_complex_type branch vcgen_result_sp x
            with
            | Not_found -> find_complex_type branch vcgen_result_sp t

and find_vcgen branch vc_sp vc_wp =
  try
    List.find (fun x -> equal_stmt vc_sp.statement x.statement) vc_wp
  with
  | Not_found -> find_complex_type branch vc_sp vc_wp

let find_type branch vcgen_result_sp  =
  let kf = Kernel_function.find_englobing_kf vcgen_result_sp.statement in
  let vcl_wp = get_comp_wp vcgen_result_sp.statement in          
  let vcl = 
          begin
          match vcl_wp.stype with
          | IfS (vcl1,vcl2) -> if(branch) then vcl1 else vcl2
          | BlockS vclb -> vclb
          | LoopS  vcll -> vcll
          | SimpleS -> raise (Invalid_argument "SimpleS: Not a complex type")
          | StartS -> raise (Invalid_argument "StartS: Not a complex type")
          | EndS -> raise (Invalid_argument "EndS: Not a complex type")
          end
  in
  vcl

let rec apply_slice_spec slice_type vcgen_results_sp vcgen_results_wp provers_list =
  match vcgen_results_sp with
  | [] -> []
  | h :: t -> statement_kind_spec slice_type h vcgen_results_wp provers_list @ apply_slice_spec slice_type t (my_tail vcgen_results_wp) provers_list 

and statement_kind_spec slicing_type elem vcgen_results_wp provers_list  =
  match elem.stype with
  | StartS -> apply_slicing slicing_type elem vcgen_results_wp provers_list
  | EndS -> []
  | SimpleS -> apply_slicing slicing_type elem vcgen_results_wp provers_list
  | IfS (vcl1,vcl2) -> let succ_fi = List.hd vcgen_results_wp in
                       (apply_slicing slicing_type elem vcgen_results_wp provers_list) @ 
                       (apply_kind_spec slicing_type vcl1 ((find_type true elem) @ [succ_fi]) provers_list) @ 
                       (apply_kind_spec slicing_type vcl2 ((find_type false elem) @ [succ_fi])  provers_list) @
                       (apply_slicing slicing_type elem (find_type true elem)  provers_list) @
                       (apply_slicing slicing_type elem (find_type false elem) provers_list) 
  | BlockS vclb -> (apply_slicing slicing_type elem vcgen_results_wp provers_list) @ (apply_kind_spec slicing_type vclb (find_type false elem ) provers_list) 
  | LoopS vcll -> (apply_slicing slicing_type elem vcgen_results_wp provers_list) @ (apply_kind_spec slicing_type vcll (find_type false elem ) provers_list) 

and apply_kind_spec  slice_type vcgen_results_sp vcgen_results_wp  provers_list = 
  match vcgen_results_sp with
  | [] -> []
  | x::t -> slicing2 slice_type vcgen_results_sp (my_tail vcgen_results_wp) provers_list

and slicing2 slice_type vcgen_results_sp  vcgen_results_wp  provers_list =
  apply_slice_spec slice_type vcgen_results_sp vcgen_results_wp provers_list 



