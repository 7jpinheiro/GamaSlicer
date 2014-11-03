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

let rec apply_slicing slicing_type elem vcgen_results provers_list =
  match vcgen_results with
  | [] -> []
  | h :: t -> 
        let formula = build_imp slicing_type elem h in
        let prl = List.map (fun prov -> 
                                    try
                                      send_to_prover formula prov
                                    with Decl.UnboundVar tv -> Gs_options.Self.result"Why3 tvsymbol not found %a\n" Pretty.print_vs tv;
                                                               let nf = Term.t_exists_close_simp [tv] [] formula in
                                                               send_to_prover nf prov
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
  Cil_datatype.Stmt.equal statement1 statement2

let find_type branch vcgen_result_sp  =
  let kf = Kernel_function.find_englobing_kf vcgen_result_sp.statement in
  let fun_dec = get_fun kf in 
  let vgen_wp = fun_dec.vcgen_result_wp in
  let vcl_wp = List.find (fun x -> equal_stmt vcgen_result_sp.statement x.statement) vgen_wp in
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
  | h :: t -> statement_kind_spec slice_type h vcgen_results_wp provers_list @ apply_slice_spec slice_type t (List.tl vcgen_results_wp) provers_list 

and statement_kind_spec slicing_type elem vcgen_results_wp provers_list  =
  match elem.stype with
  | StartS -> apply_slicing slicing_type elem vcgen_results_wp provers_list
  | EndS -> []
  | SimpleS -> apply_slicing slicing_type elem vcgen_results_wp provers_list
  | IfS (vcl1,vcl2) -> (apply_slicing slicing_type elem vcgen_results_wp provers_list) @ (apply_kind_spec slicing_type vcl1 (find_type true elem ) provers_list) @ (apply_kind_spec slicing_type vcl2 (find_type false elem ) provers_list)
  | BlockS vclb -> (apply_slicing slicing_type elem vcgen_results_wp provers_list) @ (apply_kind_spec slicing_type vclb (find_type false elem ) provers_list) 
  | LoopS vcll -> (apply_slicing slicing_type elem vcgen_results_wp provers_list) @ (apply_kind_spec slicing_type vcll (find_type false elem ) provers_list) 

and apply_kind_spec  slice_type vcgen_results_sp vcgen_results_wp  provers_list = 
  match vcgen_results_sp with
  | [] -> []
  | x::t -> slicing2 slice_type vcgen_results_sp vcgen_results_wp provers_list

and slicing2 slice_type vcgen_results_sp vcgen_results_wp  provers_list =
  apply_slice_spec slice_type vcgen_results_sp vcgen_results_wp provers_list 



