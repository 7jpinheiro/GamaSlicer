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
  mutable slice_statement : stmt ;                    (* The statement  *)
  mutable formula : Term.term;                  (* The statement is LoopS, if contains a Loop with one block *)
  mutable prover_result: prover_result list ;                         (* The statement is LoopS, if contains a Loop with one block *)
  mutable slicing_type: assert_slicing_type;    (* The statement is LoopS, if contains a Loop with one block *)
}

let build_imp elem1 elem2 = 
  let po1 = get_po elem1 in
  let po2 = get_po elem2 in
  let form = Term.t_implies po1 po2 in
  let b_form = Towhy3.bound_vars form in
  b_form

let build_slicing_result statement form prover_result slicing_type = 
  {
   slice_statement = statement;
   formula = form;
   slicing_type = slicing_type;
   prover_result = prover_result;
  }


let rec post_slicing elem vcgen_results provers_list =
  match vcgen_results with
  | [] -> []
  | h :: t -> 
        let formula = build_imp elem h in
        let prl = List.map (fun prov -> send_to_prover formula prov) provers_list in 
        (build_slicing_result h.statement formula prl Post_slicing) :: (post_slicing elem t provers_list)


let rec apply_and_remove slicing_type elem vcgen_results  provers_list  =
  match vcgen_results with
  | [] -> []
  | h :: t -> (post_slicing elem vcgen_results provers_list) @ (apply_and_remove slicing_type h t provers_list)

let slicing slice_type vcgen_results provers_list = 
  match slice_type with
  | Post_slicing -> apply_and_remove Post_slicing (List.hd vcgen_results) (List.tl vcgen_results) provers_list 
  | Prec_slicing -> raise (Invalid_argument "Precondition-based slicing not yet implemented")
  | Spec_slicing -> raise (Invalid_argument "Specification-based slicing not yet implemented")