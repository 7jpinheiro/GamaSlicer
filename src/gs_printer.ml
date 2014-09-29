open Cil_types
open Printer
open Why3
open Provers
open Slicing
open Vcgen


(* Prints a predicate(condition in this case) *)
let print_why3_term term =
	Towhy3.Self.result "Why3 Formula: %a\n" Pretty.print_term term

let print_why3_type ty = 
	Towhy3.Self.result "Why3 Type: %a\n" Pretty.print_ty ty

let print_why3_ls ls =
	Towhy3.Self.result "Why3 Ls: %a\n" Pretty.print_ls ls


let print_why3_typenode tn =
  match tn with
  | Ty.Tyvar tvsymbol -> Towhy3.Self.result"Why3 Tyvar %a\n" Pretty.print_tv tvsymbol
  | Ty.Tyapp (tysymbol2,ty_list) -> Towhy3.Self.result"Why3 Tyapp %a\n" Pretty.print_ts tysymbol2

(* Prints a predicate(condition in this case) *)
let print_predicate cond =
	Towhy3.Self.result "Predicate: %a\n" pp_predicate_named cond

(* Prints a statement *)
let print_statement stmt =
	Towhy3.Self.result "Statement: %a" pp_stmt stmt;
  Towhy3.Self.result "S_id: %d\n" stmt.sid

(* Prints a term *)
let print_term term =
	Towhy3.Self.result "Term: %a\n" pp_term term

(* Prints a Logic Label *)
let print_logic_label logic_label =
	Towhy3.Self.result "Logic Label: %a\n" pp_logic_label logic_label

(* Prints a list of statements *)
let print_statements list_statements = 
	List.iter
		(
		 fun s -> Towhy3.Self.result "%a\n" pp_stmt s
		) list_statements

(* Prints a List of tuples of a list of statements and a condition *)
let print_ss_postcondtion l =
	List.iter
	(
	 fun (x,y) -> print_statements x;
	 			  print_predicate y  
	) l

let print_prover_result prover_result =
  Towhy3.Self.result "Prover: %s\n " prover_result.name;
  Towhy3.Self.result "Validity: %s\n " prover_result.result;
  Towhy3.Self.result "Time: %f\n " prover_result.time
  
	
let print_slice_result result =
  print_statement result.slice_statement;
  print_why3_term result.formula;
  List.iter
  (
   fun x -> Towhy3.Self.result "****************** \n\n";           
            print_prover_result x
  ) result.prover_result


let print_slice_results results =
   List.iter
  (
   fun x -> Towhy3.Self.result "--------------------------\n\n";
            print_slice_result x;
            Towhy3.Self.result "--------------------------\n\n"
  ) results

