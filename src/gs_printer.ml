open Cil_types
open Printer
open Why3
open Provers
open Slicing
open Vcgen
open Graph
open Slicegraph

(* Prints a predicate(condition in this case) *)
let print_why3_term term =
	Gs_options.Self.result "Why3 Formula: %a\n" Pretty.print_term term

let print_why3_type ty = 
	Gs_options.Self.result "Why3 Type: %a\n" Pretty.print_ty ty

let print_why3_ls ls =
	Gs_options.Self.result "Why3 Ls: %a\n" Pretty.print_ls ls


let print_why3_typenode tn =
  match tn with
  | Ty.Tyvar tvsymbol -> Gs_options.Self.result"Why3 Tyvar %a\n" Pretty.print_tv tvsymbol
  | Ty.Tyapp (tysymbol2,ty_list) -> Gs_options.Self.result"Why3 Tyapp %a\n" Pretty.print_ts tysymbol2

(* Prints a predicate(condition in this case) *)
let print_predicate cond =
	Gs_options.Self.result "Predicate: %a\n" pp_predicate_named cond

(* Prints a statement *)
let print_statement stmt =
	Gs_options.Self.result "Statement: %a" pp_stmt stmt;
  Gs_options.Self.result "S_id: %d\n" stmt.sid

let print_simple_statement stmt = 
 (* Gs_options.Self.result "S_id: %d\n" stmt.sid; *)
  match stmt.skind with
  | If (e,b1,b2,loc) -> Format.printf  "if (%a)\n" pp_exp e
  | _ -> Format.printf  "%a\n" pp_stmt stmt
  

(* Prints a term *)
let print_term term =
	Gs_options.Self.result "Term: %a\n" pp_term term

(* Prints a Logic Label *)
let print_logic_label logic_label =
	Gs_options.Self.result "Logic Label: %a\n" pp_logic_label logic_label

(* Prints a list of statements *)
let print_statements list_statements = 
	List.iter
		(
		 fun s -> Gs_options.Self.result "%a\n" pp_stmt s
		) list_statements

(* Prints a List of tuples of a list of statements and a condition *)
let print_ss_postcondtion l =
	List.iter
	(
	 fun (x,y) -> print_statements x;
	 			  print_predicate y  
	) l



let print_prover_result prover_result =
  Gs_options.Self.result "Prover: %s\n " prover_result.name;
  Gs_options.Self.result "Validity: %s\n " prover_result.result;
  Gs_options.Self.result "Time: %f\n " prover_result.time
  
let print_slice_result result =
  print_statement result.stmt_1;
  print_statement result.stmt_2;
  print_why3_term result.formula;
  List.iter
  (
   fun x -> Gs_options.Self.result "****************** \n\n";           
            print_prover_result x
  ) result.prover_result


let print_slice_result_simple result =
  Gs_options.Self.result "%d -> %d\n" result.stmt_1.sid result.stmt_2.sid;
  Gs_options.Self.result "****************** \n\n";           
  print_prover_result (List.hd result.prover_result)

let print_slice_results results =
   List.iter
  (
   fun x -> Gs_options.Self.result "--------------------------\n\n";
            print_slice_result x;
            Gs_options.Self.result "--------------------------\n\n"
  ) results



let print_slice_results_simple results =
   List.iter
  (
   fun x -> Gs_options.Self.result "--------------------------\n\n";
            print_slice_result_simple x;
            Gs_options.Self.result "--------------------------\n\n"
  ) results

let print_vertex g =
    G.iter_vertex( 
              fun v -> let stmt = G.V.label v in
                       print_statement stmt
                 ) g

let print_edges g =
    G.iter_edges(
      fun v1 v2 -> let stmt1 = (G.V.label v1) in
                   let stmt2 = (G.V.label v2) in
                   Gs_options.Self.result "<<><><><>>";
                   print_statement stmt1;
                   Gs_options.Self.result "--------->";
                   print_statement stmt2
      ) g


let print_fi () =  
 Gs_options.Self.result "Printing fi stmt";
  Hashtbl.iter( fun key value -> 
                                 let stmt =  (G.V.label value) in
                                 Gs_options.Self.result "KEY: %d -> \n" key;
                                 Gs_options.Self.result "fi : %a" pp_stmt stmt;
                                 Gs_options.Self.result "fi_S_id: %d\n" stmt.sid 

              ) fi_hash
  
let print_path edges_list =
  Gs_options.Self.result "--------------------------\n\n";
  Gs_options.Self.result "Sliced program: ";
  let print_stack = Stack.create () in
  List.iter(
            fun x -> let stmt = (G.V.label x) in
                     print_simple_statement stmt 
                    (*   print_final stmt print_stack *)
           ) edges_list

let print_result r =
  match r with
  | V_result stmt -> print_simple_statement stmt
  | S_result s ->  Format.printf  "%s\n" s


let print_results results = 
  Gs_options.Self.result "--------------------------\n\n";
  Gs_options.Self.result "Sliced program: ";
  List.iter(
            fun x -> print_result x 
           ) results

let rec print_type vcgen = 
 match vcgen.stype with 
| StartS -> Gs_options.Self.result "Stype: StartS"  
| EndS -> Gs_options.Self.result "Stype: EndS" 
| SimpleS -> Gs_options.Self.result "Stype: SimpleS"                                     (* The statement is SimpleS, if contains no block *)
| IfS  (a,b) -> Gs_options.Self.result "Stype: IfS";
                  print_vcgen a;
                  print_vcgen b
| BlockS e -> Gs_options.Self.result "Stype: BlockS";
              print_vcgen e   
| LoopS q -> Gs_options.Self.result "Stype: LoopS";
              print_vcgen q

and print_vcgen l =
    List.iter(
            fun x ->   Gs_options.Self.result "--------------------------\n\n";
                     print_statement x.statement;
                     print_why3_term x.po.proof_obligation;
                     print_type x
           ) l
