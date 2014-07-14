open Cil_types


(* Gets option *)
let get_opt = function
  | Some x -> x
  | None   -> raise (Invalid_argument "Empty Function behavior")

(* Computes cfg for all functions and fills in info information on fundec (smaxstmid and sallsmts) *)
let computeCfg () =
	Globals.Functions.iter_on_fundecs
	(
      fun fundec -> 
      	Cfg.prepareCFG fundec;
      	Cfg.computeCFGInfo fundec false  
	)

(* Prints a predicate(condition in this case) *)
let print_condtion cond =
	Format.printf"Post_condition: %a\n" Printer.pp_predicate_named cond

(* Prints a list of statements *)
let print_statements list_statements = 
	List.iter
		(
		 fun s -> Format.printf"%a\n" Printer.pp_stmt s
		) list_statements

(* Prints a List of tuples of a list of statements and a condition *)
let print_ss_postcondtion l =
	List.iter
	(
	 fun (x,y) -> print_statements x;
	 			  print_condtion y  
	) l
	
(* Converts the generated predicates to stmt language *)
let gen_po predicate = "proof"

(* Gets a list of logic_vars acording to the type of parameter e and the function *)
let get_logic_vars e function = 
	let var_set = function e in
	let var_list = Set.elements var_set in
	List.map (fun x -> Cil.cvar_to_lvar x ) var_list 

(* Gets a list of logic_vars from a lval *)
let get_lval_logic_vars lval =
	get_logic_vars lval Cil.extract_varinfos_from_lval

(* Gets a list of logic_vars from a exp *)
let get_exp_logic_vars exp =
	get_logic_vars exp Cil.extract_varinfos_from_exp

(* Gets a list of logic_vars from a predicate *)
let get_predicate_logic_vars predicate = 
	let var_set = Cil.extract_free_logicvars_from_predicate predicate in
	Set.elements var_set

(* Gets a list of logic_vars from a term *)
let get_term_logic_vars term = 
	let var_set = Cil.extract_free_logicvars_from_term term in
	Set.elements var_set 

(* Gets the name of the logic_var *)
let get_logicvar_name_list logicv_list =
	List.map (fun x -> x.lv_name) logicv_list



(* Matches the instruction with the definitions and replaces the predicate
 on the instruction, generating a new predicate resulting from the replacement *)
let replace_instruction inst predicate = 
	match inst with
	| Set (lval,exp,location) -> 
	| Call (lval_op,exp,exp_list,location) ->
	| Skip location -> predicate 
    (* Falta asm e code_annot *)


(* Matches the statement with the definitions and replaces the predicate
 on the statement, generating a new predicate resulting from the replacement *)
let replace_statement statement predicate =
	match statement.kind with 
	| Instr i -> replace_instruction i predicate
	| Return _ -> Format.pp_print_string out "<return>"
	| Goto _ -> Format.pp_print_string out "<goto>"
	| Break _ -> Format.pp_print_string out "<break>"
 	| Continue _ -> Format.pp_print_string out "<continue>"
 	| If (e,_,_,_) -> Format.fprintf out "if %a" Printer.pp_exp e
 	| Switch (e,_,_,_) -> Format.fprintf out "switch %a" Printer.pp_exp e
 	| Loop _ -> Format.fprintf out "<loop>"
 	| Block _ -> Format.fprintf out "<block>"
 	| UnspecifiedSequence _ -> Format.fprintf out "<unspecified sequence>"
 	| TryFinally _ | TryExcept _ -> Format.fprintf out "<try>"
	

(* Genetares proof obligations, and returns a list with tuples (statement,proof obligation) *)
let rec vcgen list_statements predicate =
	match list_statements with
	|[] -> []
	| s::stail -> 
		let sub_predicate = replace_condition s predicate in
		let po = gen_po sub_predicate in
		(s,po)::(vcgen stail sub_predicate)


(* Returns a reversed list of statements found in fundec.sallstmts after the computation of the cfg *)
let get_list_of_statements fundec = 
	Format.printf"Getting list of statements.\n";
	let list_statements = fundec.sallstmts in
	List.rev list_statements


(* Get condition depeding ond the func_bulidcondtion input *)
let get_Condtion  funspec func_buildcondition =
	Format.printf"Getting Condition.\n";
	let funbehavior = Cil.find_default_behavior funspec in
	let post_condition =  func_buildcondition (get_opt funbehavior) Normal in
	post_condition 

(* Visits and applys if there kf has definition *)
let apply_if_defition def kf =
	match def with
	|true ->
		let fundec = Kernel_function.get_definition kf in
      	let funspec = Annotations.funspec kf in 
      	let list_behaviors = Annotations.behaviors kf in 
        let post_condt = get_Condtion funspec  Ast_info.behavior_postcondition  in
        let list_statements = get_list_of_statements fundec in
        [(list_statements,post_condt)]
	|false -> []

(* Visits functions *)
let visitFunctions () =
	Format.printf"Visting functions.\n";
	Globals.Functions.fold
	(
      fun kf acc -> (apply_if_defition (Kernel_function.is_definition kf) kf) @ acc
	) []

  (* Main function *)
  let run () =

     Ast.compute (); 
     if (Ast.is_computed()) then Format.printf"AST computed.\n"; 	

     let c_file = Ast.get () in
     Cfg.clearFileCFG c_file;
     computeCfg ();
     let list_stm_and_post = visitFunctions () in
     print_ss_postcondtion list_stm_and_post
     
let () = Db.Main.extend run 