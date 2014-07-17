open Cil_types

(* Gets option *)
let get_opt = function
  | Some x -> x
  | None   -> raise (Invalid_argument "Empty Function behavior")

(* Gets a list of logic_vars acording to the type of parameter e and the function *)
let get_logic_vars e func = 
	let var_set = func e in
	Cil_datatype.Varinfo.Set.fold 
		(
		 fun x acc -> (Cil.cvar_to_lvar x) :: acc
		) var_set 

(* Gets a list of logic_vars from a lval *)
let get_lval_logic_vars lval =
	get_logic_vars lval Cil.extract_varinfos_from_lval

(* Gets a list of logic_vars from a exp *)
let get_exp_logic_vars exp =
	get_logic_vars exp Cil.extract_varinfos_from_exp

(* Gets a list of logic_vars from a predicate *)
let get_predicate_logic_vars predicate = 
	let var_set = Cil.extract_free_logicvars_from_predicate predicate in
	Cil_datatype.Logic_var.Set.elements var_set

(* Gets a list of logic_vars from a term *)
let get_term_logic_vars term = 
	let var_set = Cil.extract_free_logicvars_from_term term in
	Cil_datatype.Logic_var.Set.elements var_set 

(* Gets the name of the logic_var *)
let get_logicvar_name_list logicv_list =
	List.map (fun x -> x.lv_name) logicv_list

(* Gets a name from tlval, if not a TVar returns "NOT_A_LOGIC_VARIABLE"*)
let get_var_name_from_tlval (th,_) = 
	match th with
	|TVar logic_var -> logic_var.lv_name 
	| _ -> "NOT_A_LOGIC_VARIABLE" 

(* Gets a name from lval, if not a TVar returns "NOT_A_LOGIC_VARIABLE"*)
let get_var_name_from_lval (lh,_) = 
	match lh with
	|Var varinfo -> varinfo.vname  
	| _ -> "NOT_A_VARIABLE" 



(* Visitor that visits a predicate, when it finds a term that contains the logic_var, it replaces it the expression term *)
class replace_term_on_predicate  exprterm var_name = object 
	inherit Visitor.frama_c_inplace 
	
	method vterm t = 
		match t.term_node with
		| TLval term_lval ->
			let name = get_var_name_from_tlval term_lval in
			if (var_name == name) then exprterm else t;
			DoChildren
		| _ -> DoChildren
		
	end



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

let print_statement stmt =
	Format.printf"%a\n" Printer.pp_stmt stmt


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

(* Prints a list of triples(at the moment pos are not printed) *)
let print_ss_po_postcondtion l =
	List.iter
	(
	 fun (x,_,z) -> print_statement x;
	 			    print_condtion z
	) l
	
(* Converts the generated predicates to stmt language *)
let gen_po predicate = "proof"


(* Replaces the predicate  *)
let replace lval exp predicate  =
	let folded_exp = Cil.constFold false exp in 
	let exp_term = Logic_utils.expr_to_term true folded_exp in
    let var_name = get_var_name_from_lval lval in
    if (var_name == "NOT_A_VARIABLE") then 
   		 Visitor.visitFramacPredicateNamed (new replace_term_on_predicate exp_term var_name) predicate 
    	else predicate

			


(* Matches the instruction with the definitions and replaces the predicate
 on the instruction, generating a new predicate resulting from the replacement *)
let replace_instruction inst predicate = 
	match inst with
	| Set (lval,exp,location) -> replace lval exp predicate
	| Call (lval_op,exp,exp_list,location) -> predicate
	| Skip location -> predicate 
    | Asm _ -> predicate
    | Code_annot _ -> predicate


(* Matches the statement with the definitions and replaces the predicate
 on the statement, generating a new predicate resulting from the replacement *)
let replace_statement statement predicate =
	match statement.skind with 
	| Instr i -> replace_instruction i predicate
	| Return _ -> predicate
	| Goto _ -> predicate
	| Break _ -> predicate
 	| Continue _ -> predicate
 	| If (e,_,_,_) -> predicate
 	| Switch (e,_,_,_) -> predicate
 	| Loop _ -> predicate
 	| Block _ -> predicate
 	| UnspecifiedSequence _ -> predicate
 	| TryFinally _ | TryExcept _ -> predicate
	

(* Genetares proof obligations, and returns a list with tuples (statement,proof obligation) *)
let rec vcgen list_statements predicate =
	match list_statements with
	|[] -> []
	| s::stail -> 
		let sub_predicate = replace_statement s predicate in
		let po = gen_po sub_predicate in
		(s,po,sub_predicate)::(vcgen stail sub_predicate)


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
        let spo_list = vcgen list_statements post_condt in
        spo_list	
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
     print_ss_po_postcondtion list_stm_and_post
     
let () = Db.Main.extend run 