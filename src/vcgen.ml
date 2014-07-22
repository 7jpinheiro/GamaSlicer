open Cil_types

type po = 
{ 
 proof_obligation : string;
}

type vcgen_type =
| SimpleS 
(*| BlockS  of vcgen_result list
| WhileS  of vcgen_result list
*)

type vcgen_result = 
{
	mutable statement : stmt ;
	mutable po : po ;
	mutable predicate : predicate named;
	mutable stype : vcgen_type
}


let build_vcgen_type typei = 
	match typei with
	|SimpleS -> SimpleS


let build_vcgen_resut statement po predicate typei =
	{
		statement = statement;
		po = po;
		predicate = predicate;
		stype = build_vcgen_type typei ; 
	}

(* Gets option *)
let get_opt = function
  | Some x -> x
  | None   -> raise (Invalid_argument "Empty Function behavior")


(* Prints a predicate(condition in this case) *)
let print_condtion cond =
	Format.printf"Post_condition: %a\n" Printer.pp_predicate_named cond

(* Prints a statement *)
let print_statement stmt =
	Format.printf"Statement: %a\n" Printer.pp_stmt stmt

(* Prints a term *)
let print_term term =
	Format.printf"Term: %a\n" Printer.pp_term term

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
let print_vcgen_result l =
	List.iter
	(
	 fun (x) -> print_statement x.statement;
	 			    print_condtion x.predicate
	) l
	

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
class replace_term_on_predicate prj  exprterm var_name = object (self)
	inherit Visitor.frama_c_copy  prj 
	
	method vterm t =
		match t.term_node with
		| TLval term_lval ->
			let name = get_var_name_from_tlval term_lval in
		    let result = if (var_name == name) then exprterm else t in
			Cil.ChangeTo(result)
		| _ -> Cil.DoChildren
		
	end



(* Computes cfg for all functions and fills in info information on fundec (smaxstmid and sallsmts) *)
let computeCfg () =
	Globals.Functions.iter_on_fundecs
	(
      fun fundec -> 
      	Cfg.prepareCFG fundec;
      	Cfg.computeCFGInfo fundec false  
	)


(* Converts the generated predicates to stmt language *)
let gen_po predicate = {proof_obligation ="proof";}


(* Replaces the predicate  *)
let replace lval exp predicate  =
	let folded_exp = Cil.constFold false exp in 
	let exp_term = Logic_utils.expr_to_term ~cast:true folded_exp in
    let var_name = get_var_name_from_lval lval in
    if (var_name <> "NOT_A_VARIABLE") then 
   		 Visitor.visitFramacPredicateNamed (new replace_term_on_predicate (Project.current ()) exp_term var_name) predicate 
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
	| Instr i -> 
			let new_predicate = replace_instruction i predicate in
			let po = gen_po new_predicate in
			build_vcgen_resut statement po new_predicate SimpleS
	| Return _ ->
			let po = gen_po predicate in
			build_vcgen_resut statement po predicate SimpleS
	| Goto _ -> 
			let po = gen_po predicate in
			build_vcgen_resut statement po predicate SimpleS
	| Break _ ->
			let po = gen_po predicate in
			build_vcgen_resut statement po predicate SimpleS
 	| Continue _ -> 
 			let po = gen_po predicate in
			build_vcgen_resut statement po predicate SimpleS
 	| If (e,b1,b2,loc) ->
 			let po = gen_po predicate in
			build_vcgen_resut statement po predicate SimpleS
 	| Switch (e,_,_,_) ->
 			let po = gen_po predicate in
			build_vcgen_resut statement po predicate SimpleS
 	| Loop _ -> 
 			let po = gen_po predicate in
			build_vcgen_resut statement po predicate SimpleS
 	| Block _ ->
 			let po = gen_po predicate in
			build_vcgen_resut statement po predicate SimpleS
 	| UnspecifiedSequence _ ->
 			let po = gen_po predicate in
			build_vcgen_resut statement po predicate SimpleS
 	| TryFinally _ | TryExcept _ -> 
 			let po = gen_po predicate in
			build_vcgen_resut statement po predicate SimpleS
	

(* Genetares proof obligations, and returns a list with tuples (statement,proof obligation) *)
let rec sequence list_statements predicate =
	match list_statements with
	|[] -> []
	| s::stail -> 
		let vcgen_result = replace_statement s predicate in
		vcgen_result::(sequence stail vcgen_result.predicate)


let vcgen list_statements predicate =
	sequence list_statements predicate

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
     print_vcgen_result list_stm_and_post
     
let () = Db.Main.extend run 