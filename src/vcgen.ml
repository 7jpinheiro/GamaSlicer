open Cil_types
open Printer
open Why3

module Options = Gs_options

type vc_type =
| Wp
| Sp

(* Datatype that stores the stmt proof obligation *)
type po = 
{ 
 proof_obligation : Term.term;				
}(* Datatype that stores the vcgen_result  *)

type vcgen_result = 
{
	mutable statement : stmt ;										(* Statement that originated the result *)
	mutable po : po ;												(* Stores stmt proof obligation  *)
	mutable predicate : predicate named;							(* Stores the result predicate from wp calculus *)
	mutable stype : vcgen_type ;									(* Stores the statement type *)
}(* Datatype that stores the type of statement, 
each vcgen_result list comes from a block of that statement *)
and vcgen_type =
| SimpleS 															(* The statement is SimpleS, if contains no block *)
| IfS  of vcgen_result list * vcgen_result list 					(* The statement is Ifs, if contains a If with blocks *)
| BlockS of vcgen_result list 										(* The statement is BlocS, if is a Block  *)
| LoopS  of vcgen_result list 										(* The statement is LoopS, if contains a Loop with one block *)



(* Gets option *)
let get_opt = function
  | Some x -> x
  | None   -> raise (Invalid_argument "Empty Function behavior")


(* Converts the generated predicates to why3 language *)
let gen_po predicate = {
  proof_obligation = 
    try
      Options.Self.result "Converting %a to Why3...\n" pp_predicate_named predicate;
      Towhy3.pred2why predicate 
    with
    | Not_found -> Options.Self.fatal "lsymbol not found"
    | Ty.TypeMismatch(ty1,ty2) -> 
                    Options.Self.result" BEGIN ERROR REPORT\n ";
                    let equal = Ty.ty_equal ty1 ty2 in
                    Options.Self.result"Ty1 == ty2: %b\n" equal; 
                    Options.Self.fatal" END ERROR REPORT\n "
}
  

(* Builds vcgen_result with simple type *)
let build_vcgen_result_simple statement predicate  =
	{
		statement = statement;
		po =  gen_po predicate;
		predicate = predicate;
		stype = SimpleS; 
	}

(* Builds vcgen_result with Ifs type *)
let build_vcgen_result_if statement predicate vcgen_result_list1 vcgen_result_list2  =
	{
		statement = statement;
		po =  gen_po predicate;
		predicate = predicate;
		stype = IfS  (vcgen_result_list1,vcgen_result_list2) ; 
	}

(* Builds vcgen_result with WhileS type *)
let build_vcgen_result_loop statement invariant vcgen_result_list   =
	{
		statement = statement;
		po =  gen_po invariant;
		predicate = invariant;
		stype = LoopS vcgen_result_list ; 
	}

let get_po vcgen_result = 
    vcgen_result.po.proof_obligation


let isReturnStmt stmtkind =
  match stmtkind with
  | Return (_,_) -> true
  | _ -> false



(* Gets a list of logic_vars acording to the type of parameter e and the function *)
let get_logic_vars e func = 
	let var_set = func e in
	Cil_datatype.Varinfo.Set.fold 
		(
		 fun x acc -> (Cil.cvar_to_lvar x) :: acc
		) var_set []

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



(* If code content is type AInvariant returns the predicate, else true *)
let get_predicate_named code_content = 
	match code_content with 
	| AInvariant (bh_list,isnormall,pred) -> pred
	| _ -> Logic_const.ptrue
	
(* Gets an invariant from a code annotation *)
let get_invariant cod_annot = 
	let content = cod_annot.annot_content in
	get_predicate_named content 


(* Builds invariant from a list of code annotations aplying the logic conector && *)
let build_invariant cod_annot_list predicate =
    List.fold_right
	(
	 fun x acc -> 
	 		if Logic_utils.is_invariant x 
	 		then 
	 			let inv = get_invariant x in
	 			Logic_const.pand (inv,acc) 
	 		else acc
	) cod_annot_list predicate


let filterReturn vcgen_result =
   if (isReturnStmt vcgen_result.statement.skind) then false else true 

let removeReturnStatement vcgen_results = 
  List.filter filterReturn vcgen_results 

(* Visitor that visits a predicate, when it finds a term that contains the logic_var, it replaces it the expression term *)
class replace_term prj  exprterm var_name = object 
	inherit Visitor.frama_c_copy  prj 
	
	method vterm t =
		match t.term_node with
		| TLval term_lval ->
			let name = get_var_name_from_tlval term_lval in
		    let result = if (var_name == name) then exprterm else t in
			Cil.ChangeTo(result)
		| _ -> Cil.DoChildren
		
	end


(* Generic sequence rule *)
let rec sequence list_statements predicate func =
  match list_statements with
  |[] -> []
  | s::stail -> 
    let vcgen_result = func s predicate in
    vcgen_result::(sequence stail vcgen_result.predicate func)    

(* Tests if the vcgen_result list is empty, if it is returns the predicate true,
 if contains elements returns the last resulting predicate *)
let ifVcgenResultIsEmpty vcgen_result_list =
	match vcgen_result_list with
	| [] -> Logic_const.ptrue
	| l  -> 
		let last_vcgen_result = List.hd (List.rev l) in
		last_vcgen_result.predicate

(* Replaces the predicate  *)
let replace_wp lval exp predicate  =
	let folded_exp = Cil.constFold false exp in 
	let exp_term = Logic_utils.expr_to_term ~cast:true folded_exp in
    let var_name = get_var_name_from_lval lval in
    if (var_name <> "NOT_A_VARIABLE") then 
   		 Visitor.visitFramacPredicateNamed (new replace_term (Project.current ()) exp_term var_name) predicate 
    	else predicate
		


(* Matches the instruction with the definitions and replaces the predicate
 on the instruction, generating a new predicate resulting from the replacement *)
let replace_instruction_wp inst predicate = 
	match inst with
	| Set (lval,exp,location) -> replace_wp lval exp predicate 						(* Wp assigment rule *)
	| Call (lval_op,exp,exp_list,location) -> predicate
	| Skip location -> predicate 
  | Asm _ -> predicate
  | Code_annot _ -> predicate

(* Conditional wp rule, with sequence rule already aplied to the two blocks*)
let conditional_wp statement exp_term predicate vcgen_result_b1_list vcgen_result_b2_list =
 	let newpredicateb1 = ifVcgenResultIsEmpty vcgen_result_b1_list in
 	let newpredicateb2 = ifVcgenResultIsEmpty vcgen_result_b2_list in
 	let new_predicate = Logic_const.pif (exp_term, newpredicateb1, newpredicateb2) in
	build_vcgen_result_if statement new_predicate  vcgen_result_b1_list vcgen_result_b2_list


(* Matches the statement with the definitions and replaces the predicate
 on the statement, generating a new predicate resulting from the replacement of wp *)
let rec replace_statement_wp statement predicate =
	match statement.skind with 
	| Instr i -> 
			let new_predicate = replace_instruction_wp i predicate in
			build_vcgen_result_simple statement new_predicate 
	| Return (_,_) ->
			build_vcgen_result_simple statement predicate 
	| Goto _ -> 
			build_vcgen_result_simple statement  predicate 
	| Break _ ->
			build_vcgen_result_simple statement  predicate  
 	| Continue _ -> 
 			build_vcgen_result_simple statement  predicate  
 	| If (e,b1,b2,loc) ->
 			let logic_e = Logic_utils.expr_to_term ~cast:true e in
 			let vcgen_result_b1_list = sequence (List.rev b1.bstmts) predicate replace_statement_wp in
 			let vcgen_result_b2_list = sequence (List.rev b2.bstmts) predicate replace_statement_wp in
 			conditional_wp statement logic_e predicate vcgen_result_b1_list vcgen_result_b2_list
 	| Switch (e,_,_,_) ->
 			build_vcgen_result_simple statement  predicate 
 	| Loop (ca_list,block,loc,stmt_op1,stmt_op2) -> 
 			let invariant = build_invariant ca_list Logic_const.ptrue in
 			let vcgen_result_list = sequence (List.rev block.bstmts) predicate replace_statement_wp in
 			build_vcgen_result_loop statement invariant vcgen_result_list
 	| Block _ ->
 			build_vcgen_result_simple statement  predicate 
 	| UnspecifiedSequence _ ->
 			build_vcgen_result_simple statement  predicate  
 	| TryFinally _ | TryExcept _ -> 
 			build_vcgen_result_simple statement  predicate  

(* Sequence rule of weakeast precondition calculus *) 
let rec sequence_wp list_statements predicate =
  match list_statements with
  |[] -> []
  | s::stail -> 
    let vcgen_result = replace_statement_wp s predicate in
    vcgen_result::(sequence_wp stail vcgen_result.predicate)


(* Replaces the predicate  *)
let replace_sp lval exp predicate  =
  let folded_exp = Cil.constFold false exp in 
  let exp_term = Logic_utils.expr_to_term ~cast:true folded_exp in
  let logic_var_list = get_lval_logic_vars lval in 
  let llogic_var = List.hd logic_var_list in 
  let q_logic_var = Cil_const.make_logic_var_quant "v" llogic_var.lv_type in 
  let qtlvar = Logic_const.tvar q_logic_var in 
  let tlvar = Logic_const.tvar llogic_var in
    let var_name = get_var_name_from_lval lval in
    if (var_name <> "NOT_A_VARIABLE") then 
      let new_predicate = Visitor.visitFramacPredicateNamed (new replace_term (Project.current ()) qtlvar var_name) predicate in
      let new_term = Visitor.visitFramacTerm (new replace_term (Project.current ()) qtlvar var_name) exp_term in
      let eq_predicate = Logic_const.prel (Req,tlvar,new_term) in 
      let and_predicate = Logic_const.pand (new_predicate,eq_predicate) in
      Logic_const.pexists ([q_logic_var],and_predicate)
      else predicate

(* Matches the instruction with the definitions and replaces the predicate
 on the instruction, generating a new predicate resulting from the replacement *)
let replace_instruction_sp inst predicate = 
  match inst with
  | Set (lval,exp,location) -> replace_sp lval exp predicate             (* Wp assigment rule *)
  | Call (lval_op,exp,exp_list,location) -> predicate
  | Skip location -> predicate 
  | Asm _ -> predicate
  | Code_annot _ -> predicate


(* Matches the statement with the definitions and replaces the predicate
 on the statement, generating a new predicate resulting from the replacement of wp *)
let rec replace_statement_sp statement predicate =
  match statement.skind with 
  | Instr i -> 
      let new_predicate = replace_instruction_sp i predicate in
      build_vcgen_result_simple statement new_predicate 
  | Return (_,_) ->
      build_vcgen_result_simple statement predicate 
  | Goto _ -> 
      build_vcgen_result_simple statement  predicate 
  | Break _ ->
      build_vcgen_result_simple statement  predicate  
  | Continue _ -> 
      build_vcgen_result_simple statement  predicate  
  | If (e,b1,b2,loc) ->
      let logic_e = Logic_utils.expr_to_term ~cast:true e in
      let vcgen_result_b1_list = sequence (List.rev b1.bstmts) predicate replace_statement_sp in
      let vcgen_result_b2_list = sequence (List.rev b2.bstmts) predicate replace_statement_sp in
      conditional_wp statement logic_e predicate vcgen_result_b1_list vcgen_result_b2_list
  | Switch (e,_,_,_) ->
      build_vcgen_result_simple statement  predicate 
  | Loop (ca_list,block,loc,stmt_op1,stmt_op2) -> 
      let invariant = build_invariant ca_list Logic_const.ptrue in
      let vcgen_result_list = sequence (List.rev block.bstmts) predicate replace_statement_sp in
      build_vcgen_result_loop statement invariant vcgen_result_list
  | Block _ ->
      build_vcgen_result_simple statement  predicate 
  | UnspecifiedSequence _ ->
      build_vcgen_result_simple statement  predicate  
  | TryFinally _ | TryExcept _ -> 
      build_vcgen_result_simple statement  predicate  


(* Sequence rule of strongest postcondition calculus *) 
let rec sequence_sp list_statements predicate =
  match list_statements with
  |[] -> []
  | s::stail -> 
    let vcgen_result = replace_statement_sp s predicate in
    vcgen_result::(sequence_sp stail vcgen_result.predicate)

(* Genetares proof obligations, and returns a list with vcgen_result *)
let vcgen vc_type list_statements pre_condt post_condt =
  match vc_type with
	| Wp -> List.rev (sequence_wp (List.rev list_statements) post_condt)
 (*) | Sp -> sequence_sp list_statements pre_condt*)
  | _ -> raise (Invalid_argument "SP not implemented")
(* Returns a list of statements found in fundec.sallstmts after the computation of the cfg *)
let get_list_of_statements fundec = 
	Options.Self.result "Getting list of statements.\n";
	let list_statements = fundec.sallstmts in
  list_statements

(* Get postcondition depeding ond the func_bulidcondtion input *)
let get_PostCondtion  funbehavior  =
	let post_condition =  Ast_info.behavior_postcondition (get_opt funbehavior) Normal in
	post_condition 

(* Get postcondition depeding ond the func_bulidcondtion input *)
let get_PreCondtion  funbehavior  =
  let pre_condition =  Ast_info.behavior_precondition (get_opt funbehavior) in
  pre_condition 

(* Visits and applys if there kf has definition *)
let apply_if_defition vc_type def kf =
	match def with
	|true ->
	     	let fundec = Kernel_function.get_definition kf in
      	let funspec = Annotations.funspec kf in 
      	let list_behaviors = Annotations.behaviors kf in 
        let formals = List.map (fun v -> Towhy3.create_var v false) (Kernel_function.get_formals kf) in
        let locals = List.map (fun v -> Towhy3.create_var v true) (Kernel_function.get_locals kf) in
        let funbehavior = Cil.find_default_behavior funspec in
        let pre_condt = get_PreCondtion funbehavior in 
        let post_condt = get_PostCondtion funbehavior in
        let list_statements = get_list_of_statements fundec in
        let vc_list = vcgen vc_type list_statements post_condt in
        vc_list	
	|false -> []


let calculus vc_type =
  Options.Self.result "Visting functions.\n";
  Globals.Functions.fold
  (
      fun kf acc -> (apply_if_defition vc_type (Kernel_function.is_definition kf) kf) @ acc
  ) []


