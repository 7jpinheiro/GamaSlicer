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
| StartS
| EndS
| SimpleS 															          (* The statement is SimpleS, if contains no block *)
| IfS  of vcgen_result list * vcgen_result list 	(* The statement is Ifs, if contains a If with blocks *)
| BlockS of vcgen_result list 										(* The statement is BlocS, if is a Block  *)
| LoopS  of vcgen_result list 										(* The statement is LoopS, if contains a Loop with one block *)


type fun_dec = 
{
  mutable end_stmt : stmt; 
  mutable start_stmt : stmt;  
  mutable vcgen_result_sp : vcgen_result list;
  mutable vcgen_result_wp : vcgen_result list;
}


let fun_hash = Hashtbl.create 257

let add_fun kf fun_dec =
  Hashtbl.add fun_hash kf fun_dec

let get_fun kf =
  try
    Hashtbl.find fun_hash kf
  with Not_found ->
    Gs_options.Self.fatal "Kernel_function not found"

let sp_aux = ref 0

let start_stmt_sid = ref 0
let end_stmt_sid = ref 0


(* Gets option *)
let get_opt = function
  | Some x -> x
  | None   -> raise (Invalid_argument "Empty Function behavior")


(* Converts the generated predicates to why3 language *)
let gen_po predicate = {
  proof_obligation = 
    try
      Towhy3.pred2why predicate 
    with
    | Not_found -> Options.Self.fatal "lsymbol not found"
    | Ty.TypeMismatch(ty1,ty2) -> 
                    Options.Self.result" BEGIN ERROR REPORT\n ";
                    let equal = Ty.ty_equal ty1 ty2 in
                    Options.Self.result"Ty1 == ty2: %b\n" equal; 
                    Options.Self.fatal" END ERROR REPORT\n "
}

let isReturnStmt stmtkind =
  match stmtkind with
  | Return (_,_) -> true
  | _ -> false


let filterReturn vcgen_result =
   if (isReturnStmt vcgen_result.statement.skind) then false else true 

let removeReturnStatement vcgen_results = 
  List.filter filterReturn vcgen_results 

(* Builds vcgen_result with simple type *)
let build_vcgen_result_simple statement predicate  =
	{
		statement = statement;
		po =  gen_po predicate;
		predicate = predicate;
		stype = SimpleS; 
	}


(* Builds vcgen_result with start type *)
let build_vcgen_result_start statement predicate  =
  {
    statement = statement;
    po =  gen_po predicate;
    predicate = predicate;
    stype = StartS; 
  }

  (* Builds vcgen_result with end type *)
let build_vcgen_result_end statement predicate  =
  {
    statement = statement;
    po =  gen_po predicate;
    predicate = predicate;
    stype = EndS; 
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

let build_fun_dec end_stmt start_stmt vcg_wp vcg_sp =
  {
    end_stmt = end_stmt;
    start_stmt =  start_stmt;
    vcgen_result_wp = removeReturnStatement vcg_wp;
    vcgen_result_sp = removeReturnStatement vcg_sp; 
  }

let get_po vcgen_result = 
    vcgen_result.po.proof_obligation

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


(* Replaces the predicate using sp assigment rule *)
let replace_sp lval exp predicate  =
  let folded_exp = Cil.constFold false exp in 
  let exp_term = Logic_utils.expr_to_term ~cast:true folded_exp in
  let logic_var_list = get_lval_logic_vars lval in 
  let llogic_var = List.hd logic_var_list in
  sp_aux := !sp_aux + 1;
  let q_logic_var = Cil_const.make_logic_var_quant ("v"^(string_of_int !sp_aux)) llogic_var.lv_type in 
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



(* Conditional sp rule, with sequence rule already aplied to the two blocks*)
let conditional_sp statement  vcgen_result_b1_list vcgen_result_b2_list =
  let newpredicateb1 = ifVcgenResultIsEmpty vcgen_result_b1_list in
  let newpredicateb2 = ifVcgenResultIsEmpty vcgen_result_b2_list in
  let new_predicate = Logic_const.por (newpredicateb1, newpredicateb2) in
  build_vcgen_result_if statement new_predicate  vcgen_result_b1_list vcgen_result_b2_list


(* Matches the instruction with the definitions and replaces the predicate
 on the instruction, generating a new predicate resulting from the replacement *)
let replace_instruction_sp inst predicate = 
  match inst with
  | Set (lval,exp,location) -> replace_sp lval exp predicate             (* Sp assigment rule *)
  | Call (lval_op,exp,exp_list,location) -> predicate
  | Skip location -> predicate 
  | Asm _ -> predicate
  | Code_annot _ -> predicate


let bin2rel bin =
  match bin with
  | Lt -> Rlt  
  | Gt -> Rgt 
  | Le -> Rle  
  | Ge -> Rge 
  | Eq -> Req 
  | Ne -> Rneq
  | _ -> raise (Invalid_argument "Bin2rel: Only arithmetic comparison implemented\n")

let rec binTerm2relPred term =
  match term.term_node with
  | TBinOp (bin,t1,t2)        -> Logic_const.unamed (Prel (bin2rel bin,t1,t2))
  | TCastE (ty1,cter1)        -> binTerm2relPred cter1
  | TConst lc                 -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TConst not yet implemented")
  | TLval tvar                -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TLval not yet implemented")
  | TUnOp (unop,tnp1)         -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TUnOp not yet implemented")
  | TLogic_coerce (ty,terl)   -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TLogic_coerce not yet implemented")
  | Tat (tat1,ll1)            -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tat not yet implemented")
  | TSizeOf _                 -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TSizeOf not yet implemented")
  | TSizeOfE _                -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TSizeOfE not yet implemented")
  | TSizeOfStr _              -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TSizeOfStr not yet implemented")
  | TAlignOf _                -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TAlignOf not yet implemented")
  | TAlignOfE _               -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TAlignOfE not yet implemented")
  | TAddrOf _                 -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TAddrOf not yet implemented")
  | TStartOf _                -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TStartOf not yet implemented")
  | Tapp _                    -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tapp not yet implemented")
  | Tlambda _                 -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tlambda not yet implemented")
  | TDataCons _               -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TDataCons not yet implemented")
  | Tif _                     -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tif not yet implemented")
  | Tbase_addr _              -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tbase_addr not yet implemented")
  | Toffset _                 -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Toffset not yet implemented")
  | Tblock_length _           -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tblock_length not yet implemented")
  | Tnull                     -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tnull not yet implemented")
  | TCoerce (_,_)             -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TCoerce not yet implemented")
  | TCoerceE (_,_)            -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TCoerce not yet implemented")
  | TUpdate _                 -> raise (Invalid_argument "BinTerm2rel. Logic term with type: TUpdate not yet implemented")
  | Ttypeof _                 -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Ttypeof not yet implemented")
  | Ttype _                   -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Ttype not yet implemented")
  | Tempty_set                -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tempty_set not yet implemented")
  | Tunion _                  -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tunion not yet implemented")
  | Tinter _                  -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tinter not yet implemented")
  | Tcomprehension _          -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tcomprehension not yet implemented")
  | Trange _                  -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Trange not yet implemented")
  | Tlet _                    -> raise (Invalid_argument "BinTerm2rel. Logic term with type: Tlet not yet implemented")

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
      let pred_logic_e = binTerm2relPred logic_e in 
      let n_pred_logic_e = Logic_const.pnot pred_logic_e in 
      let predicateb1 = Logic_const.pand (pred_logic_e,predicate) in
      let predicateb2 = Logic_const.pand (n_pred_logic_e,predicate) in  
      let vcgen_result_b1_list = sequence b1.bstmts predicateb1 replace_statement_sp in
      let vcgen_result_b2_list = sequence b2.bstmts predicateb2 replace_statement_sp in
      conditional_sp statement vcgen_result_b1_list vcgen_result_b2_list
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
let vcgen_wp list_statements post_condt =
  let end_stmt = Cil.mkEmptyStmt ~ghost:true ~valid_sid:true () in
  end_stmt_sid := end_stmt.sid;
  let vc_wp = List.rev (sequence_wp (List.rev list_statements) post_condt) in
  ((vc_wp @ [build_vcgen_result_end end_stmt post_condt]),end_stmt)

let vcgen_sp list_statements pre_condt  =
  let start_stmt = Cil.mkEmptyStmt ~ghost:true ~valid_sid:true () in
  start_stmt_sid := start_stmt.sid;
  let vc_sp = sequence_sp list_statements pre_condt in
  (([build_vcgen_result_start start_stmt pre_condt] @ vc_sp),start_stmt)


(* Returns a list of statements found in fundec.sallstmts after the computation of the cfg *)
let get_list_of_statements fundec = 
	Options.Self.result "Getting list of statements.\n";
	let list_statements = fundec.sbody.bstmts in
  list_statements

(* Get postcondition depeding ond the func_bulidcondtion input *)
let get_PostCondtion funbehavior  =
	let post_condition =  Ast_info.behavior_postcondition (get_opt funbehavior) Normal in
	post_condition 

(* Get postcondition depeding ond the func_bulidcondtion input *)
let get_PreCondtion funbehavior  =
  let pre_condition =  Ast_info.behavior_precondition (get_opt funbehavior) in
  pre_condition 

(* Visits and applys if there kf has definition *)
let apply_if_defition def kf =
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
        let (vc_list_wp,end_stmt) = vcgen_wp list_statements post_condt in
        let (vc_list_sp,start_stmt) = vcgen_sp list_statements pre_condt  in
        let fun_dec = build_fun_dec end_stmt start_stmt vc_list_wp vc_list_sp in
        add_fun kf fun_dec 
	|false -> ()


let calculus () =
  Options.Self.result "Visting functions.\n";
  Globals.Functions.iter
  (
    fun kf -> (apply_if_defition (Kernel_function.is_definition kf) kf)
  ) 


