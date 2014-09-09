open Cil_types
open Plugin
open Printer
open Why3 

module Self = 
  Register
    (struct
       let name = "gamaslicer" 
       let shortname = "gamaslicer"
       let help = "A frama-c plugin that implements assertion based slicing"
     end)

(* Datatype that stores the stmt proof obligation *)
type po = 
{ 
 proof_obligation : Term.term;				
}(* Datatype that stores the vcgen_result  *)
and vcgen_result = 
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


(***************)
(* environment *)
(***************)

let env,config =
  try
    (* reads the Why3 config file *)
    Self.result "Loading Why3 configuration...";
    let config : Whyconf.config = Whyconf.read_config None in
    (* the [main] section of the config file *)
    let main : Whyconf.main = Whyconf.get_main config in
    let env : Env.env = Env.create_env (Whyconf.loadpath main) in
    Self.result "Why3 environment loaded.";
    env,config
  with e ->
    Self.fatal "Exception raised while reading Why3 environment:@ %a"
      Exn_printer.exn_printer e

let find th s =
  try
    Theory.ns_find_ls th.Theory.th_export [s]
  with e ->
    Self.fatal "Exception raised while loading Why3 symbol %s:@ %a"
      s Exn_printer.exn_printer e

let find_type th s =
  try
    Theory.ns_find_ts th.Theory.th_export [s]
  with e ->
    Self.fatal "Exception raised while loading Why3 type %s:@ %a"
      s Exn_printer.exn_printer e

let () = Self.result "Loading Why3 theories..."

(* int.Int theory *)
let int_type : Ty.ty = Ty.ty_int
let int_theory : Theory.theory =
  try
    Env.find_theory env ["int"] "Int"
  with e ->
    Self.fatal "Exception raised while loading int theory:@ %a"
      Exn_printer.exn_printer e

let add_int : Term.lsymbol = find int_theory "infix +"
let sub_int : Term.lsymbol = find int_theory "infix -"
let minus_int : Term.lsymbol = find int_theory "prefix -"
let mul_int : Term.lsymbol = find int_theory "infix *"
let ge_int : Term.lsymbol = find int_theory "infix >="
let le_int : Term.lsymbol = find int_theory "infix <="
let gt_int : Term.lsymbol = find int_theory "infix >"
let lt_int : Term.lsymbol = find int_theory "infix <"

let computer_div_theory : Theory.theory =
  Env.find_theory env ["int"] "ComputerDivision"
let div_int : Term.lsymbol = find computer_div_theory "div"

(* real.Real theory *)
let real_type : Ty.ty = Ty.ty_real
let real_theory : Theory.theory = Env.find_theory env ["real"] "Real"
let add_real : Term.lsymbol = find real_theory "infix +"
let sub_real : Term.lsymbol = find real_theory "infix -"
let minus_real : Term.lsymbol = find real_theory "prefix -"
let mul_real : Term.lsymbol = find real_theory "infix *"
let ge_real : Term.lsymbol = find real_theory "infix >="

(* map.Map theory *)
let map_theory : Theory.theory = Env.find_theory env ["map"] "Map"
let map_ts : Ty.tysymbol = find_type map_theory "map"
(* let map_type (t:Ty.ty) : Ty.ty = Ty.ty_app map_ts [t] *)
let map_get : Term.lsymbol = find map_theory "get"


let () = Self.result "Loading Why3 modules..."

let find_ps mo s =
  try
    Mlw_module.ns_find_ps mo.Mlw_module.mod_export [s]
  with e ->
    Self.fatal "Exception raised while loading Why3 program symbol %s:@ %a"
      s Exn_printer.exn_printer e

let find_ls mo s = find mo.Mlw_module.mod_theory s

(* ref.Ref module *)

let ref_modules, ref_theories =
  try
    Env.read_lib_file (Mlw_main.library_of_env env) ["ref"]
  with e ->
    Self.fatal "Exception raised while loading ref module:@ %a"
      Exn_printer.exn_printer e

let ref_module : Mlw_module.modul = Stdlib.Mstr.find "Ref" ref_modules

let ref_type : Mlw_ty.T.itysymbol =
  Mlw_module.ns_find_its ref_module.Mlw_module.mod_export ["ref"]

let ref_fun : Mlw_expr.psymbol = find_ps ref_module "ref"

let get_logic_fun : Term.lsymbol = find_ls ref_module "prefix !"

let get_fun : Mlw_expr.psymbol = find_ps ref_module "prefix !"

let set_fun : Mlw_expr.psymbol = find_ps ref_module "infix :="

(* mach_int.Int32 module *)

let mach_int_modules, _mach_int_theories =
  try
    Env.read_lib_file (Mlw_main.library_of_env env) ["mach";"int"]
  with e ->
    Self.fatal "Exception raised while loading mach.int modules:@ %a"
      Exn_printer.exn_printer e

let int32_module : Mlw_module.modul =
  try
    Self.result "Looking up module mach.int.Int32";
    Stdlib.Mstr.find "Int32" mach_int_modules
  with Not_found ->
    Self.fatal "Module mach.int.Int32 not found"

let int32_type : Why3.Ty.tysymbol =
  Mlw_module.ns_find_ts int32_module.Mlw_module.mod_export ["int32"]

let int32_to_int : Term.lsymbol = find_ls int32_module "to_int"

let add32_fun : Mlw_expr.psymbol = find_ps int32_module "infix +"

let sub32_fun : Mlw_expr.psymbol = find_ps int32_module "infix -"

let mul32_fun : Mlw_expr.psymbol = find_ps int32_module "infix *"

let neg32_fun : Mlw_expr.psymbol = find_ps int32_module "prefix -"

let eq32_fun : Mlw_expr.psymbol = find_ps int32_module "eq"

let ne32_fun : Mlw_expr.psymbol = find_ps int32_module "ne"

let le32_fun : Mlw_expr.psymbol = find_ps int32_module "infix <="

let lt32_fun : Mlw_expr.psymbol = find_ps int32_module "infix <"

let ge32_fun : Mlw_expr.psymbol = find_ps int32_module "infix >="

let gt32_fun : Mlw_expr.psymbol = find_ps int32_module "infix >"

let int32ofint_fun : Mlw_expr.psymbol = find_ps int32_module "of_int"

(* mach_int.Int64 module *)

let int64_module : Mlw_module.modul =
  try
    Self.result "Looking up module mach.int.Int64";
    Stdlib.Mstr.find "Int64" mach_int_modules
  with Not_found ->
    Self.fatal "Module mach.int.Int64 not found"

let int64_type : Why3.Ty.tysymbol =
  Mlw_module.ns_find_ts int64_module.Mlw_module.mod_export ["int64"]

let int64_to_int : Term.lsymbol = find_ls int64_module "to_int"

let add64_fun : Mlw_expr.psymbol = find_ps int64_module "infix +"

let sub64_fun : Mlw_expr.psymbol = find_ps int64_module "infix -"

let mul64_fun : Mlw_expr.psymbol = find_ps int64_module "infix *"

let le64_fun : Mlw_expr.psymbol = find_ps int64_module "infix <="

let lt64_fun : Mlw_expr.psymbol = find_ps int64_module "infix <"

let int64ofint_fun : Mlw_expr.psymbol = find_ps int64_module "of_int"

let t_app ls args =
  try
    Term.t_app_infer ls args
  with
      Not_found ->
        Self.fatal "lsymbol %s not found" ls.Term.ls_name.Ident.id_string

let is_int_type t =
  match t with
    | Linteger -> true
    | Ctype(TInt (_, _)) -> true
    | _ -> false

let is_real_type t =
  match t with
    | Lreal -> true
    | Ctype(TFloat (_, _)) -> true
    | _ -> false


(* Converts the generated predicates to stmt language *)
let gen_po predicate = {proof_obligation = Term.t_true;}


let get_logic_constant_value lc = 
	match lc with
	| Integer (integer,some_value) -> Number.ConstInt (Number.int_const_dec (Pervasives.string_of_int integer))
	| LReal lr	    			   -> Number.ConstReal (Number.real_const_dec lr.r_literal)
	| LStr _ 					   -> raise (Invalid_argument "Logic constant with type: LStr not yet implemented")
	| LWStr _ 					   -> raise (Invalid_argument "Logic constant with type: LWStr not yet implemented")
	| LChar _ 					   -> raise (Invalid_argument "Logic constant with type: LChar not yet implemented")
    | LEnum _ 					   -> raise (Invalid_argument "Logic constant with type: LEnum not yet implemented")

let get_logic_var_value (t_host,t_offset) =
	match t_host with
	| TVar lc 	-> Term.create_vsymbol (Ident.id_fresh lc.lv_name ) Ty.ty_int  
	| TResult 	-> raise (Invalid_argument "Logic var host with type: LResult not yet implemented")
	| TMem  	-> raise (Invalid_argument "Logic var host with type: TMem not yet implemented")


let convert_unary2why unop term =
	match unop with
	| Neg 	-> t_app minus_int [term]
	| BNot 	-> raise (Invalid_argument "Unary operation with type: BNot not yet implemented")
	| LNot	-> raise (Invalid_argument "Unary operation with type: LNot not yet implemented")

let rec convert_binary2why binop t1 t2 =
	match binop with 	
	| PlusA			-> t_app add_int [t1;t2]
	| MinusA  		-> t_app sub_int [t1;t2]
	| Mult 			-> t_app mul_int [t1;t2]
	| Div  			-> t_app div_int [t1;t2]
	| Mod			-> raise (Invalid_argument "Binary operation with type: Mod not yet implemented")
	| Shiftlt 		-> raise (Invalid_argument "Binary operation with type: Shiftrt not yet implemented")
	| Shiftrt		-> raise (Invalid_argument "Binary operation with type: Shiftrt not yet implemented")
	| Lt			-> raise (Invalid_argument "Binary operation with type: Lt not yet implemented")
	| Gt			-> raise (Invalid_argument "Binary operation with type: Gt not yet implemented")
	| Le			-> raise (Invalid_argument "Binary operation with type: Le not yet implemented")
	| Ge			-> raise (Invalid_argument "Binary operation with type: Ge not yet implemented")
	| Eq			-> raise (Invalid_argument "Binary operation with type: Eq not yet implemented")
	| Ne			-> raise (Invalid_argument "Binary operation with type: Ne not yet implemented")
	| BAnd			-> raise (Invalid_argument "Binary operation with type: BAnd not yet implemented")
	| BXor			-> raise (Invalid_argument "Binary operation with type: BXor not yet implemented")
	| BOr			-> raise (Invalid_argument "Binary operation with type: BOr not yet implemented")
	| LAnd			-> raise (Invalid_argument "Binary operation with type: LAnd not yet implemented")
	| LOr			-> raise (Invalid_argument "Binary operation with type: LOr not yet implemented")
	| PlusPI		-> raise (Invalid_argument "Binary operation with type: PlusPI not yet implemented")
	| IndexPI		-> raise (Invalid_argument "Binary operation with type: IndexPI not yet implemented")
	| MinusPI		-> raise (Invalid_argument "Binary operation with type: MinusPI not yet implemented")
	| MinusPP		-> raise (Invalid_argument "Binary operation with type: MinusPP not yet implemented")

let rec convert_term2why term = 
	| match term.term_node with
	| TConst lc 				-> Term.t_const get_logic_constant_value lc
	| TLval tvar 				-> Term.t_var get_logic_var_value tvar
	| TUnOp (unop,tnp1) 		-> convert_unary2why unop (convert_term2why tnp1)
	| TBinOp (binop,tbp1,tbp2)	-> convert_binary2why binop (convert_term2why tbp1) (convert_term2why tbp2)
	| TSizeOf _ 				-> raise (Invalid_argument "Logic term with type: TSizeOf not yet implemented")
	| TSizeOfE _ 				-> raise (Invalid_argument "Logic term with type: TSizeOfE not yet implemented")
	| TSizeOfStr _ 				-> raise (Invalid_argument "Logic term with type: TSizeOfStr not yet implemented")
	| TAlignOf _ 				-> raise (Invalid_argument "Logic term with type: TAlignOf not yet implemented")
	| TAlignOfE _ 				-> raise (Invalid_argument "Logic term with type: TAlignOfE not yet implemented")
	| TCastE _ 					-> raise (Invalid_argument "Logic term with type: TCastE not yet implemented")
	| TAddrOf _ 				-> raise (Invalid_argument "Logic term with type: TAddrOf not yet implemented")
	| TStartOf _ 				-> raise (Invalid_argument "Logic term with type: TStartOf not yet implemented")
	| Tapp _ 					-> raise (Invalid_argument "Logic term with type: Tapp not yet implemented")
	| Tlambda _ 				-> raise (Invalid_argument "Logic term with type: Tlambda not yet implemented")
	| TDataCons _ 				-> raise (Invalid_argument "Logic term with type: TDataCons not yet implemented")
	| Tif _ 					-> raise (Invalid_argument "Logic term with type: Tif not yet implemented")
	| Tat _ 					-> raise (Invalid_argument "Logic term with type: Tat not yet implemented")
	| Tbase_addr _ 				-> raise (Invalid_argument "Logic term with type: Tbase_addr not yet implemented")
	| Toffset _ 				-> raise (Invalid_argument "Logic term with type: Toffset not yet implemented")
	| Tblock_length _ 			-> raise (Invalid_argument "Logic term with type: Tblock_length not yet implemented")
	| Tnull						-> raise (Invalid_argument "Logic term with type: Tnull not yet implemented")
	| TLogic_coerce _ 			-> raise (Invalid_argument "Logic term with type: TLogic_coerce not yet implemented")
	| TCoerceE _ 				-> raise (Invalid_argument "Logic term with type: TCoerceE not yet implemented")
	| TUpdate _ 				-> raise (Invalid_argument "Logic term with type: TUpdate not yet implemented")
	| Ttypeof _  				-> raise (Invalid_argument "Logic term with type: Ttypeof not yet implemented")
	| Ttype _ 					-> raise (Invalid_argument "Logic term with type: Ttype not yet implemented")
	| Tempty_set 				-> raise (Invalid_argument "Logic term with type: Tempty_set not yet implemented")
	| Tunion _ 					-> raise (Invalid_argument "Logic term with type: Tunion not yet implemented")
	| Tinter _ 					-> raise (Invalid_argument "Logic term with type: Tinter not yet implemented")
	| Tcomprehension _ 			-> raise (Invalid_argument "Logic term with type: Tcomprehension not yet implemented")
	| Trange _ 					-> raise (Invalid_argument "Logic term with type: Trange not yet implemented")
	| Tlet _ 					-> raise (Invalid_argument "Logic term with type: Tlet not yet implemented")



let rec convert_rel2why rlt term1 term2 =
	match rlt with 
	| Rlt 	-> t_app lt_int [term1;term2]
	| Rgt 	-> t_app gt_int [term1;term2]
	| Rle 	-> t_app le_int [term1;term2]
	| Rge 	-> t_app ge_int [term1;term2]
	| Req 	-> Term.t_equ (convert_term2why term1) (convert_term2why term2)
	| Rneq 	-> Term.t_neq (convert_term2why term1) (convert_term2why term2)   

let rec convert_pred2why predicate = 
	match predicate.content with
	| Pfalse						-> Term.t_false
	| Ptrue 						-> Term.t_true
	| Pnot 		p_not 				-> Term.t_not (convert_pred2why p_not)
	| Pand 		(pand1,pand2) 		-> Term.t_and (convert_pred2why pand1) (convert_pred2why pand2)
	| Por 		(por1,por2) 		-> Term.t_or  (convert_pred2why por1) (convert_pred2why por2)
	| Pimplies	(pim1,pim2) 		-> Term.t_implies (convert_pred2why pim1) (convert_pred2why pim2)
	| Piff 		(piff1,piff2) 		-> Term.t_iff (convert_pred2why piff1) (convert_pred2why piff2)
	| Pif 		(tif1,pif1,pif2) 	-> Term.t_if (convert_termw2hy tif1) (convert_pred2why pif1) (convert_pred2why pif2)
	| Prel 		(rlt,trl1,trl2)		-> convert_rel2why rlt trl1 trl2

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

(* Gets option *)
let get_opt = function
  | Some x -> x
  | None   -> raise (Invalid_argument "Empty Function behavior")


(* Prints a predicate(condition in this case) *)
let print_condtion cond =
	Format.printf"Post_condition: %a\n" pp_predicate_named cond

(* Prints a statement *)
let print_statement stmt =
	Format.printf"Statement: %a\n" pp_stmt stmt

(* Prints a term *)
let print_term term =
	Format.printf"Term: %a\n" pp_term term

(* Prints a list of statements *)
let print_statements list_statements = 
	List.iter
		(
		 fun s -> Format.printf"%a\n" pp_stmt s
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

(* Tests if the vcgen_result list is empty, if it is returns the predicate true,
 if contains elements returns the last resulting predicate *)
let ifVcgenResultIsEmpty vcgen_result_list =
	match vcgen_result_list with
	| [] -> Logic_const.ptrue
	| l  -> 
		let last_vcgen_result = List.hd (List.rev l) in
		last_vcgen_result.predicate

(* Replaces the predicate  *)
let replace lval exp predicate  =
	let folded_exp = Cil.constFold false exp in 
	let exp_term = Logic_utils.expr_to_term ~cast:true folded_exp in
    let var_name = get_var_name_from_lval lval in
    if (var_name <> "NOT_A_VARIABLE") then 
   		 Visitor.visitFramacPredicateNamed (new replace_term_on_predicate (Project.current ()) exp_term var_name) predicate 
    	else predicate


(* Generic sequence rule *)
let rec sequence list_statements predicate func =
	match list_statements with
	|[] -> []
	| s::stail -> 
		let vcgen_result = func s predicate in
		vcgen_result::(sequence stail vcgen_result.predicate func)				


(* Matches the instruction with the definitions and replaces the predicate
 on the instruction, generating a new predicate resulting from the replacement *)
let replace_instruction inst predicate = 
	match inst with
	| Set (lval,exp,location) -> replace lval exp predicate 						(* Wp assigment rule *)
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
			let new_predicate = replace_instruction i predicate in
			build_vcgen_result_simple statement new_predicate 
	| Return _ ->
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

(* Genetares proof obligations, and returns a list with vcgen_result *)
let vcgen list_statements predicate =
	sequence_wp list_statements predicate

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