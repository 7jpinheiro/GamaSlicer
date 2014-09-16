open Cil_types
open Plugin
open Printer
open Why3

module Self = 
  Register
    (struct
       let name = "gamaSlicer" 
       let shortname = "gamaSlicer"
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


(* Gets option *)
let get_opt = function
  | Some x -> x
  | None   -> raise (Invalid_argument "Empty Function behavior")

(* Prints a predicate(condition in this case) *)
let print_why3_term term =
	Self.result "Why3 Formula: %a\n" Pretty.print_term term

let print_why3_type ty = 
	Self.result "Why3 Type: %a\n" Pretty.print_ty ty

let print_why3_ls ls =
	Self.result "Why3 Ls: %a\n" Pretty.print_ls ls

(* Prints a predicate(condition in this case) *)
let print_condtion cond =
	Self.result "Post_condition: %a\n" pp_predicate_named cond

(* Prints a statement *)
let print_statement stmt =
	Self.result "Statement: %a\n" pp_stmt stmt

(* Prints a term *)
let print_term term =
	Self.result "Term: %a\n" pp_term term

(* Prints a Logic Label *)
let print_logic_label logic_label =
	Self.result "Logic Label: %a\n" pp_logic_label logic_label

(* Prints a list of statements *)
let print_statements list_statements = 
	List.iter
		(
		 fun s -> Self.result "%a\n" pp_stmt s
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
	 			print_condtion x.predicate;
	 			print_why3_term x.po.proof_obligation;
	 			(*build_task x.po.proof_obligation*)
	) l
	

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

let unit_type = Ty.ty_tuple []
let mlw_int_type = Mlw_ty.ity_pur Ty.ts_int []
let mlw_int32_type = Mlw_ty.ity_pur int32_type []
let mlw_int64_type = Mlw_ty.ity_pur int64_type []

let rec ctype_and_default ty =
  match ty with
    | TVoid _attr -> Mlw_ty.ity_unit, Mlw_expr.e_void
    | TInt (IInt, _attr) ->
      let n = Mlw_expr.e_const (Number.ConstInt (Number.int_const_dec "0")) in
      mlw_int32_type,
      Mlw_expr.e_app
        (Mlw_expr.e_arrow int32ofint_fun [mlw_int_type] mlw_int32_type) [n]
    | TInt (ILong, _attr) ->
      let n = Mlw_expr.e_const (Number.ConstInt (Number.int_const_dec "0")) in
      mlw_int64_type,
      Mlw_expr.e_app
        (Mlw_expr.e_arrow int64ofint_fun [mlw_int_type] mlw_int64_type) [n]
    | TInt (_, _) ->
      Self.not_yet_implemented "ctype TInt"
    | TFloat (_, _) ->
      Self.not_yet_implemented "ctype TFloat"
    | TPtr(TInt _ as t, _attr) ->
      let t,_ = ctype_and_default t in
      Mlw_ty.ity_pur map_ts [mlw_int_type ; t], Mlw_expr.e_void
    | TPtr(_ty, _attr) ->
      Self.not_yet_implemented "ctype TPtr"
    | TArray (_, _, _, _) ->
      Self.not_yet_implemented "ctype TArray"
    | TFun (_, _, _, _) ->
      Self.not_yet_implemented "ctype TFun"
    | TNamed (_, _) ->
      Self.not_yet_implemented "ctype TNamed"
    | TComp (_, _, _) ->
      Self.not_yet_implemented "ctype TComp"
    | TEnum (_, _) ->
      Self.not_yet_implemented "ctype TEnum"
    | TBuiltin_va_list _ ->
      Self.not_yet_implemented "ctype TBuiltin_va_list"

let ctype ty = fst(ctype_and_default ty)

let logic_types = Hashtbl.create 257

let type_vars = ref []

let find_type_var v =
  try
    List.assoc v !type_vars
  with Not_found -> Self.fatal "type variable %s not found" v

let push_type_var v =
  let tv = Ty.create_tvsymbol (Ident.id_fresh v) in
  type_vars := (v,tv) :: !type_vars

let pop_type_var v =
  match !type_vars with
    | (w,_) :: r ->
      if v=w then type_vars := r
      else Self.fatal "pop_type_var: %s expected,found %s" v w
    | [] -> Self.fatal "pop_type_var: empty"

let rec logic_type ty =
  match ty with
    | Linteger -> int_type
    | Lreal -> real_type
    | Ltype (lt, args) ->
      begin
        try
          let ts = Hashtbl.find logic_types lt.lt_name in
          Ty.ty_app ts (List.map logic_type args)
        with
            Not_found -> Self.fatal "logic type %s not found" lt.lt_name
      end
    | Lvar v -> Ty.ty_var (find_type_var v)
    | Ctype _
    | Larrow (_, _) ->
        Self.not_yet_implemented "logic_type"



let mk_ref ty =
    let ref_ty = Mlw_ty.ity_app_fresh ref_type [ty] in
    Mlw_expr.e_arrow ref_fun [ty] ref_ty

let mk_get ref_ty ty =
    Mlw_expr.e_arrow get_fun [ref_ty] ty

let mk_set ref_ty ty =
    (* (:=) has type (r:ref 'a) (v:'a) unit *)
    Mlw_expr.e_arrow set_fun [ref_ty; ty] Mlw_ty.ity_unit


let bound_vars = Hashtbl.create 257

let create_lvar v =
  let id = Ident.id_fresh v.lv_name in
  let vs = Term.create_vsymbol id (logic_type v.lv_type) in
(*
  Self.result "create logic variable %d" v.lv_id;
*)
  Hashtbl.add bound_vars v.lv_id vs;
  vs

let get_lvar lv =
  try
    Hashtbl.find bound_vars lv.lv_id
  with Not_found ->
    Self.fatal "logic variable %s (%d) not found" lv.lv_name lv.lv_id

let program_vars = Hashtbl.create 257

let create_var v is_mutable =
  let vs : Term.vsymbol = Term.create_vsymbol (Ident.id_fresh v.vname) Ty.ty_int in 
  Self.result "create program variable %s (%d)" v.vname v.vid;
  Hashtbl.add program_vars v.vid (vs,is_mutable,Ty.ty_int );
  vs

let get_var v =
  try
    Hashtbl.find program_vars v.vid
  with Not_found ->
    Self.fatal "program variable %s (%d) not found" v.vname v.vid

let logic_symbols = Hashtbl.create 257

let create_lsymbol li =
  let name = li.l_var_info.lv_name in
  let id = Ident.id_fresh name in
  let args = List.map create_lvar li.l_profile in
  let targs = List.map (fun v -> v.Term.vs_ty) args in
  let ret_ty = Opt.map logic_type li.l_type in
  let vs = Term.create_lsymbol id targs ret_ty in
  Self.result "creating logic symbol %d (%s)" li.l_var_info.lv_id name;
  Hashtbl.add logic_symbols li.l_var_info.lv_id vs;
  vs,args

let get_lsymbol li =
  try
    Hashtbl.find logic_symbols li.l_var_info.lv_id
  with
      Not_found -> Self.fatal "logic symbol %s not found" li.l_var_info.lv_name

let result_vsymbol =
  ref (Term.create_vsymbol (Ident.id_fresh "result") unit_type)


let t_app ls args =
  try
     Term.t_app_infer ls args 
  with
    | Not_found -> Self.fatal "lsymbol %s not found" ls.Term.ls_name.Ident.id_string
    | Ty.TypeMismatch(ty1,ty2) -> Self.result" BEGIN ERROR REPORT\n ";
    							  print_why3_type ty1;
    							  print_why3_type ty2;
    							  print_why3_ls ls;
    							  List.map (fun x -> print_why3_term x ;  print_why3_type (get_opt x.t_ty)) args;
    							  Self.fatal" END ERROR REPORT\n ";
    							 
    							  

type label = Here | Old | At of string

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


let coerce_to_int ty t =
  match ty with
    | Linteger -> t
    | Ctype(TInt(IInt,_attr)) -> t_app int32_to_int [t]
    | Ctype(TInt(ILong,_attr)) -> t_app int64_to_int [t]
    | _ -> raise (Invalid_argument "coerce_to_int")


let get_logic_constant_value ~label lc = 
	match lc with
	| Integer (integer,some_value) -> Number.ConstInt (Number.int_const_dec (Pervasives.string_of_int (Integer.to_int integer)))
	| LReal { r_literal = s }	   -> Number.ConstReal (Number.real_const_dec "" "" (Some s))
	| LStr _ 					   -> raise (Invalid_argument "Logic constant with type: LStr not yet implemented")
	| LWStr _ 					   -> raise (Invalid_argument "Logic constant with type: LWStr not yet implemented")
	| LChr _ 					   -> raise (Invalid_argument "Logic constant with type: LChar not yet implemented")
    | LEnum _ 					   -> raise (Invalid_argument "Logic constant with type: LEnum not yet implemented")



let convert_unary2why unop ~label t1 ty1 =
	Self.result "Converting unary : ";
	print_why3_term t1;
	match unop with
	| Neg 	-> t_app minus_int [t1]
	| BNot 	-> raise (Invalid_argument "Unary operation with type: BNot not yet implemented")
	| LNot	-> raise (Invalid_argument "Unary operation with type: LNot not yet implemented")

let convert_binary2why binop ~label t1 ty1 t2 ty2 =
	Self.result "Converting binary : ";
	print_why3_term t1;
	print_why3_term t2;
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

let rec convert_term2why ~label term term_type = 
	Self.result "Converting a term : ";
	print_term term;
	match term.term_node with
	| TConst lc 				-> Term.t_const (get_logic_constant_value ~label lc)
	| TLval tvar 				-> convert_var2why ~label tvar
	| TUnOp (unop,tnp1) 		-> convert_unary2why unop ~label (convert_term2why ~label tnp1 tnp1.term_type) tnp1.term_type
	| TBinOp (binop,tbp1,tbp2)	-> convert_binary2why binop ~label (convert_term2why ~label tbp1 tbp1.term_type) tbp1.term_type (convert_term2why ~label tbp2 tbp2.term_type) tbp2.term_type 
	| TLogic_coerce (ty,terl) when is_int_type ty -> 
								 Self.result"Entrou em TLogic_coerce \n";
								 let whyterm = convert_term2why ~label terl terl.term_type in
								 begin
       								 match ty, terl.term_type with
      							    | Linteger, Ctype(TInt(IInt,_attr)) ->
        							     t_app int32_to_int [whyterm]
       							    | Linteger, Ctype(TInt(ILong,_attr)) ->
      							         t_app int64_to_int [whyterm]
     						        | _ ->
           								 raise (Invalid_argument "Logic term with type: TLogic_coerce without type int (1) not yet implemented")
      							end
    | TLogic_coerce (_,_)		-> raise (Invalid_argument "Logic term with type: TLogic_coerce without type int (2) not yet implemented")
	| Tat (t, lab) ->			 begin
       								 match lab with
        						    | LogicLabel(None, "Here") -> convert_term2why ~label:Here t t.term_type
        							| LogicLabel(None, "Old") -> convert_term2why ~label:Old t t.term_type
        							| LogicLabel(None, lab) -> convert_term2why ~label:(At lab) t t.term_type
        							| LogicLabel(Some _, _lab) ->
         								Self.not_yet_implemented "term_node Tat/LogicLabel/Some"
          							| StmtLabel _ ->
           							 Self.not_yet_implemented "term_node Tat/StmtLabel"
      								end
	| TCastE (ty1,cter1)		-> convert_term2why ~label cter1 cter1.term_type
	| TSizeOf _ 				-> raise (Invalid_argument "Logic term with type: TSizeOf not yet implemented")
	| TSizeOfE _ 				-> raise (Invalid_argument "Logic term with type: TSizeOfE not yet implemented")
	| TSizeOfStr _ 				-> raise (Invalid_argument "Logic term with type: TSizeOfStr not yet implemented")
	| TAlignOf _ 				-> raise (Invalid_argument "Logic term with type: TAlignOf not yet implemented")
	| TAlignOfE _ 				-> raise (Invalid_argument "Logic term with type: TAlignOfE not yet implemented")
	| TAddrOf _ 				-> raise (Invalid_argument "Logic term with type: TAddrOf not yet implemented")
	| TStartOf _ 				-> raise (Invalid_argument "Logic term with type: TStartOf not yet implemented")
	| Tapp _ 					-> raise (Invalid_argument "Logic term with type: Tapp not yet implemented")
	| Tlambda _ 				-> raise (Invalid_argument "Logic term with type: Tlambda not yet implemented")
	| TDataCons _ 				-> raise (Invalid_argument "Logic term with type: TDataCons not yet implemented")
	| Tif _ 					-> raise (Invalid_argument "Logic term with type: Tif not yet implemented")
	| Tbase_addr _ 				-> raise (Invalid_argument "Logic term with type: Tbase_addr not yet implemented")
	| Toffset _ 				-> raise (Invalid_argument "Logic term with type: Toffset not yet implemented")
	| Tblock_length _ 			-> raise (Invalid_argument "Logic term with type: Tblock_length not yet implemented")
	| Tnull						-> raise (Invalid_argument "Logic term with type: Tnull not yet implemented")
	| TCoerce (_,_) 			-> raise (Invalid_argument "Logic term with type: TCoerce not yet implemented")
	| TCoerceE (_,_) 			-> raise (Invalid_argument "Logic term with type: TCoerce not yet implemented")
	| TUpdate _ 				-> raise (Invalid_argument "Logic term with type: TUpdate not yet implemented")
	| Ttypeof _  				-> raise (Invalid_argument "Logic term with type: Ttypeof not yet implemented")
	| Ttype _ 					-> raise (Invalid_argument "Logic term with type: Ttype not yet implemented")
	| Tempty_set 				-> raise (Invalid_argument "Logic term with type: Tempty_set not yet implemented")
	| Tunion _ 					-> raise (Invalid_argument "Logic term with type: Tunion not yet implemented")
	| Tinter _ 					-> raise (Invalid_argument "Logic term with type: Tinter not yet implemented")
	| Tcomprehension _ 			-> raise (Invalid_argument "Logic term with type: Tcomprehension not yet implemented")
	| Trange _ 					-> raise (Invalid_argument "Logic term with type: Trange not yet implemented")
	| Tlet _ 					-> raise (Invalid_argument "Logic term with type: Tlet not yet implemented")

and convert_var2why ~label (t_host,t_offset) =
	Self.result "Entered convert_var2why \n";
	 match t_host,t_offset with
    | TResult _, TNoOffset -> Term.t_var !result_vsymbol
    | TVar lv, TNoOffset ->
      begin
        let t =
          match lv.lv_origin with
            | None -> Term.t_var (get_lvar lv)
            | Some v -> Self.result "Entered Some\n";
              let (vs,is_mutable,_ty) = get_var v in
              match is_mutable with
              |true ->  Self.result "Entered true\n";
              		t_app get_logic_fun [Term.t_var vs]
              |false ->  Self.result "Entered false\n";
              			Term.t_var vs
        in
        match label with
          | Here -> Self.result "Entered Here\n"; t
          | Old -> Self.result "Entered Old\n"; print_why3_term (Mlw_wp.t_at_old t); Mlw_wp.t_at_old t
          | At _lab ->
            (* t_app Mlw_wp.fs_at [t; ??? lab] *)
      Self.not_yet_implemented "tlval TVar/At"
      end
    | TVar _, (TField (_, _)|TModel (_, _)|TIndex (_, _)) ->
      Self.not_yet_implemented "tlval TVar"
    | TResult _, _ ->
      Self.not_yet_implemented "tlval Result"
    | TMem({term_node = TBinOp((PlusPI|IndexPI),t,i)}), TNoOffset ->
      (* t[i] *)
      t_app map_get [(convert_term2why ~label t t.term_type);(convert_term2why ~label i i.term_type)]
    | TMem({term_node = TBinOp(_,t,i)}), TNoOffset ->
      Self.not_yet_implemented "tlval Mem(TBinOp(_,%a,%a), TNoOffset)"
        Cil_printer.pp_term t Cil_printer.pp_term i
    | TMem t, TNoOffset ->
      Self.not_yet_implemented "tlval Mem(%a, TNoOffset)"
        Cil_printer.pp_term t
    | TMem _t, TField _ ->
      Self.not_yet_implemented "tlval Mem TField"
    | TMem _t, TModel _ ->
      Self.not_yet_implemented "tlval Mem TModel"
    | TMem _t, TIndex _ ->
      Self.not_yet_implemented "tlval Mem TNoOffset"


let eq op ty1 t1 ty2 t2 =
  match ty1,ty2 with
    | ty1, ty2 when is_int_type ty1 && is_int_type ty2 ->
      op (coerce_to_int ty1 t1) (coerce_to_int ty2 t2)
    | Lreal, Lreal -> op t1 t2
    | Ctype _,_ ->
      Self.not_yet_implemented "eq Ctype"
    | Ltype _, Ltype _ when ty1 = ty2 -> op t1 t2
    | Lvar _,_ ->
      Self.not_yet_implemented "eq Lvar"
    | Larrow _,_ ->
      Self.not_yet_implemented "eq Larrow"
    | _,_ ->
      Self.not_yet_implemented "eq"


let compare op ty1 t1 ty2 t2 =
  match ty1,ty2 with
    | ty1,ty2 when is_int_type ty1 && is_int_type ty2 ->
      t_app op [coerce_to_int ty1 t1;coerce_to_int ty2 t2]
    | Lreal, Lreal -> assert false
    | Ctype _,_ ->
      Self.not_yet_implemented "compare Ctype"
    | Ltype _, Ltype _ -> assert false
    | Lvar _,_ ->
      Self.not_yet_implemented "compare Lvar"
    | Larrow _,_ ->
      Self.not_yet_implemented "compare Larrow"
    | _,_ ->
      Self.not_yet_implemented "compare"


let convert_rel2why ~label rlt t1 ty1 t2 ty2 =
	Self.result "Converting relation : ";
	print_why3_term t1;
	print_why3_term t2;
	 match rlt with
    | Req -> eq Term.t_equ ty1 t1 ty2 t2
    | Rneq -> eq Term.t_neq ty1 t1 ty2 t2
    | Rge when is_int_type ty1 && is_int_type ty2 -> compare ge_int ty1 t1 ty2 t2
    | Rle when is_int_type ty1 && is_int_type ty2 -> compare le_int ty1 t1 ty2 t2
    | Rgt when is_int_type ty1 && is_int_type ty2 -> compare gt_int ty1 t1 ty2 t2
    | Rlt when is_int_type ty1 && is_int_type ty2 -> compare lt_int ty1 t1 ty2 t2
    | Rge when is_real_type ty1 && is_real_type ty2 -> t_app ge_real [t1;t2]
    | Rge ->
      Self.not_yet_implemented "rel Rge"
    | Rle ->
      Self.not_yet_implemented "rel Rle"
    | Rgt ->
      Self.not_yet_implemented "rel Rgt"
    | Rlt ->
      Self.not_yet_implemented "rel Rlt %a %a"
        Cil_printer.pp_logic_type ty1 Cil_printer.pp_logic_type ty2

let rec convert_pred2why ~label predicate =
	Self.result "Converting predicate : ";
	print_condtion predicate;
	match predicate.content with
	| Pfalse					-> Term.t_false
	| Ptrue 					-> Term.t_true
	| Pnot p_not 				-> Term.t_not (convert_pred2why ~label p_not)
	| Pand (pand1,pand2) 		-> Term.t_and (convert_pred2why ~label pand1) (convert_pred2why ~label pand2)
	| Por (por1,por2) 			-> Term.t_or  (convert_pred2why ~label por1) (convert_pred2why ~label por2)
	| Pimplies (pim1,pim2) 		-> Term.t_implies (convert_pred2why ~label pim1) (convert_pred2why ~label pim2)
	| Piff (piff1,piff2) 		-> Term.t_iff (convert_pred2why ~label piff1) (convert_pred2why ~label piff2)
	| Pif (tif1,pif1,pif2) 		-> Term.t_if (convert_term2why ~label tif1 tif1.term_type) (convert_pred2why ~label pif1) (convert_pred2why ~label pif2)
	| Prel (rlt,trl1,trl2)		-> convert_rel2why ~label rlt (convert_term2why ~label trl1 trl1.term_type) trl1.term_type (convert_term2why ~label trl2 trl2.term_type) trl2.term_type
	| Papp _ 					-> raise (Invalid_argument "Logic predicate with type: Papp not yet implemented")	
	| Pseparated _  			-> raise (Invalid_argument "Logic predicate with type: Pseparated not yet implemented")
	| Pxor _ 					-> raise (Invalid_argument "Logic predicate with type: Pxor not yet implemented")
	| Plet _ 					-> raise (Invalid_argument "Logic predicate with type: Plet not yet implemented")
	| Pforall _ 				-> raise (Invalid_argument "Logic predicate with type: Pforall not yet implemented")
	| Pexists _ 				-> raise (Invalid_argument "Logic predicate with type: Pexists not yet implemented")
	| Pat  _ 					-> raise (Invalid_argument "Logic predicate with type: Pat not yet implemented")
	| Pvalid_read _ 			-> raise (Invalid_argument "Logic predicate with type: Pvalid_read not yet implemented")
	| Pvalid _ 					-> raise (Invalid_argument "Logic predicate with type: Pvalid not yet implemented")
	| Pinitialized _ 			-> raise (Invalid_argument "Logic predicate with type: Pinitialized not yet implemented")
	| Pallocable _ 				-> raise (Invalid_argument "Logic predicate with type: Pallocable not yet implemented")
	| Pfreeable _ 				-> raise (Invalid_argument "Logic predicate with type: Pfreeable not yet implemented")
	| Pfresh _ 					-> raise (Invalid_argument "Logic predicate with type: Pfresh not yet implemented")
	| Psubtype _ 				-> raise (Invalid_argument "Logic predicate with type: Psubtype not yet implemented")

(* Converts the generated predicates to stmt language *)
let gen_po predicate = {proof_obligation = convert_pred2why ~label:Here predicate;}


let build_task why3term = 
	let why3_task = None in
	let why3_goal = Decl.create_prsymbol (Ident.id_fresh "goal1") in
	let why3_task = Task.add_prop_decl why3_task Decl.Pgoal why3_goal why3term in
	Self.result "task is: \n %a" Pretty.print_task why3_task

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
	Self.result "Getting list of statements.\n";
	let list_statements = fundec.sallstmts in
	List.rev list_statements


(* Get condition depeding ond the func_bulidcondtion input *)
let get_Condtion  funspec func_buildcondition =
	Self.result "Getting Condition.\n";
	let funbehavior = Cil.find_default_behavior funspec in
	let post_condition =  func_buildcondition (get_opt funbehavior) Normal in
	post_condition 

(* Visits and applys if there kf has definition *)
let apply_if_defition def kf =
	match def with
	|true ->
		let fundec = Kernel_function.get_definition kf in
		let formals =  List.map (fun v -> create_var v false) (Kernel_function.get_formals kf) in
		let locals = List.map (fun v -> create_var v true) (Kernel_function.get_locals kf) in
      	let funspec = Annotations.funspec kf in 
      	let list_behaviors = Annotations.behaviors kf in 
        let post_condt = get_Condtion funspec  Ast_info.behavior_postcondition  in
        let list_statements = get_list_of_statements fundec in
        let spo_list = vcgen list_statements post_condt in
        spo_list	
	|false -> []

(* Visits functions *)
let visitFunctions () =
	Self.result "Visting functions.\n";
	Globals.Functions.fold
	(
      fun kf acc -> (apply_if_defition (Kernel_function.is_definition kf) kf) @ acc
	) []

  (* Main function *)
  let run () =

     Ast.compute (); 
     if (Ast.is_computed()) then Self.result "AST computed.\n"; 	

     let c_file = Ast.get () in
     Cfg.clearFileCFG c_file;
     computeCfg ();
     let list_stm_and_post = visitFunctions () in
     print_vcgen_result list_stm_and_post
     
let () = Db.Main.extend run 