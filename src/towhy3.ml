open Cil_types
open Plugin
open Printer
open Why3
open Why3.Call_provers


module Self = 
  Register
    (struct
       let name = "gamaSlicer" 
       let shortname = "gamaSlicer"
       let help = "A frama-c plugin that implements assertion based slicing"
     end)


(***************)
(* environment *)
(***************)

let config = Whyconf.read_config None
let provers = Whyconf.get_provers config
let main = Whyconf.get_main config
let env = Env.create_env (Whyconf.loadpath main)

let int_theory = Env.read_theory  env ["int"] "Int"
let computer_division_theory = Env.read_theory env ["int"] "ComputerDivision"
let ref_module = Mlw_module.read_module env ["ref"] "Ref"


let bound_vars = Hashtbl.create 257

let create_lvar v =
  let id = Ident.id_fresh v.lv_name in
  let vs = Term.create_vsymbol id Ty.ty_int in
  Hashtbl.add bound_vars v.lv_id vs;
  vs

let get_lvar lv =
  try
    Hashtbl.find bound_vars lv.lv_id
  with Not_found ->
    Self.fatal "logic variable %s (%d) not found" lv.lv_name lv.lv_id

let program_vars = Hashtbl.create 257

let create_var v is_mutable =
  let vs = Term.create_vsymbol (Ident.id_fresh v.vname) Ty.ty_int in 
  Self.result "create program variable %s (%d)" v.vname v.vid;
  Hashtbl.add program_vars v.vname (vs,is_mutable,Ty.ty_int );
  vs

let get_var v =
  try
    Hashtbl.find program_vars v.vname
  with Not_found ->
    Self.fatal "program variable %s (%d) not found" v.vname v.vid


let rec getToBound toBound = function
  | ter ->
     begin 
       match ter.Term.t_node with
       | Term.Tconst(n) -> toBound
       | Term.Tnot(t) -> getToBound toBound t
       | Term.Tvar (vs) ->
    begin
      if List.mem vs toBound then toBound
      else vs :: toBound
    end
       | Term.Tapp(s,ts) -> List.concat (List.map (getToBound toBound) ts)
       | Term.Tbinop(binop,t1,t2) -> (getToBound toBound t1) @ (getToBound toBound t2)
       | Term.Tquant(ts,tqua) ->
    begin
      let triple = Term.t_open_quant tqua in
      let _,_,t = triple in
      getToBound toBound t
    end
       | _ -> toBound
     end

let bound_vars term =
   let varToBound = getToBound [] term in
   let newFormula = Term.t_forall_close varToBound [] term in
   newFormula

let const2why lc = 
  match lc with
  | Integer (integer,some_value)  -> let int_const = Number.ConstInt (Number.int_const_dec (Pervasives.string_of_int (Integer.to_int integer))) in
                                     Term.t_const int_const
  | LReal { r_literal = s }       -> let real_const = Number.ConstReal (Number.real_const_dec "" "" (Some s)) in
                                     Term.t_const real_const 
  | LStr _                        -> raise (Invalid_argument "Logic constant with type: LStr not yet implemented")
  | LWStr _                       -> raise (Invalid_argument "Logic constant with type: LWStr not yet implemented")
  | LChr _                        -> raise (Invalid_argument "Logic constant with type: LChar not yet implemented")
  | LEnum _                       -> raise (Invalid_argument "Logic constant with type: LEnum not yet implemented")

let var2why (t_host,t_offset) =
  match t_host with
  | TVar lc   -> 
      begin    
        let tvar =
          match lc.lv_origin with
            | None -> Term.t_var (get_lvar lc)
            | Some v -> 
              let (vs,is_mutable,_ty) = get_var v in
              match is_mutable with
              |true -> 
                      let get_logic_fun = Theory.ns_find_ls ref_module.Mlw_module.mod_theory.Theory.th_export ["prefix !"] in
                      Term.t_app_infer get_logic_fun [Term.t_var vs]
              |false -> 
                      Term.t_var vs
        in
        tvar
        end
  | TResult _ -> raise (Invalid_argument "Logic var host with type: LResult not yet implemented")
  | TMem  _   -> raise (Invalid_argument "Logic var host with type: TMem not yet implemented")

let rec term2why term = 
  match term.term_node with
  | TConst lc                 -> const2why lc
  | TLval tvar                -> var2why tvar
  | TUnOp (unop,tnp1)         -> una2why unop tnp1
  | TBinOp (binop,tbp1,tbp2)  -> bin2why binop tbp1 tbp2
  | TLogic_coerce (ty,terl)   -> term2why terl
  | Tat (tat1,ll1)            -> term2why tat1
  | TCastE (ty1,cter1)        -> term2why cter1
  | TSizeOf _                 -> raise (Invalid_argument "Logic term with type: TSizeOf not yet implemented")
  | TSizeOfE _                -> raise (Invalid_argument "Logic term with type: TSizeOfE not yet implemented")
  | TSizeOfStr _              -> raise (Invalid_argument "Logic term with type: TSizeOfStr not yet implemented")
  | TAlignOf _                -> raise (Invalid_argument "Logic term with type: TAlignOf not yet implemented")
  | TAlignOfE _               -> raise (Invalid_argument "Logic term with type: TAlignOfE not yet implemented")
  | TAddrOf _                 -> raise (Invalid_argument "Logic term with type: TAddrOf not yet implemented")
  | TStartOf _                -> raise (Invalid_argument "Logic term with type: TStartOf not yet implemented")
  | Tapp _                    -> raise (Invalid_argument "Logic term with type: Tapp not yet implemented")
  | Tlambda _                 -> raise (Invalid_argument "Logic term with type: Tlambda not yet implemented")
  | TDataCons _               -> raise (Invalid_argument "Logic term with type: TDataCons not yet implemented")
  | Tif _                     -> raise (Invalid_argument "Logic term with type: Tif not yet implemented")
  | Tbase_addr _              -> raise (Invalid_argument "Logic term with type: Tbase_addr not yet implemented")
  | Toffset _                 -> raise (Invalid_argument "Logic term with type: Toffset not yet implemented")
  | Tblock_length _           -> raise (Invalid_argument "Logic term with type: Tblock_length not yet implemented")
  | Tnull                     -> raise (Invalid_argument "Logic term with type: Tnull not yet implemented")
  | TCoerce (_,_)             -> raise (Invalid_argument "Logic term with type: TCoerce not yet implemented")
  | TCoerceE (_,_)            -> raise (Invalid_argument "Logic term with type: TCoerce not yet implemented")
  | TUpdate _                 -> raise (Invalid_argument "Logic term with type: TUpdate not yet implemented")
  | Ttypeof _                 -> raise (Invalid_argument "Logic term with type: Ttypeof not yet implemented")
  | Ttype _                   -> raise (Invalid_argument "Logic term with type: Ttype not yet implemented")
  | Tempty_set                -> raise (Invalid_argument "Logic term with type: Tempty_set not yet implemented")
  | Tunion _                  -> raise (Invalid_argument "Logic term with type: Tunion not yet implemented")
  | Tinter _                  -> raise (Invalid_argument "Logic term with type: Tinter not yet implemented")
  | Tcomprehension _          -> raise (Invalid_argument "Logic term with type: Tcomprehension not yet implemented")
  | Trange _                  -> raise (Invalid_argument "Logic term with type: Trange not yet implemented")
  | Tlet _                    -> raise (Invalid_argument "Logic term with type: Tlet not yet implemented")

and una2why unop term =
  match unop with
  | Neg   -> let neg_int = Theory.ns_find_ls int_theory.Theory.th_export ["prefix -"] in
             Term.fs_app neg_int [term2why term] Ty.ty_int
  | BNot  -> raise (Invalid_argument "Unary operation with type: BNot not yet implemented")
  | LNot  -> raise (Invalid_argument "Unary operation with type: LNot not yet implemented")

and bin2why binop t1 t2 =
  match binop with  
  | PlusA       -> let add_int = Theory.ns_find_ls int_theory.Theory.th_export ["infix +"] in
                   Term.fs_app add_int [term2why t1; term2why t2] Ty.ty_int
  | MinusA      -> let sub_int = Theory.ns_find_ls int_theory.Theory.th_export ["infix -"] in
                   Term.fs_app sub_int [term2why t1; term2why t2] Ty.ty_int
  | Mult        -> let mul_int = Theory.ns_find_ls int_theory.Theory.th_export ["infix *"] in
                   Term.fs_app mul_int [term2why t1; term2why t2] Ty.ty_int
  | Div         -> let div_int = Theory.ns_find_ls computer_division_theory.Theory.th_export ["div"] in
                   Term.fs_app div_int [term2why t1; term2why t2] Ty.ty_int
  | Mod         -> let mod_int = Theory.ns_find_ls computer_division_theory.Theory.th_export ["mod"] in
                   Term.fs_app mod_int [term2why t1; term2why t2] Ty.ty_int
  | Shiftlt     -> raise (Invalid_argument "Binary operation with type: Shiftrt not yet implemented")
  | Shiftrt     -> raise (Invalid_argument "Binary operation with type: Shiftrt not yet implemented")
  | Lt          -> raise (Invalid_argument "Binary operation with type: Lt not yet implemented")
  | Gt          -> raise (Invalid_argument "Binary operation with type: Gt not yet implemented")
  | Le          -> raise (Invalid_argument "Binary operation with type: Le not yet implemented")
  | Ge          -> raise (Invalid_argument "Binary operation with type: Ge not yet implemented")
  | Eq          -> raise (Invalid_argument "Binary operation with type: Eq not yet implemented")
  | Ne          -> raise (Invalid_argument "Binary operation with type: Ne not yet implemented")
  | BAnd        -> raise (Invalid_argument "Binary operation with type: BAnd not yet implemented")
  | BXor        -> raise (Invalid_argument "Binary operation with type: BXor not yet implemented")
  | BOr         -> raise (Invalid_argument "Binary operation with type: BOr not yet implemented")
  | LAnd        -> raise (Invalid_argument "Binary operation with type: LAnd not yet implemented")
  | LOr         -> raise (Invalid_argument "Binary operation with type: LOr not yet implemented")
  | PlusPI      -> raise (Invalid_argument "Binary operation with type: PlusPI not yet implemented")
  | IndexPI     -> raise (Invalid_argument "Binary operation with type: IndexPI not yet implemented")
  | MinusPI     -> raise (Invalid_argument "Binary operation with type: MinusPI not yet implemented")
  | MinusPP     -> raise (Invalid_argument "Binary operation with type: MinusPP not yet implemented")


let rel2why rlt term1 term2 =
  match rlt with 
  | Rlt  -> let lt_int = Theory.ns_find_ls int_theory.Theory.th_export ["infix <"]  in
            Term.ps_app lt_int [term2why term1; term2why term2]
  | Rgt  -> let gt_int = Theory.ns_find_ls int_theory.Theory.th_export ["infix >"]  in
            Term.ps_app gt_int [term2why term1; term2why term2]
  | Rle  -> let le_int = Theory.ns_find_ls int_theory.Theory.th_export ["infix <="] in
            Term.ps_app le_int [term2why term1; term2why term2]
  | Rge  -> let ge_int = Theory.ns_find_ls int_theory.Theory.th_export ["infix >="] in
            Term.ps_app ge_int [term2why term1; term2why term2]
  | Req  -> let eq_int = Theory.ns_find_ls int_theory.Theory.th_export ["infix ="] in
            Term.ps_app eq_int [term2why term1; term2why term2]
  | Rneq -> let eq_int = Theory.ns_find_ls int_theory.Theory.th_export ["infix ="] in
            Term.t_not (Term.ps_app eq_int [term2why term1; term2why term2])

let rec pred2why predicate = 
  match predicate.content with
  | Pfalse                 -> Term.t_false
  | Ptrue                  -> Term.t_true
  | Pnot p_not             -> Term.t_not (pred2why p_not)
  | Pand (pand1,pand2)     -> Term.t_and (pred2why pand1) (pred2why pand2)
  | Por (por1,por2)        -> Term.t_or  (pred2why por1) (pred2why por2)
  | Pimplies (pim1,pim2)   -> Term.t_implies (pred2why pim1) (pred2why pim2)
  | Piff (piff1,piff2)     -> Term.t_iff (pred2why piff1) (pred2why piff2)
  | Pif (tif1,pif1,pif2)   -> Term.t_if (term2why tif1) (pred2why pif1) (pred2why pif2)
  | Prel (rlt,trl1,trl2)   -> rel2why rlt trl1 trl2
  | Papp _                 -> raise (Invalid_argument "Logic predicate with type: Papp not yet implemented") 
  | Pseparated _           -> raise (Invalid_argument "Logic predicate with type: Pseparated not yet implemented")
  | Pxor _                 -> raise (Invalid_argument "Logic predicate with type: Pxor not yet implemented")
  | Plet _                 -> raise (Invalid_argument "Logic predicate with type: Plet not yet implemented")
  | Pforall _              -> raise (Invalid_argument "Logic predicate with type: Pforall not yet implemented")
  | Pexists _              -> raise (Invalid_argument "Logic predicate with type: Pexists not yet implemented")
  | Pat  _                 -> raise (Invalid_argument "Logic predicate with type: Pat not yet implemented")
  | Pvalid_read _          -> raise (Invalid_argument "Logic predicate with type: Pvalid_read not yet implemented")
  | Pvalid _               -> raise (Invalid_argument "Logic predicate with type: Pvalid not yet implemented")
  | Pinitialized _         -> raise (Invalid_argument "Logic predicate with type: Pinitialized not yet implemented")
  | Pallocable _           -> raise (Invalid_argument "Logic predicate with type: Pallocable not yet implemented")
  | Pfreeable _            -> raise (Invalid_argument "Logic predicate with type: Pfreeable not yet implemented")
  | Pfresh _               -> raise (Invalid_argument "Logic predicate with type: Pfresh not yet implemented")
  | Psubtype _             -> raise (Invalid_argument "Logic predicate with type: Psubtype not yet implemented")