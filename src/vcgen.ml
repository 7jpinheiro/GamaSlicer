open Cil_types

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


(* Visits Statements *)
let visitStatements fundec funspec list_behaviors =
	let funbehavior = Cil.find_default_behavior funspec in
	let post_condition = Ast_info.behavior_postcondition (get_opt funbehavior) Normal in
	post_condition 

(* Visits functions *)
let visitFunctions () = 
	Globals.Functions.iter
	(
      fun kf -> 
      	let fundec = Kernel_function.get_definition kf in
      	let funspec = Annotations.funspec kf in 
      	let list_behaviors = Annotations.behaviors kf in 
        let post_condt = visitStatements fundec funspec list_behaviors in
        ()
	)

  (* Main function *)
  let run () =

     Ast.compute (); 
     if (Ast.is_computed()) then Format.printf"AST computed.\n";

     let c_file = Ast.get() in
     Cfg.clearFileCFG c_file;
     computeCfg ()
     
let () = Db.Main.extend run 