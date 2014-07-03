open Cil_types

(* Computes cfg for all functions and fills in info information on fundec (smaxstmid and sallsmts) *)
let computeCfg () =
	Globals.Functions.iter_on_fundecs
	(
      fun fundec -> 
      	Cfg.prepareCFG fundec;
      	Cfg.computeCFGInfo fundec false  
	)


(* Visits Statements *)
let visitStatements fd fs =
	Format.printf"Statements.\n"


(* Visits functions *)
let visitFunctions () = 
	Globals.Functions.iter
	(
      fun kf -> 
      	let fundec = Kernel_function.get_definition kf in
      	let funspec = Annotations.funspec kf in 
        visitStatements fundec funspec
	)

  (* Main function *)
  let run () =

     Ast.compute (); 
     if (Ast.is_computed()) then Format.printf"AST computed.\n";

     let c_file = Ast.get() in
     Cfg.clearFileCFG c_file;
     computeCfg ()
     
let () = Db.Main.extend run 