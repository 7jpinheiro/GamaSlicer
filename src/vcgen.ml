open Cil_types

  (* Main function *)
  let run () =

     Ast.compute (); 
     if (Ast.is_computed()) then Format.printf"AST computed.\n";

     let c_file = Ast.get() in
     Cfg.computeFileCFG c_file
     
let () = Db.Main.extend run 