open Why3
open Why3.Call_provers
open Towhy3


type sup_provers =
| Alt_ergo
| Z3
| CVC3
| CVC4
| Yices
| EProver

type prover_result =
{
  mutable name : string;
  mutable version : string;
  mutable result : string;
  mutable time : float;
}

let parseProverAnswer = function
  | Valid -> "Valid"
  | Invalid -> "Invalid"
  | Timeout -> "Timeout"
  | OutOfMemory -> "Ouf Of Memory"
  | Unknown "" -> "Unknown"
  | Failure "" -> "Failure"
  | Unknown s -> Format.sprintf "Unknown (%s)" s
  | Failure s -> Format.sprintf "Failure (%s)" s
  | HighFailure -> "HighFailure"

let build_prover_result result time name version =
  {
   name = name;
   version = version;
   result = result; 
   time = time;
  }


let alt_ergo : Whyconf.config_prover =
  try
    let prover = {Whyconf.prover_name = "Alt-Ergo";
                  prover_version = "0.95.2";
                  prover_altern = ""} in
    Whyconf.Mprover.find prover provers
  with Not_found ->
    Format.eprintf "Prover alt-ergo not installed or not configured@.";
    exit 0

let z3 : Whyconf.config_prover =
  try
    let prover = {Whyconf.prover_name = "Z3";
                  prover_version = "4.3.1";
                  prover_altern = ""} in
    Whyconf.Mprover.find prover provers
  with Not_found ->
    Format.eprintf "Prover Z3 not installed or not configured@.";
    exit 0    


let cvc4 : Whyconf.config_prover =
  try
    let prover = {Whyconf.prover_name = "CVC4";
                  prover_version = "1.4";
                  prover_altern = ""} in
    Whyconf.Mprover.find prover provers
  with Not_found ->
    Format.eprintf "Prover cvc4 not installed or not configured@.";
    exit 0

let cvc3 : Whyconf.config_prover =
  try
    let prover = {Whyconf.prover_name = "CVC3";
                  prover_version = "2.4.1";
                  prover_altern = ""} in
    Whyconf.Mprover.find prover provers
  with Not_found ->
    Format.eprintf "Prover cvc3 not installed or not configured@.";
    exit 0

let yices : Whyconf.config_prover =
  try
    let prover = {Whyconf.prover_name = "Yices";
                  prover_version = "2.2.2";
                  prover_altern = ""} in
    Whyconf.Mprover.find prover provers
  with Not_found ->
    Format.eprintf "Prover yices not installed or not configured@.";
    exit 0

let e_prover : Whyconf.config_prover =
  try
    let prover = {Whyconf.prover_name = "Eprover";
                  prover_version = "1.8-001";
                  prover_altern = ""} in
    Whyconf.Mprover.find prover provers
  with Not_found ->
    Format.eprintf "Prover E-prover not installed or not configured@.";
    exit 0

let alt_ergo_driver : Driver.driver =
  try
    Driver.load_driver env alt_ergo.Whyconf.driver []
  with e ->
    Format.eprintf "Failed to load driver for alt-ergo: %a@."
      Exn_printer.exn_printer e;
    exit 1

  let z3_driver : Driver.driver =
  try
    Driver.load_driver env z3.Whyconf.driver []
  with e ->
    Format.eprintf "Failed to load driver for Z3: %a@."
      Exn_printer.exn_printer e;
    exit 1


let cvc4_driver : Driver.driver =
  try
    Driver.load_driver env cvc4.Whyconf.driver []
  with e ->
    Format.eprintf "Failed to load driver for cvc4: %a@."
      Exn_printer.exn_printer e;
    exit 1

let cvc3_driver : Driver.driver =
  try
    Driver.load_driver env cvc3.Whyconf.driver []
  with e ->
    Format.eprintf "Failed to load driver for cvc3: %a@."
      Exn_printer.exn_printer e;
    exit 1

let yices_driver : Driver.driver =
  try
    Driver.load_driver env yices.Whyconf.driver []
  with e ->
    Format.eprintf "Failed to load driver for yices: %a@."
      Exn_printer.exn_printer e;
    exit 1

let e_prover_driver : Driver.driver =
  try
    Driver.load_driver env e_prover.Whyconf.driver []
  with e ->
    Format.eprintf "Failed to load driver for e_prover: %a@."
      Exn_printer.exn_printer e;
    exit 1


 let proveAltErgo term = 
       let task = None in
       let task = Task.use_export task int_theory in
       let task = Task.use_export task computer_division_theory in
       let goal = Decl.create_prsymbol (Ident.id_fresh "goal") in
       let task = Task.add_prop_decl task Decl.Pgoal goal term in

       let result : Call_provers.prover_result = Call_provers.wait_on_call (Driver.prove_task ~command:alt_ergo.Whyconf.command alt_ergo_driver task ()) () in

       let answer = parseProverAnswer (result.pr_answer) in
       
       (answer,result.pr_time) 

let rec proveZ3  term =
       let task = None in
       let task = Task.use_export task int_theory in
       let task = Task.use_export task computer_division_theory in
       let goal = Decl.create_prsymbol (Ident.id_fresh "goal") in
       let task = Task.add_prop_decl task Decl.Pgoal goal term in

       let result : Call_provers.prover_result = Call_provers.wait_on_call (Driver.prove_task ~command:z3.Whyconf.command z3_driver task ()) () in

       let answer = parseProverAnswer (result.pr_answer) in
       
       (answer,result.pr_time)    


let proveCVC4 term =
       let task = None in
       let task = Task.use_export task int_theory in
       let task = Task.use_export task computer_division_theory in
       let goal = Decl.create_prsymbol (Ident.id_fresh "goal") in
       let task = Task.add_prop_decl task Decl.Pgoal goal term in

       let result : Call_provers.prover_result = Call_provers.wait_on_call (Driver.prove_task ~command:cvc4.Whyconf.command cvc4_driver task ()) () in

       let answer = parseProverAnswer (result.pr_answer) in
       
      (answer,result.pr_time) 


let proveCVC3 term =
       let task = None in
       let task = Task.use_export task int_theory in
       let task = Task.use_export task computer_division_theory in
       let goal = Decl.create_prsymbol (Ident.id_fresh "goal") in
       let task = Task.add_prop_decl task Decl.Pgoal goal term in

       let result : Call_provers.prover_result = Call_provers.wait_on_call (Driver.prove_task ~command:cvc3.Whyconf.command cvc3_driver task ()) () in

       let answer = parseProverAnswer (result.pr_answer) in
       
      (answer,result.pr_time)

let proveYices term = 
       let task = None in
       let task = Task.use_export task int_theory in
       let task = Task.use_export task computer_division_theory in
       let goal = Decl.create_prsymbol (Ident.id_fresh "goal") in
       let task = Task.add_prop_decl task Decl.Pgoal goal term in

       let result : Call_provers.prover_result = Call_provers.wait_on_call (Driver.prove_task ~command:yices.Whyconf.command yices_driver task ()) () in

       let answer = parseProverAnswer (result.pr_answer) in
       
       (answer,result.pr_time)


let proveEProver term = 
       let task = None in
       let task = Task.use_export task int_theory in
       let task = Task.use_export task computer_division_theory in
       let goal = Decl.create_prsymbol (Ident.id_fresh "goal") in
       let task = Task.add_prop_decl task Decl.Pgoal goal term in

       let result : Call_provers.prover_result = Call_provers.wait_on_call (Driver.prove_task ~command:e_prover.Whyconf.command e_prover_driver task ()) () in

       let answer = parseProverAnswer (result.pr_answer) in
       
       (answer,result.pr_time) 


let send_to_prover form prover  =
  match prover with 
  | Alt_ergo ->
            let result = proveAltErgo form in
            let name = alt_ergo.prover.prover_name in
            let version = alt_ergo.prover.prover_version in 
            build_prover_result (fst result) (snd result) name  version
  | CVC3 -> 
            let result = proveAltErgo form in
            let name = cvc3.prover.prover_name in
            let version = cvc3.prover.prover_version in 
            build_prover_result (fst result) (snd result) name  version
  | CVC4 -> 
            let result = proveAltErgo form in
            let name = cvc4.prover.prover_name in
            let version = cvc4.prover.prover_version in 
            build_prover_result (fst result) (snd result) name  version
  | Yices -> 
            let result = proveYices form in
            let name = yices.prover.prover_name in
            let version = yices.prover.prover_version in 
            build_prover_result (fst result) (snd result) name  version
  | EProver -> 
            let result = proveEProver form in
            let name = e_prover.prover.prover_name in
            let version = e_prover.prover.prover_version in 
            build_prover_result (fst result) (snd result) name  version                   
  | Z3 -> raise (Invalid_argument "Z3 prover not implemented")



