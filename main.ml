(*
  Cours "Typage et Analyse Statique"
  Université Pierre et Marie Curie
  Antoine Miné 2015
*)


module ConcreteAnalysis =
  Interpreter.Interprete(Concrete_domain.Concrete)
    
module ConstantAnalysis =
  Interpreter.Interprete
    (Non_relational_domain.NonRelational
       (Constant_domain.Constants))

module IntervalAnalysis =
  Interpreter.Interprete
    (Non_relational_domain.NonRelational
       (Interval_domain.Intervals)) 

module ParityAnalysis =
  Interpreter.Interprete
    (Non_relational_domain.NonRelational
       (Parity_domain.Parity))   

(* parse and print filename *)
let doit filename =
  let prog = File_parser.parse_file filename in
  Abstract_syntax_printer.print_prog Format.std_formatter prog

    
(* default action: print back the source *)
let eval_prog prog =
  Abstract_syntax_printer.print_prog Format.std_formatter prog

(* entry point *)
let main () =
  let action = ref eval_prog in
  let files = ref [] in
  (* parse arguments *)
  Arg.parse
    (* handle options *)
    ["-trace", Arg.Set Interpreter.trace, "";
     "-concrete", Arg.Unit (fun () -> action := ConcreteAnalysis.eval_prog),"";
     "-constant", Arg.Unit (fun () -> action := ConstantAnalysis.eval_prog),"";
     "-interval", Arg.Unit (fun () -> action := IntervalAnalysis.eval_prog),"";
     "-parity", Arg.Unit (fun () -> action := ParityAnalysis.eval_prog),"";
     "-delay",         Arg.Set_int (Interpreter.widen_delay),"";
     "-unroll",        Arg.Set_int (Interpreter.loop_unrolling),"";
   ]
    (* handle filenames *)
    (fun filename -> files := (!files)@[filename])
    "";
  List.iter
    (fun filename ->
      let prog = File_parser.parse_file filename in
      !action prog
    )
    !files
    
let _ = main ()
