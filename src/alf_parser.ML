(*  Title:      IsaRARE/alf_parser.ML
    Author:     Hanna Lachnitt, Stanford University

    Parser for "RARE as an Eunoia fragment" rules.
*)

signature ALF_PARSER =
sig
    exception ALF_PARSER of string

    val parse_single_alf_rule : Proof.context -> int * string list -> REWRITE_RULE_AST.rewrite_rule

end;

structure ALF_PARSER: ALF_PARSER =
struct

open ALF_AST

(* Exceptions and their handlers *)
exception ALF_PARSER of string

fun debug_msg_parser ctxt msg =
  (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> ("Parser: " ^ msg)))
fun parser_debug_prefix l = "Parser error in rule starting in line " ^ Int.toString(l)  ^ ": "
fun raise_parser_error l msg = raise ALF_PARSER(parser_debug_prefix l  ^ msg)

(* TODO: this could be a service shared with the RARE parser *)
fun ignore_chars l c cs =
  Scan.catch (Scan.many (curry (op =) c)) cs
  handle (Fail _) => raise_parser_error l ("Was expecting more input but rule might have ended prematurely. ")

(* TODO: this could be a service shared with the RARE parser *)
fun least_one_char l err_msg c cs =
  Scan.catch (Scan.many1 (curry (op =) c)) cs
  handle (Fail _) => raise_parser_error l ("Expected at least one '" ^ c ^ "' but could not find any." ^ err_msg)

(* TODO: define parse_single_alf_rule in terms of the following: *)
(* val parse_single_alf_rule : Proof.context -> (int * string) list -> ALF_ASR.eunoia_rule list *)
(* val compile_eunoia_into_rare : ALF_ASR.eunoia_rule list -> REWRITE_RULE_AST.rewrite_rule list *)
(* *)
(* TODO: parsing should receive already the tokens parsed *)
fun parse_single_alf_rule ctxt tokens = {
           rule_type = REWRITE_RULE_AST.DEFINE_RULE,
           rule_name = "dummy_rule_name",
           params = [],
           let_defs = NONE,
           precondition = NONE,
           (* TODO: arbitrary value for compilation purposes *)
           match = SMTLIB.Num 1,
           target = SMTLIB.Num 1,
           context_expr = NONE
         }

(* let *)
  
(*   fun debug_msg ctxt msg f (x,t) cs = *)
(*   ((debug_msg_parser ctxt ("Parsed " ^ msg ^ ". Token parsed in is: " ^  f t );((x,t),cs))) *)

(*   val (((((_,alfT),rname),rparams),rexpressions),cs') *)
(*     = cs *)
(*       |> *)
(*       Scan.succeed (debug_msg_parser ctxt ("Start parsing alf rule in line " ^ Int.toString(l) )) *)
(*       --| (Scan.one (fn c => c = "(")) *)
(*       --| ignore_chars l " " *)
(*       -- ALF_LEXER.alf_type_lexer l *)
(*       --| least_one_char l "No whitespace after type found." " " *)
(*       (* -- name_parser l *) *)
(*       (* :|-- debug_msg ctxt "name" I *) *)
(*       --| least_one_char l "No whitespace after name found." " " *)
(*       (* TODO: param_parser depends on parse_next_term, which should be something *)
(*                language dependent *) *)
(*       (* --  param_parser l *) *)
(*       (* :|-- debug_msg ctxt "parameter" (fn xs => String.concat (map str_of_par xs)) *) *)
(*       (* -- Scan.repeat *) *)
(*       (*   ((Scan.many1 (curry (op =) " ")) *) *)
(*       (*   |-- (expression_parser l)) *) *)
(*       (* :|-- debug_msg ctxt "expressions" (fn xs => String.concat (map SMTLIB.str_of xs)) *) *)
(*       --| ignore_chars l " " *)
(*       --| (Scan.one (fn c => c = ")")) *)
(*       --| (fn cs => if cs = [] then Scan.succeed [] cs else raise_parser_error l "Text found after end of rule") *)

(*   fun seperate_expr_rule ((SMTLIB.Key "premises")::p::(SMTLIB.Key "conclusion")::[c]) = (DEFINE_COND_RULE,SOME p,c) | *)
(*       seperate_expr_rule ((SMTLIB.Key "conclusion")::[c,SMTLIB.Key "rare-fixed-point"]) = (DEFINE_RULE_STAR,NONE,c) | (*TODO: Ask Andy does this has the context expr as argument? Or do thy not exist anymore?*) *)
(*       seperate_expr_rule ((SMTLIB.Key "conclusion")::[c]) = (DEFINE_RULE,NONE,c) | *)
(*       seperate_expr_rule xs =(@{print}("xs",xs); *)
(*         raise_parser_error l ("Found " *)
(*         ^ Int.toString(length xs) ^ " expressions in rule but expected less or more than that.")) *)

(*   fun seperate_expr_axiom (c::[SMTLIB.Key "rare-fixed-point"]) = (DEFINE_RULE_STAR,NONE,c) | *)
(*       seperate_expr_axiom [c] = (DEFINE_RULE,NONE,c) | *)
(*       seperate_expr_axiom xs = (@{print}("xs",xs); *)
(*         raise_parser_error l ("Found " *)
(*         ^ Int.toString(length xs) ^ " expressions in axiom but expected less or more than that.")) *)


(*   val (rtyp,rprecondition,conclusion) = rexpressions |> (if alfT = ALF_RULE then seperate_expr_rule else seperate_expr_axiom) *)

(*   val (rmatch,rtarget) = (fn (SMTLIB.S [SMTLIB.Sym "=", x,y]) => (x,y) | _ => raise_parser_error l "" ) conclusion *)
(* in *)

(* ({ *)
(*     rule_type = rtyp, *)
(*     rule_name = rname, *)
(*     params= rparams, *)
(*     let_defs = NONE, *)
(*     precondition = rprecondition, *)
(*     match = rmatch, *)
(*     target = rtarget, *)
(*     context_expr = NONE *)
(*   } : rewrite_rule) *)

(* end *)

end;
