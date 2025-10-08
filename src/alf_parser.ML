(*  Title:      IsaRARE/alf_parser.ML
    Author:     Hanna Lachnitt, Stanford University

    Parser for "RARE as an Eunoia fragment" rules.
*)

signature ALF_PARSER =
sig

    val parse_single_alf_rule : Proof.context -> int * string list -> REWRITE_RULE_AST.rewrite_rule

end;

structure ALF_PARSER: ALF_PARSER =
struct

(* Parser Components *)

(*
 Lemma names in Isabelle cannot have dashes in them, so they must be replaced by underscores
 when parsing the name of a rewrite
*)

fun alf_name_parser l cs =
  Scan.catch Scan.many (curry (op <>) " ") cs
  |>> map (fn "-" => "_" | x => x)
  |>> implode
  handle (Fail _) => PARSER_UTILS.raise_parser_error l "Could not parse in rule name"

(* Rule parameters *)

(*
parameter are a list of SMT-LIB terms in parenthesis, the single parameters
are separated by a single whitespace from each other. Parameters can have
attributes starting with a colon. For now only the attribute is :list.
*)
fun alf_parse_par l (par:string) = (
case String.tokens (curry (op =) #":") par of
  [_] => (REWRITE_RULE_AST.Par (PARSER_UTILS.get_smtlib_term l [par])) |
  [x,y] => if String.isPrefix "list" y
             andalso Library.translate_string (fn " " => "" | x => x) y = "list)"
           then (REWRITE_RULE_AST.ListPar (PARSER_UTILS.get_smtlib_term l [(x ^ ")")]))
           else PARSER_UTILS.raise_parser_error l "parameter has unknown attribute" |
  _ => PARSER_UTILS.raise_parser_error l "parameter has too many attributes")

fun alf_par_parser l = (PARSER_UTILS.parse_next_term l ALF_LEXER.alf_lexer >> implode) :|-- (fn s => fn cs => if s<>"" then ((alf_parse_par l s),cs) else Scan.fail cs)

fun alf_param_parser l =
  PARSER_UTILS.expect_char l "Could not find first opening parentheses in parameter list" "(" 
  --| (Scan.many (curry (op =) " "))
  |-- (Scan.repeat (alf_par_parser l --| (Scan.many1 (curry (op =) " ")))
      @@@ (Scan.option (alf_par_parser l) >> (fn NONE => [] | SOME xs => [xs])))
 --| PARSER_UTILS.expect_char l "Could not find final closing parentheses in parameter list" ")" 

(* Expressions *)

(* In RARE expressions might not be in parenthesis if they are a single sequence, so we have to need
parenthesis in front of these*)
fun alf_expression_parser l = PARSER_UTILS.parse_next_term l ALF_LEXER.alf_lexer >> implode >> Library.single >> PARSER_UTILS.get_smtlib_term l



(* TODO: define parse_single_alf_rule in terms of the following: *)
(* val parse_single_alf_rule : Proof.context -> (int * string) list -> ALF_ASR.eunoia_rule list *)
(* val compile_eunoia_into_rare : ALF_ASR.eunoia_rule list -> REWRITE_RULE_AST.rewrite_rule list *)
(* *)
(* TODO: parsing should receive already the tokens parsed *)
fun parse_single_alf_rule ctxt (l, cs) = 
let
  
  fun debug_msg ctxt msg f (x,t) cs =
  ((PARSER_UTILS.debug_msg_parser ctxt ("Parsed " ^ msg ^ ". Token parsed in is: " ^  f t );((x,t),cs)))

  val (((((_,alfT),rname),rparams),rexpressions),cs')
    = cs
      |>
      Scan.succeed (PARSER_UTILS.debug_msg_parser ctxt ("Start parsing alf rule in line " ^ Int.toString(l) ))
      --| (Scan.one (fn c => c = "("))
      --| PARSER_UTILS.ignore_chars l " "
      -- ALF_LEXER.alf_type_lexer l
      --| PARSER_UTILS.least_one_char l "No whitespace after type found." " "
      -- alf_name_parser l
      :|-- debug_msg ctxt "name" I
      --| PARSER_UTILS.least_one_char l "No whitespace after name found." " "
      (* TODO: param_parser depends on parse_next_term, which should be something *)
(*                language dependent *)
      --  alf_param_parser l
      :|-- debug_msg ctxt "parameter" (fn xs => String.concat (map PARSER_UTILS.str_of_par xs))
      -- Scan.repeat
        ((Scan.many1 (curry (op =) " "))
        |-- (alf_expression_parser l))
      :|-- debug_msg ctxt "expressions" (fn xs => String.concat (map SMTLIB.str_of xs))
      --| PARSER_UTILS.ignore_chars l " "
      --| (Scan.one (fn c => c = ")"))
      --| (fn cs => if cs = [] then Scan.succeed [] cs else PARSER_UTILS.raise_parser_error l "Text found after end of rule")

  fun seperate_expr_rule ((SMTLIB.Key "premises")::p::(SMTLIB.Key "conclusion")::[c]) = (REWRITE_RULE_AST.DEFINE_COND_RULE,SOME p,c) |
      seperate_expr_rule ((SMTLIB.Key "conclusion")::[c,SMTLIB.Key "rare-fixed-point"]) = (REWRITE_RULE_AST.DEFINE_RULE_STAR,NONE,c) | (*TODO: Ask Andy does this has the context expr as argument? Or do thy not exist anymore?*)
      seperate_expr_rule ((SMTLIB.Key "conclusion")::[c]) = (REWRITE_RULE_AST.DEFINE_RULE,NONE,c) |
      seperate_expr_rule xs =(@{print}("xs",xs);
        PARSER_UTILS.raise_parser_error l ("Found "
        ^ Int.toString(length xs) ^ " expressions in rule but expected less or more than that."))

  fun seperate_expr_axiom (c::[SMTLIB.Key "rare-fixed-point"]) = (REWRITE_RULE_AST.DEFINE_RULE_STAR,NONE,c) |
      seperate_expr_axiom [c] = (REWRITE_RULE_AST.DEFINE_RULE,NONE,c) |
      seperate_expr_axiom xs = (@{print}("xs",xs);
        PARSER_UTILS.raise_parser_error l ("Found "
        ^ Int.toString(length xs) ^ " expressions in axiom but expected less or more than that."))


  val (rtyp,rprecondition,conclusion) = rexpressions |> (if alfT = ALF_AST.ALF_RULE then seperate_expr_rule else seperate_expr_axiom)

  val (rmatch,rtarget) = (fn (SMTLIB.S [SMTLIB.Sym "=", x,y]) => (x,y) | _ => PARSER_UTILS.raise_parser_error l "" ) conclusion
in

({
    rule_type = rtyp,
    rule_name = rname,
    params= rparams,
    let_defs = NONE,
    precondition = rprecondition,
    match = rmatch,
    target = rtarget,
    context_expr = NONE
  } : REWRITE_RULE_AST.rewrite_rule)

end

end;
