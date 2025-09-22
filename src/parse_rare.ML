(*  Title:      IsaRARE/parse_rare.ML
    Author:     Hanna Lachnitt, Stanford University

Diagnostic tools for IsaRARE.

*)

(*

This file contains functionality to parse RARE rules into an AST in Isabelle.

Overview:

 While rule type and rule name are directly parsed in, the parameters and the expressions are given
 to SMTLIB.parse to efficiently reuse its capabilities:

 For example,
  The RARE Rule: (define-rule bool-eq-refl ((t Bool)) (= t s) true) is split up into three parts:
    SMTLIB.parse "(t Bool)" and
    SMTLIB.parse "(= t s)" and
    SMTLIB.parse "true"
  which results in the Abstract Syntax Trees:
    S [S [Sym "t",Sym "Bool"]] and S [S [Sym "=", Sym "t", Sym "s"]] and S [Sym "true"]

Binarization of n-ary operators in rare rules:

 Note that we cannot use the type ListVar here yet since that would lead to incorrect type
 inferences. We have to introduce it in the second step of parsing (rewrites_to_lemma) where we
 also add cvc_list operators to reuse the binarization procedure in SMTLIB_Proof.

*)

signature PARSE_RARE =
sig
  exception PARSE of string
  exception TREE of string

  datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
  datatype par = Par of SMTLIB.tree | ListPar of SMTLIB.tree

  type rewrite_rule =
  {
    rule_type : rule_type,
    rule_name : string,
    params : par list,
    let_defs : (SMTLIB.tree * SMTLIB.tree) list option,
    precondition : SMTLIB.tree option,
    match : SMTLIB.tree,
    target : SMTLIB.tree,
    context_expr : SMTLIB.tree option
  }

  val pretty_rewrite_rule: rewrite_rule -> Pretty.T
  val str_of: rewrite_rule -> string

  val lex_rewrites : Proof.context -> string list -> (int * string) list
  val parse_rewrites : Proof.context -> (int * string) list -> rewrite_rule list

end;

structure Parse_RARE: PARSE_RARE =
struct

exception PARSE of string
exception TREE of string


datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
datatype par = Par of SMTLIB.tree | ListPar of SMTLIB.tree

type rewrite_rule =
{
  rule_type : rule_type,
  rule_name : string,
  params : par list,
  let_defs : (SMTLIB.tree * SMTLIB.tree) list option,
  precondition : SMTLIB.tree option,
  match : SMTLIB.tree,
  target : SMTLIB.tree,
  context_expr : SMTLIB.tree option
}


(* Printing *)

fun str_of_type DEFINE_RULE = "define-rule" |
    str_of_type DEFINE_COND_RULE = "define-cond-rule" |
    str_of_type DEFINE_RULE_STAR = "define-rule*" 

fun str_of_par (Par t) = "(" ^ SMTLIB.str_of t ^ ")" |
    str_of_par (ListPar t) = "(" ^ SMTLIB.str_of t ^ " :list)"

fun str_of_lets xs = "(def" ^ String.concat (map (fn (v,t) => " (" ^ SMTLIB.str_of v ^ " " ^ SMTLIB.str_of t ^ ")") xs) ^ ")"

fun pretty_rewrite_rule (rule : rewrite_rule) = 
 [
  #rule_type rule |> str_of_type |> Pretty.str,
  #rule_name rule |> Pretty.str,
  #params rule |> map str_of_par |> map Pretty.str |> Pretty.separate "" |> Pretty.enclose "" ""
 ]
 @ (if Option.isSome (#let_defs rule)
    then [ str_of_lets (Option.valOf (#let_defs rule))|> Pretty.str ] 
    else [])
 @ (if Option.isSome (#precondition rule)
    then [ map SMTLIB.pretty_tree [(Option.valOf (#precondition rule))] |> Pretty.separate " " |> Pretty.enclose "(" ")"] 
    else [])
 @ [SMTLIB.pretty_tree (#match rule),
    SMTLIB.pretty_tree (#target rule)]
 @ (if Option.isSome (#context_expr rule)
    then [ map SMTLIB.pretty_tree [(Option.valOf (#context_expr rule))] |> Pretty.separate " " |> Pretty.enclose "(" ")"] 
    else [])
 |> Pretty.separate ""
 |> Pretty.enclose "(" ")"

val str_of = Pretty.unformatted_string_of o pretty_rewrite_rule


(* General Util *)

(*
 Parses the next token from a list of string characters,  either starting with an opening
 parenthesis until the matching closing parenthesis or if the first character is not an opening
 parenthesis it returns everything up to the first white space or closing parenthesis.

 E.g., parse_token NONE "((s1 ?) (s2 ? :list) (m Int))"
 is Finished (((s1 ?) (s2 ? :list) (m Int)),"")

 I.e. parse_token NONE "(s1 ?) (s2 ? :list) (n Int) (m Int)"
 is Finished ((s1 ?)," (s2 ? :list) (n Int) (m Int)")

 If the string s does not contain the final closing parenthesis Unfinished(s,i) is returned where
 i is the number of unclosed parenthesis in s.
*)

datatype token = None | Unfinished of string list * int | Finished of string list * string list
exception TOKEN of string

fun parse_token s [] = s |
  parse_token None ("("::cs) = parse_token (Unfinished(["("],1)) cs |
  parse_token None (")"::cs) = Scan.fail cs |
  parse_token None cs = Finished (Scan.catch Scan.many (fn c => c <> " " andalso c <> ")") cs) |
  parse_token (Unfinished (s,i)) ("("::cs) = parse_token (Unfinished ("("::s,i+1)) cs |
  parse_token (Unfinished (_,0)) (")"::_) = raise TOKEN("too many closing parenthesis") |
  parse_token (Unfinished (s,1)) (")"::xs) = Finished(rev (")"::s),xs) |
  parse_token (Unfinished (s,i)) (")"::cs) = parse_token (Unfinished (")"::s,i-1)) cs |
  parse_token (Unfinished (s,i)) (c::cs) = parse_token (Unfinished (c::s,i)) cs |
  parse_token _ _ = raise TOKEN("error parsing token")


(* Lexer Util *)

fun debug_msg_lexer ctxt l msg =
  (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> ("Lexer in line " ^ Int.toString(l) ^ ": " ^ msg)))
fun verbose_msg_lexer ctxt msg =
  (IsaRARE_Config.verbose_msg ctxt (fn () => \<^print> ("Lexer: " ^ msg)))

fun lexer_debug_prefix l = "Lexer error in line " ^ Int.toString(l)  ^ ": "
fun raise_lexer_error l msg = raise PARSE(lexer_debug_prefix l ^ msg)


(* Lexer *)

fun lexer_add_line ctxt l line uf =
let
  val _ = verbose_msg_lexer ctxt ("reading line nr. " ^ Int.toString(l) ^ ": " ^ line)
  val trimmed_lines = raw_explode line |> Library.trim (curry (op =) " ")
in
  case trimmed_lines of
    [] => (debug_msg_lexer ctxt l ("found empty line , skip"); uf) |
    (";"::_) => (debug_msg_lexer ctxt l "Lexer found comment, skip entire line"; uf) |
    _ => 
      let
        val _ = debug_msg_lexer ctxt l ("found non empty line, start parsing rule");
        (* If line has a comment in it cut it *)
        val sanitized_lines =
          Library.take (Library.find_index (curry (op =) ";") trimmed_lines) trimmed_lines  |> Library.trim (curry (op =) " ")
        val token =
          parse_token uf sanitized_lines
          handle 
           (TOKEN msg) => raise_lexer_error l msg
      in
        case token of (*TOOD: Check manually here parse_token changed*)
          None => raise_lexer_error l "expected opening parenthesis" |
          t => t
       end
end

fun lexer _ [] (Unfinished (s,i)) l l_start =
    raise_lexer_error l ("expected eof but last rule (starting at line nr "
      ^ Int.toString(l_start) ^ ") was not closed. Counted " ^ Int.toString(i)
      ^ " opened but not closed parenthesis far. Part already parsed in: \n"
      ^ (rev s |> String.concat)) |
  lexer ctxt [] _ l _ = (debug_msg_lexer ctxt l "Finished lexing file";[]) |
  lexer ctxt (line::lines) uf l l_start =
    case lexer_add_line ctxt l line uf of
      Finished (s,[]) => (l_start,String.concat s) :: lexer ctxt lines None (l+1) (l+1) |
      Finished (_,s') => raise_lexer_error l ("text after final closing parenthesis found! "
        ^ String.concat s') |
      Unfinished (s,s') => lexer ctxt lines (Unfinished ([" "] @ s,s')) (l+1) l_start |
      None => lexer ctxt lines uf (l+1) (l+1)

fun lex_rewrites ctxt cs = lexer ctxt cs None 1 1


(* Parser Utils *)

fun debug_msg_parser ctxt msg =
  (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> ("Parser: " ^ msg)))
fun parser_debug_prefix l = "Parser error in rule starting in line " ^ Int.toString(l)  ^ ": "
fun raise_parser_error l msg = raise PARSE(parser_debug_prefix l  ^ msg)

fun get_smtlib_term l t = SMTLIB.parse t
  handle
   SMTLIB.PARSE (_,msg) => raise_parser_error l ("Error parsing SMT-LIB term " ^ String.concat t ^ msg)

fun parse_next_term l cs =
let
  val token =  (parse_token None cs)
    handle
      (Fail _) => Scan.fail cs |
      (TOKEN msg) => raise_parser_error l msg
in
 case token of
   None => (Scan.fail cs) |
   Finished (t,cs') => (Scan.succeed t cs') |
   Unfinished _ => raise_parser_error l "closing parenthesis missing"
end

fun expect_char l err_msg c cs =
  Scan.catch (Scan.one (curry (op =) c)) cs
  handle (Fail _) => raise_parser_error l ("Expected '" ^ c ^ "' but could not find it." ^ err_msg)

fun least_one_char l err_msg c cs =
  Scan.catch (Scan.many1 (curry (op =) c)) cs
  handle (Fail _) => raise_parser_error l ("Expected at least one '" ^ c ^ "' but could not find any." ^ err_msg)

fun ignore_chars l c cs =
  Scan.catch (Scan.many (curry (op =) c)) cs
  handle (Fail _) => raise_parser_error l ("Was expecting more input but rule might have ended prematurely. ")


(* Parser Components *)

(* Rule type *)

fun type_parser _ (("d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::"*":: cs)) =
    (DEFINE_RULE_STAR,cs) |
  type_parser _ (("d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e":: cs)) =
    (DEFINE_RULE,cs) |
  type_parser _ (("d"::"e"::"f"::"i"::"n"::"e"::"-"::"c"::"o"::"n"::"d"::"-"
                  ::"r"::"u"::"l"::"e"::cs)) = (DEFINE_COND_RULE,cs) |
  type_parser l _ = raise_parser_error l "Could not read type!"

(* In alf the rule type is determined by annotations and not by a keyword. However, there is some
syntax sugar that allows to write declare-axiom for rules without any conditions. Since the type
depends on whether a :rare-fixed-point or a :premises ((= F false)) term is found later in the
rule we cannot determine it here yet. *)

datatype alf_rule_type = ALF_AXIOM | ALF_RULE

fun alf_type_parser _ (("d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"a"::"x"::"i"::"o"::"m":: cs)) =
    (ALF_AXIOM,cs) |
  alf_type_parser _ (("d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"r"::"u"::"l"::"e":: cs)) =
    (ALF_RULE,cs) |
  alf_type_parser l _ = raise_parser_error l "Could not read type of alf rule!"

(* Rule name *)

(*
 Lemma names in Isabelle cannot have dashes in them, so they must be replaced by underscores
 when parsing the name of a rewrite
*)

fun name_parser l cs =
  Scan.catch Scan.many (curry (op <>) " ") cs
  |>> map (fn "-" => "_" | x => x)
  |>> implode
  handle (Fail _) => raise_parser_error l "Could not parse in rule name"

(* Rule parameters *)

(*
parameter are a list of SMT-LIB terms in parenthesis, the single parameters
are separated by a single whitespace from each other. Parameters can have
attributes starting with a colon. For now only the attribute is :list.
*)
fun parse_par l (par:string) = (
case String.tokens (curry (op =) #":") par of
  [_] => (Par (get_smtlib_term l [par])) |
  [x,y] => if String.isPrefix "list" y
             andalso Library.translate_string (fn " " => "" | x => x) y = "list)"
           then (ListPar (get_smtlib_term l [(x ^ ")")]))
           else raise_parser_error l "parameter has unknown attribute" |
  _ => raise_parser_error l "parameter has too many attributes")

fun par_parser l = (parse_next_term l >> implode) :|-- (fn s => fn cs => if s<>"" then ((parse_par l s),cs) else Scan.fail cs)

fun param_parser l =
  expect_char l "Could not find first opening parentheses in parameter list" "(" 
  --| (Scan.many (curry (op =) " "))
  |-- (Scan.repeat (par_parser l --| (Scan.many1 (curry (op =) " ")))
      @@@ (Scan.option (par_parser l) >> (fn NONE => [] | SOME xs => [xs])))
 --| expect_char l "Could not find final closing parentheses in parameter list" ")" 

(* Let definitions *)

fun let_parser l (cs : string list) = (@{print}("let",cs);
  cs |> 
  Scan.catch(
  (Scan.many1 (curry (op =) " "))
  --| (Scan.one (curry (op =) "("))
  -- Scan.many (curry (op =) " ")
  --| Scan.one (curry (op =) "d")
  --| Scan.one (curry (op =) "e")
  --| Scan.one (curry (op =) "f")
  --| Scan.many1 (curry (op =) " ")
  |-- (Scan.repeat ((
        (Scan.one (curry (op =) "("))
        |-- parse_next_term l
        --| (Scan.many1 (curry (op =) " "))
        -- parse_next_term l
        --| (Scan.many (curry (op =) " "))
        --| (Scan.one (curry (op =) ")"))
        --| (Scan.many (curry (op =) " "))
      )
      >> (fn (v,t) => (get_smtlib_term l v,get_smtlib_term l t))
      ))
  --| Scan.many (curry (op =) " ")
  --| Scan.one (curry (op =) ")"))
  >> Option.SOME
  handle
    (Fail _) => (NONE,cs)
)
(* Expressions *)

(* In RARE expressions might not be in parenthesis if they are a single sequence, so we have to need
parenthesis in front of these*)
fun expression_parser l = parse_next_term l >> implode >> Library.single >> get_smtlib_term l


fun parse_single_rule ctxt (l,cs) =
let
  
  fun debug_msg ctxt msg f (x,t) cs =
  ((debug_msg_parser ctxt ("Parsed " ^ msg ^ ". Token parsed in is: " ^  f t );((x,t),cs)))

  val ((((((_,rtyp),rname),rparams),rlet),rexpressions),cs')
    = cs
      |>
      Scan.succeed (debug_msg_parser ctxt ("Start parsing rule in line " ^ Int.toString(l) ))
      --| (Scan.one (fn c => c = "("))
      -- ignore_chars l " "
      -- type_parser l
      :|-- debug_msg ctxt "type" str_of_type
      --| least_one_char l "No whitespace after type found." " "
      -- name_parser l
      :|-- debug_msg ctxt "name" I
      --| least_one_char l "No whitespace after name found." " "
      --  param_parser l
      :|-- debug_msg ctxt "parameter" (fn xs => String.concat (map str_of_par xs))
      -- let_parser l
      :|-- debug_msg ctxt "possible let defs" (fn (SOME xs) => str_of_lets xs | NONE => "")
      -- Scan.repeat
        ((Scan.many1 (curry (op =) " "))
        |-- (expression_parser l))
      :|-- debug_msg ctxt "expressions" (fn xs => String.concat (map SMTLIB.str_of xs))
      --| ignore_chars l " "
      --| (Scan.one (fn c => c = ")"))
      --| (fn cs => if cs = [] then Scan.succeed [] cs else raise_parser_error l "Text found after end of rule")
 
  fun seperate_expr DEFINE_RULE [m,t] = (NONE,m,t,NONE) |
      seperate_expr DEFINE_COND_RULE [p,m,t] = (SOME p,m,t,NONE) |
      seperate_expr DEFINE_RULE_STAR [m,t] = (NONE,m,t,NONE) |
      seperate_expr DEFINE_RULE_STAR [m,t,c] = (NONE,m,t,SOME c) |
      seperate_expr r xs =
        raise_parser_error l ("Rule type is " ^ str_of_type r ^ " but found "
        ^ Int.toString(length xs) ^ "expressions")

  val (rprecondition,rmatch,rtarget,rcontext_expr) = seperate_expr rtyp rexpressions
in 

({
    rule_type = rtyp,
    rule_name = rname,
    params= rparams,
    let_defs = rlet,
    precondition = rprecondition,
    match = rmatch,
    target = rtarget,
    context_expr = rcontext_expr
  } : rewrite_rule)

end




fun parse_single_alf_rule ctxt (l,cs) =
let
  
  fun debug_msg ctxt msg f (x,t) cs =
  ((debug_msg_parser ctxt ("Parsed " ^ msg ^ ". Token parsed in is: " ^  f t );((x,t),cs)))

  val (((((_,alfT),rname),rparams),rexpressions),cs')
    = cs
      |>
      Scan.succeed (debug_msg_parser ctxt ("Start parsing alf rule in line " ^ Int.toString(l) ))
      --| (Scan.one (fn c => c = "("))
      --| ignore_chars l " "
      -- alf_type_parser l
      --| least_one_char l "No whitespace after type found." " "
      -- name_parser l
      :|-- debug_msg ctxt "name" I
      --| least_one_char l "No whitespace after name found." " "
      --  param_parser l
      :|-- debug_msg ctxt "parameter" (fn xs => String.concat (map str_of_par xs))
      -- Scan.repeat
        ((Scan.many1 (curry (op =) " "))
        |-- (expression_parser l))
      :|-- debug_msg ctxt "expressions" (fn xs => String.concat (map SMTLIB.str_of xs))
      --| ignore_chars l " "
      --| (Scan.one (fn c => c = ")"))
      --| (fn cs => if cs = [] then Scan.succeed [] cs else raise_parser_error l "Text found after end of rule")

  fun seperate_expr_rule ((SMTLIB.Key "premises")::p::(SMTLIB.Key "conclusion")::[c]) = (DEFINE_COND_RULE,SOME p,c) |
      seperate_expr_rule ((SMTLIB.Key "conclusion")::[c,SMTLIB.Key "rare-fixed-point"]) = (DEFINE_RULE_STAR,NONE,c) | (*TODO: Ask Andy does this has the context expr as argument? Or do thy not exist anymore?*)
      seperate_expr_rule ((SMTLIB.Key "conclusion")::[c]) = (DEFINE_RULE,NONE,c) |
      seperate_expr_rule xs =(@{print}("xs",xs);
        raise_parser_error l ("Found "
        ^ Int.toString(length xs) ^ " expressions in rule but expected less or more than that."))

  fun seperate_expr_axiom (c::[SMTLIB.Key "rare-fixed-point"]) = (DEFINE_RULE_STAR,NONE,c) |
      seperate_expr_axiom [c] = (DEFINE_RULE,NONE,c) |
      seperate_expr_axiom xs = (@{print}("xs",xs);
        raise_parser_error l ("Found "
        ^ Int.toString(length xs) ^ " expressions in axiom but expected less or more than that."))


  val (rtyp,rprecondition,conclusion) = rexpressions |> (if alfT = ALF_RULE then seperate_expr_rule else seperate_expr_axiom)

  val (rmatch,rtarget) = (fn (SMTLIB.S [SMTLIB.Sym "=", x,y]) => (x,y) | _ => raise_parser_error l "" ) conclusion
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
  } : rewrite_rule)

end


fun parse_rewrites ctxt xs =
   map ((if Config.get ctxt IsaRARE_Config.ruleFormat = "RARE"
         then parse_single_rule
         else if Config.get ctxt IsaRARE_Config.ruleFormat = "ALF"
         then parse_single_alf_rule
         else raise_parser_error 0 "Unkown proof format set") ctxt)
   (map (fn (i,x) => (i,raw_explode x)) xs)

end;