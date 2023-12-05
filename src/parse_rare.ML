(*  Title:      IsaRARE/parse_rare.ML
    Author:     Hanna Lachnitt, Stanford University

  Parsing functionality for RARE rules
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

Binarisation of n-ary operators in rare rules:

 Note that we cannot use the type ListVar here yet since that would lead to incorrect type
 inferences. We have to introduce it in the second step of parsing (rewrites_to_lemma) where we
 also add cvc_list operators to reuse the binarisation procedure in SMTLIB_Proof.

*)

signature PARSE_RARE =
sig
  exception PARSE of int * string
  exception PARSE_RARE_FORMAT of int * string

  datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
  datatype par = Param of SMTLIB.tree | ListParam of SMTLIB.tree

  datatype rewrite_tree = 
    Rule_Type of rule_type |
    Rule_Name of string |
    Par of par list | (*TODO: Should also be option?*)
    Let_Defs of SMTLIB.tree list option |
    Precondition of SMTLIB.tree |
    Match of SMTLIB.tree |
    Target of SMTLIB.tree |
    Context_Expr of SMTLIB.tree option |
    Rewrite_Rule of rewrite_tree list

  val parse_rewrites: Proof.context -> string list -> rewrite_tree list
  val pretty_rewrite_tree: rewrite_tree -> Pretty.T
  val str_of: rewrite_tree list -> string
end;

structure Parse_RARE: PARSE_RARE =
struct

exception PARSE of int * string
exception PARSE_RARE_FORMAT of int * string

datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
datatype unfinished = None | String of string | Symbol of string | TreeList of SMTLIB.tree list
datatype par = Param of SMTLIB.tree | ListParam of SMTLIB.tree

datatype rewrite_tree = 
  Rule_Type of rule_type |
  Rule_Name of string |
  Par of par list |
  Let_Defs of SMTLIB.tree list option |
  Precondition of SMTLIB.tree |
  Match of SMTLIB.tree |
  Target of SMTLIB.tree |
  Context_Expr of SMTLIB.tree option |
  Rewrite_Rule of rewrite_tree list

(*
 Lemma names in Isabelle cannot have dashes in them, so they must be replaced by underscores
 when parsing the name of a rewrite
*)
fun parse_string l (c :: cs) None error_msg =
       if Symbol.is_ascii_blank c then parse_string l cs None error_msg (*Ignore leading space*)
       else parse_string l cs (String c) error_msg | (*Start of a word*)
    parse_string l (c :: cs) (String s) error_msg =
       if Symbol.is_ascii_blank c then (cs, s) (*End of a word*)
       else if c = "-" then parse_string l cs (String (s ^ "_")) error_msg (*Replace - in name by _ *)
       else parse_string l cs (String (s ^ c)) error_msg | (*Word continues*)
    parse_string l _ _  error_msg = raise PARSE (l, error_msg)

(*
 A parameter has to be of the form <symbol> <sort> <attr>*
 The symbol and the sort need to be parsed in. If the attribute is :list, the type of the 
 parameter still needs to be whatever type the elements of this list have.  
*)
local

 (*TODO: THERE CAN BE NESTED PARENTHESIS (c (_ BitVec 1))*)
  fun parse_par_type (":"::cs) typ _ l = parse_par_type cs typ true l
    | parse_par_type (")"::cs) typ is_list _ = (cs, typ, is_list)
    (*| parse_par_type (" "::cs) typ is_list l = parse_par_type cs typ is_list l*) (*TODO*)
    | parse_par_type (_::cs) typ true l = parse_par_type cs typ true l
    | parse_par_type (c::cs) typ false l = parse_par_type cs (typ^c) false l
    | parse_par_type _ _ _ l = raise PARSE (l, "parameter is not well-formed.")

in
  fun parse_pars ("("::")"::cs) None _ _ = (cs,[],[]) (*Par list is empty*)
 | parse_pars ("("::cs) None [] l = parse_pars cs (TreeList []) [] l (*Very first opening parenthesis*) 
 | parse_pars ("("::cs) (TreeList xs) list_pars l =
    let
      val (cs',par_name) = parse_string l cs None "Parameter name could not be parsed in"
      (*TODO: This is a hotfix for nested parenthesis*)
      val (cs'',par_type,is_list) = if hd cs' = "(" then parse_par_type (tl cs') "" false l else parse_par_type cs' "" false l
      val cs'' = if hd cs' = "(" then tl cs'' else cs''
      val par_type = if hd cs' = "(" then "("^par_type^")" else par_type
      val par = SMTLIB.parse ["("^par_name^" " ^ par_type^")"]
      val new_list_pars = (if is_list then par::list_pars else list_pars)
    in parse_pars cs'' (TreeList (par::xs)) new_list_pars l end
 | parse_pars (")"::cs) (TreeList xs) list_pars _ = (cs, xs, list_pars) (*Very last closing parenthesis*)
 | parse_pars (" "::cs) (TreeList xs) list_pars l = parse_pars cs (TreeList xs) list_pars l (*Skip spaces between pars*)
 | parse_pars _ _ _ l = raise PARSE (l, "parameter list is not well-formed.")
end

local 
  fun read_rule_smtlib_tree _ (match :: [target])
         = [Match match, Target target] |
      read_rule_smtlib_tree l _ = raise PARSE (l, "not a valid instance of a define-rule")

  fun read_cond_rule_smtlib_tree _ (precondition :: match :: [target])
         = [Precondition precondition, Match match, Target target] |
      read_cond_rule_smtlib_tree l _ = raise PARSE (l, "not a valid instance of a define-cond-rule")

  fun read_star_rule_smtlib_tree _ (match :: [target])
        = [Context_Expr NONE, Match match, Target target] |
      read_star_rule_smtlib_tree _ (match :: target :: [context_expr])
        = (@{print}("target",target);@{print}("match",match);@{print}("context_expr",context_expr);[Context_Expr (SOME context_expr), Match match, Target target]) |
      read_star_rule_smtlib_tree l _ = raise PARSE (l, "not a valid instance of a define-star-rule")

  fun read_rewrite_name l cs = parse_string l cs None "Rule name could not be parsed in" ||> Rule_Name

  fun parse_rare rule l cs f ctxt = 
  let
    val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Parsed rule type:", rule))
    val (wth_name, name) = read_rewrite_name l cs
    val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Parsed name:", name))
    val (wth_par, parsed_par, list_pars) = parse_pars wth_name None [] l
    val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Parsed parameters:", parsed_par))
(*TODO: This does not work if a rewrite has a whitespace at the end! Fix split_up below*)
    val wth_last_parenthesis = take (length wth_par - 1) wth_par

  (*A statement is either in between parenthesis or a single token*)
    (*Empty strings cannot be parsed in by the SMTLIB parser. For now strings are excluded here*)
    fun read_token [] token _ = ([],token) |
        read_token (" "::cs) token _ = (cs,token) |
        read_token ("\""::"\""::cs) token false = read_token cs (token^"(str.const emptyString)") true | (*TDOO: replace by ''s?*)
        read_token ("\""::cs) token false = read_token cs (token^"(str.const ") true | (*TDOO: replace by ''s?*)
        read_token ("\""::cs) token true = read_token cs (token^")") false |
        read_token (c::cs) token x = read_token cs (token^c) x

    (*TODO: string constants*)
    (*TODO: Use nested lists instead of counter and then flatten them?*)
    fun split_up [] _ _ _ = [] |
        split_up (" "::cs) 0 None str_const = split_up cs 0 None str_const | (*Skip blanks in between expressions*)
        split_up ("("::cs) 0 None str_const = split_up cs 1 (String "(") str_const | (*Expression starts with a parenthesis*)
        split_up ("("::cs) i (String str) str_const = split_up cs (i+1) (String (str ^ "(")) str_const | (*Expression starts with a parenthesis*)
        split_up (c::cs) 0 None str_const =
          let 
            val (new_cs,token) = read_token (c::cs) "" false
          in 
            [token]::split_up new_cs 0 None str_const
          end | (*Expression is a token wth parenthesis*)
        split_up (")"::cs) 1 (String str) str_const = [str ^ ")"] :: split_up cs 0 None str_const |
        split_up (")"::cs) i (String str) str_const = split_up cs (i-1) (String (str^")")) str_const |
        split_up ("\""::"\""::cs) i (String str) false = split_up cs i (String (str^"(str.const)")) false |
        split_up ("\""::cs) i (String str) false = split_up cs i (String (str^"str.const(")) true |
        split_up ("\""::cs) i (String str) true = split_up cs i (String (str^")")) false |
        split_up (c::cs) i (String str) str_const = split_up cs i (String (str^c)) str_const |
        split_up _ _ _ _ = raise PARSE (l, "rule cannot be parsed in")

(*TODO: string list instead of string list list*)

(* Split up blocks. Then, test if first block is a def block or not *)

  val expr_list = split_up wth_last_parenthesis 0 None false
  val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Parsed in single components:", expr_list))

  val pot_def_list = implode (hd expr_list)

  val (expr_list, ld) =
   if String.isPrefix "(def" pot_def_list
   then
   let
     val wth_def = unprefix "(def" pot_def_list (*TODO: Delete last element*)
     val defs = split_up (fst (split_last (raw_explode wth_def))) 0 None false
   in (tl expr_list, SOME (map SMTLIB.parse defs)) end
   else (expr_list, NONE)

   (*Separate components (match, target, condition, context) from each other: *)
   val expr = f l (map SMTLIB.parse expr_list)
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Parsed rule expression:", expr))
  in
    rule :: [name] (*@ [Par (parsed_par,list_pars)]*) @ [Let_Defs ld] @ expr
  end

in 
  fun parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::" ":: cs)
        = parse_rare (Rule_Type DEFINE_RULE) l cs read_rule_smtlib_tree | 
      parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"c"::"o"::"n"::"d"::"-"::"r"::"u"::"l"::"e"::" ":: cs)
        = parse_rare (Rule_Type DEFINE_COND_RULE) l cs read_cond_rule_smtlib_tree | 
      parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::"*"::" ":: cs)
        = parse_rare (Rule_Type DEFINE_RULE_STAR) l cs read_star_rule_smtlib_tree | 
      parse_according_to_type l _ = raise PARSE (l, "could not read rule type")
end

(* Overall parser: *)
fun read_tree l line ctxt
   = parse_according_to_type l line ctxt |> Rewrite_Rule

fun add_line ctxt line (l, rewrite_trees) =
  let
    val _ = IsaRARE_Config.verbose_msg ctxt (fn _ => "parsing line nr. " ^ Int.toString(l) ^ ": " ^ line) []
    val line_list = (raw_explode line)
  in
    if size line = 0 then (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Found empty line, skip"));(l + 1, rewrite_trees)) (*Skip empty lines*)
    else if hd line_list = ";"
    then (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Found comment, skip"));(l + 1, rewrite_trees)) (*Skip comments*)
    else
      let
        val tree = read_tree l line_list ctxt
        val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Complete parsed tree:", tree))
      in
        (l + 1, tree :: rewrite_trees) (*Get rewrite tree for current line and append*)
      end
  end

(*TEMP: Figure out how to parse this in a string list automatically, seperating at\n *)

fun parse_rewrites ctxt lines = (fold (add_line ctxt) lines (1,[])) |> snd |> rev


(*FIXME: Attempt to allow IsaRARE to read rules over multiple lines*)

(*Change in IsaRARE.thy so that I have a single string*)



(*Split at white space, end line or comment*)
(*fun parse_comp f (" "::cs) = 
 parse_comp f (c::cs) = 





val parse_command = [("define-rule",(Rule_Type DEFINE_RULE))]

fun parse_according_to_string instr (c::cs) = 
let
  
*)

















(*New Parser*)
(*Parsing comments*)

val test22 = drop_prefix (fn x => x = " ") (raw_explode "   sdf  dsf  ")
val _ = @{print}("  test22",test22)

val test23 = trim (fn x => x = " ") (raw_explode "    sdfd  sf  ")
val _ = @{print}("  test23",test23)

fun skip p cs = drop_prefix (fn x => x = p) cs

fun skip_to_eol [] = [] |
    skip_to_eol ("\\"::"n"::cs) = cs |
    skip_to_eol (_::cs) = skip_to_eol cs

fun parse_if_comment l (";"::ts) = (l+1,skip_to_eol ts) |
    parse_if_comment l ts = (l,ts)

(*Consume tokens*)

fun consume_single_token l t [] = raise PARSE (l, "expected character '" ^ t ^ "' but found empty string") |
    consume_single_token l t (c::cs) =
      (if t = c
       then cs
       else raise PARSE (l, "expected character '" ^ t ^ "' but found " ^ c))

fun consume_token_greedy t cs = drop_prefix (fn x => x = t) cs

val consume_whitespaces_greedy = consume_token_greedy " "

(*tss has to be sorted from longest string to shortest in case there elements that are substrings
from each other*)
fun consume_prefix l [] _ = raise PARSE (l, "syntax error") |
    consume_prefix l ((ts,f)::tss) cs =
   (case String.isPrefix ts cs of
     true => (f,Library.prefix ts cs) |
     false => consume_prefix l tss cs
    )

(*If given a list of tuples check if any of the first elements of these tuples are prefixes of the
input string list cs and apply the corresponding function if true*)
fun consume_prefix [] _ = NONE |
    consume_prefix ((ts,f)::tss) cs =
    let
      fun
          consume_prefix_h [] cs' = SOME cs' |
          consume_prefix_h _ [] = NONE |
          consume_prefix_h (t::ts') (c::cs') = (if c = t then consume_prefix_h ts' cs' else NONE)
    in
      case consume_prefix_h ts cs  of
        NONE => consume_prefix tss cs |
        SOME cs' => SOME (f cs')
    end

fun (*TODO: Work with unfinished to catch more malformed inputs*)
    parse_nested l ("("::cs) ps i = parse_nested l cs ("("::ps) (i+1) | (*Opening parenthesis*)
    parse_nested l (")"::cs) ps 1 = (l, cs,")"::ps) | (*Last closing parenthesis*)
    parse_nested l (")"::cs) ps 0 = (l, ")"::cs,ps) | (*No opening parenthesis*)
    parse_nested l (")"::cs) ps i = parse_nested l cs (")"::ps) (i-1) | (*Nested closing parenthesis*)
    parse_nested l (";"::cs) ps i = parse_nested l (skip_to_eol cs) ps i |
    parse_nested l ("\\"::"n"::cs) ps i = parse_nested (l+1) cs ps i |
    parse_nested l (c::cs) ps i = parse_nested l cs (c::ps) i



(*Single components parser*)
(*Input: Current line number and rest of input string*)
(*Output: Option, if component was found, the line after parsing component, parsed component, and rest of string without component *)
(*Should raise error if component cannot be parsed as expected and is not optional*)

type rewrite_rule_comp = int * (string list * rewrite_tree list)
type str_comp_parser = int * (string list * string list)


fun comp_parser (l,(cs,t)) str_comp_parser str_to_rewrite_tree_parser = 
  str_comp_parser (l,(cs,[])) ||> (fn (y,z) => (y,str_to_rewrite_tree_parser z::t))

(*Special component parser*)
fun expect_char c (l,(cs,rest)) = (l,(consume_single_token l c cs,rest))
fun parse_to_blank c (l,cs,rest) = (l,chop_prefix (fn c => not (Symbol.is_blank c)) cs)

fun expect_char c (l,(cs,t)) = (l,(consume_single_token l c cs,t)) : rewrite_rule_comp
fun parse_to_blank (l,(cs,t)) = (l,(chop_prefix (fn c => not (Symbol.is_blank c)) cs,t))

(*Rule Type*)
fun parse_type_RARE (l,(cs,t)) =
let
 val str_to_type = [("define-rule*", DEFINE_RULE_STAR),
                    ("define-rule",DEFINE_RULE),
                    ("define-cond-rule", DEFINE_COND_RULE)] 

 val parse_type_f = map (fn (str,f) => (raw_explode str, fn rest => (Rule_Type f,rest))) str_to_type
in
 case consume_prefix parse_type_f cs of
  NONE => raise PARSE_RARE_FORMAT(l, "A rule must start with define-rule, define-rule* or define-cond-rule followed by at least one white space!") |
  (SOME (rule_type, cs')) => (l,(cs',rule_type::t))
end : rewrite_rule_comp

(*Rule Name*)

fun parse_rule_name (l,cs,t) = 
let
  val (name,cs') = chop_prefix (fn c => not (Symbol.is_blank c)) cs
  val name' = name |> map (fn c => (if c="-" then "_" else c))
in
  (l,(cs',(Rule_Name (implode name'))::t))
end : rewrite_rule_comp

(*Parameter List*)
fun parse_param (l,(("("::cs),(Par xs)::ts))  =
let
  (*First parse name, then parse nested, then parse last parenthesis*)
  val (par_name,cs') = chop_prefix (fn c => not (Symbol.is_blank c)) cs
  val (l',(cs'',_)) = expect_char " " (l,(cs',[]))
  val (l'',cs''',par_type) = parse_nested l' cs'' [] 0
  val p = SMTLIB.parse ["("^ implode par_name ^ " " ^ implode par_type ^ ")"]

  val str_to_type = [(" :list", Param p),
                    (")",Param p)] 
  val parse_type_f = map (fn (str,f) => (raw_explode str, fn rest => (f,rest))) str_to_type
  val (pa,cs'''') = 
   case consume_prefix parse_type_f cs of
    NONE => raise PARSE_RARE_FORMAT(l, "Problem parsing parameters") |
    (SOME (pa, rest)) => (pa,rest)

in 
 (l'',(cs'''',(Par (Param p :: xs))::ts))
end |
parse_param (l,(cs,t)) = (l,(cs,t))

(*
fun parse_param_list_h1 (l,(cs,ts)) = 
let
  val (l', (cs',ts')) = parse_param (l, (cs,ts))

in
  if then parse_param_list_h1 (l,(cs,ts)) else 
end
*)




(*

fun parse_param_list l cs = parse_param_list_h1 l cs []

(*Overall component parser*)

val components = [expect_char "(",
                  parse_type_RARE,
                  expect_char " ",
                  parse_rule_name,
                  expect_char " ",
                  expect_char "(",
                  parse_param_list,
                  expect_char ")"
                  ]
*)
fun parse_comps _ _ [] = [] |
 parse_comps l cs (f::fs) =
let
   val (l',cs',comp) = f l cs

in
 case comp of
  NONE => parse_comps l' cs' fs |
  (SOME y) => y :: parse_comps l' cs' fs 
end
(*
val test111 = parse_comps 0 (raw_explode "(define-rule rulesNAME ((x ?BitVec) (i Int) (j Int) (k Int) (l Int) )") components

val _ = @{print}("test parse comp", test111)
*)






















fun parse_string l (c :: cs) None error_msg =
       if Symbol.is_ascii_blank c then parse_string l cs None error_msg (*Ignore leading space*)
       else parse_string l cs (String c) error_msg | (*Start of a word*)
    parse_string l (c :: cs) (String s) error_msg =
       if Symbol.is_ascii_blank c then (s,cs) (*End of a word*)
       else if c = "-" then parse_string l cs (String (s ^ "_")) error_msg (*Replace - in name by _ *)
       else parse_string l cs (String (s ^ c)) error_msg | (*Word continues*)
    parse_string l _ _  error_msg = raise PARSE (l, error_msg)

fun parse_rule_name l cs = parse_string l cs None "Rule name could not be parsed in" 



(*Definition*)

fun parse_def_RARE l cs =
let

 val parse_def_f = [(raw_explode "(def", (fn rest => (Let_Defs NONE,rest)(*TODO: Here parse def list and then parse remaining )*)))]
in
 case consume_prefix parse_def_f cs of
  NONE => (l, Let_Defs NONE ,cs) (*No defs found*) |
  (SOME (rule_type, cs')) => (l,rule_type,cs')
end








(*Overall component parser*)

fun parse_single_char l c cs = (l,NONE,tl cs) (*TODO*)

val components = [parse_type_RARE] (*Can be written more succinct without swap*)
(*First parse type then decide components based on that*)

(*Parses a single component (e.g., rule name, match) according to the function f while deleting white spaces and comments before and after*)
fun parse_component l cs f = 
let
  val (l',comp,cs') = (l, cs) ||> consume_whitespaces_greedy |> f (*trim trailing white space and apply function*)
  val cs'' = consume_whitespaces_greedy cs' (*white space after component*)
  val (l'',cs''') = parse_if_comment l' cs''
in
  (l'',cs''',comp)
end
(*val test345 = (raw_explode "(define-cond-rule rulesNAME") |> consume_single_token 0 "(" |> parse_type_RARE 0 

val _ = @{print}("parse comp", test345)
*)



fun parse_comps l cs (f::fs) comps =
let
  val cs' = consume_whitespaces_greedy cs (*white space at before component*)
  val (l',cs'',comp) = f l cs'  
  val cs''' = consume_whitespaces_greedy cs'' (*white space after component*)
  val (l'',cs'''') = parse_if_comment l' cs'''


in
cs
end


(*("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::" ":: cs)
      = parse_rare2 (Rule_Type DEFINE_RULE) l cs read_rule_smtlib_tree | 
    parse_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"c"::"o"::"n"::"d"::"-"::"r"::"u"::"l"::"e"::" ":: cs)
      = parse_rare2 (Rule_Type DEFINE_COND_RULE) l cs read_cond_rule_smtlib_tree | 
    parse_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::"*"::" ":: cs)
      = parse_rare2 (Rule_Type DEFINE_RULE_STAR) l cs read_star_rule_smtlib_tree | 
    parse_type l _ = raise PARSE (l, "could not read rule type")
*)

(*Parse one token (could be comment)*)

fun parse_rewrites_h2 ctxt l [] = (l,[]) | (*Reached end of file*)
    parse_rewrites_h2 ctxt l ("\\"::"n"::ts) = (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Found empty line, skip"));(l+1,skip_to_eol ts)) |
    parse_rewrites_h2 ctxt l (";"::ts) = (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Found comment, skip"));(l+1,skip_to_eol ts)) |
    (*parse_rewrites_h2 ctxt l ("("::ts) =
     let
      val rule = parse_comp l ts []
     in 
       parse_rewrites_h2 ctxt l tss
     end  
    |*)
    parse_rewrites_h2 ctxt l (" "::ts) = parse_rewrites_h2 ctxt l ts (*Leading whitespace*) |
    parse_rewrites_h2 ctxt l (_::ts) = raise PARSE (l, "file not formatted correctly") 





fun pretty_rewrite_tree (Rule_Type DEFINE_RULE) = Pretty.str ("define-rule ")
  | pretty_rewrite_tree (Rule_Type DEFINE_COND_RULE) = Pretty.str ("define-cond-rule ")
  | pretty_rewrite_tree (Rule_Type DEFINE_RULE_STAR) = Pretty.str ("define-rule* ")
  | pretty_rewrite_tree (Rule_Name s) = Pretty.str s
  (*| pretty_rewrite_tree (Par (trees,_))
    = Pretty.enclose "(" ")" (Pretty.separate "" (map SMTLIB.pretty_tree trees)))*)
  | pretty_rewrite_tree (Let_Defs NONE) = Pretty.str ("")
  | pretty_rewrite_tree (Let_Defs (SOME s))
    = Pretty.enclose "(" ")" (Pretty.separate "" (map SMTLIB.pretty_tree s))
  | pretty_rewrite_tree (Precondition tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Match tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Target tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Context_Expr NONE) = Pretty.str ""
  | pretty_rewrite_tree (Context_Expr (SOME tree)) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Rewrite_Rule trees) =
      Pretty.enclose "(" ")" (Pretty.separate "" (map pretty_rewrite_tree trees))

fun pretty_rewrite_rules cs = Pretty.block (map pretty_rewrite_tree cs)

val str_of = Pretty.unformatted_string_of o pretty_rewrite_rules

end;