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
  datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
  datatype par = Param of SMTLIB.tree | ListParam of SMTLIB.tree

  (* TODO: Switch to this type? *)
  type rewrite_rule =
  {
    rule_type : rule_type,
    rule_name : string,
    par : par list,
    let_defs : SMTLIB.tree list option,
    precondition : SMTLIB.tree,
    target : SMTLIB.tree,
    context_expr : SMTLIB.tree option
  }
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

  val pretty_rewrite_tree: rewrite_tree -> Pretty.T
  val str_of: rewrite_tree list -> string

  val lex_rewrites : Proof.context -> string list -> string list
  (*Temp for testing*)
  val parse_all : Proof.context -> int * string list -> rewrite_tree list
(*  val parse_rewrites: Proof.context -> string list -> rewrite_tree list*)

end;

structure Parse_RARE: PARSE_RARE =
struct

exception PARSE of string

datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
datatype par = Param of SMTLIB.tree | ListParam of SMTLIB.tree

(* TODO: Switch to this type? *)
type rewrite_rule =
{
  rule_type : rule_type,
  rule_name : string,
  par : par list,
  let_defs : SMTLIB.tree list option,
  precondition : SMTLIB.tree,
  target : SMTLIB.tree,
  context_expr : SMTLIB.tree option
}

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

(* Printing *)

fun pretty_rewrite_tree (Rule_Type DEFINE_RULE) = Pretty.str ("define-rule ")
  | pretty_rewrite_tree (Rule_Type DEFINE_COND_RULE) = Pretty.str ("define-cond-rule ")
  | pretty_rewrite_tree (Rule_Type DEFINE_RULE_STAR) = Pretty.str ("define-rule* ")
  | pretty_rewrite_tree (Rule_Name s) = Pretty.str s
  | pretty_rewrite_tree (Par (trees)) =
      Pretty.enclose "(" ")" (Pretty.separate "" (map SMTLIB.pretty_tree
      (map (fn (Param p) => p | (ListParam p) => SMTLIB.S [p,SMTLIB.Sym ":list"]) trees)))
  | pretty_rewrite_tree (Let_Defs NONE) = Pretty.str ("")
  | pretty_rewrite_tree (Let_Defs (SOME s)) =
      Pretty.enclose "(" ")" (Pretty.separate "" (map SMTLIB.pretty_tree s))
  | pretty_rewrite_tree (Precondition tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Match tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Target tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Context_Expr NONE) = Pretty.str ""
  | pretty_rewrite_tree (Context_Expr (SOME tree)) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Rewrite_Rule trees) =
      Pretty.enclose "(" ")" (Pretty.separate "" (map pretty_rewrite_tree trees))

fun pretty_rewrite_rules cs = Pretty.block (map pretty_rewrite_tree cs)

val str_of = Pretty.unformatted_string_of o pretty_rewrite_rules

(* General Util *)

(*
Parses the next token from a string list, starting with an opening parenthesis until the matching
closing parenthesis.

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
  parse_token None _ = raise TOKEN("expected opening parenthesis") |
  parse_token (Unfinished (s,i)) ("("::cs) = parse_token (Unfinished ("("::s,i+1)) cs |
  parse_token (Unfinished (_,0)) (")"::_) = raise TOKEN("too many closing parenthesis") |
  parse_token (Unfinished (s,1)) (")"::xs) = Finished(rev (")"::s),xs) |
  parse_token (Unfinished (s,i)) (")"::cs) = parse_token (Unfinished (")"::s,i-1)) cs |
  parse_token (Unfinished (s,i)) (c::cs) = parse_token (Unfinished (c::s,i)) cs |
  parse_token _ _ = raise TOKEN("error parsing token")


(* Lexer Util *)

fun debug_msg_lexer ctxt msg =
  (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> "Lexer: " ^ msg))
fun verbose_msg_lexer ctxt msg =
  (IsaRARE_Config.verbose_msg ctxt (fn () => \<^print> "Lexer: " ^ msg))

fun lexer_debug_prefix l = "Lexer error in line " ^ Int.toString(l)  ^ ": "
fun raise_lexer_error l msg = raise PARSE(lexer_debug_prefix l ^ msg)


(* Lexer *)

fun lexer_add_line ctxt l line uf =
let
  val _ = verbose_msg_lexer ctxt ("reading line nr. " ^ Int.toString(l) ^ ": " ^ line)
  val trimmed_lines = raw_explode line |> Library.trim (curry (op =) " ")
in
  case trimmed_lines of
    [] => (debug_msg_lexer ctxt "found empty line, skip"; uf) |
    (";"::_) => (debug_msg_lexer ctxt "Lexer found comment, skip entire line"; uf) |
    _ => 
      let
        (* If line has a comment in it cut it *)
        val sanitized_lines
          = Library.take (Library.find_index (curry (op =) ";") trimmed_lines) trimmed_lines  |> Library.trim (curry (op =) " ")
       in
         parse_token uf sanitized_lines
         handle 
           (TOKEN msg) => raise_lexer_error l msg
       end
end


fun lexer _ [] (Unfinished (s,i)) l =
    raise_lexer_error l ("expected eof but last rule was not closed. Parsed " ^ Int.toString(l)
    ^ "parenthesis far and parse in: \n" ^ (rev s |> String.concat) )|
  lexer ctxt [] _ _ = (debug_msg_lexer ctxt "Finished lexing file";[]) |
  lexer ctxt (line::lines) uf l =
    case lexer_add_line ctxt l line uf of
      Finished (s,[]) => String.concat s :: lexer ctxt lines None (l+1) |
      Finished (_,s') => raise_lexer_error l ("text after final closing parenthesis found! " ^ String.concat s') |
      Unfinished (s,s') => lexer ctxt lines (Unfinished ([" "]@s,s')) (l+1) |
      None => lexer ctxt lines uf (l+1)

fun lex_rewrites ctxt cs = lexer ctxt cs None 1

(* Parser Utils *)

fun debug_msg_parser ctxt msg =
  (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> "Parser: " ^ msg))
fun parser_debug_prefix l = "Parser error in rule starting in line " ^ Int.toString(l)  ^ ": "
fun raise_parser_error l msg = raise PARSE(parser_debug_prefix l  ^ msg)

fun get_smtlib_term l t =
  SMTLIB.parse t
  handle
   err => raise_parser_error l "Error parsing SMT-LIB term"

fun parse_next_term l cs =
let
  val token = parse_token None cs
    handle
      (TOKEN msg) => raise_parser_error l msg
in
 case token of
   None => NONE |
   Finished (t,cs') => SOME (t,cs') |
   Unfinished _ => raise_parser_error l "closing parenthesis missing"
end

fun consume_char c cs = (if hd cs = c then SOME (tl cs) else NONE)

fun expected l x =
  case x of
    NONE => raise_parser_error l "mandatory component not found" |
    SOME cs' => cs'

(*
parameter are a list of SMT-LIB terms in parenthesis, the single parameters
are separated by a single whitespace from each other. Parameters can have
attributes starting with a colon. For now only the attribute is :list.
*)
fun parse_par l par = 
let
  val i = Library.find_index (curry (op =) ":") par
in
  if i = ~1
  then (Param (get_smtlib_term l par))
  else
    let
      val (par,attr) = Library.chop i par
    in
      if attr = (raw_explode ":list)")
      then (ListParam (get_smtlib_term l (par @ [")"])))
      else raise_parser_error l "parameter has unknown attribute"
    end
end

fun param_parser ctxt l cs =
let
  fun parse_param_list ts cs =
    case parse_next_term l cs of
      NONE => (Par ts,cs) | (* No parameters *)
      SOME (t,cs') =>
      let
        val par = parse_par l t
      in
        case consume_char " " cs' of
          NONE => (Par (par::ts),cs') |
          SOME cs'' => parse_param_list (par::ts) cs''
      end

  val cs' = consume_char "(" cs |> expected l
  val (params,cs'') = parse_param_list [] cs'
  val cs''' = consume_char ")" cs'' |> expected l
  val _ = debug_msg_parser ctxt ("Finished parsing parameters. Parsed in: " ^ str_of [params])
  val _ = debug_msg_parser ctxt ("After finishing parameters, the rest of the input is: " ^ implode cs''')
in
  (params,cs''')
end


(*
 Lemma names in Isabelle cannot have dashes in them, so they must be replaced by underscores
 when parsing the name of a rewrite
*)
datatype token = None | Unfinished of string | Finished of string

fun parse_string l (c :: cs) None error_msg =
       if Symbol.is_ascii_blank c then parse_string l cs None error_msg (*Ignore leading space*)
       else parse_string l cs (Unfinished c) error_msg | (*Start of a word*)
    parse_string l (c :: cs) (Unfinished s) error_msg =
       if Symbol.is_ascii_blank c then (cs, s) (*End of a word*)
       else if c = "-" then parse_string l cs (Unfinished (s ^ "_")) error_msg (*Replace - in name by _ *)
       else parse_string l cs (Unfinished (s ^ c)) error_msg | (*Word continues*)
    parse_string l _ _  error_msg = raise PARSE (error_msg)

fun name_parser l cs =
let
  fun parse_name (" "::cs) s = (rev s,cs) |
      parse_name ("-"::cs) s = parse_name cs ("-"::s) |
      parse_name (c::cs) s = parse_name cs (c::s)

  val (name, cs'') = parse_name cs [] |>> implode |>> Rule_Name
in 
  (name,cs'')
end


fun type_parser l (("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::" ":: cs)) =
    ((Rule_Type DEFINE_RULE),cs) |
  type_parser l (("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"c"::"o"::"n"::"d"::"-"::"r"::"u"::"l"::"e"::" ":: cs)) =
    ((Rule_Type DEFINE_COND_RULE),cs) |
  type_parser l (("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::"*"::" ":: cs)) =
    ((Rule_Type DEFINE_RULE_STAR),cs) |
  type_parser l (_) = raise_parser_error l "Could not read type!"

fun expression_parser l f cs =
parse_next_term l cs |> expected l |>> get_smtlib_term l |>> f

fun let_parser l cs = ((Rule_Type DEFINE_RULE),cs)

(*TODO catch error*)
fun some_whitespace l = Scan.permissive Scan.some (fn c => if c = " " then SOME c else NONE)
handle
  FAIL => raise_parser_error l "expected ' ' but not found"


fun parse_all ctxt (l,cs) =
let
  val ((((Rule_Type rtyp,name),params),let_def),cs')
    = cs 
      |>  type_parser l
      --| some_whitespace l
      --  name_parser l
      --| some_whitespace l
      --  param_parser ctxt l
      --| some_whitespace l
      --  Scan.option (let_parser l)
in
 if rtyp = DEFINE_COND_RULE
 then
  let
    val (((cond,match),target),cs'') = (expression_parser l Precondition -- expression_parser l Match -- expression_parser l Target) cs'
  in Rewrite_Rule [(Rule_Type rtyp),name,params,cond,match,target] :: parse_all ctxt (l,cs'') end
 else
Rewrite_Rule [(Rule_Type rtyp),name,params] :: []
end


(*
(* Component Parser *)
(* Input: Current line number and rest of input string *)
(* Output: NONE if component was not found, 
          SOME if component was found (the line after parsing component,
                                       parsed component (if exists),
                                       and rest of string without component *)

type single_comp_parser = int * string list -> (rewrite_tree option * (int * string list)) option

type total_comp_parser = int * string list -> (rewrite_tree option * (int * string list))

fun optional (cp : single_comp_parser) : total_comp_parser = 
(fn x =>
 case cp x of
  NONE => (NONE,x) |
  SOME (t,x') => (t,x'))

fun mandatory (cp : single_comp_parser) : total_comp_parser = 
(fn (i,cs) =>
 case cp (i,cs) of
  NONE => raise_parser_error i "Problem in parser, could not find mandatory component!" |
  SOME (t,(i',cs')) => (t,(i',cs'))
)

type comp_parser = rewrite_tree list * (int * string list) -> rewrite_tree list * (int * string list)

fun repeat_comp_parser (cp:single_comp_parser) (ts,(i,cs)) =
 case cp (i,cs) of
  NONE => (ts,(i,cs)) |
  SOME (NONE,(i',cs')) => repeat_comp_parser cp (ts,(i',cs')) |
  SOME (SOME t,(i',cs')) => repeat_comp_parser cp ((t::ts),(i',cs'))

fun next_comp cp (t,(i,cs)) =
  cp (i,cs) |>> (fn t' => (if Option.isSome t' then Option.valOf t' :: t  else t))

(* Util component parsers *)

fun skip_to_eol (l,[]) = (SOME (NONE,(l,[]))) |
    skip_to_eol (l,("\\"::"n"::cs)) = (SOME (NONE,(l+1,cs))) |
    skip_to_eol (l,(_::cs)) = skip_to_eol (l,cs)

fun skip_comment (_,[]) = NONE |
    skip_comment (l,(";"::cs)) = skip_to_eol (l,cs) |
    skip_comment (_,_) = NONE 

fun skip_token c (l,[]) = NONE |
    skip_token c (l,(c'::cs)) = if c = c' then SOME(NONE,(l,cs)) else NONE

fun expect_token c (l,[])
      = raise PARSE("Expected character " ^ c  ^ "but reached end of file") |
    expect_token c (l,(c'::cs)) =
      if c = c'
      then SOME(NONE,(l,cs))
      else raise PARSE( "Expected character " ^ c ^ " but found " ^ c')


fun consume_token c (l,[]) = NONE |
    consume_token c (l,(c'::cs)) =
      if c = c'
      then SOME(NONE,(l,cs))
      else NONE
      
val comment_parser : comp_parser = repeat_comp_parser skip_comment

fun skip_chars_parser c = skip_token c |> repeat_comp_parser 

fun debug_parser message ctxt (ts,(i,cs)) = (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  (message ^ "\nIn line: ", i));NONE)


(* RARE component parsers *)

(*Parse nested term*)



(*
fun parse_nested_term  = 

fun parse_smt_lib_tree = 


(*(t ?Array)*)
fun parse_param (i,cs) =
let
  val (t,(i,cs)) = consume_token "(" (i,cs)
  val (name,(i,cs)) = parse_until " "
  val (typ,(i,cs)) = parse_smt_lib_tree
list
  val (t,(i,cs)) = consume_token ")" (i,cs)

in 
""
end

fun parse_params (t,(i,cs)) =
let
  val (ts,(i',cs')) = repeat_comp_parser parse_param ([],(i,cs))

*)
(*
   type  (char, string) reader = string -> (char * string) option    

    val skipWS : (char, string) reader -> string -> string

*)





*)





(*



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
    rule :: [name] @ (*[Par (parsed_par,list_pars)] @*) [Let_Defs ld] @ expr
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
fun parse_rewrites ctxt lines = (fold (add_line ctxt) lines (1,[])) |> snd |> rev

*)
(*TEMP: Figure out how to parse this in a string list automatically, seperating at\n *)


end;