(*  Title:      IsaRARE/alf_parser.ML
    Author:     Hanna Lachnitt, Stanford University

    Lexer for "RARE as an Eunoia fragment".
*)

signature ALF_LEXER =
sig
  exception ALF_LEXER of string
  val alf_lexer : PARSER_UTILS.token -> string list -> PARSER_UTILS.token
  (* TODO: remove this from the signature once we put the lexing
           stuff in the lex_alf *)
  val alf_declare_rule_lexer : int -> string list -> ALF_AST.alf_rule_type * string list
  val alf_name_lexer : int -> string list -> string * string list
end;

structure ALF_LEXER: ALF_LEXER =
struct

(* Exceptions and handlers *)
exception ALF_LEXER of string

fun lexer_debug_prefix l = "Lexer error in rule starting in line " ^ Int.toString(l)  ^ ": "

fun raise_lexer_error l msg = raise ALF_LEXER(lexer_debug_prefix l  ^ msg)

(* Lexing routines. *)
fun alf_declare_rule_lexer _ (("d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"r"::"u"::"l"::"e":: cs)) =
    (ALF_AST.ALF_RULE,cs) |
  alf_declare_rule_lexer l _ = raise_lexer_error l "Could not read type of alf rule!"

(*
 Lemma names in Isabelle cannot have dashes in them, so they must be replaced by underscores
 when parsing the name of a rewrite
*)

fun alf_name_lexer l cs =
  Scan.catch Scan.many (curry (op <>) " ") cs
  |>> map (fn "-" => "_" | x => x)
  |>> implode
  handle (Fail _) => PARSER_UTILS.raise_parser_error l "Could not parse in rule name"

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

fun alf_lexer s [] = s |
  alf_lexer PARSER_UTILS.None ("("::cs) = alf_lexer (PARSER_UTILS.Unfinished(["("],1)) cs |
  alf_lexer PARSER_UTILS.None (")"::cs) = Scan.fail cs |
  alf_lexer PARSER_UTILS.None cs = PARSER_UTILS.Finished (Scan.catch Scan.many (fn c => c <> " " andalso c <> ")") cs) |
  alf_lexer (PARSER_UTILS.Unfinished (s,i)) ("("::cs) = alf_lexer (PARSER_UTILS.Unfinished ("("::s,i+1)) cs |
  alf_lexer (PARSER_UTILS.Unfinished (_,0)) (")"::_) = raise PARSER_UTILS.TOKEN("too many closing parenthesis") |
  alf_lexer (PARSER_UTILS.Unfinished (s,1)) (")"::xs) = PARSER_UTILS.Finished(rev (")"::s),xs) |
  alf_lexer (PARSER_UTILS.Unfinished (s,i)) (")"::cs) = alf_lexer (PARSER_UTILS.Unfinished (")"::s,i-1)) cs |
  alf_lexer (PARSER_UTILS.Unfinished (s,i)) (c::cs) = alf_lexer (PARSER_UTILS.Unfinished (c::s,i)) cs |
  alf_lexer _ _ = raise PARSER_UTILS.TOKEN("error parsing token")

end;
