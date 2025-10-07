(*  Title:      IsaRARE/alf_parser.ML
    Author:     Hanna Lachnitt, Stanford University

    Lexer for "RARE as an Eunoia fragment".
*)

signature ALF_LEXER =
sig
  exception ALF_LEXER of string
  val lex_alf : Proof.context -> string list -> (int * string) list
  (* TODO: remove this from the signature once we put the lexing
           stuff in the lex_alf *)
  val alf_type_lexer : int -> string list -> ALF_AST.alf_rule_type * string list
end;

structure ALF_LEXER: ALF_LEXER =
struct

(* Exceptions and handlers *)
exception ALF_LEXER of string

fun debug_msg_lexer ctxt msg =
  (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> ("Lexer: " ^ msg)))

fun lexer_debug_prefix l = "Lexer error in rule starting in line " ^ Int.toString(l)  ^ ": "

fun raise_lexer_error l msg = raise ALF_LEXER(lexer_debug_prefix l  ^ msg)

(* Lexing routines. *)
(* TODO: this is more lexing-related *)
fun alf_type_lexer _ (("d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"a"::"x"::"i"::"o"::"m":: cs)) =
    (ALF_AST.ALF_AXIOM,cs) |
  alf_type_lexer _ (("d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"r"::"u"::"l"::"e":: cs)) =
    (ALF_AST.ALF_RULE,cs) |
  alf_type_lexer l _ = raise_lexer_error l "Could not read type of alf rule!"

(* TODO: alf lexer! *)
fun lex_alf ctxt cs = []

end;
