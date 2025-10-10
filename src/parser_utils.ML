(*  Title:      IsaRARE/parser_utils.ML
    Author:     Hanna Lachnitt, Stanford University

    Parsing and related routines shared by ALF and RARE parsers.
*)
signature PARSER_UTILS =
sig
    (* Exceptions and exception handling mechanisms. *)
    exception PARSE of string
    exception TOKEN of string
    (* TODO: it would be better to have this put in another module *)
    datatype token = None | Unfinished of string list * int | Finished of string list * string list
    val debug_msg_parser : Proof.context -> string -> unit
    val parser_debug_prefix : int -> string
    val raise_parser_error : int -> string -> 'a

    (* Printing *)
    val str_of_par : REWRITE_RULE_AST.par -> string

    (* Common parsing-related routines. *)
    val get_smtlib_term : int -> string list -> SMTLIB.tree
    val parse_next_term : int  -> (token -> string list -> token) -> string list -> string list * string list
    val expect_char : int -> string -> string -> string list -> string * string list
    val least_one_char : int -> string -> string -> string list -> string list * string list
    val ignore_chars : int -> ''a -> ''a list -> ''a list * ''a list

end;

structure PARSER_UTILS: PARSER_UTILS =
struct

(* Exceptions and exception handling mechanisms. *)
exception PARSE of string
exception TOKEN of string

fun debug_msg_parser ctxt msg =
  (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> ("Parser: " ^ msg)))
fun parser_debug_prefix l = "Parser error in rule starting in line " ^ Int.toString(l)  ^ ": "
fun raise_parser_error l msg = raise PARSE(parser_debug_prefix l  ^ msg)

datatype token = None | Unfinished of string list * int | Finished of string list * string list


(* Printing of s-expressions. *)

fun str_of_par (REWRITE_RULE_AST.Par t) = "(" ^ SMTLIB.str_of t ^ ")" |
    str_of_par (REWRITE_RULE_AST.ListPar t) = "(" ^ SMTLIB.str_of t ^ " :list)"

fun get_smtlib_term l t = SMTLIB.parse t
  handle
   SMTLIB.PARSE (_,msg) => raise_parser_error l ("Error parsing SMT-LIB term " ^ String.concat t ^ msg)

fun parse_next_term l (parse_token :  (token -> string list -> token)) (cs : string list) =
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


end;
