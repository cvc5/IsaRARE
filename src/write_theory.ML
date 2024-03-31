(*  Title:      IsaRARE/write_theory.ML
    Author:     Hanna Lachnitt, Stanford University

This signature provides functionality to write a term as a lemma and print a proof sketch
*)

signature WRITE_THEORY =
sig
  exception WRITE_THEORY_FROM_DSL_REWRITE of string

  val write_lemma: Proof.context -> Process_RARE.rewrite_rule_term -> string
  val write_thy: Proof.context -> string -> string -> Process_RARE.rewrite_rule_term list -> string
end;

open SMTLIB_Proof
open Parse_RARE
open Process_RARE

structure Write_Theory: WRITE_THEORY =
struct
  exception WRITE_THEORY_FROM_DSL_REWRITE of string

(* Utilities *)

fun hackish_string_of_term ctxt =
 Print_Mode.setmp [] (Syntax.string_of_term ctxt)
  #> YXML.content_of

fun hackish_string_of_type ctxt =
 Print_Mode.setmp [] (Syntax.string_of_typ ctxt)
  #> YXML.content_of

(* Theory *)

fun write_file_header ctxt theory_name theory_imports 
 = Library.cat_lines
  ["theory " ^ theory_name,
   "  imports \"HOL-CVC.Dsl_Nary_Ops\" " ^ theory_imports,
   "begin\n",
   "(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!",
   "All that remains to do is to prove any lemma whose provided proof fails.",
   "If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy \n\n",
   "The options used to print this file were: ", IsaRARE_Config.print_options ctxt, "*)\n\n" ]

val write_file_footer = "end"

(* Lemma *)

fun write_lemma_header name
 = Library.cat_lines
   ["named_theorems rewrite_" ^ name ^ " \<open>automatically_generated\<close>\n",
    "lemma [rewrite_" ^ name ^ "]:"]

fun write_body ctxt ({rule_name,params,concl}:rewrite_rule_term) =
  let
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Writing body "))

   val str_body = hackish_string_of_term ctxt concl
  
   val goal' = "NO_MATCH cvc_a (undefined" ^ (map fst params |> map (curry (op ^) " ") |> String.concat) ^") \<Longrightarrow> "
  in
   "  shows \"" ^ goal' ^ str_body ^ "\"" 
  end

(* Proofs *)

fun 

(* Combined *)

fun write_lemma ctxt (lemma as {rule_name,params,concl} : rewrite_rule_term) =
  write_lemma_header rule_name ^  "\n" ^ write_body ctxt lemma ^ "\n"

fun write_thy ctxt theory_name theory_imports cs =
 write_file_header ctxt theory_name theory_imports ^ String.concat (map (write_lemma ctxt) cs)
           

end;