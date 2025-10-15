(*  Title:      IsaRARE/write_theory.ML
    Author:     Hanna Lachnitt, Stanford University

This signature provides functionality to write a term as a lemma and print a proof sketch
*)

signature WRITE_THEORY =
sig
  exception WRITE_THEORY_FROM_DSL_REWRITE of string

  val write_lemma: Proof.context -> int -> Process_RARE.rewrite_rule_lemma -> string
  val write_thy: Proof.context -> string -> string -> Process_RARE.rewrite_rule_lemma list -> string
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
  (*#> YXML.content_of*)

fun hackish_string_of_sort ctxt = (*Maybe there is an option for hackish_string_of_type instead*)
 Print_Mode.setmp [] (Syntax.string_of_sort ctxt)
  (*#> YXML.content_of*)
  #> Sledgehammer_Util.simplify_spaces
  #> raw_explode #> Library.filter_out (curry (op =) "?") #> implode

fun hackish_string_of_type ctxt =
 Print_Mode.setmp [] (Syntax.string_of_typ ctxt)
  (*#> YXML.content_of*)
  #> Sledgehammer_Util.simplify_spaces
  #> raw_explode #> Library.filter_out (curry (op =) "?") #> implode

(*We could use string_of_sort for lemmas like arith_elim_gt but we don't really want it to be that
general. It should only be Real and Int. But then we don't always want to generate several lemmas...
We could find closest anchestor but who guarantees us that we can prove the lemma?
*)

(* Theory *)

fun write_file_header ctxt theory_name theory_imports 
 = Library.cat_lines
  ["theory " ^ theory_name,
   "  imports \"HOL.Dsl_Nary_Ops\" " ^ theory_imports,
   "begin\n",
   "(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!",
   "All that remains to do is to prove any lemma whose provided proof fails.",
   "If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy \n\n",
   "The options used to print this file were: ", IsaRARE_Config.print_options ctxt, "*)\n\n" ]

val write_file_footer = "end"

(* Lemma *)

fun write_lemma_header ctxt name nr
 = if IsaRARE_Config.named_theorems ctxt
   then
    Library.cat_lines
    ["named_theorems rewrite_" ^ name ^ " \<open>automatically_generated\<close>\n",
    "lemma [rewrite_" ^ name ^ "]:"]
   else
    "lemma " ^ name ^ (if nr = 0 then "" else Int.toString nr) ^ ":"

fun write_params ctxt [] = "" |
 write_params ctxt params =
 "  fixes " ^
 (((map (fn (par,typL) => par ^ " :: \"" ^ (hackish_string_of_type ctxt typL) 
^ (if  Term.is_TFree typL orelse Term.is_TVar typL then " :: " ^ (hackish_string_of_sort ctxt (Type.sort_of_atyp typL)) else "") ^ "\"") params) |> map (fn x => x ^ " and ") |> String.concat)
  |> Library.unsuffix " and ")
 ^ "\n"

fun write_body ctxt ({params,concl}:rewrite_rule_term) =
  let
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Writing body "))

   val str_body = hackish_string_of_term ctxt concl
  
   val goal' =
    if IsaRARE_Config.print_nomatch ctxt
    then "NO_MATCH cvc_a (undefined" ^ (map fst params |> map (curry (op ^) " ") |> String.concat) ^") \<Longrightarrow> " (*Do this somewhere else eventually*)
    else ""
  in
   "  shows \"" ^ goal' ^ str_body ^ "\"" 
  end

(* Proofs *)

val write_sorry = "  sorry"
val write_done = "  done"

(*Should be able to use Tactical.CHANGED  but not clear what error it throws have to test out*)

datatype status = Unchanged | Changed of string*thm | Solved of string*thm

fun changed_goal thm thm' = not (Thm.eq_thm (thm, thm'))
fun solved_goal thm' = thm' |> Thm.no_prems

fun print_tac ctxt (tac,tac_str) thm =
  let
    val _ = @{print}("Trying tactic: ", tac_str)
    val thm' = (Tactic.rule_by_tactic|> Timeout.apply (Time.fromSeconds 1)) ctxt (tac|> Timeout.apply (Time.fromSeconds 1)) thm 
    val _ = @{print}("Thm after tactic ", thm')

  in
    if solved_goal thm' then Solved (tac_str ^ "\n" ^ write_done,thm')
    else if changed_goal thm thm' then Changed (tac_str,thm')
    else Unchanged  
  end

(*How to distinguish if it has been solved?*)
fun apply_all _ [] proof thm = SOME proof |
  apply_all ctxt ((tac,tac_str)::tacs) proof thm =
  (case print_tac ctxt (tac,tac_str) thm of
    Unchanged => apply_all ctxt tacs proof thm |
    (Changed (str,thm')) => apply_all ctxt tacs (proof ^ "  " ^ str ^ "\n") thm' |
    (Solved (str,_)) => SOME (proof ^ "  " ^ str ^ "\n"))

fun apply_all_until_success _ [] _ _ = NONE |
  apply_all_until_success ctxt ((tac,tac_str)::tacs) proof thm =
  (case print_tac ctxt (tac,tac_str) thm |> @{print} of
    Unchanged => apply_all_until_success ctxt tacs proof thm |
    (Changed (str,thm')) => apply_all_until_success ctxt tacs (proof ^ "  " ^ str ^ "\n") thm' |
    (Solved (str,_)) => SOME (proof ^ "  " ^ str ^ "\n"))

fun apply_no_incomplete _ [] _ = NONE |
   apply_no_incomplete ctxt ((tac,tac_str)::tacs) thm =
  (case print_tac ctxt (tac,tac_str) thm of
    Unchanged => apply_no_incomplete ctxt tacs thm |
    (Changed (_,_)) => apply_no_incomplete ctxt tacs thm |
    (Solved (str,_)) => SOME ("  " ^ str ^ "\n"))

fun partial_simplify_tac ctxt thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps @{thms simp_thms} addsimps thms)
  |> Simplifier.full_simp_tac

fun use_simp ctxt = (Basic_Simplifier.simp_tac ctxt 1,"apply simp ?")

fun use_auto ctxt = (Clasimp.auto_tac ctxt,"apply auto ?")
(*
Problem ist das unfold auch HOL_basic_ss benutzt und dann zu eager sein kann. unfolding kann
irgendwie nicht mithalten
fun unfold_tac ctxt ths =
  ALLGOALS (full_simp_tac (clear_simpset (put_simpset HOL_basic_ss ctxt) addsimps ths));
*)
(*fun smt_unfold ctxt = (unfold_tac ctxt [@{thm xor_def},@{thm SMT.z3div_def}],"unfolding xor_def SMT.z3div_def")*)
fun smt_unfold ctxt = (unfold_tac ctxt [@{thm SMT.z3div_def}],"unfolding xor_def SMT.z3div_def")

fun unfold_str_substr ctxt = (partial_simplify_tac ctxt  [@{thm Smtlib_String.smtlib_str_substr_def}] 1,"unfolding smtlib_str_substr_def")
fun string_simplify ctxt = (partial_simplify_tac ctxt (Named_Theorems.get ctxt "Smtlib_String.cvc_string_rewrite_defs") 1,"apply (simp_all add: cvc_string_rewrite_defs)")
fun simplify_lists ctxt = (partial_simplify_tac ctxt @{thms cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op} 1, "    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)\n" )  

fun cases ctxt = (Induct.cases_tac ctxt , "apply (cases name)")

fun print_subgoal xs = "subgoal or "



fun find_proof ctxt concl =
 ( Const ("HOL.Trueprop",@{typ "bool \<Rightarrow> prop"})) $ concl
 |> Thm.cterm_of ctxt |> Goal.init
 |> apply_all_until_success ctxt [use_simp ctxt, unfold_str_substr ctxt, simplify_lists ctxt, string_simplify ctxt,smt_unfold ctxt,use_auto ctxt] ""
 |> (fn SOME x => x | NONE => write_sorry)
 handle Timeout.TIMEOUT _ => write_sorry


(* Combined *)


fun write_lemma ctxt i (lemma as {rule_name,rule_body} : rewrite_rule_lemma) =
 case rule_body of
 [] => "" |
 [(b as {params,concl} :rewrite_rule_term)] => write_lemma_header ctxt rule_name i ^  "\n" ^ write_params ctxt params
 ^  write_body ctxt b ^ "\n" ^ find_proof ctxt concl ^ "\n"^ "\n" |
 ((b as {params,concl} :rewrite_rule_term)::xs) => write_lemma_header ctxt rule_name i ^  "\n" ^ write_params ctxt params
 ^  write_body ctxt b ^ "\n" ^ find_proof ctxt concl ^ "\n"^ "\n" ^ write_lemma ctxt (i + 1) ({rule_name=rule_name,rule_body=xs})



fun write_thy ctxt theory_name theory_imports cs = (@{print}("cs",cs);
 write_file_header ctxt theory_name theory_imports ^ String.concat (map (write_lemma ctxt 0) cs) ^ write_file_footer)
           

end;