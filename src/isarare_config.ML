(*  Title:      IsaRARE/isarare_config.ML
    Author:     Hanna Lachnitt, Stanford University

Diagnostic tools for IsaRARE.

*)

signature ISARARE_CONFIG =
sig
  datatype proof_strategy = None | Minimum | Full | TACAS_Autoprove 
  datatype proof_strategy_theory = All | Strings | Arith | BV

  (*Options*)      
  val verbose: bool Config.T
  val debug: bool Config.T
  val ruleFormat: string Config.T
  val implAssump: bool Config.T
  val listsAsVar: bool Config.T
  val proofStrategy: string Config.T
  val proofStrategyTheory: string Config.T
  val IsaRAREHome: string Config.T

  (*Diagnostics*)
  val verbose_msg: Proof.context -> ('a -> string) -> 'a -> unit
  val debug_msg: Proof.context -> ('a -> string) -> 'a -> unit
  val debug_msg_raw: Proof.context -> (unit -> 'a) -> unit

  val getStrategy: Proof.context -> proof_strategy
  val getStrategyTheory: Proof.context -> proof_strategy_theory

  (*Print*)
  val print_options: Proof.context -> string
end;

structure IsaRARE_Config: ISARARE_CONFIG =
struct

datatype proof_strategy = None | Minimum | Full | TACAS_Autoprove 
datatype proof_strategy_theory = All | Strings | Arith | BV

val verbose = Attrib.setup_config_bool \<^binding>\<open>IsaRARE_verbose\<close> (K false)
val debug = Attrib.setup_config_bool \<^binding>\<open>IsaRARE_debug\<close> (K false)
val ruleFormat = Attrib.setup_config_string \<^binding>\<open>IsaRARE_ruleFormat\<close> (K "RARE")
val implAssump = Attrib.setup_config_bool \<^binding>\<open>IsaRARE_implAssump\<close> (K true)
val listsAsVar = Attrib.setup_config_bool \<^binding>\<open>IsaRARE_listsAsVar\<close> (K false)
val proofStrategy = Attrib.setup_config_string \<^binding>\<open>IsaRARE_proofStrategy\<close> (K "Full")
val proofStrategyTheory = Attrib.setup_config_string \<^binding>\<open>IsaRARE_proofStrategyTheory\<close> (K "All")
val IsaRAREHome = Attrib.setup_config_string \<^binding>\<open>IsaRARE_HOME\<close> (K "")

val str_to_proof_strategy = [("None",None),("Minimum",Minimum),("Full", Full),("TACAS_Autoprove",TACAS_Autoprove)]
val str_to_proof_strategy_theory = [("All",All),("Strings",Strings),("Arith",Arith),("BV",BV)]

fun getStrategy ctxt =
  (case List.find (fn (str,_) => (Config.get ctxt proofStrategy) = str) str_to_proof_strategy of
    NONE => None |
    (SOME (_,strat)) => strat)

fun getStrategyTheory ctxt =
  (case List.find (fn (str,_) => (Config.get ctxt proofStrategyTheory) = str) str_to_proof_strategy_theory of
    NONE => All |
    (SOME (_,strat)) => strat)

fun cond_msg cond ctxt f x = if (Config.get ctxt cond) then tracing ("IsaRARE: " ^ f x) else ()
fun verbose_msg ctxt f x = cond_msg verbose ctxt f x
fun debug_msg ctxt f x = cond_msg debug ctxt f x
fun debug_msg_raw ctxt (x : unit -> 'a) = if (Config.get ctxt debug) then ignore(x ()) else ()

fun print_options ctxt =
 "The options currently set for IsaRARE are:\n" ^ 
 "home directory set to: " ^ (Config.get ctxt IsaRAREHome) ^ "\n" ^ 
 "verbose: " ^ Bool.toString (Config.get ctxt verbose) ^ "\n" ^ 
 "debug: " ^ Bool.toString (Config.get ctxt debug) ^ "\n" ^ 
 "implicit assumption generation: " ^ Bool.toString (Config.get ctxt implAssump) ^ "\n" ^ 
 "lists are treated as variables: " ^ Bool.toString (Config.get ctxt listsAsVar) ^ "\n" ^ 
 "the proof strategy is set to: " ^  (Config.get ctxt proofStrategy) ^ "\n" ^ 
 "the proof theory strategy is set to: " ^  (Config.get ctxt proofStrategyTheory) ^ "\n"

end;