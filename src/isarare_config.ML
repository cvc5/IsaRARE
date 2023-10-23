(*  Title:      IsaRARE/isarare_config.ML
    Author:     Hanna Lachnitt, Stanford University

Diagnostic tools for IsaRARE.

*)

signature ISARARE_CONFIG =
sig
  datatype proof_strategy = None | Minimum | Full 
  datatype proof_strategy_theory = All | Strings | Arith

  (*Options*)
  val verbose: bool Config.T
  val debug: bool Config.T
  val implAssump: bool Config.T
  val listsAsVar: bool Config.T
  val proofStrategy: string Config.T
  val proofStrategyTheory: string Config.T

  (*Diagnostics*)
  val verbose_msg: Proof.context -> ('a -> string) -> 'a -> unit
  val debug_msg: Proof.context -> ('a -> string) -> 'a -> unit
  val debug_msg_raw: Proof.context -> (unit -> 'a) -> unit

  val getStrategy: Proof.context -> proof_strategy
  val getStrategyTheory: Proof.context -> proof_strategy_theory

end;

structure IsaRARE_Config: ISARARE_CONFIG =
struct

datatype proof_strategy = None | Minimum | Full 
datatype proof_strategy_theory = All | Strings | Arith

val verbose = Attrib.setup_config_bool \<^binding>\<open>IsaRARE_verbose\<close> (K false)
val debug = Attrib.setup_config_bool \<^binding>\<open>IsaRARE_debug\<close> (K false)
val implAssump = Attrib.setup_config_bool \<^binding>\<open>IsaRARE_implAssump\<close> (K true)
val listsAsVar = Attrib.setup_config_bool \<^binding>\<open>IsaRARE_listsAsVar\<close> (K false)
val proofStrategy = Attrib.setup_config_string \<^binding>\<open>IsaRARE_proofStrategy\<close> (K "Full")
val proofStrategyTheory = Attrib.setup_config_string \<^binding>\<open>IsaRARE_proofStrategyTheory\<close> (K "All")

val str_to_proof_strategy = [("None",None),("Minimum",Minimum),("Full", Full)]
val str_to_proof_strategy_theory = [("All",All),("Strings",Strings),("Arith",Arith)]

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

end;