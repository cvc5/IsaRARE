theory IsaRARE_Tests
  imports "../IsaRARE"
begin


declare[[IsaRARE_verbose = true]] (*Get additional information*)
declare[[IsaRARE_debug = true]] (*Get debugging information*)
declare[[IsaRARE_implAssump = true]] (*Turn implicit assumption generation on or off (Warning this is an expert option: Lemmas might not be provable without the assumptions) *)
declare[[IsaRARE_listsAsVar = false]] (*When turned on list parameters are parsed as if they were variables (Warning this is an expert option: Lemmas might be proven but corresponding RARE rule is not correct) *)
declare [[ML_print_depth=10000]]


(*Test*)
(*TODO: Get current directory*)

(*For boolean rewrites the proof strategy using induction is often to eager, the lemmas are proven directly and 
all further steps fail since the goal is already discharged. Therefore, for our boolean rewrites that tend to be 
extremely simple we use a strategy that merely deletes all custom definitions from the lemma.
In practise the user can also generate full proofs and delete unnecessary steps, although we recommend
using the Minimum strategy for these cases  *)
declare[[IsaRARE_proofStrategy = "Minimum"]]
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/boolean_rewrites" "Boolean_Rewrites_Lemmas" "Boolean_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/uf_rewrites" "" "UF_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/builtin_rewrites" "" "Builtin_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/set_rewrites" "" "Set_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/array_rewrites" "" "Array_Rewrites"

(*Set strategy to Arith so proofs for lemmas with lists can all be done automatic *)
declare[[IsaRARE_proofStrategyTheory = "Arith"]]
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/arith_rewrites" "Arith_Rewrites_Lemmas" "Arith_Rewrites"

(*Set strategy to String so proofs for lemmas with lists can all be done automatic *)
declare[[IsaRARE_proofStrategyTheory = "Strings"]]
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/string_rewrites" "" "String_Rewrites"
declare[[IsaRARE_proofStrategyTheory = "All"]]




(*


parse_rare_file "~/Sources/IsaRARE/Tests/Regression/bv_rewrites" "" "Bitvector_Rewrites"*)

end