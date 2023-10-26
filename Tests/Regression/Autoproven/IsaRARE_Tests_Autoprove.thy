theory IsaRARE_Tests_Autoprove
  imports "IsaRARE"
begin

(*This was an attempt to give TACAS reviewers the chance to test the autoproven feature but it 
would be unreasonable time consuming for them so we are abandoning it.*)

declare[[IsaRARE_verbose = true]] (*Get additional information*)
declare[[IsaRARE_debug = true]] (*Get debugging information*)
declare[[IsaRARE_implAssump = true]] (*Turn implicit assumption generation on or off (Warning this is an expert option: Lemmas might not be provable without the assumptions) *)
declare[[IsaRARE_listsAsVar = false]] (*When turned on list parameters are parsed as if they were variables (Warning this is an expert option: Lemmas might be proven but corresponding RARE rule is not correct) *)
declare [[ML_print_depth=10000]]

declare[[IsaRARE_proofStrategy = "TACAS_Autoprove"]]
parse_rare_file "~/Sources/Tests/Regression/Autoproven/euf_rewrites_autoproven" "" "EUF_Rewrites_Autoproven_new"
parse_rare_file "~/Sources/Tests/Regression/Autoproven/set_rewrites_autoproven" "" "Set_Rewrites_new"
parse_rare_file "~/Sources/Tests/Regression/Autoproven/array_rewrites_autoproven" "" "Array_Rewrites_new"

(*Set strategy to Arith so proofs for lemmas with lists can all be done automatic *)
declare[[IsaRARE_proofStrategyTheory = "Arith"]]
parse_rare_file "~/Sources/Tests/Regression/Autoproven/arith_rewrites_autoproven" "" "Arith_Rewrites_Autoproven_new"

(*Set strategy to String so proofs for lemmas with lists can all be done automatic *)
declare[[IsaRARE_proofStrategyTheory = "Strings"]]
parse_rare_file "~/Sources/Tests/Regression/Autoproven/string_rewrites_autoproven" "" "String_Rewrites_Autoproven_new"
declare[[IsaRARE_proofStrategyTheory = "All"]]

parse_rare_file "~/Sources/Tests/Regression/Autoproven/bv_rewrites" "" "Bitvector_Rewrites_Autoproven_new"

end
