theory Level0_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" 
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy 


The options used to print this file were: 
The options currently set for IsaRARE are:
home directory set to: 
verbose: false
debug: false
rule format RARE
implicit assumption generation: true
lists are treated as variables: false
the proof strategy is set to: Full
the proof theory strategy is set to: All

*)

named_theorems rewrite_bool_double_not_elim \<open>automatically_generated\<close>

lemma [rewrite_bool_double_not_elim]:
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (\<not> \<not> t) = t"
named_theorems rewrite_bool_eq_true \<open>automatically_generated\<close>

lemma [rewrite_bool_eq_true]:
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = True) = t"
named_theorems rewrite_bool_eq_false \<open>automatically_generated\<close>

lemma [rewrite_bool_eq_false]:
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = False) = (\<not> t)"
named_theorems rewrite_bool_eq_nrefl \<open>automatically_generated\<close>

lemma [rewrite_bool_eq_nrefl]:
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x = (\<not> x)) = False"
named_theorems rewrite_bool_impl_false1 \<open>automatically_generated\<close>

lemma [rewrite_bool_impl_false1]:
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t \<longrightarrow> False) = (\<not> t)"
named_theorems rewrite_bool_impl_false2 \<open>automatically_generated\<close>

lemma [rewrite_bool_impl_false2]:
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (False \<longrightarrow> t) = True"
named_theorems rewrite_bool_impl_true1 \<open>automatically_generated\<close>

lemma [rewrite_bool_impl_true1]:
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t \<longrightarrow> True) = True"
named_theorems rewrite_bool_impl_true2 \<open>automatically_generated\<close>

lemma [rewrite_bool_impl_true2]:
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (True \<longrightarrow> t) = t"
named_theorems rewrite_bool_impl_elim \<open>automatically_generated\<close>

lemma [rewrite_bool_impl_elim]:
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> (t \<longrightarrow> s) = (\<not> t \<or> s)"
named_theorems rewrite_bool_xor_refl \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_refl]:
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> x [+] x = False"
named_theorems rewrite_bool_xor_nrefl \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_nrefl]:
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> x [+] (\<not> x) = True"
named_theorems rewrite_bool_xor_false \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_false]:
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> x [+] False = x"
named_theorems rewrite_bool_xor_true \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_true]:
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> x [+] True = (\<not> x)"
named_theorems rewrite_bool_xor_comm \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_comm]:
  shows "NO_MATCH cvc_a (undefined y x) \<Longrightarrow> x [+] y = y [+] x"
named_theorems rewrite_bool_xor_elim \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_elim]:
  shows "NO_MATCH cvc_a (undefined y x) \<Longrightarrow> x [+] y = (x \<noteq> y)"
named_theorems rewrite_ite_neg_branch \<open>automatically_generated\<close>

lemma [rewrite_ite_neg_branch]:
  shows "NO_MATCH cvc_a (undefined y x c) \<Longrightarrow> (\<not> y) = x \<longrightarrow> (if c then x else y) = (c = x)"
named_theorems rewrite_ite_then_true \<open>automatically_generated\<close>

lemma [rewrite_ite_then_true]:
  shows "NO_MATCH cvc_a (undefined x c) \<Longrightarrow> (if c then True else x) = (c \<or> x)"
named_theorems rewrite_ite_else_false \<open>automatically_generated\<close>

lemma [rewrite_ite_else_false]:
  shows "NO_MATCH cvc_a (undefined x c) \<Longrightarrow> (if c then x else False) = (c \<and> x)"
named_theorems rewrite_ite_then_false \<open>automatically_generated\<close>

lemma [rewrite_ite_then_false]:
  shows "NO_MATCH cvc_a (undefined x c) \<Longrightarrow> (if c then False else x) = (\<not> c \<and> x)"
named_theorems rewrite_ite_else_true \<open>automatically_generated\<close>

lemma [rewrite_ite_else_true]:
  shows "NO_MATCH cvc_a (undefined x c) \<Longrightarrow> (if c then x else True) = (\<not> c \<or> x)"
named_theorems rewrite_ite_then_lookahead_self \<open>automatically_generated\<close>

lemma [rewrite_ite_then_lookahead_self]:
  shows "NO_MATCH cvc_a (undefined x c) \<Longrightarrow> (if c then c else x) = (if c then True else x)"
named_theorems rewrite_ite_else_lookahead_self \<open>automatically_generated\<close>

lemma [rewrite_ite_else_lookahead_self]:
  shows "NO_MATCH cvc_a (undefined x c) \<Longrightarrow> (if c then x else c) = (if c then x else False)"
