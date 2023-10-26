theory Arith_Rewrites_Autoproven
  imports "HOL-CVC.Dsl_Nary_Ops"
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_arith_int_div_one \<open>automatically_generated\<close>

lemma [rewrite_arith_int_div_one]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> SMT.z3div t (1::int) = t"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_neg_neg_one \<open>automatically_generated\<close>

lemma [rewrite_arith_neg_neg_one]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> - (1::int) * (- (1::int) * t) = t"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_elim_uminus \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_uminus]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> - t = - (1::int) * t"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_elim_minus \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_minus]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> t - s = t + - (1::int) * s"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_elim_gt \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_gt]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (s < t) = (\<not> t \<le> s)"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_elim_lt \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_lt]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t < s) = (\<not> s \<le> t)"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_elim_leq \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_leq]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<le> s) = (t \<le> s)"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_leq_norm \<open>automatically_generated\<close>

lemma [rewrite_arith_leq_norm]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<le> s) = (\<not> s + (1::int) \<le> t)"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_geq_tighten \<open>automatically_generated\<close>

lemma [rewrite_arith_geq_tighten]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (\<not> s \<le> t) = (t + (1::int) \<le> s)"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_geq_norm \<open>automatically_generated\<close>

lemma [rewrite_arith_geq_norm]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (s \<le> t) = ((0::int) \<le> t - s)"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_refl_leq \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_leq]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t \<le> t) = True"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_refl_lt \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_lt]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t < t) = False"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_refl_geq \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_geq]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t \<le> t) = True"
    using cvc_arith_rewrite_defs by auto

named_theorems rewrite_arith_refl_gt \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_gt]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t < t) = False"
  using cvc_arith_rewrite_defs by auto

end