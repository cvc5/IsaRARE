theory Mixed_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" 
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_bool_double_not_elim \<open>automatically_generated\<close>

lemma [rewrite_bool_double_not_elim]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (\<not> \<not> t) = t"
  by auto


named_theorems rewrite_bool_and_flatten \<open>automatically_generated\<close>

lemma [rewrite_bool_and_flatten]:
  fixes xs::"bool cvc_ListVar" and b::"bool" and ys::"bool cvc_ListVar" and zs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_left (\<and>) xs
    (cvc_list_right (\<and>) (cvc_list_right (\<and>) b ys) zs) =
   cvc_list_left (\<and>) xs (b \<and> cvc_list_both (\<and>) True ys zs)"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: bool_and_flatten_lemma)
  done


named_theorems rewrite_ite_then_false \<open>automatically_generated\<close>

lemma [rewrite_ite_then_false]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then False else x) = (\<not> c \<and> x)"
  by auto


named_theorems rewrite_arith_geq_tighten \<open>automatically_generated\<close>

lemma [rewrite_arith_geq_tighten]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (\<not> s \<le> t) = (t + (1::int) \<le> s)"
  by auto


named_theorems rewrite_arith_elim_uminus \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_uminus]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> - t = - (1::int) * t"
  by auto


named_theorems rewrite_arith_plus_cancel1 \<open>automatically_generated\<close>

lemma [rewrite_arith_plus_cancel1]:
  fixes t::"int cvc_ListVar" and x::"int" and s::"int cvc_ListVar" and r::"int cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined t x s r) \<Longrightarrow> cvc_list_right (+)
    (cvc_list_right (+) (cvc_list_left (+) t x) s + - (1::int) * x) r =
   cvc_list_right (+) (cvc_list_both (+) (0::int) t s) r"
  apply (cases r)
  apply (cases s)
  apply (cases t)
  subgoal for rs ss ts 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: arith_plus_cancel1_lemma)
  done


named_theorems rewrite_ite_then_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_then_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then if c then x else y else z) = (if c then x else z)"
  by auto


named_theorems rewrite_eq_refl \<open>automatically_generated\<close>

lemma [rewrite_eq_refl]:
  fixes t::"'a::type"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = t) = True"
  by auto


named_theorems rewrite_sets_inter_member \<open>automatically_generated\<close>

lemma [rewrite_sets_inter_member]:
  fixes x::"'a::type" and y::"'a::type set" and z::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y z) \<Longrightarrow> (x \<in> y \<inter> z) = (x \<in> y \<and> x \<in> z)"
  by auto


named_theorems rewrite_sets_member_singleton \<open>automatically_generated\<close>

lemma [rewrite_sets_member_singleton]:
  fixes x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<in> {y}) = (x = y)"
  by auto


named_theorems rewrite_array_read_over_write2 \<open>automatically_generated\<close>

lemma [rewrite_array_read_over_write2]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type" and j::"'a::type" and e::"'b::type option"
  shows "NO_MATCH cvc_a (undefined t i j e) \<Longrightarrow> i \<noteq> j \<longrightarrow> (t(i := e)) j = t j"
  by auto

end