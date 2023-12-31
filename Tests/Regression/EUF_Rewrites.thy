theory EUF_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" Boolean_Rewrites_Lemmas
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_bool_double_not_elim \<open>automatically_generated\<close>

lemma [rewrite_bool_double_not_elim]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (\<not> \<not> t) = t"
  by auto


named_theorems rewrite_bool_eq_true \<open>automatically_generated\<close>

lemma [rewrite_bool_eq_true]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = True) = t"
  by auto


named_theorems rewrite_bool_eq_false \<open>automatically_generated\<close>

lemma [rewrite_bool_eq_false]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = False) = (\<not> t)"
  by auto


named_theorems rewrite_bool_eq_nrefl \<open>automatically_generated\<close>

lemma [rewrite_bool_eq_nrefl]:
  fixes x::"bool"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x = (\<not> x)) = False"
  by auto


named_theorems rewrite_bool_impl_false1 \<open>automatically_generated\<close>

lemma [rewrite_bool_impl_false1]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t \<longrightarrow> False) = (\<not> t)"
  by auto


named_theorems rewrite_bool_impl_false2 \<open>automatically_generated\<close>

lemma [rewrite_bool_impl_false2]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (False \<longrightarrow> t) = True"
  by auto


named_theorems rewrite_bool_impl_true1 \<open>automatically_generated\<close>

lemma [rewrite_bool_impl_true1]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t \<longrightarrow> True) = True"
  by auto


named_theorems rewrite_bool_impl_true2 \<open>automatically_generated\<close>

lemma [rewrite_bool_impl_true2]:
  fixes t::"bool"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (True \<longrightarrow> t) = t"
  by auto


named_theorems rewrite_bool_impl_elim \<open>automatically_generated\<close>

lemma [rewrite_bool_impl_elim]:
  fixes t::"bool" and s::"bool"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<longrightarrow> s) = (\<not> t \<or> s)"
  by auto


named_theorems rewrite_bool_or_true \<open>automatically_generated\<close>

lemma [rewrite_bool_or_true]:
  fixes xs::"bool cvc_ListVar" and ys::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_left (\<or>) xs (cvc_list_right (\<or>) True ys) = True"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: bool_or_true_lemma)
  done


named_theorems rewrite_bool_or_false \<open>automatically_generated\<close>

lemma [rewrite_bool_or_false]:
  fixes xs::"bool cvc_ListVar" and ys::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_left (\<or>) xs (cvc_list_right (\<or>) False ys) =
   cvc_list_both (\<or>) False xs ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: bool_or_false_lemma)
  done


named_theorems rewrite_bool_or_flatten \<open>automatically_generated\<close>

lemma [rewrite_bool_or_flatten]:
  fixes xs::"bool cvc_ListVar" and b::"bool" and ys::"bool cvc_ListVar" and zs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_left (\<or>) xs
    (cvc_list_right (\<or>) (cvc_list_right (\<or>) b ys) zs) =
   cvc_list_left (\<or>) xs (b \<or> cvc_list_both (\<or>) False ys zs)"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: bool_or_flatten_lemma)
  done


named_theorems rewrite_bool_or_dup \<open>automatically_generated\<close>

lemma [rewrite_bool_or_dup]:
  fixes xs::"bool cvc_ListVar" and b::"bool" and ys::"bool cvc_ListVar" and zs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_left (\<or>) xs
    (b \<or> cvc_list_left (\<or>) ys (cvc_list_right (\<or>) b zs)) =
   cvc_list_left (\<or>) xs (b \<or> cvc_list_both (\<or>) False ys zs)"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: bool_or_dup_lemma)
  done


named_theorems rewrite_bool_and_true \<open>automatically_generated\<close>

lemma [rewrite_bool_and_true]:
  fixes xs::"bool cvc_ListVar" and ys::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_left (\<and>) xs (cvc_list_right (\<and>) True ys) =
   cvc_list_both (\<and>) True xs ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: bool_and_true_lemma)
  done


named_theorems rewrite_bool_and_false \<open>automatically_generated\<close>

lemma [rewrite_bool_and_false]:
  fixes xs::"bool cvc_ListVar" and ys::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_left (\<and>) xs (cvc_list_right (\<and>) False ys) = False"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: bool_and_false_lemma)
  done


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


named_theorems rewrite_bool_and_dup \<open>automatically_generated\<close>

lemma [rewrite_bool_and_dup]:
  fixes xs::"bool cvc_ListVar" and b::"bool" and ys::"bool cvc_ListVar" and zs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_left (\<and>) xs
    (b \<and> cvc_list_left (\<and>) ys (cvc_list_right (\<and>) b zs)) =
   cvc_list_left (\<and>) xs (b \<and> cvc_list_both (\<and>) True ys zs)"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: bool_and_dup_lemma)
  done


named_theorems rewrite_bool_and_conf \<open>automatically_generated\<close>

lemma [rewrite_bool_and_conf]:
  fixes xs::"bool cvc_ListVar" and w::"bool" and ys::"bool cvc_ListVar" and zs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs w ys zs) \<Longrightarrow> cvc_list_left (\<and>) xs
    (w \<and>
     cvc_list_left (\<and>) ys (cvc_list_right (\<and>) (\<not> w) zs)) =
   False"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: bool_and_conf_lemma)
  done


named_theorems rewrite_bool_or_taut \<open>automatically_generated\<close>

lemma [rewrite_bool_or_taut]:
  fixes xs::"bool cvc_ListVar" and w::"bool" and ys::"bool cvc_ListVar" and zs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs w ys zs) \<Longrightarrow> cvc_list_left (\<or>) xs
    (w \<or>
     cvc_list_left (\<or>) ys (cvc_list_right (\<or>) (\<not> w) zs)) =
   True"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp_all only: bool_or_taut_lemma)
  done


named_theorems rewrite_bool_xor_refl \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_refl]:
  fixes x::"bool"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<noteq> x) = False"
  by auto


named_theorems rewrite_bool_xor_nrefl \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_nrefl]:
  fixes x::"bool"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<noteq> (\<not> x)) = True"
  by auto


named_theorems rewrite_bool_xor_false \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_false]:
  fixes x::"bool"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<noteq> False) = x"
  by auto


named_theorems rewrite_bool_xor_true \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_true]:
  fixes x::"bool"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<noteq> True) = (\<not> x)"
  by auto


named_theorems rewrite_bool_xor_comm \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_comm]:
  fixes x::"bool" and y::"bool"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<noteq> y) = (y \<noteq> x)"
  by auto


named_theorems rewrite_bool_xor_elim \<open>automatically_generated\<close>

lemma [rewrite_bool_xor_elim]:
  fixes x::"bool" and y::"bool"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<noteq> y) = (x \<noteq> y)"
  by auto


named_theorems rewrite_ite_neg_branch \<open>automatically_generated\<close>

lemma [rewrite_ite_neg_branch]:
  fixes c::"bool" and x::"bool" and y::"bool"
  shows "NO_MATCH cvc_a (undefined c x y) \<Longrightarrow> (\<not> y) = x \<longrightarrow> (if c then x else y) = (c = x)"
  by auto


named_theorems rewrite_ite_then_true \<open>automatically_generated\<close>

lemma [rewrite_ite_then_true]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then True else x) = (c \<or> x)"
  by auto


named_theorems rewrite_ite_else_false \<open>automatically_generated\<close>

lemma [rewrite_ite_else_false]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then x else False) = (c \<and> x)"
  by auto


named_theorems rewrite_ite_then_false \<open>automatically_generated\<close>

lemma [rewrite_ite_then_false]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then False else x) = (\<not> c \<and> x)"
  by auto


named_theorems rewrite_ite_else_true \<open>automatically_generated\<close>

lemma [rewrite_ite_else_true]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then x else True) = (\<not> c \<or> x)"
  by auto


named_theorems rewrite_ite_then_lookahead_self \<open>automatically_generated\<close>

lemma [rewrite_ite_then_lookahead_self]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then c else x) = (if c then True else x)"
  by auto


named_theorems rewrite_ite_else_lookahead_self \<open>automatically_generated\<close>

lemma [rewrite_ite_else_lookahead_self]:
  fixes c::"bool" and x::"bool"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then x else c) = (if c then x else False)"
  by auto


named_theorems rewrite_ite_true_cond \<open>automatically_generated\<close>

lemma [rewrite_ite_true_cond]:
  fixes x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (if True then x else y) = x"
  by auto


named_theorems rewrite_ite_false_cond \<open>automatically_generated\<close>

lemma [rewrite_ite_false_cond]:
  fixes x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (if False then x else y) = y"
  by auto


named_theorems rewrite_ite_not_cond \<open>automatically_generated\<close>

lemma [rewrite_ite_not_cond]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y) \<Longrightarrow> (if \<not> c then x else y) = (if c then y else x)"
  by auto


named_theorems rewrite_ite_eq_branch \<open>automatically_generated\<close>

lemma [rewrite_ite_eq_branch]:
  fixes c::"bool" and x::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then x else x) = x"
  by auto


named_theorems rewrite_ite_then_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_then_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then if c then x else y else z) = (if c then x else z)"
  by auto


named_theorems rewrite_ite_else_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_else_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then x else if c then y else z) = (if c then x else z)"
  by auto


named_theorems rewrite_ite_then_neg_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_then_neg_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then if \<not> c then x else y else z) = (if c then y else z)"
  by auto


named_theorems rewrite_ite_else_neg_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_else_neg_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then x else if \<not> c then y else z) = (if c then x else y)"
  by auto


named_theorems rewrite_eq_refl \<open>automatically_generated\<close>

lemma [rewrite_eq_refl]:
  fixes t::"'a::type"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = t) = True"
  by auto


named_theorems rewrite_eq_symm \<open>automatically_generated\<close>

lemma [rewrite_eq_symm]:
  fixes t::"'a::type" and s::"'a::type"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t = s) = (s = t)"
  by auto


named_theorems rewrite_distinct_binary_elim \<open>automatically_generated\<close>

lemma [rewrite_distinct_binary_elim]:
  fixes t::"'a::type" and s::"'a::type"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<noteq> s) = (t \<noteq> s)"
  by auto

end