theory String_Rewrites_Autoproven
  imports "HOL-CVC.Dsl_Nary_Ops"
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_str_concat_flatten \<open>automatically_generated\<close>

lemma [rewrite_str_concat_flatten]:
  fixes xs::"char list cvc_ListVar" and s::"char list" and ys::"char list cvc_ListVar" and zs::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right smtlib_str_concat
    (cvc_list_left smtlib_str_concat xs
      (cvc_list_right smtlib_str_concat s ys))
    zs =
   cvc_list_right smtlib_str_concat
    (cvc_list_right smtlib_str_concat (cvc_list_left smtlib_str_concat xs s)
      ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: fold_append_concat_rev foldr_conv_fold smtlib_str_concat_def)
  done


named_theorems rewrite_str_concat_flatten_eq \<open>automatically_generated\<close>

lemma [rewrite_str_concat_flatten_eq]:
  fixes x::"char list" and x1::"char list cvc_ListVar" and x2::"char list cvc_ListVar" and y::"char list"
  shows "NO_MATCH cvc_a (undefined x x1 x2 y) \<Longrightarrow> (cvc_list_right smtlib_str_concat (cvc_list_right smtlib_str_concat x x1)
     x2 =
    y) =
   (y =
    cvc_list_right smtlib_str_concat (cvc_list_right smtlib_str_concat x x1)
     x2)"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2s x1s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by blast
  done


named_theorems rewrite_str_concat_flatten_eq_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_flatten_eq_rev]:
  fixes x::"char list" and x1::"char list cvc_ListVar" and x2::"char list cvc_ListVar" and y::"char list"
  shows "NO_MATCH cvc_a (undefined x x1 x2 y) \<Longrightarrow> (cvc_list_left smtlib_str_concat x2
     (cvc_list_left smtlib_str_concat x1 x) =
    y) =
   (y = smtlib_str_concat (cvc_list_both smtlib_str_concat [] x2 x1) x)"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2s x1s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (metis append.assoc concat_conv_foldr fold_append_concat_rev foldr_conv_fold rev_rev_ident smtlib_str_concat_def)
  done


named_theorems rewrite_str_substr_empty_str \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_str]:
  fixes n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined n m) \<Longrightarrow> smtlib_str_substr (''''::char list) n m = ''''"
  by (simp add: cvc_string_rewrite_defs)


named_theorems rewrite_str_substr_empty_range \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_range]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> m \<le> (0::int) \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
  by (simp add: cvc_string_rewrite_defs)


named_theorems rewrite_str_substr_empty_start \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_start]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> smtlib_str_len x \<le> n \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
  by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_str_substr_empty_start_neg \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_start_neg]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> n < (0::int) \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
  by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_str_substr_eq_empty \<open>automatically_generated\<close>

lemma [rewrite_str_substr_eq_empty]:
  fixes s::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined s n m) \<Longrightarrow> n = (0::int) \<and> n < m \<longrightarrow>
   (smtlib_str_substr s n m = (''''::char list)) = (s = '''')"
  by (simp add: cvc_string_rewrite_defs)
 

named_theorems rewrite_str_len_replace_inv \<open>automatically_generated\<close>

lemma [rewrite_str_len_replace_inv]:
  fixes t::"char list" and s::"char list" and r::"char list"
  shows "NO_MATCH cvc_a (undefined t s r) \<Longrightarrow> smtlib_str_len s = smtlib_str_len r \<longrightarrow>
   smtlib_str_len (smtlib_str_replace t s r) = smtlib_str_len t"
       by (simp add: smtlib_str_replace_def smtlib_str_replace_length_h2)
 

named_theorems rewrite_str_len_update_inv \<open>automatically_generated\<close>

lemma [rewrite_str_len_update_inv]:
  fixes t::"char list" and n::"int" and r::"char list"
  shows "NO_MATCH cvc_a (undefined t n r) \<Longrightarrow> smtlib_str_len (smtlib_str_update t n r) = smtlib_str_len t"
  apply (simp add: cvc_string_rewrite_defs)
  by fastforce


named_theorems rewrite_str_len_substr_in_range \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_in_range]:
  fixes s::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined s n m) \<Longrightarrow> (0::int) \<le> n \<and>
   (0::int) \<le> m \<and> n + m \<le> smtlib_str_len s \<longrightarrow>
   smtlib_str_len (smtlib_str_substr s n m) = m"
  apply (simp add: cvc_string_rewrite_defs)
  by fastforce

named_theorems rewrite_str_len_substr_ub1 \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_ub1]:
  fixes s::"char list" and n::"int" and m::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined s n m k) \<Longrightarrow> (0::int) \<le> k \<and> m \<le> k \<longrightarrow>
   (smtlib_str_len (smtlib_str_substr s n m) \<le> k) = True"
  apply (simp add: cvc_string_rewrite_defs)
  by fastforce 

named_theorems rewrite_str_len_substr_ub2 \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_ub2]:
  fixes s::"char list" and n::"int" and m::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined s n m k) \<Longrightarrow> (0::int) \<le> k \<and> smtlib_str_len s - n \<le> k \<longrightarrow>
   (smtlib_str_len (smtlib_str_substr s n m) \<le> k) = True"
  apply (simp add: cvc_string_rewrite_defs)
  by fastforce 

named_theorems rewrite_re_in_empty \<open>automatically_generated\<close>

lemma [rewrite_re_in_empty]:
  fixes t::"char list"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> smtlib_str_in_re t smtlib_re_none = False"
  by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_re_in_sigma \<open>automatically_generated\<close>

lemma [rewrite_re_in_sigma]:
  fixes t::"char list"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> smtlib_str_in_re t smtlib_re_allchar = (smtlib_str_len t = (1::int))"
  by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_re_in_sigma_star \<open>automatically_generated\<close>

lemma [rewrite_re_in_sigma_star]:
  fixes t::"char list"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> smtlib_str_in_re t (smtlib_re_star smtlib_re_allchar) = True"
   apply (simp add: cvc_string_rewrite_defs)
  using smtlib_re_allchar_def smtlib_re_star_def smtlib_re_star_smtlib_re_allchar by auto

named_theorems rewrite_re_in_cstring \<open>automatically_generated\<close>

lemma [rewrite_re_in_cstring]:
  fixes t::"char list" and s::"char list"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> smtlib_str_in_re t (smtlib_str_to_re s) = (t = s)"
   by (simp add: cvc_string_rewrite_defs)
 

named_theorems rewrite_re_in_comp \<open>automatically_generated\<close>

lemma [rewrite_re_in_comp]:
  fixes t::"char list" and r::"char list set"
  shows "NO_MATCH cvc_a (undefined t r) \<Longrightarrow> smtlib_str_in_re t (smtlib_re_comp r) = (\<not> smtlib_str_in_re t r)"
  by (simp add: cvc_string_rewrite_defs)
 

named_theorems rewrite_str_concat_clash \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 t1 t2) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (cvc_list_right smtlib_str_concat s1 s2 =
    cvc_list_right smtlib_str_concat t1 t2) =
   False"
  apply (cases t2)
  apply (cases s2)
  subgoal for t2s s2s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: cvc_string_rewrite_defs)
  done

named_theorems rewrite_str_prefixof_elim \<open>automatically_generated\<close>

lemma [rewrite_str_prefixof_elim]:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_prefixof s t =
   (s = smtlib_str_substr t (0::int) (smtlib_str_len s))"
  apply (simp add: cvc_string_rewrite_defs)
  by (metis append_eq_conv_conj length_take min.commute prefix_def take_is_prefix)

named_theorems rewrite_str_substr_full \<open>automatically_generated\<close>

lemma [rewrite_str_substr_full]:
  fixes s::"char list" and n::"int"
  shows "NO_MATCH cvc_a (undefined s n) \<Longrightarrow> smtlib_str_len s \<le> n \<longrightarrow>
   smtlib_str_substr s (0::int) n = s"
  apply (simp add: cvc_string_rewrite_defs)
  by (metis dual_order.strict_trans1 length_greater_0_conv of_nat_0_less_iff)

named_theorems rewrite_str_contains_refl \<open>automatically_generated\<close>

lemma [rewrite_str_contains_refl]:
  fixes x::"char list"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> smtlib_str_contains x x = True"
   apply (simp add: cvc_string_rewrite_defs)
  by (metis append.left_neutral append_Nil2)

named_theorems rewrite_str_contains_concat_find \<open>automatically_generated\<close>

lemma [rewrite_str_contains_concat_find]:
  fixes xs::"char list cvc_ListVar" and y::"char list" and zs::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs y zs) \<Longrightarrow> smtlib_str_contains
    (cvc_list_right smtlib_str_concat (cvc_list_left smtlib_str_concat xs y)
      zs)
    y =
   True"
  apply (cases zs)
  apply (cases xs)
  subgoal for zss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (metis append.right_neutral fold_append_concat_rev foldr_conv_fold smtlib_str_concat_def smtlib_str_contains2_def smtlib_str_contains_append smtlib_str_contains_equal)
  done


named_theorems rewrite_str_contains_split_char \<open>automatically_generated\<close>

lemma [rewrite_str_contains_split_char]:
  fixes x::"char list" and y::"char list" and z::"char list cvc_ListVar" and w::"char list"
  shows "NO_MATCH cvc_a (undefined x y z w) \<Longrightarrow> smtlib_str_len w = (1::int) \<longrightarrow>
   smtlib_str_contains
    (cvc_list_right smtlib_str_concat (smtlib_str_concat x y) z) w =
   (smtlib_str_contains x w \<or>
    smtlib_str_contains (cvc_list_right smtlib_str_concat y z) w)"
  apply (cases z)
  subgoal for zs 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: smtlib_str_concat_def smtlib_str_contains_append_Singleton)
  done

named_theorems rewrite_str_at_elim \<open>automatically_generated\<close>

lemma [rewrite_str_at_elim]:
  fixes x::"char list" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> smtlib_str_at x n = smtlib_str_substr x n (1::int)"
  by (simp add: smtlib_str_at_def)

named_theorems rewrite_re_all_elim \<open>automatically_generated\<close>

lemma [rewrite_re_all_elim]:
  shows "NO_MATCH cvc_a (undefined ) \<Longrightarrow> smtlib_re_all = smtlib_re_star smtlib_re_allchar"
  using smtlib_re_all_def by auto

named_theorems rewrite_re_opt_elim \<open>automatically_generated\<close>

lemma [rewrite_re_opt_elim]:
  fixes x::"char list set"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> smtlib_re_opt x = smtlib_re_union (smtlib_str_to_re (''''::char list)) x"
  using smtlib_re_opt_def smtlib_re_union_def by auto

named_theorems rewrite_re_concat_emp \<open>automatically_generated\<close>

lemma [rewrite_re_concat_emp]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_concat
    (cvc_list_left smtlib_re_concat xs (smtlib_str_to_re (''''::char list)))
    ys =
   cvc_list_both smtlib_re_concat ({[]}::char list set) xs ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
   by (metis cvc_ListOp_neutral_re_concat cvc_isListOp.simps smtlib_re_concat_foldr smtlib_str_to_re_def)
  done


named_theorems rewrite_re_concat_none \<open>automatically_generated\<close>

lemma [rewrite_re_concat_none]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_concat
    (cvc_list_left smtlib_re_concat xs smtlib_re_none) ys =
   smtlib_re_none"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (metis emptyE equals0I smtlib_re_concat_foldr smtlib_re_concat_ind.cases smtlib_re_concat_smtlib_re_concat_induct smtlib_re_none_def)
  done


named_theorems rewrite_re_concat_flatten \<open>automatically_generated\<close>

lemma [rewrite_re_concat_flatten]:
  fixes xs::"char list set cvc_ListVar" and s::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right smtlib_re_concat
    (cvc_list_left smtlib_re_concat xs
      (cvc_list_right smtlib_re_concat s ys))
    zs =
   cvc_list_right smtlib_re_concat
    (cvc_list_right smtlib_re_concat (cvc_list_left smtlib_re_concat xs s)
      ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using smtlib_re_concat_foldr by auto
  done

named_theorems rewrite_str_len_concat_rec \<open>automatically_generated\<close>

lemma [rewrite_str_len_concat_rec]:
  fixes s1::"char list" and s2::"char list" and s3::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 s3) \<Longrightarrow> smtlib_str_len
    (cvc_list_right smtlib_str_concat (smtlib_str_concat s1 s2) s3) =
   smtlib_str_len s1 +
   smtlib_str_len (cvc_list_right smtlib_str_concat s2 s3)"
  apply (cases s3)
  subgoal for s3s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by force
  done

end