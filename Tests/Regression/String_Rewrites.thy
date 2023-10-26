theory String_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" String_Rewrites_Lemmas
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_str_eq_ctn_false \<open>automatically_generated\<close>

lemma [rewrite_str_eq_ctn_false]:
  fixes x1::"char list cvc_ListVar" and x::"char list" and x2::"char list cvc_ListVar" and y::"char list"
  shows "NO_MATCH cvc_a (undefined x1 x x2 y) \<Longrightarrow> smtlib_str_contains y x = False \<longrightarrow>
   (cvc_list_right smtlib_str_concat (cvc_list_left smtlib_str_concat x1 x)
     x2 =
    y) =
   False"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2s x1s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using str_eq_ctn_false_lemma by auto
  done


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
    using str_concat_flatten_lemma by auto
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
    using str_concat_flatten_eq_lemma by auto
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
    using str_concat_flatten_eq_rev_lemma by auto
  done


named_theorems rewrite_str_substr_empty_str \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_str]:
  fixes n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined n m) \<Longrightarrow> smtlib_str_substr (''''::char list) n m = ''''"
    using str_substr_empty_str_lemma 
    by auto 

named_theorems rewrite_str_substr_empty_range \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_range]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> m \<le> (0::int) \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
    using str_substr_empty_range_lemma 
    by auto 

named_theorems rewrite_str_substr_empty_start \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_start]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> smtlib_str_len x \<le> n \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
    using str_substr_empty_start_lemma 
    by auto 

named_theorems rewrite_str_substr_empty_start_neg \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_start_neg]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> n < (0::int) \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
    using str_substr_empty_start_neg_lemma 
    by auto 

named_theorems rewrite_str_substr_eq_empty \<open>automatically_generated\<close>

lemma [rewrite_str_substr_eq_empty]:
  fixes s::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined s n m) \<Longrightarrow> n = (0::int) \<and> n < m \<longrightarrow>
   (smtlib_str_substr s n m = (''''::char list)) = (s = '''')"
    using str_substr_eq_empty_lemma 
    by auto 

named_theorems rewrite_str_len_replace_inv \<open>automatically_generated\<close>

lemma [rewrite_str_len_replace_inv]:
  fixes t::"char list" and s::"char list" and r::"char list"
  shows "NO_MATCH cvc_a (undefined t s r) \<Longrightarrow> smtlib_str_len s = smtlib_str_len r \<longrightarrow>
   smtlib_str_len (smtlib_str_replace t s r) = smtlib_str_len t"
    using str_len_replace_inv_lemma 
    by auto 

named_theorems rewrite_str_len_update_inv \<open>automatically_generated\<close>

lemma [rewrite_str_len_update_inv]:
  fixes t::"char list" and n::"int" and r::"char list"
  shows "NO_MATCH cvc_a (undefined t n r) \<Longrightarrow> smtlib_str_len (smtlib_str_update t n r) = smtlib_str_len t"
    using str_len_update_inv_lemma 
    by auto 

named_theorems rewrite_str_len_substr_in_range \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_in_range]:
  fixes s::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined s n m) \<Longrightarrow> (0::int) \<le> n \<and>
   (0::int) \<le> m \<and> n + m \<le> smtlib_str_len s \<longrightarrow>
   smtlib_str_len (smtlib_str_substr s n m) = m"
    using str_len_substr_in_range_lemma 
    by auto 

named_theorems rewrite_str_len_substr_ub1 \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_ub1]:
  fixes s::"char list" and n::"int" and m::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined s n m k) \<Longrightarrow> (0::int) \<le> k \<and> m \<le> k \<longrightarrow>
   (smtlib_str_len (smtlib_str_substr s n m) \<le> k) = True"
    using str_len_substr_ub1_lemma 
    by auto 

named_theorems rewrite_str_len_substr_ub2 \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_ub2]:
  fixes s::"char list" and n::"int" and m::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined s n m k) \<Longrightarrow> (0::int) \<le> k \<and> smtlib_str_len s - n \<le> k \<longrightarrow>
   (smtlib_str_len (smtlib_str_substr s n m) \<le> k) = True"
    using str_len_substr_ub2_lemma 
    by auto 

named_theorems rewrite_re_in_empty \<open>automatically_generated\<close>

lemma [rewrite_re_in_empty]:
  fixes t::"char list"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> smtlib_str_in_re t smtlib_re_none = False"
    using re_in_empty_lemma 
    by auto 

named_theorems rewrite_re_in_sigma \<open>automatically_generated\<close>

lemma [rewrite_re_in_sigma]:
  fixes t::"char list"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> smtlib_str_in_re t smtlib_re_allchar = (smtlib_str_len t = (1::int))"
    using re_in_sigma_lemma 
    by auto 

named_theorems rewrite_re_in_sigma_star \<open>automatically_generated\<close>

lemma [rewrite_re_in_sigma_star]:
  fixes t::"char list"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> smtlib_str_in_re t (smtlib_re_star smtlib_re_allchar) = True"
    using re_in_sigma_star_lemma 
    by auto 

named_theorems rewrite_re_in_cstring \<open>automatically_generated\<close>

lemma [rewrite_re_in_cstring]:
  fixes t::"char list" and s::"char list"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> smtlib_str_in_re t (smtlib_str_to_re s) = (t = s)"
    using re_in_cstring_lemma 
    by auto 

named_theorems rewrite_re_in_comp \<open>automatically_generated\<close>

lemma [rewrite_re_in_comp]:
  fixes t::"char list" and r::"char list set"
  shows "NO_MATCH cvc_a (undefined t r) \<Longrightarrow> smtlib_str_in_re t (smtlib_re_comp r) = (\<not> smtlib_str_in_re t r)"
    using re_in_comp_lemma 
    by auto 

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
    using str_concat_clash_lemma by auto
  done


named_theorems rewrite_str_concat_clash_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash_rev]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 t1 t2) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (cvc_list_left smtlib_str_concat s2 s1 =
    cvc_list_left smtlib_str_concat t2 t1) =
   False"
  apply (cases t2)
  apply (cases s2)
  subgoal for t2s s2s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using str_concat_clash_rev_lemma by auto
  done


named_theorems rewrite_str_concat_clash2 \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash2]:
  fixes s1::"char list" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 t1 t2) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (s1 = cvc_list_right smtlib_str_concat t1 t2) = False"
  apply (cases t2)
  subgoal for t2s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using str_concat_clash2_lemma by auto
  done


named_theorems rewrite_str_concat_clash2_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash2_rev]:
  fixes s1::"char list" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 t1 t2) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (s1 = cvc_list_left smtlib_str_concat t2 t1) = False"
  apply (cases t2)
  subgoal for t2s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using str_concat_clash2_rev_lemma by auto
  done


named_theorems rewrite_str_concat_unify \<open>automatically_generated\<close>

lemma [rewrite_str_concat_unify]:
  fixes s1::"char list" and s2::"char list" and s3::"char list cvc_ListVar" and t2::"char list" and t3::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 s3 t2 t3) \<Longrightarrow> (cvc_list_right smtlib_str_concat (smtlib_str_concat s1 s2) s3 =
    cvc_list_right smtlib_str_concat (smtlib_str_concat s1 t2) t3) =
   (cvc_list_right smtlib_str_concat s2 s3 =
    cvc_list_right smtlib_str_concat t2 t3)"
  apply (cases t3)
  apply (cases s3)
  subgoal for t3s s3s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using str_concat_unify_lemma by auto
  done


named_theorems rewrite_str_concat_unify_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_unify_rev]:
  fixes s1::"char list" and s2::"char list" and s3::"char list cvc_ListVar" and t2::"char list" and t3::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 s3 t2 t3) \<Longrightarrow> (smtlib_str_concat (cvc_list_right smtlib_str_concat s2 s3) s1 =
    smtlib_str_concat (cvc_list_right smtlib_str_concat t2 t3) s1) =
   (cvc_list_right smtlib_str_concat s2 s3 =
    cvc_list_right smtlib_str_concat t2 t3)"
  apply (cases t3)
  apply (cases s3)
  subgoal for t3s s3s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using str_concat_unify_rev_lemma by auto
  done


named_theorems rewrite_str_concat_clash_char \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash_char]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and s3::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar" and t3::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 s3 t1 t2 t3) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (cvc_list_right smtlib_str_concat
     (cvc_list_right smtlib_str_concat s1 s2) s3 =
    cvc_list_right smtlib_str_concat
     (cvc_list_right smtlib_str_concat t1 t2) t3) =
   False"
  apply (cases t3)
  apply (cases t2)
  apply (cases s3)
  apply (cases s2)
  subgoal for t3s t2s s3s s2s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using str_concat_clash_char_lemma by auto
  done


named_theorems rewrite_str_concat_clash_char_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash_char_rev]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and s3::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar" and t3::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 s3 t1 t2 t3) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (cvc_list_left smtlib_str_concat s3
     (cvc_list_left smtlib_str_concat s2 s1) =
    cvc_list_left smtlib_str_concat t3
     (cvc_list_left smtlib_str_concat t2 t1)) =
   False"
  apply (cases t3)
  apply (cases t2)
  apply (cases s3)
  apply (cases s2)
  subgoal for t3s t2s s3s s2s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using str_concat_clash_char_rev_lemma by auto
  done


named_theorems rewrite_str_prefixof_elim \<open>automatically_generated\<close>

lemma [rewrite_str_prefixof_elim]:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_prefixof s t =
   (s = smtlib_str_substr t (0::int) (smtlib_str_len s))"
    using str_prefixof_elim_lemma 
    by auto 

named_theorems rewrite_str_suffixof_elim \<open>automatically_generated\<close>

lemma [rewrite_str_suffixof_elim]:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_suffixof s t =
   (s =
    smtlib_str_substr t (smtlib_str_len t - smtlib_str_len s)
     (smtlib_str_len s))"
    using str_suffixof_elim_lemma 
    by auto 

named_theorems rewrite_str_prefixof_one \<open>automatically_generated\<close>

lemma [rewrite_str_prefixof_one]:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_len t = (1::int) \<longrightarrow>
   smtlib_str_prefixof s t = smtlib_str_contains t s"
    using str_prefixof_one_lemma 
    by auto 

named_theorems rewrite_str_suffixof_one \<open>automatically_generated\<close>

lemma [rewrite_str_suffixof_one]:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_len t = (1::int) \<longrightarrow>
   smtlib_str_suffixof s t = smtlib_str_contains t s"
    using str_suffixof_one_lemma 
    by auto 

named_theorems rewrite_str_substr_combine1 \<open>automatically_generated\<close>

lemma [rewrite_str_substr_combine1]:
  fixes s::"char list" and n1::"int" and m1::"int" and n2::"int" and m2::"int"
  shows "NO_MATCH cvc_a (undefined s n1 m1 n2 m2) \<Longrightarrow> (0::int) \<le> n1 \<and>
   (0::int) \<le> n2 \<and> (0::int) \<le> m2 - (m1 - n2) \<longrightarrow>
   smtlib_str_substr (smtlib_str_substr s n1 m1) n2 m2 =
   smtlib_str_substr s (n1 + n2) (m1 - n2)"
    using str_substr_combine1_lemma 
    by auto 

named_theorems rewrite_str_substr_combine2 \<open>automatically_generated\<close>

lemma [rewrite_str_substr_combine2]:
  fixes s::"char list" and n1::"int" and m1::"int" and n2::"int" and m2::"int"
  shows "NO_MATCH cvc_a (undefined s n1 m1 n2 m2) \<Longrightarrow> (0::int) \<le> n1 \<and>
   (0::int) \<le> n2 \<and> (0::int) \<le> m1 - n2 - m2 \<longrightarrow>
   smtlib_str_substr (smtlib_str_substr s n1 m1) n2 m2 =
   smtlib_str_substr s (n1 + n2) m2"
    using str_substr_combine2_lemma 
    by auto 

named_theorems rewrite_str_substr_concat1 \<open>automatically_generated\<close>

lemma [rewrite_str_substr_concat1]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined s1 s2 n m) \<Longrightarrow> (0::int) \<le> n \<and> n + m \<le> smtlib_str_len s1 \<longrightarrow>
   smtlib_str_substr (cvc_list_right smtlib_str_concat s1 s2) n m =
   smtlib_str_substr s1 n m"
  apply (cases s2)
  subgoal for s2s 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using str_substr_concat1_lemma by auto
  done


named_theorems rewrite_str_substr_full \<open>automatically_generated\<close>

lemma [rewrite_str_substr_full]:
  fixes s::"char list" and n::"int"
  shows "NO_MATCH cvc_a (undefined s n) \<Longrightarrow> smtlib_str_len s \<le> n \<longrightarrow>
   smtlib_str_substr s (0::int) n = s"
    using str_substr_full_lemma 
    by auto 

named_theorems rewrite_str_contains_refl \<open>automatically_generated\<close>

lemma [rewrite_str_contains_refl]:
  fixes x::"char list"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> smtlib_str_contains x x = True"
    using str_contains_refl_lemma 
    by auto 

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
    using str_contains_concat_find_lemma by auto
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
    using str_contains_split_char_lemma by auto
  done


named_theorems rewrite_str_contains_leq_len_eq \<open>automatically_generated\<close>

lemma [rewrite_str_contains_leq_len_eq]:
  fixes x::"char list" and y::"char list"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> smtlib_str_len x \<le> smtlib_str_len y \<longrightarrow>
   smtlib_str_contains x y = (x = y)"
    using str_contains_leq_len_eq_lemma 
    by auto 

named_theorems rewrite_str_concat_emp \<open>automatically_generated\<close>

lemma [rewrite_str_concat_emp]:
  fixes xs::"char list cvc_ListVar" and ys::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_str_concat
    (cvc_list_left smtlib_str_concat xs (''''::char list)) ys =
   cvc_list_both smtlib_str_concat [] xs ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using str_concat_emp_lemma by auto
  done


named_theorems rewrite_str_at_elim \<open>automatically_generated\<close>

lemma [rewrite_str_at_elim]:
  fixes x::"char list" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> smtlib_str_at x n = smtlib_str_substr x n (1::int)"
    using str_at_elim_lemma 
    by auto 

named_theorems rewrite_re_all_elim \<open>automatically_generated\<close>

lemma [rewrite_re_all_elim]:

  shows "NO_MATCH cvc_a (undefined ) \<Longrightarrow> smtlib_re_all = smtlib_re_star smtlib_re_allchar"
    using re_all_elim_lemma 
    by auto 

named_theorems rewrite_re_opt_elim \<open>automatically_generated\<close>

lemma [rewrite_re_opt_elim]:
  fixes x::"char list set"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> smtlib_re_opt x = smtlib_re_union (smtlib_str_to_re (''''::char list)) x"
    using re_opt_elim_lemma 
    by auto 

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
    using re_concat_emp_lemma by auto
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
    using re_concat_none_lemma by auto
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
    using re_concat_flatten_lemma by auto
  done


named_theorems rewrite_re_concat_star_swap \<open>automatically_generated\<close>

lemma [rewrite_re_concat_star_swap]:
  fixes xs::"char list set cvc_ListVar" and r::"char list set" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs r ys) \<Longrightarrow> cvc_list_right smtlib_re_concat
    (smtlib_re_concat (cvc_list_left smtlib_re_concat xs (smtlib_re_star r))
      r)
    ys =
   cvc_list_right smtlib_re_concat
    (smtlib_re_concat (cvc_list_left smtlib_re_concat xs r)
      (smtlib_re_star r))
    ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using re_concat_star_swap_lemma by auto
  done


named_theorems rewrite_re_union_all \<open>automatically_generated\<close>

lemma [rewrite_re_union_all]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_union
    (cvc_list_left smtlib_re_union xs (smtlib_re_star smtlib_re_allchar))
    ys =
   smtlib_re_star smtlib_re_allchar"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using re_union_all_lemma by auto
  done


named_theorems rewrite_re_union_none \<open>automatically_generated\<close>

lemma [rewrite_re_union_none]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_union
    (cvc_list_left smtlib_re_union xs smtlib_re_none) ys =
   cvc_list_both smtlib_re_union ({}::char list set) xs ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using re_union_none_lemma by auto
  done


named_theorems rewrite_re_union_flatten \<open>automatically_generated\<close>

lemma [rewrite_re_union_flatten]:
  fixes xs::"char list set cvc_ListVar" and b::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_right smtlib_re_union
    (cvc_list_left smtlib_re_union xs (cvc_list_right smtlib_re_union b ys))
    zs =
   cvc_list_right smtlib_re_union
    (cvc_list_right smtlib_re_union (cvc_list_left smtlib_re_union xs b) ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using re_union_flatten_lemma by auto
  done


named_theorems rewrite_re_union_dup \<open>automatically_generated\<close>

lemma [rewrite_re_union_dup]:
  fixes xs::"char list set cvc_ListVar" and b::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_right smtlib_re_union
    (smtlib_re_union
      (cvc_list_right smtlib_re_union (cvc_list_left smtlib_re_union xs b)
        ys)
      b)
    zs =
   cvc_list_right smtlib_re_union
    (cvc_list_right smtlib_re_union (cvc_list_left smtlib_re_union xs b) ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using re_union_dup_lemma by auto
  done


named_theorems rewrite_re_inter_all \<open>automatically_generated\<close>

lemma [rewrite_re_inter_all]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_inter
    (cvc_list_left smtlib_re_inter xs (smtlib_re_star smtlib_re_allchar))
    ys =
   cvc_list_both smtlib_re_inter (UNIV::char list set) xs ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using re_inter_all_lemma by auto
  done


named_theorems rewrite_re_inter_none \<open>automatically_generated\<close>

lemma [rewrite_re_inter_none]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_inter
    (cvc_list_left smtlib_re_inter xs smtlib_re_none) ys =
   smtlib_re_none"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using re_inter_none_lemma by auto
  done


named_theorems rewrite_re_inter_flatten \<open>automatically_generated\<close>

lemma [rewrite_re_inter_flatten]:
  fixes xs::"char list set cvc_ListVar" and b::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_right smtlib_re_inter
    (cvc_list_left smtlib_re_inter xs (cvc_list_right smtlib_re_inter b ys))
    zs =
   cvc_list_right smtlib_re_inter
    (cvc_list_right smtlib_re_inter (cvc_list_left smtlib_re_inter xs b) ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using re_inter_flatten_lemma by auto
  done


named_theorems rewrite_re_inter_dup \<open>automatically_generated\<close>

lemma [rewrite_re_inter_dup]:
  fixes xs::"char list set cvc_ListVar" and b::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_right smtlib_re_inter
    (smtlib_re_inter
      (cvc_list_right smtlib_re_inter (cvc_list_left smtlib_re_inter xs b)
        ys)
      b)
    zs =
   cvc_list_right smtlib_re_inter
    (cvc_list_right smtlib_re_inter (cvc_list_left smtlib_re_inter xs b) ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using re_inter_dup_lemma by auto
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
    using str_len_concat_rec_lemma by auto
  done


named_theorems rewrite_str_in_re_range_elim \<open>automatically_generated\<close>

lemma [rewrite_str_in_re_range_elim]:
  fixes s::"char list" and c1::"char list" and c2::"char list"
  shows "NO_MATCH cvc_a (undefined s c1 c2) \<Longrightarrow> smtlib_str_len c1 = (1::int) \<and>
   smtlib_str_len c2 = (1::int) \<longrightarrow>
   smtlib_str_in_re s (smtlib_re_range c1 c2) =
   (smtlib_str_to_code c1 \<le> smtlib_str_to_code s \<and>
    smtlib_str_to_code s \<le> smtlib_str_to_code c2)"
    using str_in_re_range_elim_lemma 
    by auto 
end