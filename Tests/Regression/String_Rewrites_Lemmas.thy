theory String_Rewrites_Lemmas
  imports "HOL.Dsl_Nary_Ops" 
begin

lemma str_eq_ctn_false_lemma:
  shows "smtlib_str_contains y x = False \<longrightarrow> (smtlib_str_concat (foldr smtlib_str_concat x1s x) (foldr smtlib_str_concat x2s []) = y) = False"
    apply (simp_all add: cvc_string_rewrite_defs)
      apply (simp_all add: cvc_rewrites_fold)
  by auto

lemma str_concat_flatten_lemma:
  shows "smtlib_str_concat (foldr smtlib_str_concat xss (smtlib_str_concat s (foldr smtlib_str_concat yss []))) (foldr smtlib_str_concat zss []) =
    smtlib_str_concat (smtlib_str_concat (foldr smtlib_str_concat xss s) (foldr smtlib_str_concat yss [])) (foldr smtlib_str_concat zss [])"
  by (simp add: fold_append_concat_rev foldr_conv_fold smtlib_str_concat_def)


lemma str_concat_flatten_eq_lemma:
  shows " (smtlib_str_concat (smtlib_str_concat x (foldr smtlib_str_concat x1s [])) (foldr smtlib_str_concat x2s []) = y) =
    (y = smtlib_str_concat (smtlib_str_concat x (foldr smtlib_str_concat x1s [])) (foldr smtlib_str_concat x2s []))"
  by blast


lemma str_concat_flatten_eq_rev_lemma:
  shows "(foldr smtlib_str_concat x2s (foldr smtlib_str_concat x1s x) = y) = (y = smtlib_str_concat (foldr smtlib_str_concat x2s (foldr smtlib_str_concat x1s [])) x)"
  by (metis append.right_neutral fold_append_concat_rev foldr_append foldr_conv_fold smtlib_str_concat_def)


lemma str_substr_empty_str_lemma:
  fixes n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined n m) \<Longrightarrow> smtlib_str_substr (''''::char list) n m = ''''"
    by (simp add: cvc_string_rewrite_defs)

lemma str_substr_empty_range_lemma:
  fixes x::"char list" and n::"int" and m::"int"
  shows "m \<le> (0::int) \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
    by (simp add: cvc_string_rewrite_defs)

lemma str_substr_empty_start_lemma:
  fixes x::"char list" and n::"int" and m::"int"
  shows "smtlib_str_len x \<le> n \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
    by (simp add: cvc_string_rewrite_defs)

lemma str_substr_empty_start_neg_lemma:
  fixes x::"char list" and n::"int" and m::"int"
  shows "n < (0::int) \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
    by (simp add: cvc_string_rewrite_defs)

lemma str_substr_eq_empty_lemma:
  fixes s::"char list" and n::"int" and m::"int"
  shows "n = (0::int) \<and> n < m \<longrightarrow>
   (smtlib_str_substr s n m = (''''::char list)) = (s = '''')"
    by (simp add: cvc_string_rewrite_defs)

lemma str_len_replace_inv_lemma:
  fixes t::"char list" and s::"char list" and r::"char list"
  shows "smtlib_str_len s = smtlib_str_len r \<longrightarrow>
   smtlib_str_len (smtlib_str_replace t s r) = smtlib_str_len t"
  using smtlib_str_len_def smtlib_str_replace_def smtlib_str_replace_length by presburger

lemma str_len_update_inv_lemma:
  fixes t::"char list" and n::"int" and r::"char list"
  shows "smtlib_str_len (smtlib_str_update t n r) = smtlib_str_len t"
  apply (simp add: cvc_string_rewrite_defs)
  by auto

lemma str_len_substr_in_range_lemma:
  fixes s::"char list" and n::"int" and m::"int"
  shows "(0::int) \<le> n \<and>
   (0::int) \<le> m \<and> n + m \<le> smtlib_str_len s \<longrightarrow>
   smtlib_str_len (smtlib_str_substr s n m) = m"
  apply (simp add: cvc_string_rewrite_defs)
  by auto

lemma str_len_substr_ub1_lemma:
  fixes s::"char list" and n::"int" and m::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined s n m k) \<Longrightarrow> (0::int) \<le> k \<and> m \<le> k \<longrightarrow>
   (smtlib_str_len (smtlib_str_substr s n m) \<le> k) = True"
  apply (simp add: cvc_string_rewrite_defs)
  by auto

lemma str_len_substr_ub2_lemma:
  fixes s::"char list" and n::"int" and m::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined s n m k) \<Longrightarrow> (0::int) \<le> k \<and> smtlib_str_len s - n \<le> k \<longrightarrow>
   (smtlib_str_len (smtlib_str_substr s n m) \<le> k) = True"
  apply (simp add: cvc_string_rewrite_defs)
  by auto

lemma re_in_empty_lemma:
  fixes t::"char list"
  shows "smtlib_str_in_re t smtlib_re_none = False"
    by (simp add: cvc_string_rewrite_defs)

lemma re_in_sigma_lemma:
  fixes t::"char list"
  shows "smtlib_str_in_re t smtlib_re_allchar = (smtlib_str_len t = (1::int))"
    by (simp add: cvc_string_rewrite_defs)

lemma re_in_sigma_star_lemma:
  fixes t::"char list"
  shows "smtlib_str_in_re t (smtlib_re_star smtlib_re_allchar) = True"
  by (simp add: smtlib_str_in_re_def)

lemma re_in_cstring_lemma:
  fixes t::"char list" and s::"char list"
  shows "smtlib_str_in_re t (smtlib_str_to_re s) = (t = s)"
    by (simp add: cvc_string_rewrite_defs)

lemma re_in_comp_lemma:
  fixes t::"char list" and r::"char list set"
  shows "smtlib_str_in_re t (smtlib_re_comp r) = (\<not> smtlib_str_in_re t r)"
    by (simp add: cvc_string_rewrite_defs)

lemma str_concat_clash_lemma:
" s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
    (smtlib_str_concat s1 (foldr smtlib_str_concat s2s []) = smtlib_str_concat t1 (foldr smtlib_str_concat t2s [])) = False"
  by (simp add: smtlib_str_concat_def smtlib_str_len_def)

lemma str_concat_clash_rev_lemma:
" s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow> (foldr smtlib_str_concat s2s s1 = foldr smtlib_str_concat t2s t1) = False"
  by (metis append_eq_append_conv nat_int smtlib_str_concat_def smtlib_str_len_def str_concat_flatten_eq_rev_lemma)

lemma str_concat_clash2_lemma:
"s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow> (s1 = smtlib_str_concat t1 (foldr smtlib_str_concat t2s [])) = False"
  using smtlib_str_concat_def smtlib_str_len_def by fastforce

lemma str_concat_clash2_rev_lemma:
"s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow> (s1 = foldr smtlib_str_concat t2s t1) = False"
  by (metis foldr_append str_concat_clash_rev_lemma)

lemma str_concat_unify_lemma:
"(smtlib_str_concat (smtlib_str_concat s1 s2) (foldr smtlib_str_concat s3s []) =
     smtlib_str_concat (smtlib_str_concat s1 t2) (foldr smtlib_str_concat t3s [])) =
    (smtlib_str_concat s2 (foldr smtlib_str_concat s3s []) = smtlib_str_concat t2 (foldr smtlib_str_concat t3s []))"
  by (simp add: smtlib_str_concat_def)

lemma str_concat_unify_rev_lemma:
"(smtlib_str_concat (smtlib_str_concat s2 (foldr smtlib_str_concat s3s [])) s1 =
     smtlib_str_concat (smtlib_str_concat t2 (foldr smtlib_str_concat t3s [])) s1) =
    (smtlib_str_concat s2 (foldr smtlib_str_concat s3s []) = smtlib_str_concat t2 (foldr smtlib_str_concat t3s []))"
  by (simp add: smtlib_str_concat_def)

lemma str_concat_clash_char_lemma:
" s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
    (smtlib_str_concat (smtlib_str_concat s1 (foldr smtlib_str_concat s2s [])) (foldr smtlib_str_concat s3s []) =
     smtlib_str_concat (smtlib_str_concat t1 (foldr smtlib_str_concat t2s [])) (foldr smtlib_str_concat t3s [])) =
    False"
  using smtlib_str_concat_def smtlib_str_len_def by auto

lemma str_concat_clash_char_rev_lemma:
" s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
    (foldr smtlib_str_concat s3s (foldr smtlib_str_concat s2s s1) = foldr smtlib_str_concat t3s (foldr smtlib_str_concat t2s t1)) = False"
  by (metis foldr_append str_concat_clash_rev_lemma)

lemma rewrite_str_prefixof_elim_lemma:
  fixes s::"char list" and t::"char list"
  shows "smtlib_str_prefixof s t =
   (s = smtlib_str_substr t (0::int) (smtlib_str_len s))"
  unfolding smtlib_str_prefixof_def smtlib_str_substr_def smtlib_str_len_def
  apply simp
  by (metis append_eq_conv_conj min_def prefixE prefix_length_le take_is_prefix)

lemma str_prefixof_elim_lemma:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_prefixof s t =
   (s = smtlib_str_substr t (0::int) (smtlib_str_len s))"
   by (simp add: rewrite_str_prefixof_elim_lemma)

lemma str_suffixof_elim_lemma_h1:
"(length s \<le> length t \<and> s \<noteq> [] \<longrightarrow>
     suffix s t = (s = drop (nat (int (length t) - int (length s))) t)) \<and>
    ((length s \<le> length t \<longrightarrow> s = []) \<longrightarrow> suffix s t = (s = []))"
    apply (cases "length s \<le> length t \<and> s \<noteq> [] ")
     apply simp_all
  apply (metis (no_types, lifting) append_eq_append_conv diff_diff_cancel length_drop nat_diff_distrib' nat_int of_nat_0_le_iff suffix_def suffix_drop)
  using suffix_bot.bot_least suffix_length_le by blast

lemma str_suffixof_elim_lemma:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_suffixof s t =
   (s =
    smtlib_str_substr t (smtlib_str_len t - smtlib_str_len s)
     (smtlib_str_len s))"
  by (simp add: smtlib_str_len_def smtlib_str_substr_def smtlib_str_suffixof_def str_suffixof_elim_lemma_h1)

lemma str_prefixof_one_lemma_h1:
" int (length t) = 1 \<Longrightarrow>  prefix s t = (\<exists>w1 w3. t = w1 @ s @ w3)"
  apply (cases "length s = 1")
   apply simp_all
  apply (metis (no_types, lifting) add_is_1 append_eq_append_conv2 append_self_conv2 length_append length_greater_0_conv prefix_def)
  by (metis add_is_1 append_self_conv2 length_append length_greater_0_conv prefix_append prefix_def)

lemma str_suffixof_one_lemma_h1:
"  int (length t) = 1 \<Longrightarrow> suffix s t = (\<exists>w1 w3. t = w1 @ s @ w3)"
  apply (cases "length s = 1")
   apply simp_all
  apply (metis Nil_is_append_conv add_is_1 append.right_neutral length_append length_greater_0_conv suffix_def)
  by (metis Nil_is_append_conv add_is_1 append_Nil2 length_0_conv length_append suffixE suffixI)


lemma str_prefixof_one_lemma:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_len t = (1::int) \<longrightarrow>
   smtlib_str_prefixof s t = smtlib_str_contains t s"
  by (simp add: smtlib_str_contains2_def smtlib_str_contains_equal smtlib_str_len_def smtlib_str_prefixof_def str_prefixof_one_lemma_h1)


lemma str_suffixof_one_lemma:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_len t = (1::int) \<longrightarrow>
   smtlib_str_suffixof s t = smtlib_str_contains t s"
   by (simp add: smtlib_str_contains2_def smtlib_str_contains_equal smtlib_str_len_def smtlib_str_suffixof_def str_suffixof_one_lemma_h1)


lemma str_substr_combine1_lemma:
  fixes s::"char list" and n1::"int" and m1::"int" and n2::"int" and m2::"int"
  shows "NO_MATCH cvc_a (undefined s n1 m1 n2 m2) \<Longrightarrow> (0::int) \<le> n1 \<and>
   (0::int) \<le> n2 \<and> (0::int) \<le> m2 - (m1 - n2) \<longrightarrow>
   smtlib_str_substr (smtlib_str_substr s n1 m1) n2 m2 =
   smtlib_str_substr s (n1 + n2) (m1 - n2)"
unfolding smtlib_str_substr_def[of s n1 m1]
  apply (cases "n1 < int (length s)")
   apply simp_all
   apply (cases "0 < m1 ")
    apply simp_all
  unfolding smtlib_str_substr_def[of "[]"]
    apply simp_all
  unfolding smtlib_str_substr_def[of s "(n1 + n2)" "(m1 - n2)"]
    apply simp_all
  apply (cases "n1 + n2 < int (length s)")
   apply simp_all
  apply (cases "n2 < m1")
    apply simp_all
    apply (cases "(nat m1)\<le> (length s - nat n1)")  
     apply simp_all
     apply (cases "(nat (m1 - n2)) \<le> (length s - nat (n1 + n2))")
      apply simp_all
  unfolding  smtlib_str_substr_def[of "(take (nat m1) (drop (nat n1) s))" n2 m2]
      apply simp
  apply (smt (verit, ccfv_threshold) add_diff_cancel_left' drop_drop drop_take le_add_diff_inverse2 min_absorb2 nat_diff_distrib' nat_mono take_take)
    using nat_int_comparison(3) apply force
    apply (smt (verit, ccfv_SIG) \<open>smtlib_str_substr (take (nat m1) (drop (nat n1) s)) n2 m2 \<equiv> if 0 \<le> n2 \<and> n2 < int (length (take (nat m1) (drop (nat n1) s))) \<and> 0 < m2 then take (min (nat m2) (length (take (nat m1) (drop (nat n1) s)) - nat n2)) (drop (nat n2) (take (nat m1) (drop (nat n1) s))) else []\<close> add_diff_cancel_left' drop_drop drop_take le_add_diff_inverse2 le_diff_iff length_drop min_absorb2 nat_diff_distrib' nat_le_linear nat_less_iff nat_mono order_less_le take_all_iff take_take)
    apply (simp add: \<open>smtlib_str_substr (take (nat m1) (drop (nat n1) s)) n2 m2 \<equiv> if 0 \<le> n2 \<and> n2 < int (length (take (nat m1) (drop (nat n1) s))) \<and> 0 < m2 then take (min (nat m2) (length (take (nat m1) (drop (nat n1) s)) - nat n2)) (drop (nat n2) (take (nat m1) (drop (nat n1) s))) else []\<close> nat_le_iff of_nat_diff)
    by (simp add: int_ops(6) of_nat_min smtlib_str_substr_def)


lemma str_substr_combine2_lemma:
  fixes s::"char list" and n1::"int" and m1::"int" and n2::"int" and m2::"int"
  shows "NO_MATCH cvc_a (undefined s n1 m1 n2 m2) \<Longrightarrow> (0::int) \<le> n1 \<and>
   (0::int) \<le> n2 \<and> (0::int) \<le> m1 - n2 - m2 \<longrightarrow>
   smtlib_str_substr (smtlib_str_substr s n1 m1) n2 m2 =
   smtlib_str_substr s (n1 + n2) m2"
  unfolding smtlib_str_substr_def[of s n1 m1] apply simp
  apply (cases "n1 < int (length s)")
  apply simp_all
  unfolding smtlib_str_substr_def[of "[]"]
    apply simp_all
   apply (cases "0 < m1 ")
  apply simp_all
  unfolding smtlib_str_substr_def[of s "n1+n2" m2] apply simp
  apply (cases "(nat m1) \<le> (length s - nat n1)")
     apply simp_all
   apply (cases "n1 + n2 < int (length s) ")
    apply simp_all
  apply (cases "0 < m2")
     apply simp_all
  unfolding smtlib_str_substr_def[of "(take (nat m1) (drop (nat n1) s))" n2 m2]
     apply simp
  apply (smt (verit, del_insts) drop_drop drop_take min_absorb1 nat_0_le nat_add_distrib nat_diff_distrib' nat_int_comparison(3) take_take)
  apply presburger
  using int_ops(6) nat_le_iff apply force
  by (smt (verit) drop_drop length_drop nat_add_distrib nat_less_iff smtlib_str_substr_def zero_less_diff)

lemma str_substr_concat1_lemma:
 "0 \<le> n \<and> n + m \<le> smtlib_str_len s1 \<Longrightarrow> smtlib_str_substr (smtlib_str_concat s1 (foldr smtlib_str_concat s2 [])) n m = smtlib_str_substr s1 n m"
  unfolding smtlib_str_substr_def smtlib_str_concat_def
  apply (induction s2)
   apply simp
  by (simp add: nat_le_iff of_nat_diff smtlib_str_len_def)

lemma str_contains_split_char_lemma:
"smtlib_str_len w = 1 \<Longrightarrow> smtlib_str_contains (smtlib_str_concat (smtlib_str_concat x y) (foldr smtlib_str_concat z [])) w =
    (smtlib_str_contains x w \<or> smtlib_str_contains (smtlib_str_concat y (foldr smtlib_str_concat z [])) w)"
  apply (induction z)
   apply simp_all
   apply (simp add: smtlib_str_concat_def)
  apply (simp add: smtlib_str_contains_append_Singleton)
  by (simp add: smtlib_str_concat_def smtlib_str_contains_append_Singleton)

lemma str_len_concat_rec_lemma:
" smtlib_str_len (smtlib_str_concat (smtlib_str_concat s1 s2) (foldr smtlib_str_concat s3s [])) =
    smtlib_str_len s1 + smtlib_str_len (smtlib_str_concat s2 (foldr smtlib_str_concat s3s []))"
  apply (induction s3s)
  by simp_all

lemma str_substr_full_lemma:
  fixes s::"char list" and n::"int"
  shows "NO_MATCH cvc_a (undefined s n) \<Longrightarrow> smtlib_str_len s \<le> n \<longrightarrow>
   smtlib_str_substr s (0::int) n = s"
  apply (simp add: cvc_string_rewrite_defs)
  using order_le_less by fastforce

lemma str_contains_refl_lemma:
  fixes x::"char list"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> smtlib_str_contains x x = True"
  apply (simp add: cvc_string_rewrite_defs)
  by (metis append.left_neutral append_Nil2)

lemma str_contains_concat_find_lemma:
  shows "smtlib_str_contains (smtlib_str_concat (foldr smtlib_str_concat xss y) (foldr smtlib_str_concat zss [])) y = True"
  apply (induction zss)
    apply simp_all
    apply (induction xss)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
      apply (simp_all add: cvc_rewrites_fold)
      apply (metis append.left_neutral append_Nil2)
    apply (metis append.assoc)
    by blast

lemma str_contains_leq_len_eq_lemma:
  fixes x::"char list" and y::"char list"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> smtlib_str_len x \<le> smtlib_str_len y \<longrightarrow>
   smtlib_str_contains x y = (x = y)"
  apply (induction x)
  using smtlib_str_contains2_def smtlib_str_contains_equal apply force
  using smtlib_str_contains_def smtlib_str_len_def by force

lemma str_concat_emp_lemma:
  "smtlib_str_concat (foldr smtlib_str_concat xs []) (foldr smtlib_str_concat ys []) = foldr smtlib_str_concat xs (foldr smtlib_str_concat ys [])"
  apply (induction xs)
  apply (induction ys)
  apply (simp add: smtlib_str_concat_def)
   apply (simp add: smtlib_str_concat_def)
  apply (induction ys)
  apply (simp add: smtlib_str_concat_def)
  by (simp add: smtlib_str_concat_def)

lemma rewrite_str_at_elim_lemma:
  fixes x::"char list" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> smtlib_str_at x n = smtlib_str_substr x n (1::int)"
      by (simp add: cvc_string_rewrite_defs)

lemma re_all_elim_lemma:
  shows "NO_MATCH cvc_a (undefined ) \<Longrightarrow> smtlib_re_all = smtlib_re_star smtlib_re_allchar"
  by (simp add: smtlib_re_all_def)

lemma re_opt_elim_lemma:
  fixes x::"char list set"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> smtlib_re_opt x = smtlib_re_union (smtlib_str_to_re (''''::char list)) x"
  using smtlib_re_opt_def smtlib_re_union_def by auto

value " cvc_list_both smtlib_re_concat {} (ListVar []) (ListVar [])"
value "smtlib_re_concat (foldr smtlib_re_concat [] (smtlib_str_to_re [])) (foldr smtlib_re_concat [] {[]})"
value "(foldr smtlib_re_concat [] (smtlib_str_to_re []))"
value "(smtlib_str_to_re [])"


lemma re_concat_none_lemma:
  shows " smtlib_re_concat (foldr smtlib_re_concat xss smtlib_re_none) (foldr smtlib_re_concat yss {[]}) = smtlib_re_none"
    by (metis cvc_ListVar.exhaust cvc_bin_op2.simps cvc_list_left_transfer cvc_list_right_def ex_in_conv smtlib_re_concat_foldr smtlib_re_concat_ind.cases smtlib_re_concat_smtlib_re_concat_induct smtlib_re_none_def)

lemma str_at_elim_lemma:
  fixes x::"char list" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> smtlib_str_at x n = smtlib_str_substr x n (1::int)"
  by (simp add: cvc_string_rewrite_defs)

lemma re_concat_flatten_lemma:
  fixes xs::"char list set cvc_ListVar" and s::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "smtlib_re_concat (foldr smtlib_re_concat xss (smtlib_re_concat s (foldr smtlib_re_concat yss {[]}))) (foldr smtlib_re_concat zss {[]}) =
    smtlib_re_concat (smtlib_re_concat (foldr smtlib_re_concat xss s) (foldr smtlib_re_concat yss {[]})) (foldr smtlib_re_concat zss {[]})"
  using smtlib_re_concat_foldr by simp

lemma re_concat_star_swap_lemma:
"    smtlib_re_concat
     (smtlib_re_concat (foldr smtlib_re_concat xs (smtlib_re_star r)) r)
     (foldr smtlib_re_concat ys {[]}) =
    smtlib_re_concat
     (smtlib_re_concat (foldr smtlib_re_concat xs r) (smtlib_re_star r))
     (foldr smtlib_re_concat ys {[]})"
  apply (rule HOL.arg_cong[of "(smtlib_re_concat (foldr smtlib_re_concat xs (smtlib_re_star r)) r)"])
  by (metis re_concat_star_swap smtlib_re_concat_foldr smtlib_re_star_def)

lemma substr_concat1_lemma:
 "0 \<le> n \<and> n + m \<le> smtlib_str_len s1 \<Longrightarrow> smtlib_str_substr (smtlib_str_concat s1 (foldr smtlib_str_concat s2 [])) n m = smtlib_str_substr s1 n m"
  unfolding smtlib_str_substr_def smtlib_str_concat_def
  apply (induction s2)
   apply simp
  by (simp add: nat_le_iff of_nat_diff smtlib_str_len_def)

lemma concat_clash2_rev_lemma:
"s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<Longrightarrow> s1 \<noteq> foldr smtlib_str_concat t2 t1"
  unfolding smtlib_str_len_def smtlib_str_concat_def
  apply (induction t2)
   apply simp_all
  by (metis (mono_tags, opaque_lifting) append_eq_append_conv cvc_list_left_Cons cvc_list_left_transfer fold_append_concat_rev foldr_conv_fold)

lemma re_concat_emp_lemma:
"smtlib_re_concat (foldr smtlib_re_concat xss (smtlib_str_to_re [])) (foldr smtlib_re_concat yss {[]}) =
    foldr smtlib_re_concat xss (foldr smtlib_re_concat yss {[]})"
  by (metis cvc_ListOp_neutral_re_concat cvc_isListOp.simps smtlib_re_concat_foldr smtlib_str_to_re_empty)

lemma re_union_all_lemma:
  "smtlib_re_union (foldr smtlib_re_union xss (smtlib_re_star smtlib_re_allchar)) (foldr smtlib_re_union yss {}) = smtlib_re_star smtlib_re_allchar"
  apply simp
  apply (induction yss)
    apply simp_all
        apply (induction xss)
    apply simp_all
    apply (simp add: smtlib_re_union_def)
  apply (metis UNIV_eq_I Un_def Un_insert_right insertI1 insert_UNIV smtlib_re_union_def sup_bot.right_neutral)
  by (metis Un_def Un_insert_right insertI1 insert_UNIV set_eqI smtlib_re_union_def sup_aci(3))

lemma re_union_none_lemma:
"smtlib_re_union (foldr smtlib_re_union xss smtlib_re_none) (foldr smtlib_re_union yss {}) =
    foldr smtlib_re_union xss (foldr smtlib_re_union yss {})"
  apply (induction xss)
   apply (simp add: smtlib_re_none_def smtlib_re_union_def)
  apply (induction yss)
   apply simp_all
   apply (simp add: smtlib_re_union_def)
  using smtlib_re_union_def by auto

lemma re_union_flatten_lemma:
" smtlib_re_union (foldr smtlib_re_union xss (smtlib_re_union b (foldr smtlib_re_union yss {}))) (foldr smtlib_re_union zss {}) =
    smtlib_re_union (smtlib_re_union (foldr smtlib_re_union xss b) (foldr smtlib_re_union yss {})) (foldr smtlib_re_union zss {})"
      apply (induction xss)
   apply simp_all
      apply (induction yss)
     apply simp_all
    using cvc_ListOp_neutral_re_union apply force
    apply (induction zss)
     apply (simp add: smtlib_re_union_def)
    using smtlib_re_union_def by auto

lemma re_union_dup_lemma:
"smtlib_re_union (smtlib_re_union (smtlib_re_union (foldr smtlib_re_union xss b) (foldr smtlib_re_union yss {})) b) (foldr smtlib_re_union zss {}) =
    smtlib_re_union (smtlib_re_union (foldr smtlib_re_union xss b) (foldr smtlib_re_union yss {})) (foldr smtlib_re_union zss {})"
    apply (induction zss)
     apply simp_all
      apply (induction yss)
      apply simp_all
        apply (induction xss)
      apply simp_all
    apply (simp add: smtlib_re_union_def)
  using smtlib_re_union_def apply auto[1]
  apply (metis (no_types, lifting) foldr_cong mem_Collect_eq)
  using smtlib_re_union_def apply auto[1]
  apply (metis (no_types, lifting) foldr_cong mem_Collect_eq)
  using smtlib_re_union_def  
  by (metis (full_types) Un_assoc Un_commute Un_def)

lemma rewrite_re_inter_all_h1: "smtlib_re_inter (foldr smtlib_re_inter xss UNIV) A = foldr smtlib_re_inter xss A"
  apply (induction xss)
  apply (simp add: smtlib_re_inter_def)
  apply simp
  by (smt (verit, ccfv_SIG) Collect_cong mem_Collect_eq smtlib_re_inter_def)

lemma re_inter_all_lemma:
  shows " smtlib_re_inter (foldr smtlib_re_inter xss (smtlib_re_star smtlib_re_allchar)) (foldr smtlib_re_inter yss UNIV) =
    foldr smtlib_re_inter xss (foldr smtlib_re_inter yss UNIV)"
     using rewrite_re_inter_all_h1 by auto

lemma re_inter_none_lemma:
  shows "smtlib_re_inter (foldr smtlib_re_inter xss smtlib_re_none) (foldr smtlib_re_inter yss UNIV) = smtlib_re_none"
  by (metis Int_commute Int_def inf_bot_right rewrite_re_inter_all_h1 smtlib_re_inter_def smtlib_re_none_def)

lemma re_inter_flatten_lemma:
" smtlib_re_inter (foldr smtlib_re_inter xss (smtlib_re_inter b (foldr smtlib_re_inter yss UNIV))) (foldr smtlib_re_inter zss UNIV) =
    smtlib_re_inter (smtlib_re_inter (foldr smtlib_re_inter xss b) (foldr smtlib_re_inter yss UNIV)) (foldr smtlib_re_inter zss UNIV)"
  by (smt (verit, ccfv_threshold) Int_def Int_left_commute inf_commute rewrite_re_inter_all_h1 smtlib_re_inter_def)

lemma re_inter_dup_lemma:
"smtlib_re_inter (smtlib_re_inter (smtlib_re_inter (foldr smtlib_re_inter xss b) (foldr smtlib_re_inter yss UNIV)) b) (foldr smtlib_re_inter zss UNIV) =
    smtlib_re_inter (smtlib_re_inter (foldr smtlib_re_inter xss b) (foldr smtlib_re_inter yss UNIV)) (foldr smtlib_re_inter zss UNIV)"
    apply (induction xss )
   apply simp_all
      apply (induction yss )
      apply simp_all
        apply (induction zss )
      apply simp_all
    apply (simp add: smtlib_re_inter_def)
  using smtlib_re_inter_def apply auto[1]
  using smtlib_re_inter_def apply auto[1]
  by (smt (verit, ccfv_threshold) Int_commute Int_def Int_left_commute smtlib_re_inter_def)


lemma h1: "(of_char c1::int) \<ge> -1"
  unfolding of_char_def by simp

lemma h2: "(of_char c1::int) > -1"
  unfolding of_char_def by simp


lemma str_in_re_range_elim_lemma:
  fixes s::"char list" and c1::"char list" and c2::"char list"
  shows "smtlib_str_len c1 = (1::int) \<Longrightarrow>
   smtlib_str_len c2 = (1::int) \<Longrightarrow>
   smtlib_str_in_re s (smtlib_re_range c1 c2) =
   (smtlib_str_to_code c1 \<le> smtlib_str_to_code s \<and>
    smtlib_str_to_code s \<le> smtlib_str_to_code c2)"
  apply (rule iffI)
  unfolding smtlib_str_to_code_def smtlib_str_len_def
  apply simp
  unfolding smtlib_str_in_re_def smtlib_re_range_def smtlib_str_leq_def smtlib_str_less_def
  apply simp
  apply (case_tac [!] "length s")
   apply simp_all
   apply (case_tac [!] c2)
     apply simp_all
   apply (case_tac [!] c1)
   apply simp_all
  using order_le_less string_comp.elims(2) apply fastforce
  subgoal for c2' c2s c1'
    apply (cases "c2' = CHR 0x00")
     apply simp_all
    apply (cases "c1' = CHR 0x00")
      apply (simp_all add: h1)
    using h2 linorder_not_le apply blast
    using h2 linorder_not_le by blast
  by (smt (verit, ccfv_SIG) h2 Suc_length_conv char_of_char length_greater_0_conv list.size(3) nth_Cons_0 string_comp.simps(3))

  
end