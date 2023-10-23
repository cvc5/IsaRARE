theory Bitvector_Rewrites2
  imports "HOL-CVC.BV_Rewrites_Lemmas" HOL.SMT "Word_Lib.Signed_Division_Word" "Word_Lib.Reversed_Bit_Lists"
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

declare[[show_types,show_sorts]]

named_theorems rewrite_bv_concat_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_flatten]:
  fixes xs::"bool list cvc_ListVar" and s::"'a::len word" and ys::"bool list cvc_ListVar" and zs::"bool list cvc_ListVar"
  shows "(NO_MATCH cvc_a (undefined xs s ys zs::'k)::bool) \<Longrightarrow> 
 (size (x_c7::'b::len word)) =
    (size (s::'a::len word)) +  (size (x_c6::'c::len word)) \<and>
   x_c7 = word_cat s x_c6 \<and>
   x_c6 = word_cat (x_c1::'d::len word) (x_c3::'e::len word) \<and>
    (size x_c6) =  (size x_c1) +  (size x_c3) \<and>
   (x_c8::'f::len word) = word_cat (x_c0::'g::len word) x_c7 \<and>
    (size x_c8) =  (size x_c0) +  (size x_c7) \<and>
   x_c0 = concat_smt2 xs \<and>
   (0::int) < int (size xs) \<and>
   list_length_0' xs \<and>
   int (size xs) = temp_sum_length xs \<and>
    (size (x_c4::'h::len word)) =
    (size (x_c2::'i::len word)) +  (size x_c3) \<and>
   x_c4 = word_cat x_c2 x_c3 \<and>
   int (size zs) = temp_sum_length zs \<and>
   list_length_0' zs \<and>
   (0::int) < int (size zs) \<and>
   x_c3 = concat_smt2 zs \<and>
    (size x_c2) =  (size s) +  (size x_c1) \<and>
   x_c2 = word_cat s x_c1 \<and>
   int (size ys) = temp_sum_length ys \<and>
   list_length_0' ys \<and>
   (0::int) < int (size ys) \<and>
   x_c1 = concat_smt2 ys \<and>
   (x_c5::'f::len word) = word_cat x_c0 x_c4 \<and>
    (size x_c5) =  (size x_c0) +  (size x_c4) \<longrightarrow>
   x_c5 = x_c8"
 apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply rule+
   apply (elim conjE)
    subgoal premises p
      unfolding p(26) p(8)
      apply (subst arg_cong[of x_c4 "ucast x_c7" "\<lambda>k. word_cat x_c0 k"])
      subgoal
        unfolding p(15) p(21)
        unfolding p(5) p(6)
           apply (simp only: word_unat_eq_iff)
        apply (subst unat_word_cat)
        apply (metis p(14) size_word.rep_eq)
        apply (subst unat_word_cat)
         apply (metis p size_word.rep_eq)
        apply (subst unat_ucast_upcast)
        using p 
        apply (metis add_diff_cancel_left' dual_order.refl is_up.rep_eq size_word.rep_eq)
        apply (subst unat_word_cat)
         apply (metis p size_word.rep_eq)
        apply (subst unat_word_cat)
         apply (metis p size_word.rep_eq)
        by (smt (verit) add.commute group_cancel.add1 p(7) push_bit_add push_bit_push_bit word_size)
      subgoal
      apply (simp only: word_unat_eq_iff)
        apply (subst unat_word_cat)
        apply (metis p(14,27) size_word.rep_eq)
        apply (subst unat_word_cat)
         apply (metis p(4,7,9,27) size_word.rep_eq)
        apply (subst unat_ucast_upcast)
        apply (metis p(9,14,27) add_diff_cancel_left' is_up.rep_eq le_refl size_word.rep_eq)
        by (metis add.commute add_diff_cancel_right' p(27) p(9) word_size)
      done
    done
  done

lemma word_cat_comm:
 "LENGTH('a) = size t2 + size t3 \<Longrightarrow> 
          LENGTH('b) = size t1 + LENGTH('a) \<Longrightarrow> 
          LENGTH('c) = size t1 + size t2 \<Longrightarrow> 
          LENGTH('b) = size t3 + LENGTH('c) \<Longrightarrow> 
(word_cat t1 (word_cat t2 t3::'a:: len word)::'b::len word) = (word_cat (word_cat t1 t2::'c::len word) t3::'b::len word)"
         apply (simp only: word_unat_eq_iff)
  apply (subst unat_word_cat)
  apply (simp add: word_size)
  apply (subst unat_word_cat)
  apply (simp add: word_size)
  apply (subst unat_word_cat)
   apply (simp add: word_size)
  apply (subst unat_word_cat)
   apply (simp add: word_size)
  by (simp add: add.commute push_bit_add size_word.rep_eq)

named_theorems rewrite_bv_concat_extract_merge \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_extract_merge]:
  fixes xs::"bool list cvc_ListVar" and s::"'a::len word" and ys::"bool list cvc_ListVar" and i::"int" and j::"int" and j1::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined xs s ys i j j1 k) \<Longrightarrow> int (size (x_c8::'b::len word)) =
   int (size (x_c7::'c::len word)) +
   int (size (x_c3::'d::len word)) \<and>
   x_c8 = word_cat x_c7 x_c3 \<and>
   i \<le> k \<and>
   int (size x_c7) = (1::int) + (k - i) \<and>
   x_c7 = smt_extract (nat k) (nat i) s \<and>
   (x_c9::'e::len word) = word_cat (x_c0::'f::len word) x_c8 \<and>
   int (size x_c9) = int (size x_c0) + int (size x_c8) \<and>
   x_c0 = concat_smt2 xs \<and>
   (0::int) < int (size xs) \<and>
   list_length_0' xs \<and>
   int (size xs) = temp_sum_length xs \<and>
   int (size (x_c5::'g::len word)) =
   int (size (x_c1::'h::len word)) +
   int (size (x_c4::'i::len word)) \<and>
   x_c5 = word_cat x_c1 x_c4 \<and>
   j < int (size s) \<and>
   (x_c2::'j::len word) = smt_extract (nat j) (nat i) s \<and>
   int (size x_c2) = (1::int) + (j - i) \<and>
   i \<le> j \<and>
   (0::int) \<le> i \<and>
   x_c3 = concat_smt2 ys \<and>
   (0::int) < int (size ys) \<and>
   list_length_0' ys \<and>
   int (size ys) = temp_sum_length ys \<and>
   x_c4 = word_cat x_c2 x_c3 \<and>
   int (size x_c4) = int (size x_c2) + int (size x_c3) \<and>
   (0::int) \<le> j1 \<and>
   j1 \<le> k \<and>
   int (size x_c1) = (1::int) + (k - j1) \<and>
   x_c1 = smt_extract (nat k) (nat j1) s \<and>
   k < int (size s) \<and>
   (x_c6::'e::len word) = word_cat x_c0 x_c5 \<and>
   int (size x_c6) = int (size x_c0) + int (size x_c5) \<longrightarrow>
   j1 = j + (1::int) \<longrightarrow> x_c6 = x_c9"
 apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply rule+
   apply (elim conjE)
    subgoal premises p
      unfolding p(10)
      unfolding p(34)
      apply (subst arg_cong[of x_c5 "ucast x_c8" "\<lambda>k. word_cat x_c0 k"])
      subgoal
        unfolding p(17)
        unfolding p(27)
        unfolding p(32)
        unfolding p(9)
        unfolding p(19)
        unfolding p(4)
        unfolding p(6)
        unfolding p(9)
           apply (simp only: word_unat_eq_iff)
        apply (subst unat_word_cat)
        apply (metis p nat_int.Rep_inverse' nat_plus_as_int size_word.rep_eq)
        apply (subst unat_word_cat)
        apply (metis p nat_int.Rep_inverse' nat_plus_as_int size_word.rep_eq)
        apply (subst unat_ucast_upcast)
        using p 
        apply (smt (verit, ccfv_SIG) is_up.rep_eq nat_int_comparison(3) size_word.rep_eq)
        apply (subst unat_word_cat)
        apply (metis p nat_int.Rep_inverse' nat_plus_as_int size_word.rep_eq)
        apply (subst unat_smt_extract)
        using p nat_mono apply presburger
        using p zless_nat_eq_int_zless apply linarith
        using p apply (metis Suc_diff_le Suc_eq_plus1 Suc_nat_eq_nat_zadd1 diff_ge_0_iff_ge nat_diff_distrib nat_int nat_mono word_size)
        apply (subst unat_smt_extract)
        using p nat_mono apply presburger
        using p zless_nat_eq_int_zless apply linarith
        using p apply (metis Suc_diff_le Suc_eq_plus1 Suc_nat_eq_nat_zadd1 diff_ge_0_iff_ge nat_diff_distrib nat_int nat_mono word_size)
        apply (subst unat_smt_extract)
        using p nat_mono apply presburger
        using p zless_nat_eq_int_zless apply linarith
        using p apply (metis Suc_diff_le Suc_eq_plus1 Suc_nat_eq_nat_zadd1 diff_ge_0_iff_ge nat_diff_distrib nat_int nat_mono word_size)
        apply (simp add: push_bit_drop_bit)

        using word_cat_comm[of ]
        using word_cat_smt_extract[of "nat i" "nat j" "nat k" s]
        using p 
      subgoal
        apply (simp only:word_unat_eq_iff)
        apply (subst unat_word_cat)
        using p
         apply (metis nat_int.Rep_inverse' nat_plus_as_int size_word.rep_eq)
        apply (subst unat_word_cat)
        using p 
        apply (metis int_int_eq int_ops(5) word_size)
        apply (subst unat_ucast_upcast)
        using p 
        apply (smt (verit, best) is_up.rep_eq nat_int_comparison(3) size_word.rep_eq)
        by (metis diff_add_inverse nat_int of_nat_add p(11) p(35) word_size)


      done


        apply (simp add: arg_cong[of "(ucast (x_c8::'b word))::'b word" "x_c8::'b word" "\<lambda>k. word_cat x_c0 (k::'b word)"])
        unfolding p(6)
apply (subst arg_cong)
        unfolding p(12)
      
      apply (subst arg_cong)
      using p(12)
      unfolding p(1-10)
  proof-
    assume a0: " NO_MATCH cvc_a (undefined xs s ys i j j1 k)"
    "ys = ListVar yss"
    "xs = ListVar xss"
    "int (size x_c8) = int (size x_c7) + int (size x_c3) \<and>
    x_c8 = word_cat x_c7 x_c3 \<and>
    i \<le> k \<and>
    int (size x_c7) = (1::int) + (k - i) \<and>
    x_c7 = smt_extract (nat k) (nat i) s \<and>
    x_c9 = word_cat x_c0 x_c8 \<and>
    int (size x_c9) = int (size x_c0) + int (size x_c8) \<and>
    x_c0 = concat_smt2 xs \<and>
    (0::int) < int (size xs) \<and>
    list_length_0' xs \<and>
    int (size xs) = temp_sum_length xs \<and>
    int (size x_c5) = int (size x_c1) + int (size x_c4) \<and>
    x_c5 = word_cat x_c1 x_c4 \<and>
    j < int (size s) \<and>
    x_c2 = smt_extract (nat j) (nat i) s \<and>
    int (size x_c2) = (1::int) + (j - i) \<and>
    i \<le> j \<and>
    (0::int) \<le> i \<and>
    x_c3 = concat_smt2 ys \<and>
    (0::int) < int (size ys) \<and>
    list_length_0' ys \<and>
    int (size ys) = temp_sum_length ys \<and>
    x_c4 = word_cat x_c2 x_c3 \<and>
    int (size x_c4) = int (size x_c2) + int (size x_c3) \<and>
    (0::int) \<le> j1 \<and>
    j1 \<le> k \<and>
    int (size x_c1) = (1::int) + (k - j1) \<and>
    x_c1 = smt_extract (nat k) (nat j1) s \<and> k < int (size s) \<and> x_c6 = word_cat x_c0 x_c5 \<and> int (size x_c6) = int (size x_c0) + int (size x_c5)"
    "j1 = j + (1::int)"
    have t0: "x_c6 = word_cat x_c0 x_c5 "
      using a0 by simp
    have t0_a: "x_c5 = word_cat x_c1 x_c4"
      using a0 by simp
    have t0_b: "x_c8 = word_cat x_c7 x_c3"
      using a0 by simp

    have t1: " x_c9 = word_cat x_c0 x_c8"
      using a0 by simp
    have t2: "x_c7 = smt_extract (nat k) (nat i) s"
      using a0 by simp
    have t2_a: "x_c1 = smt_extract (nat k) (nat j1) s"
      using a0 by simp
    have t2_b: "x_c4 = word_cat x_c2 x_c3"
      using a0 by simp
    have t2_c: "x_c2 = smt_extract (nat j) (nat i) s"
      using a0 by simp


    have u1: "unat x_c8 = push_bit LENGTH('d) (drop_bit (nat i) (take_bit (Suc (nat k)) (unat s))) + unat x_c3 "
      unfolding t0_b
      apply (subst unat_word_cat)
       apply (metis a0(4) nat_int of_nat_add word_size)
      unfolding t2
      apply (subst unat_smt_extract)
      apply (simp add: a0(4) nat_mono)
      using a0(4) apply linarith
       apply (metis Suc_diff_le Suc_eq_plus1 Suc_nat_eq_nat_zadd1 a0(4) diff_ge_0_iff_ge nat_diff_distrib nat_int nat_mono word_size)
      by simp

 

    have u2: "unat x_c5 = push_bit LENGTH('i) (drop_bit (nat j1) (take_bit (Suc (nat k)) (unat s))) +
    (push_bit LENGTH('d) (drop_bit (nat i) (take_bit (Suc (nat j)) (unat s))) + unat x_c3)"
      unfolding t0_a t0_b
      apply (subst unat_word_cat)
       apply (metis a0(4) nat_int nat_int_add size_word.rep_eq)
      unfolding t2_a
      apply (subst unat_smt_extract)
      using a0(4) nat_mono apply blast
      apply (metis a0(4) nat_eq_iff2 nat_less_iff word_size_gt_0)
       apply (metis Suc_diff_le Suc_eq_plus1 Suc_nat_eq_nat_zadd1 a0(4) diff_ge_0_iff_ge nat_diff_distrib nat_int nat_mono word_size)
      unfolding t2_b
      apply (subst unat_word_cat)
      apply (metis a0(4) nat_int.Rep_inverse' nat_plus_as_int size_word.rep_eq)
      unfolding t2_c    
      apply (subst unat_smt_extract)
      using a0(4) nat_mono apply blast
      apply (metis a0(4) nat_eq_iff2 nat_less_iff word_size_gt_0)
      apply (metis Suc_eq_plus1 Suc_nat_eq_nat_zadd1 a0(4) a0(5) add.commute add_diff_eq nat_diff_distrib' nat_int order_trans word_size)
      by simp

 
      



    have t2: "x_c5 = smt_extract (nat k) (nat i) x_c3"
      unfolding t0_a t2_a t2_b t2_c
      apply (subst word_cat_comm)
      prefer 5
      using word_cat_smt_extract[of "nat i" "nat j" "nat k" x_c3]

    show "x_c6 = x_c9"
      unfolding t0 t1 




     apply (simp del: concat_smt2.simps)
      apply (simp only: word_unat_eq_iff)
    apply (subst unat_word_cat)
    apply (simp add: word_size)
    apply (subst  unat_word_cat)
     apply (simp add: word_size)
    apply (subst unat_word_cat)
     apply (simp add: word_size)
    apply (subst unat_word_cat)
     apply (simp add: word_size)
    apply (subst unat_word_cat)
     apply (simp add: word_size)
    apply (subst unat_smt_extract)
    using nat_mono apply blast
    apply linarith
    apply (smt (verit, del_insts) add.commute nat_0_le nat_int nat_minus_as_int of_nat_Suc plus_1_eq_Suc word_size)
    apply (subst unat_smt_extract)
    using nat_mono apply presburger
    apply (metis bot_nat_0.not_eq_extremum int_eq_iff int_ops(1) less_nat_zero_code zle_add1_eq_le zless_nat_eq_int_zless)
  apply (metis Suc_diff_le Suc_eq_plus1 Suc_nat_eq_nat_zadd1 diff_ge_0_iff_ge int_eq_iff nat_diff_distrib nat_mono word_size)
    apply (subst unat_smt_extract)
   using nat_mono apply blast
    apply linarith
    apply (smt (verit, del_insts) add.commute nat_0_le nat_int nat_minus_as_int of_nat_Suc plus_1_eq_Suc word_size)
   
   apply (simp add: drop_bit_take_bit del: concat_smt2.simps)
   sledgehammer
*)
  sorry

named_theorems rewrite_bv_extract_extract \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_extract]:
  fixes x::"'a::len word" and i::"int" and j::"int" and k::"int" and l::"int"
  shows "NO_MATCH cvc_a (undefined x i j k l) \<Longrightarrow> i + l < int (size x) \<and>
   (x_c2::'b::len word) = smt_extract (nat (i + l)) (nat (i + k)) x \<and>
   int (size x_c2) = (1::int) + (i + l - (i + k)) \<and>
   i + k \<le> i + l \<and>
   (0::int) \<le> i + k \<and>
   l < int (size (x_c0::'c::len word)) \<and>
   (x_c1::'b::len word) = smt_extract (nat l) (nat k) x_c0 \<and>
   int (size x_c1) = (1::int) + (l - k) \<and>
   k \<le> l \<and>
   (0::int) \<le> k \<and>
   j < int (size x) \<and>
   x_c0 = smt_extract (nat j) (nat i) x \<and>
   int (size x_c0) = (1::int) + (j - i) \<and>
   i \<le> j \<and> (0::int) \<le> i \<longrightarrow>
   x_c1 = x_c2"
  apply (rule impI)
  apply simp
  apply (simp only: word_unat_eq_iff)
  apply (subst unat_smt_extract[of "nat k" "nat l" "(smt_extract (nat j) (nat i) x::'c::len word)"])
     apply (simp_all add: nat_mono)
  using nat_less_iff apply auto[1]
  apply (metis Suc_diff_le Suc_eq_plus1 Suc_nat_eq_nat_zadd1 diff_ge_0_iff_ge int_eq_iff nat_diff_distrib nat_mono word_size)
  apply (subst unat_smt_extract[of "nat i" "nat j" x])
     apply (simp_all add: nat_mono)
    apply (metis len_gt_0 nat_int word_size zless_nat_conj)
  apply (metis Suc_diff_le Suc_pred' add_diff_cancel_left' int_ops(2) nat_diff_distrib nat_minus_as_int nat_mono word_size word_size_gt_0)
  apply (subst unat_smt_extract[of "nat (i+k)" "nat (i+l)" x])
     apply (simp_all add: nat_mono)
  apply (metis nat_eq_iff2 nat_less_iff word_size_gt_0)
  apply (metis Suc_diff_le Suc_nat_eq_nat_zadd1 add_diff_cancel_left add_left_mono add_less_same_cancel1 gr0_conv_Suc int_ops(1) len_gt_0 linorder_not_less nat_diff_distrib nat_int.Rep_inverse nat_mono not_less_zero of_nat_Suc of_nat_less_imp_less size_word.rep_eq)
  apply (simp add: take_bit_drop_bit)
  apply (simp add: nat_add_distrib add.commute)
  by (simp add: nat_le_eq_zle nat_plus_as_int)

named_theorems rewrite_bv_extract_whole \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_whole]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> n < int (size x) \<and>
   (x_c0::'a::len word) = smt_extract (nat n) 0 x \<and>
   int (size x_c0) = (1::int) + (n - (0::int)) \<and>
   (0::int) \<le> n \<and> (0::int) \<le> (0::int) \<longrightarrow>
   int (size x) - (1::int) \<le> n \<longrightarrow> x_c0 = x"
  apply (rule impI)+
  apply simp
  apply (cases "n = int (size x)")
   apply (simp add: size_word.rep_eq slice_id smt_extract_def take_bit_word_eq_self)
  apply (simp only: word_unat_eq_iff)
  apply (subst unat_smt_extract)
     apply simp_all
  using nat_less_iff apply blast
  apply (metis Suc_nat_eq_nat_zadd1 nat_int word_size)
  by (metis Suc_nat_eq_nat_zadd1 nat_int take_bit_length_eq unsigned_take_bit_eq word_size)

named_theorems rewrite_bv_ugt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_eliminate]:
  fixes x::"'a::ord" and y::"'a::ord"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y < x) = (y < x)"
  by auto


named_theorems rewrite_bv_uge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_uge_eliminate]:
  fixes x::"'a::ord" and y::"'a::ord"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y \<le> x) = (y \<le> x)"
  by auto


named_theorems rewrite_bv_sgt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sgt_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y <s x) = (y <s x)"
  by auto


named_theorems rewrite_bv_sge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sge_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y \<le>s x) = (y \<le>s x)"
  by auto

named_theorems rewrite_bv_sle_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<le>s y) = (\<not> y <s x)"
  by auto

named_theorems rewrite_bv_redor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redor_eliminate]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> smt_redor x = not (smt_comp x (Word.Word (0::int)))"
  unfolding smt_redor_def by auto


named_theorems rewrite_bv_redand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redand_eliminate]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> smt_redand x = (smt_comp x (not (Word.Word (0::int))))"
  unfolding smt_redand_def smt_comp_def
  by simp

named_theorems rewrite_bv_ule_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<le> y) = (\<not> y < x)"
  by auto


named_theorems rewrite_bv_comp_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_comp_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> smt_comp x y = (if x = y then Word.Word (1::int) else Word.Word (0::int))"
  unfolding smt_comp_def by auto


named_theorems rewrite_bv_repeat_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_1]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c2::'b::len word) = word_cat x (x_c1::'c::len word) \<and>
   int (size x_c2) = int (size x) + int (size x_c1) \<and>
   x_c1 = smt_repeat (nat (n - (1::int))) x \<and>
   int (size x_c1) = int (size x) * (n - (1::int)) \<and>
   (0::int) \<le> n - (1::int) \<and>
   (x_c0::'b::len word) = smt_repeat (nat n) x \<and>
   int (size x_c0) = int (size x) * n \<and>
   (0::int) \<le> n \<longrightarrow>
   (1::int) < n \<longrightarrow> x_c0 = x_c2"
apply (rule impI)+
  apply simp
proof- 
  assume a0: "(x_c2::'b::len word) = word_cat x x_c1 \<and>
    int (size x_c2) = int (size x) + int (size x_c1) \<and>
    (x_c1::'c::len word) = smt_repeat (nat (n - (1::int))) x \<and>
    int (size x_c1) = int (size x) * (n - (1::int)) \<and>
   (x_c0::'b::len word) = smt_repeat (nat n) x
 \<and> int (size x_c0) = int (size x) * n" 
  assume a1: "(1::int) < n"
  have a00: "1 < n" "LENGTH('c) = (n-1) * LENGTH('a)" "LENGTH('b) = n * LENGTH('a)"
    apply (metis a0 add_cancel_left_right int_one_le_iff_zero_less len_not_eq_0 linorder_le_less_linear mult.right_neutral mult_nonneg_nonpos nle_le of_nat_le_0_iff size_word.rep_eq)
    apply (metis a0 mult.commute size_word.rep_eq)
    by (metis a0 mult.commute size_word.rep_eq)

  have t0: "LENGTH('c::len) = (nat n - (1::nat)) * size (x::'a::len word)"
    apply (simp add: a00)
     by (metis One_nat_def a00 int_one_le_iff_zero_less mult.commute nat_diff_distrib' nat_int nat_mult_distrib of_nat_0_le_iff of_nat_1 order_less_imp_le wsst_TYs(3))

  have "unat (word_repeat (nat n) x::'b::len word) = replicate_nat (nat n) (size x) * unat x"
    apply (subst word_repeat_prop[of "nat n" x, where 'b='b])
    using a00(1) apply auto[1]
     apply (metis a00(3) mult.commute nat_int nat_mult_distrib of_nat_0_le_iff size_word.rep_eq)
    by simp
  also have "... =
 (replicate_nat (nat n - (1::nat)) (size x) + (2::nat) ^ ((nat n - (1::nat)) * size x)) * unat x"
    using replicate_nat_Suc[of "nat n - 1" "size x"] add_0 a00(1) by fastforce
  also have "... = replicate_nat (nat n - (1::nat)) (size x) * unat x + (2::nat) ^ ((nat n - (1::nat)) * size x) * unat x"
    by (metis distrib_left mult.commute)
  also have "... = unat (word_repeat (nat n-1) x::'c::len word) + (2::nat) ^ ((nat n - (1::nat)) * size x) * unat x"
    apply (subst word_repeat_prop[symmetric,of "nat n-1" x, where 'b='c])
    using a00(1) apply linarith
      apply (metis a00(1,2) int_minus int_one_le_iff_zero_less int_ops(2) less_le_not_le mult.commute nat_0_le nat_int nat_mult_distrib of_nat_0_le_iff wsst_TYs(3))
    by blast
  also have "... = push_bit LENGTH('c::len) (unat x) + unat (word_repeat (nat n-1) x::'c::len word)"
    by (simp add: push_bit_eq_mult t0)
  also have "... = unat (word_cat x (smt_repeat (nat (n - (1::int))) x::'c::len word)::'b::len word)"
    apply (subst unat_word_cat[of x "(smt_repeat (nat (n - (1::int))) x::'c::len word)", where 'c='b])
    using a00(2,3) int_distrib(3) apply auto[1]
    by (metis a00(1) int_one_le_iff_zero_less len_gt_0 less_le_not_le mult_zero_left nat_diff_distrib' nat_int of_nat_0_le_iff of_nat_1 smt_repeat_def t0)
  finally show "(smt_repeat (nat n) x::'b::len word) = word_cat x (smt_repeat (nat (n - (1::int))) x::'c::len word)"
    by (metis a00(1) int_one_le_iff_zero_less less_le_not_le nat_0_iff smt_repeat_def word_unat.Rep_inverse')
qed


named_theorems rewrite_bv_repeat_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_2]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = smt_repeat (nat (1::int)) x \<and>
   int (size x_c0) = int (size x) * (1::int) \<and>
   (0::int) \<le> (1::int) \<longrightarrow>
   x_c0 = x"
    unfolding smt_repeat_def word_repeat_def replicate_nat_def
  by (simp add: size_word.rep_eq the_equality word_eq_unatI)



named_theorems rewrite_bv_rotate_left_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_1]:
  fixes x::"'a::len word" and amount::"int"
  shows "NO_MATCH cvc_a (undefined x amount) \<Longrightarrow> (x_c2::'a::len word) =
   word_cat (x_c0::'b::len word) (x_c1::'c::len word) \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<and>
   int (size x) - (1::int) < int (size x) \<and>
   x_c1 =
   smt_extract (nat (int (size x) - (1::int)))
    (nat (int (size x) - SMT.z3mod amount (int (size x)))) x \<and>
   int (size x_c1) =
   (1::int) +
   (int (size x) - (1::int) -
    (int (size x) - SMT.z3mod amount (int (size x)))) \<and>
   int (size x) - SMT.z3mod amount (int (size x))
   \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> int (size x) - SMT.z3mod amount (int (size x)) \<and>
   int (size x) - ((1::int) + SMT.z3mod amount (int (size x)))
   < int (size x) \<and>
   x_c0 =
   smt_extract
    (nat (int (size x) - ((1::int) + SMT.z3mod amount (int (size x)))))
    (nat (0::int)) x \<and>
   int (size x_c0) =
   (1::int) +
   (int (size x) - ((1::int) + SMT.z3mod amount (int (size x))) -
    (0::int)) \<and>
   (0::int)
   \<le> int (size x) - ((1::int) + SMT.z3mod amount (int (size x))) \<and>
   (0::int) \<le> (0::int) \<and> (0::int) \<le> amount \<longrightarrow>
   SMT.z3mod amount (int (size x)) \<noteq> (0::int) \<longrightarrow>
   word_rotl (nat amount) x = x_c2"
  apply (rule impI)+
  apply (simp only: word_uint_eq_iff)
  apply (simp add: uint_word_rotl_eq)
  apply (simp add: concat_bit_eq uint_take_bit_eq)
 apply (subst uint_word_cat[of "(smt_extract
      (nat (int (size x) - ((1::int) + SMT.z3mod amount (int (size x)))))
      0 x::'b::len word)" "(smt_extract (nat (int (size x) - (1::int)))
      (nat (int (size x) - SMT.z3mod amount (int (size x)))) x::'c::len word)"])
  apply (simp add: word_size)
  apply (subst uint_smt_extract[of 0 "(nat (int (size x) - ((1::int) + SMT.z3mod amount (int (size x)))))" x, where 'b="'b"])
     apply simp_all
    apply (simp add: nat_int_comparison(2))
  apply (metis Suc_diff_le diff_Suc_Suc nat_int nat_le_iff nat_minus_as_int of_nat_Suc word_size)
  apply (subst uint_smt_extract[of "(nat (int (size x) - SMT.z3mod amount (int (size x))))" "(nat (int (size x) - (1::int)))" x])
     apply linarith
    apply linarith
  apply (metis Suc_eq_plus1 Suc_pred' add.commute add_diff_cancel_right' int_ops(2) len_gt_0 nat_int nat_minus_as_int word_size)
    apply (simp add: push_bit_take_bit)
    apply (simp add: drop_bit_take_bit)
    apply (simp add: add.commute)
    apply (subst add_mono_thms_linordered_semiring(4))
    apply simp_all
  apply (rule conjI)
    unfolding SMT.z3mod_def
  apply (simp_all add: nat_mod_as_int int_int_eq)
    apply (metis Suc_diff_Suc Suc_le_lessD add_Suc_right bintrunc_shiftl nat_int.Rep_inverse nat_int_comparison(3) nat_minus_as_int of_nat_Suc push_bit_take_bit size_word.rep_eq)
    by (smt (verit, ccfv_threshold) Suc_pred' nat_int nat_minus_as_int of_nat_1 word_size word_size_gt_0)

named_theorems rewrite_bv_rotate_left_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "NO_MATCH cvc_a (undefined x amount) \<Longrightarrow> (0::int) \<le> amount \<longrightarrow>
   SMT.z3mod amount (int (size x)) = (0::int) \<longrightarrow>
   word_rotl (nat amount) x = x"
 unfolding SMT.z3mod_def
  apply (simp only: word_uint_eq_iff)
  apply (simp add: uint_word_rotl_eq)
  apply (simp add: uint_take_bit_eq)
  unfolding concat_bit_def
  by (simp add: bintr_uint nat_mod_as_int size_word.rep_eq)


named_theorems rewrite_bv_rotate_right_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_1]:
  fixes x::"'a::len word" and amount::"int"
  shows "NO_MATCH cvc_a (undefined x amount) \<Longrightarrow> (x_c2::'a::len word) =
   word_cat (x_c0::'b::len word) (x_c1::'c::len word) \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<and>
   int (size x) - (1::int) < int (size x) \<and>
   x_c1 =
   smt_extract (nat (int (size x) - (1::int)))
    (nat (SMT.z3mod amount (int (size x)))) x \<and>
   int (size x_c1) =
   (1::int) +
   (int (size x) - (1::int) - SMT.z3mod amount (int (size x))) \<and>
   SMT.z3mod amount (int (size x)) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> SMT.z3mod amount (int (size x)) \<and>
   SMT.z3mod amount (int (size x)) - (1::int) < int (size x) \<and>
   x_c0 =
   smt_extract (nat (SMT.z3mod amount (int (size x)) - (1::int)))
    (nat (0::int)) x \<and>
   int (size x_c0) =
   (1::int) + (SMT.z3mod amount (int (size x)) - (1::int) - (0::int)) \<and>
   (0::int) \<le> SMT.z3mod amount (int (size x)) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and> (0::int) \<le> amount \<longrightarrow>
   SMT.z3mod amount (int (size x)) \<noteq> (0::int) \<longrightarrow>
   word_rotr (nat amount) x = x_c2"
 apply (rule impI)+
  apply (simp only: word_uint_eq_iff )
    apply (simp add: uint_word_rotr_eq)
  apply (simp add: concat_bit_eq uint_take_bit_eq)
  apply (subst uint_word_cat[of "(smt_extract (nat (SMT.z3mod amount (int (size x)) - (1::int)))
      0 x::'b::len word)" "(smt_extract (nat (int (size x) - (1::int)))
      (nat (SMT.z3mod amount (int (size x)))) x::'c::len word)"])
  apply (metis nat_int.Rep_inverse' nat_plus_as_int size_word.rep_eq)
  apply (subst uint_smt_extract[of 0 "(nat (SMT.z3mod amount (int (size x)) - (1::int)))" x])
     apply simp_all
    apply (simp add: nat_less_iff)
  apply (metis Suc_pred' int_ops(2) nat_minus_as_int word_size word_size_gt_0)
  apply (subst uint_smt_extract[of "(nat (SMT.z3mod amount (int (size x))))" "(nat (int (size x) - (1::int)))" x])
     apply simp_all
  using nat_le_eq_zle apply auto[1]
  apply (simp add: nat_less_iff)
  apply (metis Suc_pred len_gt_0 nat_1 nat_int nat_minus_as_int of_nat_1 word_size)
    apply (simp add: push_bit_take_bit)
  apply (simp add: drop_bit_take_bit)
  using Suc_diff_1
  unfolding SMT.z3mod_def
  apply (simp add:  nat_mod_as_int)
  sorry

named_theorems rewrite_bv_rotate_right_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "NO_MATCH cvc_a (undefined x amount) \<Longrightarrow> (0::int) \<le> amount \<longrightarrow>
   SMT.z3mod amount (int (size x)) = (0::int) \<longrightarrow>
   word_rotr (nat amount) x = x"
  unfolding SMT.z3mod_def
  apply (simp only: word_uint_eq_iff)
  apply (simp add: uint_word_rotr_eq)
  apply (simp add: uint_take_bit_eq)
  unfolding concat_bit_def
  by (simp add: bintr_uint nat_mod_as_int size_word.rep_eq)


named_theorems rewrite_bv_nand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nand_eliminate]:
  fixes x::"'a::ring_bit_operations" and y::"'a::ring_bit_operations"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> not (and x y) = not (and x y)"
  by auto


named_theorems rewrite_bv_nor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nor_eliminate]:
  fixes x::"'a::len word"  and y::"'a::len word" 
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> not (or x y) = not (or x y)"
  by auto


named_theorems rewrite_bv_xnor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_xnor_eliminate]:
  fixes x::"'a::len word"  and y::"'a::len word" 
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> not (semiring_bit_operations_class.xor x y) =
   not (semiring_bit_operations_class.xor x y)"
  by auto


(*TODO: (Word.Word (0::int)) also has to be replaced!*)
named_theorems rewrite_bv_zero_extend_eliminate \<open>automatically_generated\<close>


lemma [rewrite_bv_zero_extend_eliminate]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c2::'b::len word) = word_cat (x_c1::'c::len word) x \<and>
   int (size x_c2) = int (size x_c1) + int (size x) \<and>
   x_c1 = Word.Word (0::int) \<and>
   int (size x_c1) = n \<and>
   (x_c0::'b::len word) = Word.cast x \<and>
   int (size x_c0) = int (size x) + n \<and>
   (0::int) \<le> n \<longrightarrow>
   x_c0 = x_c2"
  apply (rule impI)
  apply simp
  apply (simp only: word_uint_eq_iff)
  apply (subst uint_word_cat)
   apply (simp add: word_size)
  apply (subst uint_up_ucast)
   apply (simp add: is_up.rep_eq size_word.rep_eq)
  by simp

named_theorems rewrite_bv_sdivo_eliminate \<open>automatically_generated\<close>


lemma rewrite_bv_sdivo_eliminate1:
  fixes x::"'a ::len word" and y::"'b ::len word"
  shows "LENGTH('c) = LENGTH('a) - 1  \<longrightarrow> smt_sdivo TYPE('c::len) x y =
   (x = word_cat (Word.Word (1::int):: 1 word) (Word.Word (0::int)::'c::len word) \<and>
    y = not (Word.Word (0::int)::'b::len word))"
    using smt_sdivo_def[of x y, where 'c="'c"] 
mask_full[where 'a="'b"]
    by (metis bit.compl_zero one_word_def word_size zero_word_def)


lemma [rewrite_bv_sdivo_eliminate]:
  fixes x::"'a::len word" and y::"'b::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c3::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c3) = int (size y) \<and>
   (x_c2::'a::len word) =
   word_cat (x_c0::'c::len word) (x_c1::'d::len word) \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<and>
   x_c1 = Word.Word (0::int) \<and>
   int (size x_c1) = int (size x) - (1::int) \<and>
   x_c0 = Word.Word (1::int) \<and>
   int (size x_c0) = (1::int) \<longrightarrow>
   smt_sdivo TYPE('d::len) x y = (x = x_c2 \<and> y = not x_c3)"
  apply (rule impI)
  apply (subst rewrite_bv_sdivo_eliminate1[of x y, where 'c='d])
   apply (metis int_ops(2) nat_int.Rep_inverse' nat_minus_as_int size_word.rep_eq)
  apply (cases "LENGTH('c) = 1")
   apply simp_all
  sorry

named_theorems rewrite_bv_usubo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_usubo_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c3::'b::len word) = Word.Word (1::int) \<and>
   int (size x_c3) = (1::int) \<and>
   int (size x) - (1::int)
   < int (size ((x_c0::'c::len word) - (x_c1::'c::len word))) \<and>
   (x_c2::'b::len word) =
   smt_extract (nat (int (size x) - (1::int)))
    (nat (int (size x) - (1::int))) (x_c0 - x_c1) \<and>
   int (size x_c2) =
   (1::int) + (int (size x) - (1::int) - (int (size x) - (1::int))) \<and>
   int (size x) - (1::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   x_c1 = Word.cast y \<and>
   int (size x_c1) = int (size y) + (1::int) \<and>
   x_c0 = Word.cast x \<and>
   int (size x_c0) = int (size x) + (1::int) \<and>
   (0::int) \<le> (1::int) \<longrightarrow>
   smt_usubo (TYPE('b::len)) x y = (x_c2 = x_c3)"
  apply (rule impI)
  unfolding smt_usubo_def
  apply simp
  apply (cases "LENGTH('b) = 1")
  apply simp_all
  oops

named_theorems rewrite_bv_ite_equal_children \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_children]:
  fixes c::"1 word" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if bit c (0::nat) then x else x) = x"
  by auto


named_theorems rewrite_bv_ite_const_children_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_1]:
  fixes c::"1 word"
  shows "NO_MATCH cvc_a (undefined c) \<Longrightarrow> (x_c1::1 word) = Word.Word (1::int) \<and>
   int (size x_c1) = (1::int) \<and>
   (x_c0::1 word) = Word.Word (0::int) \<and>
   int (size x_c0) = (1::int) \<longrightarrow>
   (if bit c (0::nat) then x_c0 else x_c1) = not c"
  by (metis (no_types, opaque_lifting) bit_1_0 len_num1 less_one not_bit_minus_numeral_Bit0_0 not_one_eq nth_0 one_word_def word_eqI word_not_not word_size zero_word_def)

named_theorems rewrite_bv_ite_const_children_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_2]:
  fixes c::"1 word"
  shows "NO_MATCH cvc_a (undefined c) \<Longrightarrow> (x_c1::1 word) = Word.Word (0::int) \<and>
   int (size x_c1) = (1::int) \<and>
   (x_c0::1 word) = Word.Word (1::int) \<and>
   int (size x_c0) = (1::int) \<longrightarrow>
   (if bit c (0::nat) then x_c0 else x_c1) = c"
   by (metis bit_1_0 less_one nth_0 of_nat_1_eq_iff one_word_def word_eqI zero_word_def)



named_theorems rewrite_bv_ite_equal_cond_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_1]:
  fixes c0::"1 word" and t0::"'a::len word" and e0::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 t0 e0 e1) \<Longrightarrow> (if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto


named_theorems rewrite_bv_ite_equal_cond_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_2]:
  fixes c0::"1 word" and t0::"'a::len word" and t1::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 t0 t1 e1) \<Longrightarrow> (if bit c0 (0::nat) then t0 else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto


named_theorems rewrite_bv_ite_equal_cond_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_3]:
  fixes c0::"1 word" and t0::"'a::len word" and e0::"'a::len word" and t1::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 t0 e0 t1 e1) \<Longrightarrow> (if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0
    else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto


named_theorems rewrite_bv_ite_merge_then_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_if]:
  fixes c0::"1 word" and c1::"1 word" and t1::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t1 e1) \<Longrightarrow> (if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else t1) =
   (if bit (and c0 (not c1)) (0::nat) then e1 else t1)"
  by (simp add: lsb0)


named_theorems rewrite_bv_ite_merge_else_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_if]:
  fixes c0::"1 word" and c1::"1 word" and t1::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t1 e1) \<Longrightarrow> (if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else e1) =
   (if bit (and c0 c1) (0::nat) then t1 else e1)"
  by (simp add: lsb0)


named_theorems rewrite_bv_ite_merge_then_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_else]:
  fixes c0::"1 word" and c1::"1 word" and t0::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t0 e1) \<Longrightarrow> (if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t0 else e1) =
   (if bit (not (or c0 c1)) (0::nat) then e1 else t0)"
  by (simp add: lsb0)


named_theorems rewrite_bv_ite_merge_else_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_else]:
  fixes c0::"1 word" and c1::"1 word" and t1::"'a::len word" and t0::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t1 t0) \<Longrightarrow> (if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t1 else t0) =
   (if bit (and (not c0) c1) (0::nat) then t1 else t0)"
  by (simp add: lsb0)


named_theorems rewrite_bv_shl_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_0]:
  fixes x::"'a::len word" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x sz) \<Longrightarrow> (x_c0::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = sz \<longrightarrow>
   push_bit (unat x_c0) x = x"
  by auto

lemma rewrite_bv_shl_by_const_11:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
LENGTH('b) = amount \<longrightarrow>
size x - (1 + amount) \<ge> 0 \<longrightarrow>
size x - (1 + amount) < size x \<longrightarrow> 
amount \<ge> 0 \<longrightarrow>
LENGTH('c) = 1 + ((size x - (1 + amount)) - 0) \<longrightarrow>
LENGTH('a) = LENGTH('b) + LENGTH('c) \<longrightarrow>
LENGTH('d) = sz \<longrightarrow>
amount < (2::int) ^ LENGTH('d) \<longrightarrow>
   (push_bit (unat (Word.Word amount::'d::len word)) x ::'a::len word)=
   word_cat
    (smt_extract (nat (int (size x) - ((1::int) + amount)))
      (nat (0::int)) x::'c::len word)
    (Word.Word (0::int)::'b::len word)"
  apply rule+
proof-
  assume a0:
    "amount < int (size x)"
    "int LENGTH('b) = amount"
    "(0::int) \<le> int (size x) - ((1::int) + amount)"
    "int (size x) - ((1::int) + amount) < int (size x)"
    "amount \<ge> 0"
    "int LENGTH('c) = (1::int) + (int (size x) - ((1::int) + amount) - (0::int))"
    "LENGTH('a) = LENGTH('b) + LENGTH('c)"
    "int LENGTH('d) = sz"
    "amount < (2::int) ^ LENGTH('d)"
  have t0: "(nat (int (size x) - ((1::int) + amount))) = (size x - 1 - nat amount::nat)"
    using a0(3) a0(4) by auto
  have t1: "(unat (Word.Word amount::'d::len word)) = nat amount"
    apply simp
    apply (simp add: unsigned_of_int)
    apply (subst take_bit_int_eq_self)
    by (simp_all add: a0)

  have "word_cat
    (smt_extract (nat (int (size x) - ((1::int) + amount)))
      (nat (0::int)) x::'c::len word)
    (Word.Word (0::int)::'b::len word)
  = word_cat (smt_extract (size x - 1 - nat amount) 0 x::'c::len word) (0::'b::len word)"
    using t0 by simp
  also have "...
  = word_cat (slice (0::nat) (take_bit (Suc (size x - (1::nat) - nat amount)) x::'a::len word)::'c::len word) (0::'b ::len word)"
    unfolding smt_extract_def by simp
  also have "...
  = word_cat (slice (0::nat) (take_bit (size x - nat amount) x::'a::len word)::'c::len word) (0::'b ::len word)"
    using Suc_diff_Suc a0(1) a0(4) by force
 also have "...
  = word_cat (ucast (take_bit (size x - nat amount) x::'a::len word)::'c::len word) (0::'b ::len word)"
   by (simp add: ucast_slice)
   also have "...
  =  push_bit LENGTH('b::len) (ucast (ucast (take_bit (size x - nat amount) x::'a::len word)::'c::len word)::'a::len word) + (ucast (0::'b::len word)::'a::len word)"
     using word_cat_eq[of "(ucast (take_bit (size x - nat amount) x::'a::len word)::'c::len word)" "(0::'b ::len word)"]
     by simp
 also have "...
  =  push_bit LENGTH('b::len) (ucast (ucast (take_bit (size x - nat amount) x::'a::len word)::'c::len word)::'a::len word)"
   by auto
 also have "...
  =  push_bit (unat (Word.Word amount::'d::len word)) (ucast (ucast (take_bit (size x - nat amount) x::'a::len word)::'c::len word)::'a::len word)"
   using t1 a0(2) by force
 also have "...
  =  push_bit (unat (Word.Word amount::'d::len word)) (take_bit LENGTH('c::len) (unsigned (take_bit (size x - nat amount) x::'a::len word)::'a::len word))"
   apply (subst unsigned_ucast_eq[of "(take_bit (size x - nat amount) x::'a::len word)"])
   by simp
also have "...
  =  push_bit (unat (Word.Word amount::'d::len word)) (take_bit LENGTH('c::len) (take_bit (size x - nat amount) (unsigned x::'a::len word)))"
  by (simp add: unsigned_take_bit_eq)
also have "...
  =  (push_bit (unat (Word.Word amount::'d::len word)) (take_bit (size x - nat amount) (unsigned x::'a::len word))::'a::len word)"
  using take_bit_take_bit
  by (metis a0(2) a0(5) a0(7) nat_eq_iff2 push_bit_take_bit t1 take_bit_length_eq)
also have "...
  =  (push_bit (unat (Word.Word amount::'d::len word)) x::'a::len word)"
  by (metis t1 take_bit_length_eq take_bit_push_bit ucast_id word_size)

  finally  show "(push_bit (unat (Word.Word amount::'d::len word)) x ::'a::len word)=
   word_cat
    (smt_extract (nat (int (size x) - ((1::int) + amount)))
      (nat (0::int)) x::'c::len word)
    (Word.Word (0::int)::'b::len word)"
    by presburger
qed

lemma h1: "amount < int (size x) \<Longrightarrow> (Suc (nat (int (size (x::'a::len word)) - ((1::int) + amount)))) =  nat (int (size x) - amount)"
  by simp

lemma h2: "amount < int (size x) \<Longrightarrow> amount \<ge> 0 \<Longrightarrow> (Suc (nat (int (size (x::'a::len word)) - ((1::int) + amount)))) =   ( (size x) - nat amount)"
  by simp

named_theorems rewrite_bv_shl_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_1]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz) \<Longrightarrow> (x_c5::'b::len word) =
   word_cat (x_c3::'c::len word) (x_c4::'d::len word) \<and>
   int (size x_c5) = int (size x_c3) + int (size x_c4) \<and>
   x_c4 = Word.Word (0::int) \<and>
   int (size x_c4) = amount \<and>
   int (size x) - ((1::int) + amount) < int (size x) \<and>
   x_c3 =
   smt_extract (nat (int (size x) - ((1::int) + amount))) (nat (0::int))
    x \<and>
   int (size x_c3) =
   (1::int) + (int (size x) - ((1::int) + amount) - (0::int)) \<and>
   (0::int) \<le> int (size x) - ((1::int) + amount) \<and>
   (0::int) \<le> (0::int) \<and>
   (x_c2::'b::len word) =
   push_bit (unat (x_c1::'a::len word)) (x_c0::'b::len word) \<and>
   int (size x_c2) = int (size x_c1) \<and>
   x_c1 = x \<and>
   int (size x_c0) = int (size x_c1) \<and>
   x_c0 = Word.Word amount \<and> int (size x_c0) = sz \<longrightarrow>
   amount < int (size x) \<longrightarrow> x_c2 = x_c5"
  apply (rule)+
  apply simp
  apply (simp only: word_uint_eq_iff)
  apply (subst uint_shiftl)
  apply simp_all
  apply (subst uint_word_cat)
   apply simp_all
   apply (metis nat_int of_nat_add word_size)
  apply (subst uint_smt_extract)
  apply blast
    apply (simp add: nat_int_comparison(2))
   apply (metis Suc_diff_Suc Suc_eq_plus1 diff_is_0_eq diff_zero len_not_eq_0 linorder_not_le nat_int nat_minus_as_int of_nat_Suc word_size)
  apply simp
  apply (subst take_bit_push_bit)
  apply (subst h2)
    apply simp_all
  apply (simp add: uint_word_of_int_eq)
  apply (cases "(unat x) = nat amount")
   apply simp_all
  apply (case_tac[!] "LENGTH('d) = nat amount ")
     apply simp_all
  apply (case_tac[!] "(uint x) =  amount")
         apply simp_all
         apply (simp_all add: word_size int_eq_iff)
  apply (metis Word.of_nat_unat len_not_eq_0 nat_0_le nat_code(2))
  apply (metis Word.of_nat_unat nat_int)
  


proof-
  assume a0: "NO_MATCH cvc_a (undefined x amount sz) \<Longrightarrow> (x_c4::'a::len word) =
   word_cat (x_c2::'b::len word) (x_c3::'c::len word) \<and>
   int (size x_c4) = int (size x_c2) + int (size x_c3) \<and>
   x_c3 = Word.Word (0::int) \<and>
   int (size x_c3) = amount \<and>
   int (size x) - ((1::int) + amount) < int (size x) \<and>
   x_c2 =
   smt_extract (nat (int (size x) - ((1::int) + amount))) (nat (0::int))
    x \<and>
   int (size x_c2) =
   (1::int) + (int (size x) - ((1::int) + amount) - (0::int)) \<and>
   (0::int) \<le> int (size x) - ((1::int) + amount) \<and>
   (0::int) \<le> (0::int) \<and>
   (x_c1::'a::len word) =
   push_bit (unat (Word.Word amount)) (x_c0::'a::len word) \<and>
   int (size x_c1) = int (size x_c0) \<and>
   x_c0 = x \<and>
   int (size (Word.Word amount)) = int (size x_c0)"

  have "(amount::int) < int (size (x::'a word))"
    
  moreover have "int LENGTH('c) = amount "
    by (metis a0(2) word_size)
  moreover have "(0::int) \<le> int (size x) - ((1::int) + amount)"
    using a0(2) by blast
  moreover have "int (size x) - ((1::int) + amount) < int (size x)"
    using a0(2) by fastforce
  moreover have "(0::int) \<le> amount"
    using calculation(4) by force
  moreover have "int LENGTH('b) = (1::int) + (int (size x) - ((1::int) + amount) - (0::int))"
    by (metis a0(2) word_size)
  moreover have "LENGTH('a) = LENGTH('c) + LENGTH('b)"
    by (metis a0(2) add.commute nat_int nat_int_add word_size)
  moreover have "int LENGTH('d) = (sz::int)"
    by (metis a0(2) word_size)
  moreover have " amount < (2::int) ^ LENGTH('d)"
    
  ultimately show "push_bit (unat x_c0) x = x_c3"
    using rewrite_bv_shl_by_const_11[of amount x sz,where 'b='c,where 'c="'b", where 'd="'d"]
    




named_theorems rewrite_bv_shl_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_2]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = int (size x) \<and>
   (x_c0::'b::len word) = Word.Word amount \<and>
   int (size x_c0) = sz \<longrightarrow>
   int (size x) \<le> amount \<longrightarrow> push_bit (unat x_c0) x = x_c1"
  apply (rule impI)
  


named_theorems rewrite_bv_lshr_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_0]:
  fixes x::"'a::len word" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x sz) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = sz \<longrightarrow>
   drop_bit (unat x) x_c0 = x"
  by auto


named_theorems rewrite_bv_lshr_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_1]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz) \<Longrightarrow> (x_c3::'b::len word) =
   word_cat (x_c1::'c::len word) (x_c2::'d::len word) \<and>
   int (size x_c3) = int (size x_c1) + int (size x_c2) \<and>
   int (size x) - (1::int) < int (size x) \<and>
   x_c2 = smt_extract (nat (int (size x) - (1::int))) (nat amount) x \<and>
   int (size x_c2) = (1::int) + (int (size x) - (1::int) - amount) \<and>
   amount \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> amount \<and>
   x_c1 = Word.Word (0::int) \<and>
   int (size x_c1) = amount \<and>
   (x_c0::'b::len word) = Word.Word amount \<and>
   int (size x_c0) = sz \<longrightarrow>
   amount < int (size x) \<longrightarrow> drop_bit (unat x) x_c0 = x_c3"
  by auto


named_theorems rewrite_bv_lshr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_2]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz) \<Longrightarrow> (x_c1::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = sz \<and>
   (x_c0::'b::len word) = Word.Word amount \<and>
   int (size x_c0) = sz \<longrightarrow>
   int (size x) \<le> amount \<longrightarrow> drop_bit (unat x) x_c0 = x_c1"
  by auto


named_theorems rewrite_bv_ashr_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_0]:
  fixes x::"'a::len word" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x sz) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = sz \<longrightarrow>
   signed_drop_bit (unat x) x_c0 = x"
  by auto

named_theorems rewrite_bv_bitwise_idemp_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_idemp_1]:
  fixes x::"'a::semiring_bit_operations"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> and x x = x"
  by auto


named_theorems rewrite_bv_bitwise_idemp_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_idemp_2]:
  fixes x::"'a::semiring_bit_operations"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> or x x = x"
  by auto


named_theorems rewrite_bv_and_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_and_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   and x x_c0 = x_c0"
  by auto


named_theorems rewrite_bv_and_one \<open>automatically_generated\<close>

lemma [rewrite_bv_and_one]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow> and x y = x"
  by auto


named_theorems rewrite_bv_or_one \<open>automatically_generated\<close>

lemma [rewrite_bv_or_one]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow> or x y = not x_c0"
  by auto


named_theorems rewrite_bv_xor_duplicate \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_duplicate]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   semiring_bit_operations_class.xor x x = x_c0"
  by auto


named_theorems rewrite_bv_xor_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_ones]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow>
   semiring_bit_operations_class.xor x y = not x"
  by auto


named_theorems rewrite_bv_xor_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   semiring_bit_operations_class.xor x x_c0 = x"
  by auto


named_theorems rewrite_bv_bitwise_not_and \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_not_and]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   and x (not x) = x_c0"
  by auto


named_theorems rewrite_bv_bitwise_not_or \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_not_or]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   or x (not x) = not x_c0"
  by auto



named_theorems rewrite_bv_not_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_not_idemp]:
  fixes x::"'a::ring_bit_operations"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> not (not x) = x"
  by auto


named_theorems rewrite_bv_ult_zero_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_1]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = int (size x) \<and>
   (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x_c0 < x) = (x_c1 \<noteq> x)"
  by (simp add: word_greater_zero_iff)


named_theorems rewrite_bv_ult_zero_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_2]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x < x_c0) = False"
  by auto


named_theorems rewrite_bv_ult_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_self]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x < x) = False"
  by simp

named_theorems rewrite_bv_ule_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_self]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<le> x) = True"
  by auto


named_theorems rewrite_bv_ule_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x \<le> x_c0) = (x = x_c0)"
  by auto


named_theorems rewrite_bv_zero_ule \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ule]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x_c0 \<le> x) = True"
  by auto


named_theorems rewrite_bv_sle_self \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_self]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<le>s x) = True"
  by auto


named_theorems rewrite_bv_ule_max \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_max]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow> (x \<le> y) = True"
  by auto


named_theorems rewrite_bv_not_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_not_ult]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (\<not> x < y) = (y \<le> x)"
  by auto


named_theorems rewrite_bv_mult_pow2_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_pow2_1]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and z::"'a::len word" and size::"int" and n::"int"
  shows "NO_MATCH cvc_a (undefined xs ys z size n) \<Longrightarrow> (x_c3::'a::len word) =
   word_cat (x_c1::'b::len word) (x_c2::'c::len word) \<and>
   int (size x_c3) = int (size x_c1) + int (size x_c2) \<and>
   x_c2 = Word.Word (0::int) \<and>
   int (size x_c2) = int (floorlog (nat n) (2::nat)) \<and>
   sizea - int (floorlog (nat n) (2::nat)) - (1::int)
   < int (size (cvc_list_right (*) (cvc_list_left (*) xs z) ys)) \<and>
   x_c1 =
   smt_extract (nat (sizea - int (floorlog (nat n) (2::nat)) - (1::int)))
    (nat (0::int)) (cvc_list_right (*) (cvc_list_left (*) xs z) ys) \<and>
   int (size x_c1) =
   (1::int) +
   (sizea - int (floorlog (nat n) (2::nat)) - (1::int) - (0::int)) \<and>
   (0::int) \<le> sizea - int (floorlog (nat n) (2::nat)) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   (x_c0::'a::len word) = Word.Word n \<and>
   int (size x_c0) = sizea \<longrightarrow>
   is_pow2 n \<longrightarrow>
   cvc_list_right (*) (cvc_list_left (*) xs z * x_c0) ys = x_c3"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction yss arbitrary: ys)
    apply simp_all
    apply (induction xss arbitrary: xs)
    apply simp_all
    apply (simp_all add: cvc_rewrites_fold)
    by (simp_all add: bv_mult_pow2_1_lemma)
  done


named_theorems rewrite_bv_mult_pow2_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_pow2_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and z::"'a::len word" and size::"int" and n::"int"
  shows "NO_MATCH cvc_a (undefined xs ys z size n) \<Longrightarrow> (x_c3::'a::len word) =
   word_cat (x_c1::'b::len word) (x_c2::'c::len word) \<and>
   int (size x_c3) = int (size x_c1) + int (size x_c2) \<and>
   x_c2 = Word.Word (0::int) \<and>
   int (size x_c2) = int (floorlog (nat (- n)) (2::nat)) \<and>
   sizea - int (floorlog (nat (- n)) (2::nat)) - (1::int)
   < int (size (cvc_list_right (*) (cvc_list_left (*) xs z) ys)) \<and>
   x_c1 =
   smt_extract
    (nat (sizea - int (floorlog (nat (- n)) (2::nat)) - (1::int)))
    (nat (0::int)) (cvc_list_right (*) (cvc_list_left (*) xs z) ys) \<and>
   int (size x_c1) =
   (1::int) +
   (sizea - int (floorlog (nat (- n)) (2::nat)) - (1::int) -
    (0::int)) \<and>
   (0::int)
   \<le> sizea - int (floorlog (nat (- n)) (2::nat)) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   (x_c0::'a::len word) = Word.Word n \<and>
   int (size x_c0) = sizea \<longrightarrow>
   is_pow2 (- n) \<longrightarrow>
   cvc_list_right (*) (cvc_list_left (*) xs z * x_c0) ys = - x_c3"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction yss arbitrary: ys)
    apply simp_all
    apply (induction xss arbitrary: xs)
    apply simp_all
    apply (simp_all add: cvc_rewrites_fold)
    by (simp_all add: bv_mult_pow2_2_lemma)
  done


named_theorems rewrite_bv_extract_mult_leading_bit \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_mult_leading_bit]:
  fixes high::"int" and low::"int" and x1i::"int" and x1in::"int" and x2::"'a::len word" and y1i::"int" and y1in::"int" and y2::"'b::len word"
  shows "NO_MATCH cvc_a (undefined high low x1i x1in x2 y1i y1in y2) \<Longrightarrow> (x_c5::'c::len word) = Word.Word (0::int) \<and>
   int (size x_c5) = (1::int) + (high - low) \<and>
   high
   < int (size ((x_c1::'d::len word) * (x_c3::'d::len word))) \<and>
   (x_c4::'c::len word) =
   smt_extract (nat high) (nat low) (x_c1 * x_c3) \<and>
   int (size x_c4) = (1::int) + (high - low) \<and>
   low \<le> high \<and>
   (0::int) \<le> low \<and>
   x_c3 = word_cat (x_c2::'e::len word) y2 \<and>
   int (size x_c3) = int (size x_c2) + int (size y2) \<and>
   x_c2 = Word.Word y1i \<and>
   int (size x_c2) = y1in \<and>
   x_c1 = word_cat (x_c0::'f::len word) x2 \<and>
   int (size x_c1) = int (size x_c0) + int (size x2) \<and>
   x_c0 = Word.Word x1i \<and> int (size x_c0) = x1in \<longrightarrow>
   (64::int) < x1in + int (size x2) \<and>
   low
   < (2::int) * (x1in + int (size x2)) -
     ((if x1i = (0::int) then x1in
       else x1in - int (floorlog (nat x1i) (2::nat))) +
      (if y1i = (0::int) then y1in
       else y1in - int (floorlog (nat y1i) (2::nat)))) \<longrightarrow>
   x_c4 = x_c5"
  by auto


named_theorems rewrite_bv_neg_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_idemp]:
  fixes x::"'a::uminus"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> - (- x) = x"
  by auto


named_theorems rewrite_bv_udiv_pow2_1p \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_1p]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "NO_MATCH cvc_a (undefined x v n) \<Longrightarrow> (x_c3::'a::len word) =
   word_cat (x_c1::'b::len word) (x_c2::'c::len word) \<and>
   int (size x_c3) = int (size x_c1) + int (size x_c2) \<and>
   n - (1::int) < int (size x) \<and>
   x_c2 =
   smt_extract (nat (n - (1::int))) (nat (int (floorlog (nat v) (2::nat))))
    x \<and>
   int (size x_c2) =
   (1::int) + (n - (1::int) - int (floorlog (nat v) (2::nat))) \<and>
   int (floorlog (nat v) (2::nat)) \<le> n - (1::int) \<and>
   (0::int) \<le> int (floorlog (nat v) (2::nat)) \<and>
   x_c1 = Word.Word (0::int) \<and>
   int (size x_c1) = int (floorlog (nat v) (2::nat)) \<and>
   (x_c0::'a::len word) = Word.Word v \<and>
   int (size x_c0) = n \<longrightarrow>
   is_pow2 v \<and> (1::int) < v \<longrightarrow> x div x_c0 = x_c3"
  by auto


named_theorems rewrite_bv_udiv_pow2_1n \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_1n]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "NO_MATCH cvc_a (undefined x v n) \<Longrightarrow> (x_c3::'a::len word) =
   word_cat (x_c1::'b::len word) (x_c2::'c::len word) \<and>
   int (size x_c3) = int (size x_c1) + int (size x_c2) \<and>
   n - (1::int) < int (size x) \<and>
   x_c2 =
   smt_extract (nat (n - (1::int)))
    (nat (int (floorlog (nat (- v)) (2::nat)))) x \<and>
   int (size x_c2) =
   (1::int) + (n - (1::int) - int (floorlog (nat (- v)) (2::nat))) \<and>
   int (floorlog (nat (- v)) (2::nat)) \<le> n - (1::int) \<and>
   (0::int) \<le> int (floorlog (nat (- v)) (2::nat)) \<and>
   x_c1 = Word.Word (0::int) \<and>
   int (size x_c1) = int (floorlog (nat (- v)) (2::nat)) \<and>
   (x_c0::'a::len word) = Word.Word v \<and>
   int (size x_c0) = n \<longrightarrow>
   is_pow2 (- v) \<and> v < - (1::int) \<longrightarrow> x div x_c0 = - x_c3"
  by auto


named_theorems rewrite_bv_udiv_pow2_2p \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_2p]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "NO_MATCH cvc_a (undefined x v n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word v \<and>
   int (size x_c0) = n \<longrightarrow>
   v = (1::int) \<longrightarrow> x div x_c0 = x"
  by auto


named_theorems rewrite_bv_udiv_pow2_2n \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_2n]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "NO_MATCH cvc_a (undefined x v n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word v \<and>
   int (size x_c0) = n \<longrightarrow>
   v = - (1::int) \<longrightarrow> x div x_c0 = - x"
  by auto



named_theorems rewrite_bv_udiv_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   smt_udiv x x_c0 = not x_c0"
  unfolding smt_udiv_def
  by (simp add: word_size)

named_theorems rewrite_bv_udiv_one \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_one]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (1::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   smt_udiv x x_c0 = x"
  apply simp
  unfolding smt_udiv_def
  by simp 


named_theorems rewrite_bv_urem_pow2_not_one \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_not_one]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "NO_MATCH cvc_a (undefined x v n) \<Longrightarrow> (x_c3::'a::len word) =
   word_cat (x_c1::'b::len word) (x_c2::'c::len word) \<and>
   int (size x_c3) = int (size x_c1) + int (size x_c2) \<and>
   int (floorlog (nat v) (2::nat)) - (1::int) < int (size x) \<and>
   x_c2 =
   smt_extract (nat (int (floorlog (nat v) (2::nat)) - (1::int)))
    (nat (0::int)) x \<and>
   int (size x_c2) =
   (1::int) + (int (floorlog (nat v) (2::nat)) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (floorlog (nat v) (2::nat)) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c1 = Word.Word (0::int) \<and>
   int (size x_c1) = n - int (floorlog (nat v) (2::nat)) \<and>
   (x_c0::'a::len word) = Word.Word v \<and>
   int (size x_c0) = n \<longrightarrow>
   is_pow2 v \<and> (1::int) < v \<longrightarrow> smt_urem x x_c0 = x_c3"
  by auto





named_theorems rewrite_bv_urem_pow2_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_1]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "NO_MATCH cvc_a (undefined x v n) \<Longrightarrow> (x_c3::'a::len word) =
   word_cat (x_c1::'b::len word) (x_c2::'c::len word) \<and>
   int (size x_c3) = int (size x_c1) + int (size x_c2) \<and>
   int (floorlog (nat v) (2::nat)) - (1::int) < int (size x) \<and>
   x_c2 =
   smt_extract (nat (int (floorlog (nat v) (2::nat)) - (1::int)))
    (nat (0::int)) x \<and>
   int (size x_c2) =
   (1::int) + (int (floorlog (nat v) (2::nat)) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (floorlog (nat v) (2::nat)) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c1 = Word.Word (0::int) \<and>
   int (size x_c1) = n - int (floorlog (nat v) (2::nat)) \<and>
   (x_c0::'a::len word) = Word.Word v \<and>
   int (size x_c0) = n \<longrightarrow>
   is_pow2 v \<and> (1::int) < v \<longrightarrow> smt_urem x x_c0 = x_c3"
  by auto


named_theorems rewrite_bv_urem_pow2_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_2]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "NO_MATCH cvc_a (undefined x v n) \<Longrightarrow> (x_c3::'a::len word) =
   word_cat (x_c1::'b::len word) (x_c2::'c::len word) \<and>
   int (size x_c3) = int (size x_c1) + int (size x_c2) \<and>
   int (floorlog (nat (- v)) (2::nat)) - (1::int) < int (size x) \<and>
   x_c2 =
   smt_extract (nat (int (floorlog (nat (- v)) (2::nat)) - (1::int)))
    (nat (0::int)) x \<and>
   int (size x_c2) =
   (1::int) +
   (int (floorlog (nat (- v)) (2::nat)) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (floorlog (nat (- v)) (2::nat)) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c1 = Word.Word (0::int) \<and>
   int (size x_c1) = n - int (floorlog (nat (- v)) (2::nat)) \<and>
   (x_c0::'a::len word) = Word.Word v \<and>
   int (size x_c0) = n \<longrightarrow>
   is_pow2 (- v) \<and> v < - (1::int) \<longrightarrow>
   smt_urem x x_c0 = x_c3"
  by auto


named_theorems rewrite_bv_urem_one_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_one_1]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = n \<and>
   (x_c0::'a::len word) = Word.Word (1::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   smt_urem x x_c0 = x_c1"
  unfolding smt_urem_def
  using unat_eq_zero by auto

named_theorems rewrite_bv_urem_one_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_one_2]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "NO_MATCH cvc_a (undefined x v n) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = n \<and>
   (x_c0::'a::len word) = Word.Word v \<and>
   int (size x_c0) = n \<longrightarrow>
   v = - (1::int) \<longrightarrow> smt_urem x x_c0 = x_c1"
  by auto


named_theorems rewrite_bv_urem_self \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_self]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   smt_urem x x = x_c0"
  unfolding smt_urem_def
  using unat_eq_zero by auto

named_theorems rewrite_bv_shl_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_zero]:
  fixes a::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined a n) \<Longrightarrow> (x_c2::'b::len word) = push_bit (unat a) (x_c1::'b::len word) \<and>
   int (size x_c2) = int (size x_c1) \<and>
   x_c1 = (x_c0::'b::len word) \<and>
   int (size a) = int (size x_c1) \<and>
   x_c0 = Word.Word (0::int) \<and> int (size x_c0) = n \<longrightarrow>
   x_c2 = x_c0"
  by auto


named_theorems rewrite_bv_lshr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_zero]:
  fixes a::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined a n) \<Longrightarrow> (x_c2::'b::len word) = drop_bit (unat a) (x_c1::'b::len word) \<and>
   int (size x_c2) = int (size x_c1) \<and>
   x_c1 = (x_c0::'b::len word) \<and>
   int (size a) = int (size x_c1) \<and>
   x_c0 = Word.Word (0::int) \<and> int (size x_c0) = n \<longrightarrow>
   x_c2 = x_c0"
  by auto


named_theorems rewrite_bv_ashr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_zero]:
  fixes a::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined a n) \<Longrightarrow> (x_c2::'b::len word) =
   signed_drop_bit (unat a) (x_c1::'b::len word) \<and>
   int (size x_c2) = int (size x_c1) \<and>
   x_c1 = (x_c0::'b::len word) \<and>
   int (size a) = int (size x_c1) \<and>
   x_c0 = Word.Word (0::int) \<and> int (size x_c0) = n \<longrightarrow>
   x_c2 = x_c0"
  by auto


named_theorems rewrite_bv_ugt_urem \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_urem]:
  fixes y::"'a::len word" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined y x) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = int (size y) \<and>
   (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   (x < smt_urem y x) = (x = x_c0 \<and> x_c1 < y)"
  unfolding smt_urem_def
  apply simp
  by (metis Word.of_nat_unat mod_by_0 not_less_iff_gr_or_eq ucast_id unsigned_0 word_arith_nat_mod word_mod_less_divisor word_not_simps(1))


named_theorems rewrite_bv_ult_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_one]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = n \<and>
   (x_c0::'a::len word) = Word.Word (1::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x < x_c0) = (x = x_c1)"
  by auto


named_theorems rewrite_bv_slt_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_slt_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c2::'b::len word) = Word.Word (1::int) \<and>
   int (size x_c2) = (1::int) \<and>
   n - (1::int) < int (size x) \<and>
   (x_c1::'b::len word) =
   smt_extract (nat (n - (1::int))) (nat (n - (1::int))) x \<and>
   int (size x_c1) = (1::int) + (n - (1::int) - (n - (1::int))) \<and>
   n - (1::int) \<le> n - (1::int) \<and>
   (0::int) \<le> n - (1::int) \<and>
   (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x <s x_c0) = (x_c1 = x_c2)"
  by auto


named_theorems rewrite_bv_zero_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ult]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x_c0 < x) = (x \<noteq> x_c0)"
  by auto


named_theorems rewrite_bv_merge_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_1]:
  fixes x::"'a::len word" and i::"int" and j::"int"
  shows "NO_MATCH cvc_a (undefined x i j) \<Longrightarrow> (x_c2::'b::len word) = Word.signed_cast x \<and>
   int (size x_c2) = int (size x) + (i + j) \<and>
   (0::int) \<le> i + j \<and>
   (x_c1::'b::len word) = Word.signed_cast (x_c0::'c::len word) \<and>
   int (size x_c1) = int (size x_c0) + i \<and>
   (0::int) \<le> i \<and>
   x_c0 = Word.signed_cast x \<and>
   int (size x_c0) = int (size x) + j \<and>
   (0::int) \<le> j \<longrightarrow>
   x_c1 = x_c2"
  apply simp
  apply rule
  apply (subst scast_up_scast[of x])
   apply simp_all
  by (simp add: is_up.rep_eq size_word.rep_eq)


named_theorems rewrite_bv_merge_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_2]:
  fixes x::"'a::len word" and i::"int" and j::"int"
  shows "NO_MATCH cvc_a (undefined x i j) \<Longrightarrow> (x_c2::'b::len word) = Word.cast x \<and>
   int (size x_c2) = int (size x) + (i + j) \<and>
   (0::int) \<le> i + j \<and>
   (x_c1::'b::len word) = Word.signed_cast (x_c0::'c::len word) \<and>
   int (size x_c1) = int (size x_c0) + i \<and>
   (0::int) \<le> i \<and>
   x_c0 = Word.cast x \<and>
   int (size x_c0) = int (size x) + j \<and>
   (0::int) \<le> j \<longrightarrow>
   (1::int) < j \<longrightarrow> x_c1 = x_c2"
  by auto


named_theorems rewrite_bv_merge_sign_extend_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_3]:
  fixes x::"'a::len word" and i::"int"
  shows "NO_MATCH cvc_a (undefined x i) \<Longrightarrow> (x_c2::'b::len word) = Word.signed_cast x \<and>
   int (size x_c2) = int (size x) + i \<and>
   (x_c1::'b::len word) = Word.signed_cast (x_c0::'c::len word) \<and>
   int (size x_c1) = int (size x_c0) + i \<and>
   (0::int) \<le> i \<and>
   x_c0 = Word.cast x \<and>
   int (size x_c0) = int (size x) + (0::int) \<and>
   (0::int) \<le> (0::int) \<longrightarrow>
   x_c1 = x_c2"
  by auto


named_theorems rewrite_bv_sign_extend_eq_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_1]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "NO_MATCH cvc_a (undefined x m c nm) \<Longrightarrow> (x_c4::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c4) = m + (1::int) \<and>
   (x_c3::'c::len word) = Word.signed_cast x \<and>
   int (size x_c3) = int (size x) + m \<and>
   (0::int) \<le> m \<and>
   nm - (1::int) < int (size (x_c0::'c::len word)) \<and>
   (x_c2::'b::len word) =
   smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
    x_c0 \<and>
   int (size x_c2) =
   (1::int) + (nm - (1::int) - (int (size x) - (1::int))) \<and>
   int (size x) - (1::int) \<le> nm - (1::int) \<and>
   int (size x) - (1::int) < int (size x_c0) \<and>
   (x_c1::'a::len word) =
   smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) x_c0 \<and>
   int (size x_c1) = (1::int) + (int (size x) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c0 = Word.Word c \<and> int (size x_c0) = nm \<longrightarrow>
   (x_c3 = x_c0) = ((x_c2 = x_c4 \<or> x_c2 = not x_c4) \<and> x = x_c1)"
  by auto


named_theorems rewrite_bv_sign_extend_eq_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_2]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "NO_MATCH cvc_a (undefined x m c nm) \<Longrightarrow> (x_c4::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c4) = m + (1::int) \<and>
   (x_c3::'c::len word) = Word.signed_cast x \<and>
   int (size x_c3) = int (size x) + m \<and>
   (0::int) \<le> m \<and>
   nm - (1::int) < int (size (x_c0::'c::len word)) \<and>
   (x_c2::'b::len word) =
   smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
    x_c0 \<and>
   int (size x_c2) =
   (1::int) + (nm - (1::int) - (int (size x) - (1::int))) \<and>
   int (size x) - (1::int) \<le> nm - (1::int) \<and>
   int (size x) - (1::int) < int (size x_c0) \<and>
   (x_c1::'a::len word) =
   smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) x_c0 \<and>
   int (size x_c1) = (1::int) + (int (size x) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c0 = Word.Word c \<and> int (size x_c0) = nm \<longrightarrow>
   (x_c0 = x_c3) = ((x_c2 = x_c4 \<or> x_c2 = not x_c4) \<and> x = x_c1)"
  by auto


named_theorems rewrite_bv_zero_extend_eq_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_1]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "NO_MATCH cvc_a (undefined x m c nm) \<Longrightarrow> (x_c4::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c4) = m \<and>
   (x_c3::'c::len word) = Word.cast x \<and>
   int (size x_c3) = int (size x) + m \<and>
   (0::int) \<le> m \<and>
   nm - (1::int) < int (size (x_c0::'c::len word)) \<and>
   (x_c2::'b::len word) =
   smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
    x_c0 \<and>
   int (size x_c2) =
   (1::int) + (nm - (1::int) - (int (size x) - (1::int))) \<and>
   int (size x) - (1::int) \<le> nm - (1::int) \<and>
   int (size x) - (1::int) < int (size x_c0) \<and>
   (x_c1::'a::len word) =
   smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) x_c0 \<and>
   int (size x_c1) = (1::int) + (int (size x) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c0 = Word.Word c \<and> int (size x_c0) = nm \<longrightarrow>
   (x_c3 = x_c0) = (x_c2 = x_c4 \<and> x = x_c1)"
  by auto


named_theorems rewrite_bv_zero_extend_eq_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_2]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "NO_MATCH cvc_a (undefined x m c nm) \<Longrightarrow> (x_c4::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c4) = m \<and>
   (x_c3::'c::len word) = Word.cast x \<and>
   int (size x_c3) = int (size x) + m \<and>
   (0::int) \<le> m \<and>
   nm - (1::int) < int (size (x_c0::'c::len word)) \<and>
   (x_c2::'b::len word) =
   smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
    x_c0 \<and>
   int (size x_c2) =
   (1::int) + (nm - (1::int) - (int (size x) - (1::int))) \<and>
   int (size x) - (1::int) \<le> nm - (1::int) \<and>
   int (size x) - (1::int) < int (size x_c0) \<and>
   (x_c1::'a::len word) =
   smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) x_c0 \<and>
   int (size x_c1) = (1::int) + (int (size x) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c0 = Word.Word c \<and> int (size x_c0) = nm \<longrightarrow>
   (x_c0 = x_c3) = (x_c2 = x_c4 \<and> x = x_c1)"
  by auto


named_theorems rewrite_bv_zero_extend_ult_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_1]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "NO_MATCH cvc_a (undefined x m c nm) \<Longrightarrow> (x_c4::'b::len word) = Word.cast x \<and>
   int (size x_c4) = int (size x) + m \<and>
   (0::int) \<le> m \<and>
   (x_c3::'c::len word) = Word.Word (0::int) \<and>
   int (size x_c3) = m \<and>
   nm - (1::int) < int (size (x_c0::'b::len word)) \<and>
   (x_c2::'c::len word) =
   smt_extract (nat (nm - (1::int))) (nat (int (size x))) x_c0 \<and>
   int (size x_c2) = (1::int) + (nm - (1::int) - int (size x)) \<and>
   int (size x) \<le> nm - (1::int) \<and>
   (0::int) \<le> int (size x) \<and>
   int (size x) - (1::int) < int (size x_c0) \<and>
   (x_c1::'a::len word) =
   smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) x_c0 \<and>
   int (size x_c1) = (1::int) + (int (size x) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c0 = Word.Word c \<and> int (size x_c0) = nm \<longrightarrow>
   x_c2 = x_c3 \<longrightarrow> (x_c4 < x_c0) = (x < x_c1)"
  by auto


named_theorems rewrite_bv_zero_extend_ult_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_2]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "NO_MATCH cvc_a (undefined x m c nm) \<Longrightarrow> (x_c4::'b::len word) = Word.cast x \<and>
   int (size x_c4) = int (size x) + m \<and>
   (0::int) \<le> m \<and>
   (x_c3::'c::len word) = Word.Word (0::int) \<and>
   int (size x_c3) = m \<and>
   nm - (1::int) < int (size (x_c0::'b::len word)) \<and>
   (x_c2::'c::len word) =
   smt_extract (nat (nm - (1::int))) (nat (int (size x))) x_c0 \<and>
   int (size x_c2) = (1::int) + (nm - (1::int) - int (size x)) \<and>
   int (size x) \<le> nm - (1::int) \<and>
   (0::int) \<le> int (size x) \<and>
   int (size x) - (1::int) < int (size x_c0) \<and>
   (x_c1::'a::len word) =
   smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) x_c0 \<and>
   int (size x_c1) = (1::int) + (int (size x) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c0 = Word.Word c \<and> int (size x_c0) = nm \<longrightarrow>
   x_c2 = x_c3 \<longrightarrow> (x_c0 < x_c4) = (x_c1 < x)"
  by auto


named_theorems rewrite_bv_sign_extend_ult_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_1]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "NO_MATCH cvc_a (undefined x m c nm) \<Longrightarrow> (x_c8::'b::len word) = Word.signed_cast x \<and>
   int (size x_c8) = int (size x) + m \<and>
   (0::int) \<le> m \<and>
   (x_c7::'b::len word) =
   push_bit (unat (Word.Word (int (size x) - (1::int))))
    (x_c6::'b::len word) \<and>
   int (size x_c7) = int (size x_c6) \<and>
   x_c6 = not (x_c5::'b::len word) \<and>
   int (size (Word.Word (int (size x) - (1::int)))) = int (size x_c6) \<and>
   x_c5 = Word.Word (0::int) \<and>
   int (size x_c5) = nm \<and>
   (x_c4::'b::len word) =
   push_bit (unat (Word.Word (int (size x) - (1::int))))
    (x_c3::'b::len word) \<and>
   int (size x_c4) = int (size x_c3) \<and>
   x_c3 = (x_c2::'b::len word) \<and>
   int (size (Word.Word (int (size x) - (1::int)))) = int (size x_c3) \<and>
   x_c2 = Word.Word (1::int) \<and>
   int (size x_c2) = nm \<and>
   int (size x) - (1::int) < int (size (x_c0::'b::len word)) \<and>
   (x_c1::'a::len word) =
   smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) x_c0 \<and>
   int (size x_c1) = (1::int) + (int (size x) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c0 = Word.Word c \<and> int (size x_c0) = nm \<longrightarrow>
   x_c0 \<le> x_c4 \<or> x_c7 \<le> x_c0 \<longrightarrow>
   (x_c8 < x_c0) = (x < x_c1)"
  by auto


named_theorems rewrite_bv_sign_extend_ult_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_2]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "NO_MATCH cvc_a (undefined x m c nm) \<Longrightarrow> (x_c10::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c10) = (1::int) \<and>
   int (size x) - (1::int) < int (size x) \<and>
   (x_c9::'b::len word) =
   smt_extract (nat (int (size x) - (1::int)))
    (nat (int (size x) - (1::int))) x \<and>
   int (size x_c9) =
   (1::int) + (int (size x) - (1::int) - (int (size x) - (1::int))) \<and>
   int (size x) - (1::int) \<le> int (size x) - (1::int) \<and>
   (x_c8::'c::len word) = Word.signed_cast x \<and>
   int (size x_c8) = int (size x) + m \<and>
   (0::int) \<le> m \<and>
   (x_c7::'c::len word) =
   push_bit (unat (Word.Word (int (size x) - (1::int))))
    (x_c6::'c::len word) \<and>
   int (size x_c7) = int (size x_c6) \<and>
   x_c6 = not (x_c5::'c::len word) \<and>
   int (size (Word.Word (int (size x) - (1::int)))) = int (size x_c6) \<and>
   x_c5 = Word.Word (0::int) \<and>
   int (size x_c5) = nm \<and>
   (x_c4::'c::len word) =
   push_bit (unat (Word.Word (int (size x) - (1::int))))
    (x_c3::'c::len word) \<and>
   int (size x_c4) = int (size x_c3) \<and>
   x_c3 = (x_c2::'c::len word) \<and>
   int (size (Word.Word (int (size x) - (1::int)))) = int (size x_c3) \<and>
   x_c2 = Word.Word (1::int) \<and>
   int (size x_c2) = nm \<and>
   int (size x) - (1::int) < int (size (x_c0::'c::len word)) \<and>
   (x_c1::'h::len word) =
   smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) x_c0 \<and>
   int (size x_c1) = (1::int) + (int (size x) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c0 = Word.Word c \<and> int (size x_c0) = nm \<longrightarrow>
   x_c4 < x_c0 \<and> x_c0 \<le> x_c7 \<longrightarrow>
   (x_c8 < x_c0) = (x_c9 = x_c10)"
  by auto


named_theorems rewrite_bv_sign_extend_ult_const_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_3]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "NO_MATCH cvc_a (undefined x m c nm) \<Longrightarrow> (x_c8::'b::len word) = Word.signed_cast x \<and>
   int (size x_c8) = int (size x) + m \<and>
   (0::int) \<le> m \<and>
   (x_c7::'c::len word) =
   push_bit (unat (Word.Word (int (size x) - (1::int))))
    (x_c6::'c::len word) \<and>
   int (size x_c7) = int (size x_c6) \<and>
   x_c6 = not (x_c5::'c::len word) \<and>
   int (size (Word.Word (int (size x) - (1::int)))) = int (size x_c6) \<and>
   x_c5 = Word.Word (0::int) \<and>
   int (size x_c5) = nm \<and>
   (x_c4::'b::len word) =
   push_bit (unat (Word.Word (int (size x) - (1::int))))
    (x_c3::'b::len word) \<and>
   int (size x_c4) = int (size x_c3) \<and>
   x_c3 = (x_c2::'b::len word) \<and>
   int (size (Word.Word (int (size x) - (1::int)))) = int (size x_c3) \<and>
   x_c2 = Word.Word (1::int) \<and>
   int (size x_c2) = nm \<and>
   int (size x) - (1::int) < int (size (x_c0::'b::len word)) \<and>
   (x_c1::'a::len word) =
   smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) x_c0 \<and>
   int (size x_c1) = (1::int) + (int (size x) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c0 = Word.Word c \<and> int (size x_c0) = nm \<longrightarrow>
   x_c0 < x_c4 \<or> not x_c4 \<le> x_c0 \<longrightarrow>
   (x_c0 < x_c8) = (x_c1 < x)"
  by auto


named_theorems rewrite_bv_sign_extend_ult_const_4 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_4]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "NO_MATCH cvc_a (undefined x m c nm) \<Longrightarrow> (x_c10::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c10) = (1::int) \<and>
   int (size x) - (1::int) < int (size x) \<and>
   (x_c9::'b::len word) =
   smt_extract (nat (int (size x) - (1::int)))
    (nat (int (size x) - (1::int))) x \<and>
   int (size x_c9) =
   (1::int) + (int (size x) - (1::int) - (int (size x) - (1::int))) \<and>
   int (size x) - (1::int) \<le> int (size x) - (1::int) \<and>
   (x_c8::'c::len word) = Word.signed_cast x \<and>
   int (size x_c8) = int (size x) + m \<and>
   (0::int) \<le> m \<and>
   (x_c7::'c::len word) =
   push_bit (unat (Word.Word (int (size x) - (1::int))))
    (x_c6::'c::len word) \<and>
   int (size x_c7) = int (size x_c6) \<and>
   x_c6 = not (x_c5::'c::len word) \<and>
   int (size (Word.Word (int (size x) - (1::int)))) = int (size x_c6) \<and>
   x_c5 = Word.Word (0::int) \<and>
   int (size x_c5) = nm \<and>
   (x_c4::'c::len word) =
   push_bit (unat (Word.Word (int (size x) - (1::int))))
    (x_c3::'c::len word) \<and>
   int (size x_c4) = int (size x_c3) \<and>
   x_c3 = (x_c2::'c::len word) \<and>
   int (size (Word.Word (int (size x) - (1::int)))) = int (size x_c3) \<and>
   x_c2 = Word.Word (1::int) \<and>
   int (size x_c2) = nm \<and>
   int (size x) - (1::int) < int (size (x_c0::'c::len word)) \<and>
   (x_c1::'h::len word) =
   smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) x_c0 \<and>
   int (size x_c1) = (1::int) + (int (size x) - (1::int) - (0::int)) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   x_c0 = Word.Word c \<and> int (size x_c0) = nm \<longrightarrow>
   not x_c7 \<le> x_c0 \<and> x_c0 \<le> not x_c4 \<longrightarrow>
   (x_c0 < x_c8) = (x_c9 = x_c10)"
  by auto


named_theorems rewrite_bv_extract_bitwise_and \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_and]:
  fixes x::"'a::len word" and y::"'a::len word" and i::"int" and j::"int"
  shows "NO_MATCH cvc_a (undefined x y i j) \<Longrightarrow> j < int (size y) \<and>
   (x_c2::'b::len word) = smt_extract (nat j) (nat i) y \<and>
   int (size x_c2) = (1::int) + (j - i) \<and>
   j < int (size x) \<and>
   (x_c1::'b::len word) = smt_extract (nat j) (nat i) x \<and>
   int (size x_c1) = (1::int) + (j - i) \<and>
   j < int (size (and x y)) \<and>
   (x_c0::'b::len word) = smt_extract (nat j) (nat i) (and x y) \<and>
   int (size x_c0) = (1::int) + (j - i) \<and>
   i \<le> j \<and> (0::int) \<le> i \<longrightarrow>
   x_c0 = and x_c1 x_c2"
  by auto


named_theorems rewrite_bv_extract_bitwise_or \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_or]:
  fixes x::"'a::len word" and y::"'a::len word" and i::"int" and j::"int"
  shows "NO_MATCH cvc_a (undefined x y i j) \<Longrightarrow> j < int (size y) \<and>
   (x_c2::'b::len word) = smt_extract (nat j) (nat i) y \<and>
   int (size x_c2) = (1::int) + (j - i) \<and>
   j < int (size x) \<and>
   (x_c1::'b::len word) = smt_extract (nat j) (nat i) x \<and>
   int (size x_c1) = (1::int) + (j - i) \<and>
   j < int (size (or x y)) \<and>
   (x_c0::'b::len word) = smt_extract (nat j) (nat i) (or x y) \<and>
   int (size x_c0) = (1::int) + (j - i) \<and>
   i \<le> j \<and> (0::int) \<le> i \<longrightarrow>
   x_c0 = or x_c1 x_c2"
  by auto


named_theorems rewrite_bv_extract_bitwise_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_xor]:
  fixes x::"'a::len word" and y::"'a::len word" and i::"int" and j::"int"
  shows "NO_MATCH cvc_a (undefined x y i j) \<Longrightarrow> j < int (size y) \<and>
   (x_c2::'b::len word) = smt_extract (nat j) (nat i) y \<and>
   int (size x_c2) = (1::int) + (j - i) \<and>
   j < int (size x) \<and>
   (x_c1::'b::len word) = smt_extract (nat j) (nat i) x \<and>
   int (size x_c1) = (1::int) + (j - i) \<and>
   j < int (size (semiring_bit_operations_class.xor x y)) \<and>
   (x_c0::'b::len word) =
   smt_extract (nat j) (nat i)
    (semiring_bit_operations_class.xor x y) \<and>
   int (size x_c0) = (1::int) + (j - i) \<and>
   i \<le> j \<and> (0::int) \<le> i \<longrightarrow>
   x_c0 = semiring_bit_operations_class.xor x_c1 x_c2"
  by auto


named_theorems rewrite_bv_extract_not \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_not]:
  fixes x::"'a::len word" and i::"int" and j::"int"
  shows "NO_MATCH cvc_a (undefined x i j) \<Longrightarrow> j < int (size x) \<and>
   (x_c1::'b::len word) = smt_extract (nat j) (nat i) x \<and>
   int (size x_c1) = (1::int) + (j - i) \<and>
   j < int (size (not x)) \<and>
   (x_c0::'b::len word) = smt_extract (nat j) (nat i) (not x) \<and>
   int (size x_c0) = (1::int) + (j - i) \<and>
   i \<le> j \<and> (0::int) \<le> i \<longrightarrow>
   x_c0 = not x_c1"
  apply simp
  apply rule+
   apply (simp only: word_uint_eq_iff)
  apply (subst uint_smt_extract)
     apply simp_all
  using nat_mono apply blast
  apply (meson nat_less_iff order_trans)
  apply (metis Suc_diff_le Suc_nat_eq_nat_zadd1 diff_ge_0_iff_ge nat_diff_distrib nat_int nat_mono word_size)
  apply (subst unsigned_not_eq)
  apply (subst unsigned_not_eq)
  apply (subst uint_smt_extract)
  using nat_mono apply presburger
     apply (metis nat_int word_size_gt_0 zless_nat_conj)
     apply (metis Suc_diff_le Suc_eq_plus1 Suc_nat_eq_nat_zadd1 diff_ge_0_iff_ge nat_diff_distrib nat_int nat_mono word_size)
  apply (subst take_bit_take_bit)
  apply (subst (2) drop_bit_take_bit)
  using bin_trunc_not[of "LENGTH('b)"]
  by (smt (verit, best) BV_Rewrites_Lemmas.rewrite_bv_extract_not add.commute drop_bit_take_bit int_Suc nat_0_le nat_int.Rep_inverse' nat_le_eq_zle nat_less_iff nat_minus_as_int plus_1_eq_Suc size_word.rep_eq take_bit_take_bit uint_smt_extract unsigned_not_eq)

named_theorems rewrite_bv_extract_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_1]:
  fixes x::"'a::len word" and low::"int" and high::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined x low high k) \<Longrightarrow> high < int (size x) \<and>
   (x_c2::'b::len word) = smt_extract (nat high) (nat low) x \<and>
   int (size x_c2) = (1::int) + (high - low) \<and>
   high < int (size (x_c0::'c::len word)) \<and>
   (x_c1::'b::len word) = smt_extract (nat high) (nat low) x_c0 \<and>
   int (size x_c1) = (1::int) + (high - low) \<and>
   low \<le> high \<and>
   (0::int) \<le> low \<and>
   x_c0 = Word.signed_cast x \<and>
   int (size x_c0) = int (size x) + k \<and>
   (0::int) \<le> k \<longrightarrow>
   high < int (size x) \<longrightarrow> x_c1 = x_c2"
  apply simp
  apply rule+
  apply (subst word_eq_iff_signed)
  unfolding smt_extract_def
  oops

named_theorems rewrite_bv_extract_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_2]:
  fixes x::"'a::len word" and low::"int" and high::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined x low high k) \<Longrightarrow> (x_c3::'b::len word) = Word.signed_cast (x_c2::'c::len word) \<and>
   int (size x_c3) =
   int (size x_c2) + ((1::int) + (high - int (size x))) \<and>
   (0::int) \<le> (1::int) + (high - int (size x)) \<and>
   int (size x) - (1::int) < int (size x) \<and>
   x_c2 = smt_extract (nat (int (size x) - (1::int))) (nat low) x \<and>
   int (size x_c2) = (1::int) + (int (size x) - (1::int) - low) \<and>
   low \<le> int (size x) - (1::int) \<and>
   high < int (size (x_c0::'d::len word)) \<and>
   (x_c1::'b::len word) = smt_extract (nat high) (nat low) x_c0 \<and>
   int (size x_c1) = (1::int) + (high - low) \<and>
   low \<le> high \<and>
   (0::int) \<le> low \<and>
   x_c0 = Word.signed_cast x \<and>
   int (size x_c0) = int (size x) + k \<and>
   (0::int) \<le> k \<longrightarrow>
   low < int (size x) \<and> int (size x) \<le> high \<longrightarrow>
   x_c1 = x_c3"
  by auto


named_theorems rewrite_bv_extract_sign_extend_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_3]:
  fixes x::"'a::len word" and low::"int" and high::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined x low high k) \<Longrightarrow> (x_c3::'b::len word) =
   smt_repeat (nat ((1::int) + (high - low))) (x_c2::'c::len word) \<and>
   int (size x_c3) = int (size x_c2) * ((1::int) + (high - low)) \<and>
   (0::int) \<le> (1::int) + (high - low) \<and>
   int (size x) - (1::int) < int (size x) \<and>
   x_c2 =
   smt_extract (nat (int (size x) - (1::int)))
    (nat (int (size x) - (1::int))) x \<and>
   int (size x_c2) =
   (1::int) + (int (size x) - (1::int) - (int (size x) - (1::int))) \<and>
   int (size x) - (1::int) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> int (size x) - (1::int) \<and>
   high < int (size (x_c0::'d::len word)) \<and>
   (x_c1::'b::len word) = smt_extract (nat high) (nat low) x_c0 \<and>
   int (size x_c1) = (1::int) + (high - low) \<and>
   low \<le> high \<and>
   (0::int) \<le> low \<and>
   x_c0 = Word.signed_cast x \<and>
   int (size x_c0) = int (size x) + k \<and>
   (0::int) \<le> k \<longrightarrow>
   int (size x) \<le> low \<longrightarrow> x_c1 = x_c3"
  by auto


named_theorems rewrite_bv_neg_mult \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_mult]:
  fixes xs::"'a::len word" and ys::"'a::len word" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined xs ys n m) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (- n) \<and>
   int (size x_c1) = m \<and>
   (x_c0::'a::len word) = Word.Word n \<and>
   int (size x_c0) = m \<longrightarrow>
   - (xs * x_c0 * ys) = xs * x_c1 * ys"
  by auto


named_theorems rewrite_bv_neg_sub \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_sub]:
  fixes x::"'a::{minus,uminus}" and y::"'a::{minus,uminus}"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> - (x - y) = y - x"
  by auto


named_theorems rewrite_bv_neg_add \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_add]:
  fixes x::"'a::{plus,uminus}" and y::"'a::{plus,uminus}" and zs::"'a::{plus,uminus} cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined x y zs) \<Longrightarrow> - (x + cvc_list_right (+) y zs) = - x + - cvc_list_right (+) y zs"
  apply (cases zs)
  subgoal for zss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss arbitrary: zs)
    apply simp_all
    apply (simp_all add: cvc_rewrites_fold)
    by (simp_all add: bv_neg_add_lemma)
  done


named_theorems rewrite_bv_mult_distrib_const_neg \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_neg]:
  fixes x::"'a::len word" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (- n) \<and>
   int (size x_c1) = m \<and>
   (x_c0::'a::len word) = Word.Word n \<and>
   int (size x_c0) = m \<longrightarrow>
   - x * x_c0 = x * x_c1"
  by auto


named_theorems rewrite_bv_mult_distrib_const_add \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_add]:
  fixes x::"'a::len word" and y::"'a::len word" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x y n m) \<Longrightarrow> (x_c0::'a::len word) = Word.Word n \<and>
   int (size x_c0) = m \<longrightarrow>
   (x + y) * x_c0 = x * x_c0 + y * x_c0"
  by (simp add: mult.commute ring_class.ring_distribs(1))


named_theorems rewrite_bv_mult_distrib_const_sub \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_sub]:
  fixes x::"'a::len word" and y::"'a::len word" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x y n m) \<Longrightarrow> (x_c0::'a::len word) = Word.Word n \<and>
   int (size x_c0) = m \<longrightarrow>
   (x - y) * x_c0 = x * x_c0 - y * x_c0"
  by auto


named_theorems rewrite_bv_mult_distrib_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_1]:
  fixes x1::"'a::{plus,times}" and x2::"'a::{plus,times}" and y::"'a::{plus,times}"
  shows "NO_MATCH cvc_a (undefined x1 x2 y) \<Longrightarrow> (x1 + x2) * y = x1 * y + x2 * y"
  by auto


named_theorems rewrite_bv_mult_distrib_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_2]:
  fixes x1::"'a::{plus,times}" and x2::"'a::{plus,times}" and y::"'a::{plus,times}"
  shows "NO_MATCH cvc_a (undefined x1 x2 y) \<Longrightarrow> y * (x1 + x2) = y * x1 + y * x2"
  by auto


named_theorems rewrite_bv_not_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_not_xor]:
  fixes x::"'a::ring_bit_operations" and xs::"'a::ring_bit_operations cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined x xs) \<Longrightarrow> not (cvc_list_right semiring_bit_operations_class.xor x xs) =
   cvc_list_right semiring_bit_operations_class.xor (not x) xs"
  apply (cases xs)
  subgoal for xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction xss arbitrary: xs)
    apply simp_all
    apply (simp_all add: cvc_rewrites_fold)
    by (simp_all add: bv_not_xor_lemma)
  done


named_theorems rewrite_bv_and_simplify_1 \<open>automatically_generated\<close>

lemma rewrite_bv_and_simplify_1_h1:" (and (and (foldr and xss x) t) x) = (and (foldr and xss x) t)"
  apply (induction xss)
   apply simp
  apply (metis and.commute and.left_idem)
  by (simp add: and.assoc)


lemma [rewrite_bv_and_simplify_1]:
  fixes xs::"'a::semiring_bit_operations cvc_ListVar" and ys::"'a::semiring_bit_operations cvc_ListVar" and zs::"'a::semiring_bit_operations cvc_ListVar" and x::"'a::semiring_bit_operations"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow>
 xs = ListVar xss \<and> xss \<noteq> [] \<longrightarrow>
   ys = ListVar yss \<and> yss \<noteq> [] \<longrightarrow>
   zs = ListVar zss \<and> zss \<noteq> [] \<longrightarrow>
 cvc_list_right and
    (and (cvc_list_right and (cvc_list_left and xs x) ys) x) zs =
   cvc_list_right and (cvc_list_right and (cvc_list_left and xs x) ys) zs"
  apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
  apply rule+
  using rewrite_bv_and_simplify_1_h1
  by metis


named_theorems rewrite_bv_and_simplify_2 \<open>automatically_generated\<close>

lemma rewrite_bv_and_simplify_2_h1:
"and (and (and (foldr and xss x)  q) (not x)) r =  (0::'a::len word)"
  by (metis and_and_not rewrite_bv_and_simplify_1_h1 word_and_le2 word_coorder.extremum_uniqueI)



lemma [rewrite_bv_and_simplify_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   xs = ListVar xss \<and> xss \<noteq> [] \<longrightarrow>
   ys = ListVar yss \<and> yss \<noteq> [] \<longrightarrow>
   zs = ListVar zss \<and> zss \<noteq> [] \<longrightarrow>
   cvc_list_right and
    (and (cvc_list_right and (cvc_list_left and xs x) ys) (not x)) zs =
   x_c0"
  apply simp
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
  using rewrite_bv_and_simplify_2_h1
  by blast


named_theorems rewrite_bv_or_simplify_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_or_simplify_1]:
  fixes xs::"'a::semiring_bit_operations cvc_ListVar" and ys::"'a::semiring_bit_operations cvc_ListVar" and zs::"'a::semiring_bit_operations cvc_ListVar" and x::"'a::semiring_bit_operations"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> cvc_list_right or (or (cvc_list_right or (cvc_list_left or xs x) ys) x)
    zs =
   cvc_list_right or (cvc_list_right or (cvc_list_left or xs x) ys) zs"
   apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (simp add: or.commute)
    apply (induction yss arbitrary: ys)
     apply simp_all
  apply (simp add: or.semigroup_axioms semigroup.assoc)
    apply (induction zss arbitrary: zs)
     apply simp_all
     apply (simp add: or.semigroup_axioms semigroup.assoc)
    by (simp add: or.assoc)
  done

named_theorems rewrite_bv_or_simplify_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_or_simplify_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   cvc_list_right or
    (or (cvc_list_right or (cvc_list_left or xs x) ys) (not x)) zs =
   not x_c0"
   apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (metis bit.disj_ac(1) bit.disj_ac(2) bit.disj_cancel_right bit.disj_one_left)
    apply (simp add: or.commute)
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (metis bit.disj_one_right word_bw_lcs(2))
  apply (simp add: or.semigroup_axioms semigroup.assoc)
    apply (induction zss arbitrary: zs)
     apply simp_all
     apply (metis (no_types, opaque_lifting) bit.disj_ac(2) bit.disj_left_commute bit.disj_one_right)
    by (metis (no_types, opaque_lifting) or.commute or.left_commute word_or_max)
  done


named_theorems rewrite_bv_xor_simplify_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_simplify_1]:
  fixes xs::"'a::semiring_bit_operations cvc_ListVar" and ys::"'a::semiring_bit_operations cvc_ListVar" and zs::"'a::semiring_bit_operations cvc_ListVar" and x::"'a::semiring_bit_operations"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> cvc_list_right semiring_bit_operations_class.xor
    (semiring_bit_operations_class.xor
      (cvc_list_right semiring_bit_operations_class.xor
        (cvc_list_left semiring_bit_operations_class.xor xs x) ys)
      x)
    zs =
   cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_both semiring_bit_operations_class.xor
      (0::'a::semiring_bit_operations) xs ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (metis (no_types, opaque_lifting) xor.assoc xor.left_neutral xor_self_eq)
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (simp add: xor.commute xor.left_commute)
    apply (induction zss arbitrary: zs)
     apply simp_all
    apply (simp add: xor.commute xor.left_commute)
    apply (metis xor.left_commute)
        by (simp add: semigroup.assoc xor.semigroup_axioms)
  done


named_theorems rewrite_bv_xor_simplify_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_simplify_2]:
  fixes xs::"'a::ring_bit_operations cvc_ListVar" and ys::"'a::ring_bit_operations cvc_ListVar" and zs::"'a::ring_bit_operations cvc_ListVar" and x::"'a::ring_bit_operations"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> cvc_list_right semiring_bit_operations_class.xor
    (semiring_bit_operations_class.xor
      (cvc_list_right semiring_bit_operations_class.xor
        (cvc_list_left semiring_bit_operations_class.xor xs x) ys)
      (not x))
    zs =
   not (cvc_list_right semiring_bit_operations_class.xor
         (cvc_list_both semiring_bit_operations_class.xor
           (0::'a::ring_bit_operations) xs ys)
         zs)"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (metis (no_types, opaque_lifting) xor.assoc xor.left_neutral xor_self_eq)
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (simp add: xor.commute xor.left_commute)
    apply (induction zss arbitrary: zs)
     apply simp_all
    apply (simp add: xor.commute xor.left_commute)
    apply (metis xor.left_commute)
        by (simp add: semigroup.assoc xor.semigroup_axioms)
  done


named_theorems rewrite_bv_xor_simplify_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_simplify_3]:
  fixes xs::"'a::ring_bit_operations cvc_ListVar" and ys::"'a::ring_bit_operations cvc_ListVar" and zs::"'a::ring_bit_operations cvc_ListVar" and x::"'a::ring_bit_operations"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> cvc_list_right semiring_bit_operations_class.xor
    (semiring_bit_operations_class.xor
      (cvc_list_right semiring_bit_operations_class.xor
        (cvc_list_left semiring_bit_operations_class.xor xs (not x)) ys)
      x)
    zs =
   not (cvc_list_right semiring_bit_operations_class.xor
         (cvc_list_both semiring_bit_operations_class.xor
           (0::'a::ring_bit_operations) xs ys)
         zs)"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (metis (no_types, opaque_lifting) xor.assoc xor.left_neutral xor_self_eq)
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (simp add: xor.commute xor.left_commute)
    apply (induction zss arbitrary: zs)
     apply simp_all
    apply (simp add: xor.commute xor.left_commute)
     apply (metis bit.xor_compl_right bit.xor_left_commute)
    by (simp add: semigroup.assoc xor.semigroup_axioms)
  done

named_theorems rewrite_bv_commutative_and \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_and]:
  fixes x::"'a::semiring_bit_operations" and y::"'a::semiring_bit_operations"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> and x y = and y x"
  by (simp add: and.commute)


named_theorems rewrite_bv_commutative_or \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_or]:
  fixes x::"'a::semiring_bit_operations" and y::"'a::semiring_bit_operations"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> or x y = or y x"
    by (simp add: or.commute)


named_theorems rewrite_bv_commutative_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_xor]:
  fixes x::"'a::semiring_bit_operations" and y::"'a::semiring_bit_operations"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> semiring_bit_operations_class.xor x y =
   semiring_bit_operations_class.xor y x"
  by (simp add: xor.commute)



named_theorems rewrite_bv_commutative_mul \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_mul]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> x * y = y * x"
  by auto


named_theorems rewrite_bv_or_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_or_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   or x x_c0 = x"
  by auto

named_theorems rewrite_bv_zero_extend_eliminate_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate_0]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.cast x \<and>
   int (size x_c0) = int (size x) + (0::int) \<and>
   (0::int) \<le> (0::int) \<longrightarrow>
   x_c0 = x"
  by auto


named_theorems rewrite_bv_sign_extend_eliminate_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eliminate_0]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.signed_cast x \<and>
   int (size x_c0) = int (size x) + (0::int) \<and>
   (0::int) \<le> (0::int) \<longrightarrow>
   x_c0 = x"
  by auto


named_theorems rewrite_bv_not_neq \<open>automatically_generated\<close>

lemma [rewrite_bv_not_neq]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (0::int) < int (size x) \<longrightarrow> (x = not x) = False"
  by (metis lsb0)


named_theorems rewrite_bv_ult_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_ones]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow> (x < y) = (x \<noteq> y)"
  by (simp add: word_order.not_eq_extremum)


named_theorems rewrite_bv_or_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_or_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right or (cvc_list_left or xs (cvc_list_right or s ys)) zs =
   cvc_list_right or (cvc_list_right or (cvc_list_left or xs s) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss arbitrary: zs)
     apply simp_all
    apply (induction yss arbitrary: ys)
    apply simp_all
    apply (induction xss arbitrary: xs)
      apply simp_all
    apply (metis (no_types, opaque_lifting) cvc_list_left_Nil cvc_list_left_transfer or.assoc or.right_neutral)
    apply (simp_all add: cvc_rewrites_fold)
    by (simp add: or.left_commute)
  done


named_theorems rewrite_bv_xor_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_flatten]:
  fixes xs::"'a::semiring_bit_operations cvc_ListVar" and s::"'a::semiring_bit_operations" and ys::"'a::semiring_bit_operations cvc_ListVar" and zs::"'a::semiring_bit_operations cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_left semiring_bit_operations_class.xor xs
      (cvc_list_right semiring_bit_operations_class.xor s ys))
    zs =
   cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_right semiring_bit_operations_class.xor
      (cvc_list_left semiring_bit_operations_class.xor xs s) ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss arbitrary: zs)
    apply simp_all
    apply (induction yss arbitrary: ys)
    apply simp_all
    apply (induction xss arbitrary: xs)
    apply simp_all
     apply (simp_all add: cvc_rewrites_fold)
     apply (metis (no_types, opaque_lifting) fold_simps(1) rev.simps(1) xor.assoc xor.right_neutral)
    by (simp add: xor.left_commute)
  done


named_theorems rewrite_bv_and_flatten \<open>automatically_generated\<close>

lemma rewrite_bv_and_flatten_h2: 
"xss \<noteq> [] \<Longrightarrow> and (foldr and xss (and s t1)) t2 = and (and (foldr and xss s) t1) t2"
  apply (induction xss)
   apply simp_all
  by (metis (no_types, opaque_lifting) and.commute and.left_commute eq_id_iff foldr_Nil)


lemma [rewrite_bv_and_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows " xs = ListVar xss \<and> xss \<noteq> [] \<Longrightarrow>
   ys = ListVar yss \<and> yss \<noteq> [] \<Longrightarrow>
   zs = ListVar zss \<and> zss \<noteq> [] \<Longrightarrow>
   NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right and (cvc_list_left and xs (cvc_list_right and s ys)) zs =
   cvc_list_right and (cvc_list_right and (cvc_list_left and xs s) ys) zs"
  apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
  using rewrite_bv_and_flatten_h2[of xss "(foldr and (butlast yss) (last yss))" "(foldr and (butlast zss) (last zss))"]
  using rewrite_bv_and_flatten_h2 by blast

named_theorems rewrite_bv_mul_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_mul_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right (*) (cvc_list_left (*) xs (cvc_list_right (*) s ys)) zs =
   cvc_list_right (*) (cvc_list_right (*) (cvc_list_left (*) xs s) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss arbitrary: zs)
    apply simp_all
    apply (induction yss arbitrary: ys)
    apply simp_all
    apply (induction xss arbitrary: xs)
      apply simp_all
     apply (metis (no_types, opaque_lifting) mult.assoc mult.right_neutral prod_list.Nil prod_list.eq_foldr)
    by (simp add: mult.left_commute)
  done

end