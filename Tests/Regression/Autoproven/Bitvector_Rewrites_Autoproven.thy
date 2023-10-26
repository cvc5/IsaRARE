theory Bitvector_Rewrites_Autoproven
  imports "HOL-CVC.Dsl_Nary_Ops" HOL.SMT "Word_Lib.Signed_Division_Word" "Word_Lib.Reversed_Bit_Lists"
  "HOL-Library.Word" Word_Lib.More_Word "HOL-Library.Log_Nat" "HOL-CVC.SMT_Word"

begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)


named_theorems rewrite_bv_ugt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y < x) = (y < x)"
  by auto

named_theorems rewrite_bv_uge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_uge_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
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
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   smt_redor x = not (smt_comp x x_c0)"
  using smt_redor_def by auto

named_theorems rewrite_bv_redand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redand_eliminate]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   smt_redand x = smt_comp x (not x_c0)"
   using smt_redand_def by auto

named_theorems rewrite_bv_ule_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<le> y) = (\<not> y < x)"
  using word_not_le by blast

named_theorems rewrite_bv_comp_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_comp_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c1::1 word) = Word.Word (0::int) \<and>
   int (size x_c1) = (1::int) \<and>
   (x_c0::1 word) = Word.Word (1::int) \<and>
   int (size x_c0) = (1::int) \<longrightarrow>
   smt_comp x y = (if x = y then x_c0 else x_c1)"
  by (metis one_word_def smt_comp_def zero_word_def)


named_theorems rewrite_bv_repeat_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_2]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = smt_repeat (nat (1::int)) x \<and>
   int (size x_c0) = int (size x) * (1::int) \<and>
   (0::int) \<le> (1::int) \<longrightarrow>
   x_c0 = x"
      unfolding smt_repeat_def word_repeat_def replicate_nat_def
  by (simp add: size_word.rep_eq the_equality word_eq_unatI)

named_theorems rewrite_bv_nand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nand_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> not (and x y) = not (and x y)"
    apply ((rule impI)+)? 
  by auto

named_theorems rewrite_bv_nor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nor_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> not (or x y) = not (or x y)"
  by auto

named_theorems rewrite_bv_xnor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_xnor_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> not (semiring_bit_operations_class.xor x y) =
   not (semiring_bit_operations_class.xor x y)"
  by auto

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
  by (metis (mono_tags, opaque_lifting) One_nat_def bit.compl_zero bot_nat_0.not_eq_extremum cancel_comm_monoid_add_class.diff_cancel decr_length_less_iff len_num1 lt1_neq0 not_bit_minus_numeral_Bit0_0 not_one_eq one_word_def test_bit_over word_exists_nth word_not_not word_order.extremum_uniqueI word_size zero_word_def)

named_theorems rewrite_bv_ite_const_children_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_2]:
  fixes c::"1 word"
  shows "NO_MATCH cvc_a (undefined c) \<Longrightarrow> (x_c1::1 word) = Word.Word (0::int) \<and>
   int (size x_c1) = (1::int) \<and>
   (x_c0::1 word) = Word.Word (1::int) \<and>
   int (size x_c0) = (1::int) \<longrightarrow>
   (if bit c (0::nat) then x_c0 else x_c1) = c"
  by (metis bit.compl_zero bit_imp_le_length len_num1 less_one lt1_neq0 not_bit_minus_numeral_Bit0_0 not_one_eq one_word.abs_eq word_exists_nth word_not_not word_order.extremum_uniqueI zero_word.abs_eq)


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
  by (simp add: bit_and_iff)


named_theorems rewrite_bv_ite_merge_else_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_else]:
  fixes c0::"1 word" and c1::"1 word" and t1::"'a::len word" and t0::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t1 t0) \<Longrightarrow> (if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t1 else t0) =
   (if bit (and (not c0) c1) (0::nat) then t1 else t0)"
   by (simp add: lsb0)

named_theorems rewrite_bv_shl_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_0]:
  fixes x::"'a::len word" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x sz) \<Longrightarrow> (x_c2::'a::len word) =
   push_bit (unat (x_c0::'b::len word)) (x_c1::'a::len word) \<and>
   int (size x_c2) = int (size x_c1) \<and>
   x_c1 = x \<and>
   int (size x_c0) = int (size x_c1) \<and>
   x_c0 = Word.Word (0::int) \<and> int (size x_c0) = sz \<longrightarrow>
   x_c2 = x"
  by auto

named_theorems rewrite_bv_lshr_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_0]:
  fixes x::"'a::len word" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x sz) \<Longrightarrow> (x_c2::'a::len word) =
   drop_bit (unat (x_c0::'b::len word)) (x_c1::'a::len word) \<and>
   int (size x_c2) = int (size x_c1) \<and>
   x_c1 = x \<and>
   int (size x_c0) = int (size x_c1) \<and>
   x_c0 = Word.Word (0::int) \<and> int (size x_c0) = sz \<longrightarrow>
   x_c2 = x"
  by auto

named_theorems rewrite_bv_bitwise_idemp_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_idemp_1]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> and x x = x"
  by auto


named_theorems rewrite_bv_bitwise_idemp_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_idemp_2]:
  fixes x::"'a::len word"
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
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> not (not x) = x"
  by auto

named_theorems rewrite_bv_ult_zero_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_1]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x_c0 < x) = (x \<noteq> x_c0)"
  using word_gt_0 by auto


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
  by auto

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

named_theorems rewrite_bv_udiv_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   smt_udiv x x_c0 = not x_c0"
  by (metis bit.compl_zero mask_full smt_udiv_def unsigned_0 word_size zero_word.abs_eq)

named_theorems rewrite_bv_udiv_one \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_one]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (1::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   smt_udiv x x_c0 = x"
  by (metis bits_div_by_1 one_word_def smt_udiv_def unsigned_1 zero_neq_one)

named_theorems rewrite_bv_urem_one \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_one]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = n \<and>
   (x_c0::'a::len word) = Word.Word (1::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   smt_urem x x_c0 = x_c1"
  by (metis Abs_fnat_hom_0 bits_mod_by_1 one_word.abs_eq smt_urem_def unat_1 unsigned_eq_0_iff zero_word.abs_eq)



named_theorems rewrite_bv_urem_self \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_self]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   smt_urem x x = x_c0"
  by (metis Abs_fnat_hom_0 mod_self smt_urem_def unat_eq_zero zero_word_def)

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
  by (metis mod_by_0 not_less_iff_gr_or_eq uint_smt_urem(2) unat_0 word_arith_nat_mod word_gt_a_gt_0 word_mod_less_divisor word_unat.Rep_inverse' zero_word.abs_eq)

named_theorems rewrite_bv_ult_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_one]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = n \<and>
   (x_c0::'a::len word) = Word.Word (1::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x < x_c0) = (x = x_c1)"
  by auto

named_theorems rewrite_bv_mult_distrib_const_neg \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_neg]:
  fixes x::"'a::len word" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (- n) \<and>
   int (size x_c1) = m \<and>
   (x_c0::'a::len word) = Word.Word n \<and>
   int (size x_c0) = m \<longrightarrow>
   - x * x_c0 = x * x_c1"
  by auto


named_theorems rewrite_bv_commutative_and \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_and]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> and x y = and y x"
  by (simp add: word_bw_comms(1))

named_theorems rewrite_bv_commutative_or \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_or]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> or x y = or y x"
  using word_bw_comms(2) by auto

named_theorems rewrite_bv_commutative_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_xor]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> semiring_bit_operations_class.xor x y =
   semiring_bit_operations_class.xor y x"
    by (simp add: word_bw_comms(3))


named_theorems rewrite_bv_commutative_mul \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_mul]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> x * y = y * x"
    by simp


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
  by (metis and_and_not mask_eq_x_eq_0 zero_neq_one)

named_theorems rewrite_bv_ult_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_ones]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow> (x < y) = (x \<noteq> y)"
    using word_order.not_eq_extremum by auto

end