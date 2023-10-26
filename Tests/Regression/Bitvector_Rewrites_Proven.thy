theory Bitvector_Rewrites_Proven
  imports "HOL-CVC.Dsl_Nary_Ops" Bitvector_Rewrites2
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_bv_concat_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_flatten]:
  fixes xs::"bool list cvc_ListVar" and s::"'a::len word" and ys::"bool list cvc_ListVar" and zs::"bool list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> int (size (x_c7::'b::len word)) =
   int (size s) + int (size (x_c6::'c::len word)) \<and>
   x_c7 = word_cat s x_c6 \<and>
   x_c6 = word_cat (x_c1::'d::len word) (x_c3::'e::len word) \<and>
   int (size x_c6) = int (size x_c1) + int (size x_c3) \<and>
   (x_c8::'f::len word) = word_cat (x_c0::'g::len word) x_c7 \<and>
   int (size x_c8) = int (size x_c0) + int (size x_c7) \<and>
   x_c0 = concat_smt2 xs \<and>
   (0::int) < int (size xs) \<and>
   list_length_0' xs \<and>
   int (size xs) = temp_sum_length xs \<and>
   int (size (x_c4::'h::len word)) =
   int (size (x_c2::'i::len word)) + int (size x_c3) \<and>
   x_c4 = word_cat x_c2 x_c3 \<and>
   int (size zs) = temp_sum_length zs \<and>
   list_length_0' zs \<and>
   (0::int) < int (size zs) \<and>
   x_c3 = concat_smt2 zs \<and>
   int (size x_c2) = int (size s) + int (size x_c1) \<and>
   x_c2 = word_cat s x_c1 \<and>
   int (size ys) = temp_sum_length ys \<and>
   list_length_0' ys \<and>
   (0::int) < int (size ys) \<and>
   x_c1 = concat_smt2 ys \<and>
   (x_c5::'f::len word) = word_cat x_c0 x_c4 \<and>
   int (size x_c5) = int (size x_c0) + int (size x_c4) \<longrightarrow>
   x_c5 = x_c8"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_concat_flatten_lemma[of cvc_a xs s ys zs ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

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
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_extract_extract_lemma[of cvc_a x i j k l ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_extract_whole \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_whole]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> n < int (size x) \<and>
   (x_c0::'a::len word) = smt_extract (nat n) (nat (0::int)) x \<and>
   int (size x_c0) = (1::int) + (n - (0::int)) \<and>
   (0::int) \<le> n \<and> (0::int) \<le> (0::int) \<longrightarrow>
   int (size x) - (1::int) \<le> n \<longrightarrow> x_c0 = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_extract_whole_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ugt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y < x) = (y < x)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ugt_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_uge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_uge_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y \<le> x) = (y \<le> x)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_uge_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_sgt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sgt_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y <s x) = (y <s x)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_sgt_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_sge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sge_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y \<le>s x) = (y \<le>s x)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_sge_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_sle_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<le>s y) = (\<not> y <s x)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_sle_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_redor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redor_eliminate]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   smt_redor x = not (smt_comp x x_c0)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_redor_eliminate_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_redand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redand_eliminate]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   smt_redand x = smt_comp x (not x_c0)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_redand_eliminate_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ule_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<le> y) = (\<not> y < x)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ule_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_comp_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_comp_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c1::1 word) = Word.Word (0::int) \<and>
   int (size x_c1) = (1::int) \<and>
   (x_c0::1 word) = Word.Word (1::int) \<and>
   int (size x_c0) = (1::int) \<longrightarrow>
   smt_comp x y = (if x = y then x_c0 else x_c1)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_comp_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_repeat_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_1]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c1::'b::len word) = smt_repeat (nat (n - (1::int))) x \<and>
   int (size x_c1) = int (size x) * (n - (1::int)) \<and>
   (0::int) \<le> n - (1::int) \<and>
   (x_c2::'c::len word) = word_cat x x_c1 \<and>
   int (size x_c2) = int (size x) + int (size x_c1) \<and>
   (x_c0::'c::len word) = smt_repeat (nat n) x \<and>
   int (size x_c0) = int (size x) * n \<and>
   (0::int) \<le> n \<longrightarrow>
   (1::int) < n \<longrightarrow> x_c0 = x_c2"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_repeat_eliminate_1_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_repeat_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_2]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = smt_repeat (nat (1::int)) x \<and>
   int (size x_c0) = int (size x) * (1::int) \<and>
   (0::int) \<le> (1::int) \<longrightarrow>
   x_c0 = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_repeat_eliminate_2_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_rotate_left_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_1]:
  fixes x::"'a::len word" and amount::"int"
  shows "NO_MATCH cvc_a (undefined x amount) \<Longrightarrow> int (size x) - ((1::int) + SMT.z3mod amount (int (size x)))
   < int (size x) \<and>
   (x_c0::'b::len word) =
   smt_extract
    (nat (int (size x) - ((1::int) + SMT.z3mod amount (int (size x)))))
    (nat (0::int)) x \<and>
   int (size x_c0) =
   (1::int) +
   (int (size x) - ((1::int) + SMT.z3mod amount (int (size x))) -
    (0::int)) \<and>
   (0::int)
   \<le> int (size x) - ((1::int) + SMT.z3mod amount (int (size x))) \<and>
   (0::int) \<le> (0::int) \<and>
   int (size x) - (1::int) < int (size x) \<and>
   (x_c1::'c::len word) =
   smt_extract (nat (int (size x) - (1::int)))
    (nat (int (size x) - SMT.z3mod amount (int (size x)))) x \<and>
   int (size x_c1) =
   (1::int) +
   (int (size x) - (1::int) -
    (int (size x) - SMT.z3mod amount (int (size x)))) \<and>
   int (size x) - SMT.z3mod amount (int (size x))
   \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> int (size x) - SMT.z3mod amount (int (size x)) \<and>
   (x_c2::'a::len word) = word_cat x_c0 x_c1 \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<and>
   (0::int) \<le> amount \<longrightarrow>
   SMT.z3mod amount (int (size x)) \<noteq> (0::int) \<longrightarrow>
   word_rotl (nat amount) x = x_c2"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_rotate_left_eliminate_1_lemma[of cvc_a x amount ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_rotate_left_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "NO_MATCH cvc_a (undefined x amount) \<Longrightarrow> (0::int) \<le> amount \<longrightarrow>
   SMT.z3mod amount (int (size x)) = (0::int) \<longrightarrow>
   word_rotl (nat amount) x = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_rotate_left_eliminate_2_lemma[of cvc_a x amount ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_rotate_right_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_1]:
  fixes x::"'a::len word" and amount::"int"
  shows "NO_MATCH cvc_a (undefined x amount) \<Longrightarrow> SMT.z3mod amount (int (size x)) - (1::int) < int (size x) \<and>
   (x_c0::'b::len word) =
   smt_extract (nat (SMT.z3mod amount (int (size x)) - (1::int)))
    (nat (0::int)) x \<and>
   int (size x_c0) =
   (1::int) + (SMT.z3mod amount (int (size x)) - (1::int) - (0::int)) \<and>
   (0::int) \<le> SMT.z3mod amount (int (size x)) - (1::int) \<and>
   (0::int) \<le> (0::int) \<and>
   int (size x) - (1::int) < int (size x) \<and>
   (x_c1::'c::len word) =
   smt_extract (nat (int (size x) - (1::int)))
    (nat (SMT.z3mod amount (int (size x)))) x \<and>
   int (size x_c1) =
   (1::int) +
   (int (size x) - (1::int) - SMT.z3mod amount (int (size x))) \<and>
   SMT.z3mod amount (int (size x)) \<le> int (size x) - (1::int) \<and>
   (0::int) \<le> SMT.z3mod amount (int (size x)) \<and>
   (x_c2::'a::len word) = word_cat x_c0 x_c1 \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<and>
   (0::int) \<le> amount \<longrightarrow>
   SMT.z3mod amount (int (size x)) \<noteq> (0::int) \<longrightarrow>
   word_rotr (nat amount) x = x_c2"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_rotate_right_eliminate_1_lemma[of cvc_a x amount ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_rotate_right_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "NO_MATCH cvc_a (undefined x amount) \<Longrightarrow> (0::int) \<le> amount \<longrightarrow>
   SMT.z3mod amount (int (size x)) = (0::int) \<longrightarrow>
   word_rotr (nat amount) x = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_rotate_right_eliminate_2_lemma[of cvc_a x amount ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_nand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nand_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> not (and x y) = not (and x y)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_nand_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_nor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nor_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> not (or x y) = not (or x y)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_nor_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_xnor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_xnor_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> not (semiring_bit_operations_class.xor x y) =
   not (semiring_bit_operations_class.xor x y)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_xnor_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_zero_extend_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c1::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = n \<and>
   (x_c2::'c::len word) = word_cat x_c1 x \<and>
   int (size x_c2) = int (size x_c1) + int (size x) \<and>
   (x_c0::'c::len word) = Word.cast x \<and>
   int (size x_c0) = int (size x) + n \<and>
   (0::int) \<le> n \<longrightarrow>
   x_c0 = x_c2"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_zero_extend_eliminate_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_sdivo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sdivo_eliminate]:
  fixes x::"'a::len word" and y::"'b::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c3::'b::len word) = Word.Word (0::int) \<and>
   int (size x_c3) = int (size y) \<and>
   (x_c0::'c::len word) = Word.Word (1::int) \<and>
   int (size x_c0) = (1::int) \<and>
   (x_c1::'d::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = int (size x) - (1::int) \<and>
   (x_c2::'a::len word) = word_cat x_c0 x_c1 \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<longrightarrow>
   smt_sdivo (itself::'e::len itself) x y = (x = x_c2 \<and> y = not x_c3)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_sdivo_eliminate_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ite_equal_children \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_children]:
  fixes c::"1 word" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if bit c (0::nat) then x else x) = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ite_equal_children_lemma[of cvc_a c x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ite_const_children_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_1]:
  fixes c::"1 word"
  shows "NO_MATCH cvc_a (undefined c) \<Longrightarrow> (x_c1::1 word) = Word.Word (1::int) \<and>
   int (size x_c1) = (1::int) \<and>
   (x_c0::1 word) = Word.Word (0::int) \<and>
   int (size x_c0) = (1::int) \<longrightarrow>
   (if bit c (0::nat) then x_c0 else x_c1) = not c"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ite_const_children_1_lemma[of cvc_a c ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ite_const_children_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_2]:
  fixes c::"1 word"
  shows "NO_MATCH cvc_a (undefined c) \<Longrightarrow> (x_c1::1 word) = Word.Word (0::int) \<and>
   int (size x_c1) = (1::int) \<and>
   (x_c0::1 word) = Word.Word (1::int) \<and>
   int (size x_c0) = (1::int) \<longrightarrow>
   (if bit c (0::nat) then x_c0 else x_c1) = c"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ite_const_children_2_lemma[of cvc_a c ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ite_equal_cond_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_1]:
  fixes c0::"1 word" and t0::"'a::len word" and e0::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 t0 e0 e1) \<Longrightarrow> (if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ite_equal_cond_1_lemma[of cvc_a c0 t0 e0 e1 ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ite_equal_cond_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_2]:
  fixes c0::"1 word" and t0::"'a::len word" and t1::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 t0 t1 e1) \<Longrightarrow> (if bit c0 (0::nat) then t0 else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ite_equal_cond_2_lemma[of cvc_a c0 t0 t1 e1 ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ite_equal_cond_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_3]:
  fixes c0::"1 word" and t0::"'a::len word" and e0::"'a::len word" and t1::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 t0 e0 t1 e1) \<Longrightarrow> (if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0
    else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ite_equal_cond_3_lemma[of cvc_a c0 t0 e0 t1 e1 ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ite_merge_then_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_if]:
  fixes c0::"1 word" and c1::"1 word" and t1::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t1 e1) \<Longrightarrow> (if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else t1) =
   (if bit (and c0 (not c1)) (0::nat) then e1 else t1)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ite_merge_then_if_lemma[of cvc_a c0 c1 t1 e1 ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ite_merge_else_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_if]:
  fixes c0::"1 word" and c1::"1 word" and t1::"'a::len word" and e1::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t1 e1) \<Longrightarrow> (if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else e1) =
   (if bit (and c0 c1) (0::nat) then t1 else e1)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ite_merge_else_if_lemma[of cvc_a c0 c1 t1 e1 ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ite_merge_else_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_else]:
  fixes c0::"1 word" and c1::"1 word" and t1::"'a::len word" and t0::"'a::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t1 t0) \<Longrightarrow> (if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t1 else t0) =
   (if bit (and (not c0) c1) (0::nat) then t1 else t0)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ite_merge_else_else_lemma[of cvc_a c0 c1 t1 t0 ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

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
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_shl_by_const_0_lemma[of cvc_a x sz ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_bitwise_idemp_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_idemp_1]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> and x x = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_bitwise_idemp_1_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_bitwise_idemp_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_idemp_2]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> or x x = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_bitwise_idemp_2_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_and_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_and_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   and x x_c0 = x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_and_zero_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_and_one \<open>automatically_generated\<close>

lemma [rewrite_bv_and_one]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow> and x y = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_and_one_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_or_one \<open>automatically_generated\<close>

lemma [rewrite_bv_or_one]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow> or x y = not x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_or_one_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_xor_duplicate \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_duplicate]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   semiring_bit_operations_class.xor x x = x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_xor_duplicate_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_xor_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_ones]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow>
   semiring_bit_operations_class.xor x y = not x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_xor_ones_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_xor_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   semiring_bit_operations_class.xor x x_c0 = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_xor_zero_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_bitwise_not_and \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_not_and]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   and x (not x) = x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_bitwise_not_and_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_bitwise_not_or \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_not_or]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   or x (not x) = not x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_bitwise_not_or_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_not_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_not_idemp]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> not (not x) = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_not_idemp_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ult_zero_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_1]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x_c0 < x) = (x \<noteq> x_c0)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ult_zero_1_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ult_zero_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_2]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x < x_c0) = False"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ult_zero_2_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ult_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_self]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x < x) = False"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ult_self_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ule_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_self]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<le> x) = True"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ule_self_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ule_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x \<le> x_c0) = (x = x_c0)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ule_zero_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_zero_ule \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ule]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x_c0 \<le> x) = True"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_zero_ule_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ule_max \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_max]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow> (x \<le> y) = True"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ule_max_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_not_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_not_ult]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (\<not> x < y) = (y \<le> x)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_not_ult_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_udiv_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   smt_udiv x x_c0 = not x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_udiv_zero_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_udiv_one \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_one]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (1::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   smt_udiv x x_c0 = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_udiv_one_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_urem_one \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_one]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = n \<and>
   (x_c0::'a::len word) = Word.Word (1::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   smt_urem x x_c0 = x_c1"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_urem_one_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_urem_self \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_self]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   smt_urem x x = x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_urem_self_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_shl_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_zero]:
  fixes a::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined a n) \<Longrightarrow> (x_c2::'b::len word) = push_bit (unat a) (x_c1::'b::len word) \<and>
   int (size x_c2) = int (size x_c1) \<and>
   x_c1 = (x_c0::'b::len word) \<and>
   int (size a) = int (size x_c1) \<and>
   x_c0 = Word.Word (0::int) \<and> int (size x_c0) = n \<longrightarrow>
   x_c2 = x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_shl_zero_lemma[of cvc_a a n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_lshr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_zero]:
  fixes a::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined a n) \<Longrightarrow> (x_c2::'b::len word) = drop_bit (unat a) (x_c1::'b::len word) \<and>
   int (size x_c2) = int (size x_c1) \<and>
   x_c1 = (x_c0::'b::len word) \<and>
   int (size a) = int (size x_c1) \<and>
   x_c0 = Word.Word (0::int) \<and> int (size x_c0) = n \<longrightarrow>
   x_c2 = x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_lshr_zero_lemma[of cvc_a a n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

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
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ashr_zero_lemma[of cvc_a a n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ugt_urem \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_urem]:
  fixes y::"'a::len word" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined y x) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = int (size y) \<and>
   (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   (x < smt_urem y x) = (x = x_c0 \<and> x_c1 < y)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ugt_urem_lemma[of cvc_a y x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ult_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_one]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c1) = n \<and>
   (x_c0::'a::len word) = Word.Word (1::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   (x < x_c0) = (x = x_c1)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ult_one_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

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
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_merge_sign_extend_1_lemma[of cvc_a x i j ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

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
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_extract_not_lemma[of cvc_a x i j ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_mult_distrib_const_neg \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_neg]:
  fixes x::"'a::len word" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> (x_c1::'a::len word) = Word.Word (- n) \<and>
   int (size x_c1) = m \<and>
   (x_c0::'a::len word) = Word.Word n \<and>
   int (size x_c0) = m \<longrightarrow>
   - x * x_c0 = x * x_c1"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_mult_distrib_const_neg_lemma[of cvc_a x n m ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_and_simplify_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_and_simplify_1]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> cvc_list_right and
    (and (cvc_list_right and (cvc_list_left and xs x) ys) x) zs =
   cvc_list_right and (cvc_list_right and (cvc_list_left and xs x) ys) zs"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_and_simplify_1_lemma[of cvc_a xs ys zs x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_and_simplify_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_and_simplify_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   cvc_list_right and
    (and (cvc_list_right and (cvc_list_left and xs x) ys) (not x)) zs =
   x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_and_simplify_2_lemma[of cvc_a xs ys zs x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_or_simplify_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_or_simplify_1]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> cvc_list_right or (or (cvc_list_right or (cvc_list_left or xs x) ys) x)
    zs =
   cvc_list_right or (cvc_list_right or (cvc_list_left or xs x) ys) zs"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_or_simplify_1_lemma[of cvc_a xs ys zs x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_or_simplify_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_or_simplify_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size x) \<longrightarrow>
   cvc_list_right or
    (or (cvc_list_right or (cvc_list_left or xs x) ys) (not x)) zs =
   not x_c0"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_or_simplify_2_lemma[of cvc_a xs ys zs x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_xor_simplify_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_simplify_1]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> cvc_list_right semiring_bit_operations_class.xor
    (semiring_bit_operations_class.xor
      (cvc_list_right semiring_bit_operations_class.xor
        (cvc_list_left semiring_bit_operations_class.xor xs x) ys)
      x)
    zs =
   cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_both semiring_bit_operations_class.xor (0::'a::len word) xs
      ys)
    zs"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_xor_simplify_1_lemma[of cvc_a xs ys zs x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_xor_simplify_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_simplify_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> cvc_list_right semiring_bit_operations_class.xor
    (semiring_bit_operations_class.xor
      (cvc_list_right semiring_bit_operations_class.xor
        (cvc_list_left semiring_bit_operations_class.xor xs x) ys)
      (not x))
    zs =
   not (cvc_list_right semiring_bit_operations_class.xor
         (cvc_list_both semiring_bit_operations_class.xor
           (0::'a::len word) xs ys)
         zs)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_xor_simplify_2_lemma[of cvc_a xs ys zs x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_xor_simplify_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_simplify_3]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined xs ys zs x) \<Longrightarrow> cvc_list_right semiring_bit_operations_class.xor
    (semiring_bit_operations_class.xor
      (cvc_list_right semiring_bit_operations_class.xor
        (cvc_list_left semiring_bit_operations_class.xor xs (not x)) ys)
      x)
    zs =
   not (cvc_list_right semiring_bit_operations_class.xor
         (cvc_list_both semiring_bit_operations_class.xor
           (0::'a::len word) xs ys)
         zs)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_xor_simplify_3_lemma[of cvc_a xs ys zs x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_commutative_and \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_and]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> and x y = and y x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_commutative_and_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_commutative_or \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_or]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> or x y = or y x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_commutative_or_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_commutative_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_xor]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> semiring_bit_operations_class.xor x y =
   semiring_bit_operations_class.xor y x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_commutative_xor_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_commutative_mul \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_mul]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> x * y = y * x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_commutative_mul_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_or_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_or_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = n \<longrightarrow>
   or x x_c0 = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_or_zero_lemma[of cvc_a x n ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_zero_extend_eliminate_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate_0]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.cast x \<and>
   int (size x_c0) = int (size x) + (0::int) \<and>
   (0::int) \<le> (0::int) \<longrightarrow>
   x_c0 = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_zero_extend_eliminate_0_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_sign_extend_eliminate_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eliminate_0]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x_c0::'a::len word) = Word.signed_cast x \<and>
   int (size x_c0) = int (size x) + (0::int) \<and>
   (0::int) \<le> (0::int) \<longrightarrow>
   x_c0 = x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_sign_extend_eliminate_0_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_not_neq \<open>automatically_generated\<close>

lemma [rewrite_bv_not_neq]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (0::int) < int (size x) \<longrightarrow> (x = not x) = False"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_not_neq_lemma[of cvc_a x ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_ult_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_ones]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x_c0::'a::len word) = Word.Word (0::int) \<and>
   int (size x_c0) = int (size y) \<longrightarrow>
   y = not x_c0 \<longrightarrow> (x < y) = (x \<noteq> y)"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_ult_ones_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_or_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_or_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right or (cvc_list_left or xs (cvc_list_right or s ys)) zs =
   cvc_list_right or (cvc_list_right or (cvc_list_left or xs s) ys) zs"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_or_flatten_lemma[of cvc_a xs s ys zs ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_xor_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_left semiring_bit_operations_class.xor xs
      (cvc_list_right semiring_bit_operations_class.xor s ys))
    zs =
   cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_right semiring_bit_operations_class.xor
      (cvc_list_left semiring_bit_operations_class.xor xs s) ys)
    zs"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_xor_flatten_lemma[of cvc_a xs s ys zs ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_and_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_and_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right and (cvc_list_left and xs (cvc_list_right and s ys)) zs =
   cvc_list_right and (cvc_list_right and (cvc_list_left and xs s) ys) zs"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_and_flatten_lemma[of cvc_a xs s ys zs ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done

named_theorems rewrite_bv_neg_sub \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_sub]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> - (x - y) = y - x"
    apply ((rule impI)+)? 
 apply (subst rewrite_bv_neg_sub_lemma[of cvc_a x y ]) 
  apply (simp add: NO_MATCH_def)
 apply force
   apply auto?
 done
end