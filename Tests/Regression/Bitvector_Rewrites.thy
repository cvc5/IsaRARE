theory Bitvector_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" 
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
    by (simp_all add: bv_concat_flatten_lemma)
  done


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
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction yss arbitrary: ys)
    apply simp_all
    apply (induction xss arbitrary: xs)
    apply simp_all
    apply (simp_all add: cvc_rewrites_fold)
    by (simp_all add: bv_concat_extract_merge_lemma)
  done

end