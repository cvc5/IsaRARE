theory Arith_Rewrites_Lemmas
  imports "HOL.Dsl_Nary_Ops" 
begin

lemma arith_plus_zero_lemma:
  shows "foldr (+) ts (0::int) + foldr (+) ss 0 = foldr (+) ts (foldr (+) ss 0)"
  apply (induction ts)
   apply simp
     apply (induction ss)
  by simp_all

lemma arith_mul_one_lemma:
  shows " foldr (*) ts (1::int) * foldr (*) ss 1 = foldr (*) ts (foldr (*) ss 1)"
  apply (induction ts)
  by simp_all

lemma arith_mul_zero_lemma:
  shows "foldr (*) ts (0::int) * foldr (*) ss 1 = 0"
  apply (induction ts)
  by simp_all

lemma arith_mult_dist_lemma:
  shows
 "x * (y + z) = x * y + x * z"
 "x * (y + z + (a + foldr (+) ws (0::int))) = x * y + x * (z + (a + foldr (+) ws (0::int)))"
  by (simp_all add: distrib_left)

lemma arith_int_div_one_lemma:
 "SMT.z3div t (1::int) = t"
  unfolding z3div_def
  by simp

lemma arith_neg_neg_one_lemma:
  "- (1::int) * (- (1::int) * t) = t"
  by simp

lemma arith_elim_uminus_lemma:
  "True"
  by simp

lemma arith_plus_flatten_lemma:
  "foldr (+) xss (w + foldr (+) yss 0) + foldr (+) zss (0::int) =
    foldr (+) xss w + foldr (+) yss 0 + foldr (+) zss 0"
  apply (induction xss)
   apply simp
  apply (induction zss)
   apply simp
  apply (induction yss)
  by simp_all

lemma arith_mult_flatten_lemma:
" foldr (*) xss (w * foldr (*) yss (1::int)) * foldr (*) zss 1 =
    foldr (*) xss w * foldr (*) yss 1 * foldr (*) zss 1"
  apply (induction xss)
   apply simp
  apply (induction zss)
   apply simp
  apply (induction yss)
   apply simp_all
  by meson


lemma arith_plus_cancel1_lemma:
"foldr (+) ts x + foldr (+) ss (0::int) + - 1 * x + foldr (+) rs 0 =
    foldr (+) ts (foldr (+) ss 0) + foldr (+) rs 0"
  apply (induction ts)
   apply simp
  apply (induction ss)
   apply simp
  apply (induction rs)
  by simp_all


lemma arith_plus_cancel2_lemma:
"foldr (+) ts (- (1::int) * x) + foldr (+) ss 0 + x + foldr (+) rs 0 =
    foldr (+) ts (foldr (+) ss 0) + foldr (+) rs 0"
  apply (induction ts)
   apply simp
  apply (induction ss)
   apply simp
  apply (induction rs)
  by simp_all


end