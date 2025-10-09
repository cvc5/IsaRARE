theory Level0_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" HOL.Real
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy 


The options used to print this file were: 
The options currently set for IsaRARE are:
home directory set to: /home/lachnitt/Sources/IsaRARE/
verbose: false
debug: true
rule format RARE
implicit assumption generation: true
lists are treated as variables: false
the proof strategy is set to: Full
the proof theory strategy is set to: All
lemmas are in the right form to use them for reconstruction (makes them a bit harder to read): false

*)

lemma arith_int_div_one_int:
  fixes t :: "int"
  shows "SMT.z3div (t::int) 1 = t"
  unfolding xor_def SMT.z3div_def
  apply auto ?
  done


lemma arith_neg_neg_one_int:
  fixes t :: "int"
  shows "- 1 * (- 1 * (t::int)) = t"
  apply simp ?
  done


lemma arith_elim_uminus_int:
  fixes t :: "int"
  shows "- (t::int) = - 1 * t"
  apply simp ?
  done


lemma arith_elim_minus_int:
  fixes s :: "int" and t :: "int"
  shows "(t::int) - (s::int) = t + - 1 * s"
  apply simp ?
  done


lemma arith_elim_gt_int:
  fixes s :: "int" and t :: "int"
  shows "((s::int) < (t::int)) = (\<not> t \<le> s)"
  apply auto ?
  done


lemma arith_elim_lt_int:
  fixes s :: "int" and t :: "int"
  shows "((t::int) < (s::int)) = (\<not> s \<le> t)"
  apply auto ?
  done


lemma arith_elim_leq_int:
  fixes s :: "int" and t :: "int"
  shows "((t::int) \<le> (s::int)) = (t \<le> s)"
  apply simp ?
  done


lemma arith_leq_norm_int:
  fixes s :: "int" and t :: "int"
  shows "((t::int) \<le> (s::int)) = (\<not> s + 1 \<le> t)"
  apply auto ?
  done


lemma arith_geq_tighten_int:
  fixes s :: "int" and t :: "int"
  shows "(\<not> (s::int) \<le> (t::int)) = (t + 1 \<le> s)"
  apply auto ?
  done


lemma arith_geq_norm_int:
  fixes s :: "int" and t :: "int"
  shows "((s::int) \<le> (t::int)) = (0 \<le> t - s)"
  apply simp ?
  done


lemma arith_refl_leq_int:
  fixes t :: "int"
  shows "((t::int) \<le> t) = True"
  apply simp ?
  done


lemma arith_refl_lt_int:
  fixes t :: "int"
  shows "((t::int) < t) = False"
  apply simp ?
  done


lemma arith_refl_geq_int:
  fixes t :: "int"
  shows "((t::int) \<le> t) = True"
  apply simp ?
  done


lemma arith_refl_gt_int:
  fixes t :: "int"
  shows "((t::int) < t) = False"
  apply simp ?
  done


lemma arith_neg_neg_one_real:
  fixes t :: "real"
  shows "- 1 * (- 1 * (t::real)) = t"
  apply simp ?
  done


lemma arith_elim_uminus_real:
  fixes t :: "real"
  shows "- (t::real) = - 1 * t"
  apply simp ?
  done


lemma arith_elim_minus_real:
  fixes s :: "real" and t :: "real"
  shows "(t::real) - (s::real) = t + - 1 * s"
  apply simp ?
  done


lemma arith_elim_gt_real:
  fixes s :: "real" and t :: "real"
  shows "((s::real) < (t::real)) = (\<not> t \<le> s)"
  apply auto ?
  done


lemma arith_elim_lt_real:
  fixes s :: "real" and t :: "real"
  shows "((t::real) < (s::real)) = (\<not> s \<le> t)"
  apply auto ?
  done


lemma arith_elim_leq_real:
  fixes s :: "real" and t :: "real"
  shows "((t::real) \<le> (s::real)) = (t \<le> s)"
  apply simp ?
  done


lemma arith_geq_norm_real:
  fixes s :: "real" and t :: "real"
  shows "((s::real) \<le> (t::real)) = (0 \<le> t - s)"
  apply simp ?
  done


lemma arith_refl_leq_real:
  fixes t :: "real"
  shows "((t::real) \<le> t) = True"
  apply simp ?
  done


lemma arith_refl_lt_real:
  fixes t :: "real"
  shows "((t::real) < t) = False"
  apply simp ?
  done


lemma arith_refl_geq_real:
  fixes t :: "real"
  shows "((t::real) \<le> t) = True"
  apply simp ?
  done


lemma arith_refl_gt_real:
  fixes t :: "real"
  shows "((t::real) < t) = False"
  apply simp ?
  done


lemma bool_double_not_elim:
  fixes t :: "bool"
  shows "(\<not> \<not> (t::bool)) = t"
  apply simp ?
  done


lemma bool_eq_true:
  fixes t :: "bool"
  shows "((t::bool) = True) = t"
  apply simp ?
  done


lemma bool_eq_false:
  fixes t :: "bool"
  shows "((t::bool) = False) = (\<not> t)"
  apply simp ?
  done


lemma bool_eq_nrefl:
  fixes x :: "bool"
  shows "((x::bool) = (\<not> x)) = False"
  apply simp ?
  done


lemma bool_impl_false1:
  fixes t :: "bool"
  shows "((t::bool) \<longrightarrow> False) = (\<not> t)"
  apply simp ?
  done


lemma bool_impl_false2:
  fixes t :: "bool"
  shows "(False \<longrightarrow> (t::bool)) = True"
  apply simp ?
  done


lemma bool_impl_true1:
  fixes t :: "bool"
  shows "((t::bool) \<longrightarrow> True) = True"
  apply simp ?
  done


lemma bool_impl_true2:
  fixes t :: "bool"
  shows "(True \<longrightarrow> (t::bool)) = t"
  apply simp ?
  done


lemma bool_impl_elim:
  fixes s :: "bool" and t :: "bool"
  shows "((t::bool) \<longrightarrow> (s::bool)) = (\<not> t \<or> s)"
  apply simp ?
  done


lemma bool_xor_refl:
  fixes x :: "bool"
  shows "((x::bool) \<noteq> x) = False"
  apply simp ?
  done


lemma bool_xor_nrefl:
  fixes x :: "bool"
  shows "((x::bool) \<noteq> (\<not> x)) = True"
  apply simp ?
  done


lemma bool_xor_false:
  fixes x :: "bool"
  shows "((x::bool) \<noteq> False) = x"
  apply simp ?
  done


lemma bool_xor_true:
  fixes x :: "bool"
  shows "((x::bool) \<noteq> True) = (\<not> x)"
  apply simp ?
  done


lemma bool_xor_comm:
  fixes y :: "bool" and x :: "bool"
  shows "((x::bool) \<noteq> (y::bool)) = (y \<noteq> x)"
  apply simp ?
  apply auto ?
  done


lemma bool_xor_elim:
  fixes y :: "bool" and x :: "bool"
  shows "((x::bool) \<noteq> (y::bool)) = (x \<noteq> y)"
  apply simp ?
  done


lemma ite_neg_branch:
  fixes y :: "bool" and x :: "bool" and c :: "bool"
  shows "(\<not> (y::bool)) = (x::bool) \<longrightarrow>
(if c::bool then x else y) = (c = x)"
  apply simp ?
  apply auto ?
  done


lemma ite_then_true:
  fixes x :: "bool" and c :: "bool"
  shows "(if c::bool then True else (x::bool)) = (c \<or> x)"
  apply simp ?
  done


lemma ite_else_false:
  fixes x :: "bool" and c :: "bool"
  shows "(if c::bool then x::bool else False) = (c \<and> x)"
  apply simp ?
  done


lemma ite_then_false:
  fixes x :: "bool" and c :: "bool"
  shows "(if c::bool then False else (x::bool)) = (\<not> c \<and> x)"
  apply simp ?
  done


lemma ite_else_true:
  fixes x :: "bool" and c :: "bool"
  shows "(if c::bool then x::bool else True) = (\<not> c \<or> x)"
  apply simp ?
  done


lemma ite_then_lookahead_self:
  fixes x :: "bool" and c :: "bool"
  shows "(if c::bool then c else (x::bool)) = (if c then True else x)"
  apply simp ?
  done


lemma ite_else_lookahead_self:
  fixes x :: "bool" and c :: "bool"
  shows "(if c::bool then x::bool else c) = (if c then x else False)"
  apply simp ?
  done


lemma str_substr_empty_str:
  fixes m :: "int" and n :: "int"
  shows "smtlib_str_substr [] (n::int) (m::int) = []"
  unfolding smtlib_str_substr_def
  apply auto ?
  done


lemma str_substr_empty_range:
  fixes m :: "int" and n :: "int" and x :: "char list"
  shows "(m::int) \<le> 0 \<longrightarrow>
smtlib_str_substr (x::char list) (n::int) m = []"
  unfolding smtlib_str_substr_def
  apply auto ?
  done


lemma str_substr_empty_start:
  fixes m :: "int" and n :: "int" and x :: "char list"
  shows "smtlib_str_len (x::char list) \<le> (n::int) \<longrightarrow>
smtlib_str_substr x n (m::int) = []"
  unfolding smtlib_str_substr_def
  apply (simp_all add: cvc_string_rewrite_defs)
  apply auto ?
  done


lemma str_substr_empty_start_neg:
  fixes m :: "int" and n :: "int" and x :: "char list"
  shows "(n::int) < 0 \<longrightarrow>
smtlib_str_substr (x::char list) n (m::int) = []"
  unfolding smtlib_str_substr_def
  apply auto ?
  done


lemma str_substr_eq_empty:
  fixes m :: "int" and n :: "int" and s :: "char list"
  shows "(n::int) = 0 \<and> n < (m::int) \<longrightarrow>
(smtlib_str_substr (s::char list) n m = []) = (s = [])"
  apply simp ?
  unfolding smtlib_str_substr_def
  apply auto ?
  done


lemma re_in_empty:
  fixes t :: "char list"
  shows "smtlib_str_in_re (t::char list) smtlib_re_none = False"
  apply simp ?
  apply (simp_all add: cvc_string_rewrite_defs)
  apply auto ?
  done


lemma re_in_sigma:
  fixes t :: "char list"
  shows "smtlib_str_in_re (t::char list) smtlib_re_allchar = (smtlib_str_len t = 1)"
  apply (simp_all add: cvc_string_rewrite_defs)
  apply auto ?
  done


lemma re_in_sigma_star:
  fixes t :: "char list"
  shows "smtlib_str_in_re (t::char list) (smtlib_re_star smtlib_re_allchar) = True"
  apply simp ?
  apply (simp_all add: cvc_string_rewrite_defs)
  apply auto ?
  done


lemma re_in_cstring:
  fixes s :: "char list" and t :: "char list"
  shows "smtlib_str_in_re (t::char list) (smtlib_str_to_re (s::char list)) = (t = s)"
  apply (simp_all add: cvc_string_rewrite_defs)
  apply auto ?
  done


lemma re_in_comp:
  fixes r :: "char list set" and t :: "char list"
  shows "smtlib_str_in_re (t::char list) (smtlib_re_comp (r::char list set)) =
(\<not> smtlib_str_in_re t r)"
  apply (simp_all add: cvc_string_rewrite_defs)
  apply auto ?
  done


lemma str_substr_combine1:
  fixes m2 :: "int" and n2 :: "int" and m1 :: "int" and n1 :: "int" and s :: "char list"
  shows "0 \<le> (n1::int) \<and>
0 \<le> (n2::int) \<and>
0 \<le> (m2::int) - ((m1::int) - n2) \<longrightarrow>
smtlib_str_substr (smtlib_str_substr (s::char list) n1 m1) n2 m2 =
smtlib_str_substr s (n1 + n2) (m1 - n2)"
  sorry

lemma str_substr_combine2:
  fixes m2 :: "int" and n2 :: "int" and m1 :: "int" and n1 :: "int" and s :: "char list"
  shows "0 \<le> (n1::int) \<and>
0 \<le> (n2::int) \<and>
0 \<le> (m1::int) - n2 - (m2::int) \<longrightarrow>
smtlib_str_substr (smtlib_str_substr (s::char list) n1 m1) n2 m2 =
smtlib_str_substr s (n1 + n2) m2"
  sorry

lemma str_contains_leq_len_eq:
  fixes y :: "char list" and x :: "char list"
  shows "smtlib_str_len (x::char list)
\<le> smtlib_str_len (y::char list) \<longrightarrow>
smtlib_str_contains x y = (x = y)"
  sorry

lemma re_all_elim:
  shows "smtlib_re_all = smtlib_re_star smtlib_re_allchar"
  apply simp ?
  apply (simp_all add: cvc_string_rewrite_defs)
  done


lemma re_opt_elim:
  fixes x :: "char list set"
  shows "smtlib_re_opt (x::char list set) = smtlib_re_union (smtlib_str_to_re []) x"
  apply simp ?
  apply (simp_all add: cvc_string_rewrite_defs)
  apply auto ?
  done


lemma str_in_re_range_elim:
  fixes c2 :: "char list" and c1 :: "char list" and s :: "char list"
  shows "smtlib_str_len (c1::char list) = 1 \<and>
smtlib_str_len (c2::char list) = 1 \<longrightarrow>
smtlib_str_in_re (s::char list) (smtlib_re_range c1 c2) =
(smtlib_str_to_code c1 \<le> smtlib_str_to_code s \<and>
 smtlib_str_to_code s \<le> smtlib_str_to_code c2)"
  sorry

end