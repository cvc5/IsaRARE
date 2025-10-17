theory Words      
  imports Main "HOL-Library.Sublist" "HOL-Library.List_Lexorder" HOL.Groups "HOL-Library.Multiset"
begin

type_synonym 'a word = "'a list"

no_notation append (infixr "@" 65)
notation append (infixr "\<cdot>" 65)
notation Nil ("\<epsilon>")

notation length ("\<bar>_\<bar>")
unbundle no abs_syntax

instantiation char::linorder begin

(* Just for convenience, so we can use literal chars for testing *)
definition less_char::"char \<Rightarrow> char \<Rightarrow> bool" where 
  "less_char a b \<equiv> ((of_char a)::nat) < ((of_char b)::nat)"

definition less_eq_char::"char \<Rightarrow> char \<Rightarrow> bool" where 
  "less_eq_char a b \<equiv> ((of_char a)::nat) \<le> ((of_char b)::nat)"

instance apply(standard)
  using less_char_def less_eq_char_def by auto

end

primrec concat_all:: "'a word list \<Rightarrow> 'a word" where
  "concat_all [] = \<epsilon>" |
  "concat_all (w#ws) = w\<cdot>(concat_all ws)"

fun factor:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where 
  "factor v w = sublist v w"

fun get_factor:: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word" ("_[_;_]" 101) where 
  "get_factor w i j = (if i \<le> j then take (j-i) (drop i w) else \<epsilon>)"

primrec contains:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where
  "contains \<epsilon> v = (v = \<epsilon>)" |
  "contains (x#u) v = ((prefix v (x#u)) \<or> (contains u v))"



fun indexof_0:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat" where 
  "indexof_0 (c#w) v = (if prefix v (c#w) then 0 else Suc (indexof_0 w v))"
| "indexof_0 [] v = 0"

fun indexof_nat:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat \<Rightarrow> nat" where 
  "indexof_nat w v n = n + indexof_0 (drop n w) v"

fun indexof:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat \<Rightarrow> nat option" where 
  "indexof w v i = (if (factor v  (w[i;\<bar>w\<bar>])) \<and> i\<le>\<bar>w\<bar> then Some (indexof_nat w v i) else None)"


fun replace:: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
  "replace w v u = (case indexof w v 0 of Some i \<Rightarrow> (take i w)\<cdot>u\<cdot>(drop (i+(length v)) w) | None => w)"

subsection "Factorization"

lemma drop_append:
  assumes "n \<le> \<bar>w\<bar> \<and> x = drop n w"
  shows "\<exists>v. ((w = v\<cdot>x) \<and> (length v) = n)"
  using assms
proof (induct w)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a w)
  then show ?case
    by (metis antisym append_take_drop_id length_take min_def)
qed

lemma factor_iff: "factor v w \<longleftrightarrow> (\<exists>i. v = (w[i; i+\<bar>v\<bar>]))"
proof 
  show "factor v w \<Longrightarrow> \<exists>i. v = (w[i;i + \<bar>v\<bar>])"
    unfolding factor.simps get_factor.simps 
    by (metis append_eq_conv_conj diff_add_inverse le_add1 sublist_def)
next
  show "\<exists>i. v = (w[i;i + \<bar>v\<bar>]) \<Longrightarrow> factor v w"
    unfolding factor.simps get_factor.simps
    by (metis le_add1 sublist_drop sublist_order.order.trans sublist_take)
qed

lemma factorization: 
  assumes "i < (List.length w)"
    and "i \<le> j"
  shows "\<exists>!v. (w[i; j]) = v \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = i \<and> \<bar>v\<bar> = min (j-i) (\<bar>w\<bar>-i))"
proof -
  have "\<exists>!v. take (j - i) (drop i w) = v \<and> (\<exists>x. (\<exists>y. w = x \<cdot> v \<cdot> y) \<and> \<bar>x\<bar> = i
          \<and> \<bar>v\<bar> = min (j - i) (\<bar>w\<bar> - i))"
    using assms by (metis  append_take_drop_id length_drop length_take min.absorb4 min.commute)
  then show ?thesis
    using assms by (simp split: if_splits)
qed

lemma factorize_if:"w = x\<cdot>v\<cdot>y \<Longrightarrow> w[\<bar>x\<bar>; \<bar>x\<bar>+\<bar>v\<bar>] = v" by auto

lemma prefix_iff_fac: "prefix v w \<longleftrightarrow> (w[0; \<bar>v\<bar>] = v)"
  by (metis append_eq_conv_conj diff_zero drop0 get_factor.elims prefix_def zero_order(1))

lemma suffix_iff_fac: "suffix v w \<longleftrightarrow> (w[\<bar>w\<bar> - \<bar>v\<bar>; \<bar>w\<bar>] = v)"
proof
  show "suffix v w \<Longrightarrow> w[\<bar>w\<bar> - \<bar>v\<bar>;\<bar>w\<bar>] = v"  
    unfolding suffix_def by auto
next
  show "w[\<bar>w\<bar> - \<bar>v\<bar>;\<bar>w\<bar>] = v \<Longrightarrow> suffix v w"
    by (metis diff_le_self get_factor.simps length_drop order_le_less suffix_drop take_all)
qed

lemma get_factor_01_is_take1: "w[0;1] = take 1 w"
  by auto

lemma empty_factor_if_i_geq_j: "i \<ge> j \<Longrightarrow> w[i;j] = \<epsilon>" 
  by auto

lemma empty_factor_if_i_geq_length: "i \<ge> (length w) \<Longrightarrow> w[i;j] = \<epsilon>" 
  by auto

lemma factor_epsilon: "\<epsilon>[i;j] = \<epsilon>" 
  by auto

lemma factor_suffix: "\<bar>w\<bar> \<le> m \<Longrightarrow> w[i; m] = drop i w" 
  by auto

lemma factor_len_0: "w[i;i] = \<epsilon>" 
  by auto

lemma factor_is_word_if_j_geq_length: "j \<ge> (length w) \<Longrightarrow> w[0;j] = w"
  by auto

lemma fac_nth:"i < (length w) \<Longrightarrow> w[i; i+1] = (w!i)#\<epsilon>"
  by (simp add: take_Suc_conv_app_nth)

lemma contains_iff_factor:"contains w v \<longleftrightarrow> factor v w"
  by (induct w) (auto simp add: sublist_Cons_right)

lemma not_contains_no_fac_has_prefix:"(\<not>contains w d) \<Longrightarrow> w = x\<cdot>y \<Longrightarrow> (\<not> prefix d y)"
  by (auto simp add: contains_iff_factor sublist_append)

lemma if_contains_then_fac_has_prefix:"(contains w d) \<Longrightarrow> \<exists>x y. w = x\<cdot>y \<and> (prefix d y)"
  by (auto simp add: contains_iff_factor prefix_def sublist_def)

lemma epsilon_contains_epsilon[simp]: "contains \<epsilon> v \<Longrightarrow> v = \<epsilon>" 
  by auto


subsection "Searching and Replacing Factors" 

lemma indexof_if_not_contains:"\<not> (factor v (w[i; \<bar>w\<bar>])) \<Longrightarrow> indexof w v i = None" 
  by simp


lemma indexof_if_not_contains''':"\<not> (factor v  (w[i; \<bar>w\<bar>])) \<Longrightarrow> indexof w v i = None"
  by simp 

lemma indexof_if_contains: "i\<ge>0 \<Longrightarrow> i\<le>\<bar>w\<bar> \<Longrightarrow> factor v (w[i; \<bar>w\<bar>]) \<Longrightarrow> \<exists>r. indexof w v i = Some r" 
  by auto

lemma indexof_if_contains''': "i\<ge>0 \<Longrightarrow> i\<le>\<bar>w\<bar> \<Longrightarrow> factor v (w[i; \<bar>w\<bar>]) \<Longrightarrow> \<exists>r. indexof w v i =  Some r"
  by simp

lemma indexof_Some_iff: "indexof w v i = Some r \<longleftrightarrow> (factor v  (w[i;\<bar>w\<bar>])) \<and> i\<le>\<bar>w\<bar> \<and> r = (indexof_nat w v i)"
  by(auto split: if_splits)

theorem indexof_01:
  assumes "factor v w"
  shows "\<exists>n. (indexof_0 w v) =  n \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> n' = \<bar>x\<bar> ) \<longrightarrow> n \<le> n')" 
  using assms
proof (induction w)
  case Nil
  then show ?case
    by auto
next
  case (Cons a w)
  then have split: "prefix v (a # w) \<or> (\<not>prefix v (a # w) \<and> sublist v w)"
    by (metis contains.simps(2) contains_iff_factor factor.elims(2))
  then have "(\<exists>x y. a # w = append x (append v y) \<and> indexof_0 (a # w) v = length x)"
  proof 
    assume "prefix v (a # w)"
    then have "indexof_0 (a # w) v = 0"
      by auto
    moreover
    have "\<exists>y. a # w = (append v y)"
      using \<open>prefix v (a # w)\<close> prefix_def by auto
    ultimately
    have "(\<exists>y. a # w = (append v y) \<and> indexof_0 (a # w) v = 0)"
      by auto
    then show "(\<exists>x y. a # w = append x (append v y) \<and> indexof_0 (a # w) v = length x)"
      by auto
  next
    assume "\<not> prefix v (a # w) \<and> sublist v w"
    then have "(\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (indexof_0 w v) = length x)"
      using Cons(1) by auto
    then show "(\<exists>x y. a # w = x\<cdot> (v\<cdot> y) \<and> indexof_0 (a # w) v = length x)"
      by (metis \<open>\<not> prefix v (a # w) \<and> sublist v w\<close> add.right_neutral add_Suc_right append_Cons list.size(4) indexof_0.simps(1))
  qed
  moreover
  have "(\<forall>n'. (\<exists>x y. a # w = x\<cdot> (v\<cdot> y) \<and> n' = length x) \<longrightarrow> indexof_0 (a # w) v \<le> n')"
  proof (rule, rule)
    fix n'
    assume "\<exists>x y. (a # w = x\<cdot> (v\<cdot> y) \<and> n' = length x)"
    then obtain x y where x_y_p: "a # w = x\<cdot>(v\<cdot> y) \<and> n' = length x"
      by auto
    from split show "indexof_0 (a # w) v \<le> n'"
    proof 
      assume "prefix v (a # w)"
      show "indexof_0 (a # w) v \<le> n'"
        by (simp add: \<open>prefix v (a # w)\<close>)
    next
      assume a: "\<not> prefix v (a # w) \<and> sublist v w "
      have n'_gr_0: "n' > 0"
        using \<open>a # w = append x (append v y) \<and> n' = length x\<close> a by force
      from a have "indexof_0 (a # w) v = Suc (indexof_0 w v)"
        by auto
      from a have "\<exists>n. (indexof_0 w v) =  n \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> n' = \<bar>x\<bar> ) \<longrightarrow> n \<le> n')"
        using Cons by auto
      then have "(\<forall>n'. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> n' = length x) \<longrightarrow> (indexof_0 w v) \<le> n')"
        by auto
      then have "(\<forall>n'. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> Suc n' = length (a#x)) \<longrightarrow> indexof_0 (a # w) v \<le> Suc n')"
        by auto
      then show "indexof_0 (a # w) v \<le> n'"
        by (smt (verit, ccfv_SIG) n'_gr_0 x_y_p a append_eq_Cons_conv gr0_implies_Suc prefixI)
    qed
  qed
  ultimately
  show ?case 
    by auto
qed

theorem str_indexof_nat1: 
  assumes "i\<le> length w" and "factor v (drop i w)"
  shows "\<exists>n. indexof_nat w v i = n \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = length x) \<and> (\<forall>n'. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n' \<and> n' = length x)  \<longrightarrow> n \<le> n')" 
proof -
  have sm: "\<exists>n. (indexof_0 (drop i w) v) =  n \<and> (\<exists>x y. (drop i w) = x\<cdot>v\<cdot>y \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. (\<exists>x y. (drop i w) = x\<cdot>v\<cdot>y \<and> n' = \<bar>x\<bar> ) \<longrightarrow> n \<le> n')"
    using assms indexof_01 by blast
  then have "\<exists>x y. (drop i w) = x\<cdot>v\<cdot>y \<and> (indexof_0 (drop i w) v) = length x"
    by auto
  then obtain x y where x_y_p: "(drop i w) = x\<cdot>v\<cdot>y \<and> (indexof_0 (drop i w) v) = length x"
    by auto
  define x' where "x' = take i w \<cdot> x"
  {
    have a: "w = x'\<cdot>v\<cdot>y"
      by (metis x_y_p append_assoc append_take_drop_id x'_def)
    moreover
    have b: "i \<le> (i + indexof_0 (drop i w) v)"
      by auto
    moreover
    have c: "i + indexof_0 (drop i w) v = length x'"
      using assms(1) x'_def x_y_p by fastforce
    ultimately
    have "(\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> (i + indexof_0 (drop i w) v) \<and> (i + indexof_0 (drop i w) v) = length x)"
      by metis
  }
  moreover
  have "\<forall>n. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = length x) \<longrightarrow> (i + indexof_0 (drop i w) v) \<le> n"
  proof (rule, rule)
    fix n
    assume "(\<exists>x'' y''. w = x''\<cdot>v\<cdot>y'' \<and> i \<le> n \<and> n = length x'')"
    then obtain x'' y'' where x''_y''_p:
      "w = x''\<cdot>v\<cdot>y''"
      "i \<le> n"
      "n = length x''"
      by auto
    define x''' where "x''' = drop i x''"
    have drop_w_split: "(drop i w) = drop i x'' \<cdot> v\<cdot>y''"
      using x''_y''_p by force
    have "\<forall>n. (\<exists>x y. (drop i w) = x\<cdot>v\<cdot>y \<and> n = length x) \<longrightarrow> indexof_0 (drop i w) v \<le> n"
      using sm by auto
    then show "(i + indexof_0 (drop i w) v) \<le> n"
      using drop_w_split x''_y''_p(2) x''_y''_p(3) by fastforce
  qed
  ultimately
  (*have "smallest_int (i + indexof_0 (drop i w)  v) (\<lambda>n. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = length x))"*) 
  have "(\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> (i + indexof_0 (drop i w)  v) \<and> (i + indexof_0 (drop i w)  v) = length x) \<and> (\<forall>n'. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n' \<and> n' = length x) \<longrightarrow> (i + indexof_0 (drop i w)  v)\<le>n')"
    by auto
  then show ?thesis 
   by simp
qed

lemma indexof_Some_iff_factor: "\<exists>r. indexof w v 0 = Some r \<longleftrightarrow> factor v w"
  by(auto split: if_splits)


lemma replace_epsilon: "replace w \<epsilon> u = u\<cdot>w"
proof -
  have "take (indexof_0 w \<epsilon>) w \<cdot> u \<cdot> drop (indexof_0 w \<epsilon>) w = u \<cdot> w"
    by (metis append_self_conv2 append_take_drop_id indexof_0.elims prefix_bot.bot_least take_eq_Nil2)
  then show ?thesis
    by (auto simp add: option.case_eq_if)
qed

lemma replace_id_if_not_contains: "\<not>contains w v \<Longrightarrow> replace w v u = w"
  using contains_iff_factor by auto

theorem replace_factor: 
  assumes "contains w v"
  shows "\<exists>x y. (w= x\<cdot>v\<cdot>y \<and> replace w v u = x\<cdot>u\<cdot>y)"
proof (cases "sublist v w")
  case True
  then have "\<exists>x y. w = x \<cdot> v \<cdot> y \<and> 
               take (indexof_0 w v) w \<cdot> u \<cdot> drop (indexof_0 w v + \<bar>v\<bar>) w = x \<cdot> u \<cdot> y"
    by (metis append.assoc append_eq_conv_conj factor.elims(3) indexof_01 length_append)
  then show ?thesis
    using True by (simp add: option.case_eq_if prefix_def)
next
  case False
  then show ?thesis 
    using assms by (simp add: contains_iff_factor)
qed
  
theorem replace_first_factor: "contains w v \<Longrightarrow> \<exists>x y. replace w v u = x\<cdot>u\<cdot>y \<and> w = x\<cdot>v\<cdot>y \<and> (\<forall> x'. (\<exists>y'. w=x'\<cdot>v\<cdot>y') \<longrightarrow> \<bar>x\<bar> \<le> \<bar>x'\<bar>)"
proof -
  assume "contains w v"
  then have "factor v w" using contains_iff_factor by auto
  then have "\<exists>n. indexof_nat w v 0 = n \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> 0 \<le> n \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> 0 \<le> n' \<and> n' = \<bar>x\<bar>)  \<longrightarrow> n \<le> n')"
    by (metis bot_nat_0.extremum drop0 str_indexof_nat1) 
  then obtain n where "indexof_nat w v 0 = n \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> 0 \<le> n' \<and> n' = \<bar>x\<bar>)  \<longrightarrow> n \<le> n')" by blast
  then have "replace w v u = (take n w)\<cdot>u\<cdot>(drop (n+\<bar>v\<bar>) w) \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. (\<exists>x' y'. w = x'\<cdot>v\<cdot>y' \<and> 0 \<le> n' \<and> n' = \<bar>x'\<bar>)  \<longrightarrow> n \<le> n')" by auto
  then have "\<exists>x y. replace w v u = x\<cdot>u\<cdot>y \<and> n = \<bar>x\<bar> \<and>  w = x\<cdot>v\<cdot>y \<and> (\<forall>n'. (\<exists>x' y'. w = x'\<cdot>v\<cdot>y' \<and> 0 \<le> n' \<and> n' = \<bar>x'\<bar>)  \<longrightarrow> n \<le> n')"
    by (metis append.assoc append_eq_conv_conj length_append)
  then have "\<exists>x y. replace w v u = x\<cdot>u\<cdot>y \<and>  w = x\<cdot>v\<cdot>y \<and> (\<forall>n'. (\<exists>x' y'. w = x'\<cdot>v\<cdot>y' \<and> 0 \<le> n' \<and> n' = \<bar>x'\<bar>)  \<longrightarrow> \<bar>x\<bar> \<le> n')" by metis 
  then show ?thesis by blast
qed

end
