theory RegEx     
  imports Regular
begin


section "Regular Expressions"

datatype 'a::linorder regex = None  | Const "'a word" 
  | Union "'a regex" "'a regex" (infixr "\<squnion>" 65)
  | Concat "'a regex" "'a regex"  (infixr "\<odot>" 65)
  | Star "'a regex"  ("_\<^sup>\<star>")
  | Inter "'a regex" "'a regex" (infixr "\<sqinter>" 65)
  | Any ("?")
  | Comp "'a regex" ("\<inverse>")
  | Diff "'a regex" "'a regex" ("\\")
  | Range "'a" "'a" ("[__]")

primrec lang:: "'a::linorder regex \<Rightarrow> 'a word set"  where
  "lang None = {}"|
  "lang Any = {w. (length w) = 1}" | 
  "lang (Const w) = {w}" |
  "lang (Union r1 r2) = (lang r1) Un (lang r2)" |
  "lang (Concat r1 r2) = concat (lang r1) (lang r2)"|
  "lang (Star r) = star (lang r)" |
  "lang (Range l u) = {(v#\<epsilon>)|v. l \<le> v \<and> v \<le> u}"|
  "lang (Inter r1 r2) = (lang r1) \<inter> (lang r2)"|
  "lang (Comp r) = -(lang r)"|
  "lang (Diff r1 r2) = (lang r1) - (lang r2)"

lemma star_any_is_univ: "w \<in> lang (Star Any)"
  by (metis lang.simps(2) lang.simps(6) singleton_set star_of_singletons_is_univ)


section "Construction functions that perform simple normalisation"

fun re_union::"'a::linorder regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where 
  "re_union r None = r"|
  "re_union None r = r"|
  "re_union (Const a) (Const b) = (if a = b then (Const a) else (Union (Const a) (Const b)))"|
  "re_union r e = Union r e"

lemma re_union_correct:"(lang (re_union r e)) = (lang (Union r e))"
  by (cases \<open>(r, e)\<close> rule: re_union.cases) auto

fun re_concat:: "'a::linorder regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where
  "re_concat r (Const \<epsilon>) = r"|
  "re_concat (Const \<epsilon>) r = r"|
  "re_concat None r = None"|
  "re_concat r None = None"|
  "re_concat r e = Concat r e"

lemma re_concat_correct:"(lang (re_concat r e)) = (lang (Concat r e))"
  by (cases \<open>(r, e)\<close> rule: re_concat.cases) (auto simp add: concat_def)

fun re_star:: "'a::linorder regex \<Rightarrow> 'a regex" where
  "re_star (Const \<epsilon>) = (Const \<epsilon>)"|
  "re_star None = (Const \<epsilon>)"|
  "re_star r = Star r"

lemma re_star_correct:"(lang (re_star r)) = (lang (Star r))"
  by (cases r rule: re_star.cases) (auto simp add: star_of_epsilon star_of_empty)

fun re_plus::"'a::linorder regex \<Rightarrow> 'a regex" where 
  "re_plus r = re_concat r (re_star r)"

fun re_inter:: "'a::linorder regex \<Rightarrow> 'a::linorder regex \<Rightarrow> 'a regex" where
  "re_inter None r = None"|
  "re_inter r None = None"|
  "re_inter (Const a) (Const b) = (if a = b then (Const a) else None)"|
  "re_inter r e = Inter r e" 

lemma re_inter_correct: "lang (re_inter r1 r2) = lang (Inter r1 r2)"
  by (cases \<open>(r1, r2)\<close> rule: re_inter.cases) auto

fun re_range::  "'a::linorder \<Rightarrow> 'a::linorder \<Rightarrow> 'a regex" where
  "re_range l u = (if (l < u) then (Range l u) else (if l = u then (Const (l#\<epsilon>)) else None))"

lemma re_range_correct: "lang (re_range l u) = (lang (Range l u))"
  by auto

fun re_comp:: "'a::linorder regex \<Rightarrow> 'a regex" where
  "re_comp None = Star Any"|
  "re_comp r = Comp r"

lemma re_comp_correct: "lang (re_comp r) = (lang (Comp r))"
  using star_any_is_univ by (cases r) auto

fun re_diff:: "'a::linorder regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where
  "re_diff None _ = None"|
  "re_diff r None = r"|
  "re_diff r1 r2  = Diff r1 r2"

lemma re_diff_correct: "lang (re_diff r1 r2) = lang (Diff r1 r2)" 
  by (cases \<open>(r1, r2)\<close> rule: re_diff.cases) auto

primrec re_pow::"'a::linorder regex \<Rightarrow> nat \<Rightarrow> 'a regex" where
  "re_pow r 0 = (Const \<epsilon>)"|
  "re_pow r (Suc n) = re_concat r (re_pow r n)"

fun re_loop::"'a::linorder regex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a regex" where
  "re_loop r (Suc a) 0 = None"|
  "re_loop r 0 0 = Const \<epsilon>"|
  "re_loop r a (Suc n) = (if a \<le> (Suc n) then re_union (re_pow r (Suc n)) (re_loop r a n) else None)"

lemma re_loop_iff1: 
  assumes "a \<le> b"
  shows "w \<in> lang (re_loop r a b) \<longleftrightarrow> (\<exists>x. a \<le> x \<and> x \<le> b \<and> w \<in> lang (re_pow r x))"
  using assms
  apply (induct b)
  apply (auto simp add: UnE le_SucI not0_implies_Suc not_less_eq_eq re_union_correct)
  apply (metis empty_iff lang.simps(1) le_Suc_eq re_loop.elims)
  using antisym not_less_eq_eq by fastforce

lemma re_loop_None_if:"a > b \<Longrightarrow> re_loop r a b = None"
  by (cases \<open>(r, a, b)\<close> rule: re_loop.cases) auto

(* A language is nullable if it accepts the empty word*)
primrec nullable:: "'a::linorder regex \<Rightarrow> bool" 
  where
    "nullable None = False" |
    "nullable Any = False" |
    "nullable (Const w) = (w = \<epsilon>)" |
    "nullable (Union r1 r2) = ((nullable r1) \<or> (nullable r2))" |
    "nullable (Inter r1 r2) = ((nullable r1) \<and> (nullable r2))"|
    "nullable (Concat r1 r2) = ((nullable r1) \<and> (nullable r2))" |
    "nullable (Star r) = True"|
    "nullable (Range _ _) = False"|
    "nullable (Comp r) = (\<not> nullable r)"|
    "nullable (Diff r1 r2) = ((nullable r1) \<and> (\<not> nullable r2))"

lemma nullability: "nullable r \<longleftrightarrow> \<epsilon> \<in> (lang r)"
  by (induct r) (auto simp add: concat_def)

(* abbreviation vu:: "'a regex \<Rightarrow> 'a regex" where "vu r \<equiv> (if (nullable r) then (Const \<epsilon>) else None)" *)

primrec vu:: "'a::linorder regex \<Rightarrow> 'a regex" where
  "vu (Const w) = (if w = \<epsilon> then (Const w) else None)" |
  "vu None = None" |
  "vu (Union r1 r2) = re_union (vu r1) (vu r2)" |
  "vu (Inter r1 r2) = re_inter (vu r1) (vu r2)" |
  "vu (Concat r1 r2) = re_concat (vu r1) (vu r2)" |
  "vu (Star r) = (Const \<epsilon>)" |
  "vu Any = None"|
  "vu (Range _ _) = None"|
  "vu (Comp r) = (if (nullable r) then None else (Const \<epsilon>))"|
  "vu (Diff r1 r2) = (if (nullable r1 \<and> \<not> nullable r2) then (Const \<epsilon>) else None)"

(* Derivatives of regular languages *)

fun rderiv :: "'a::linorder \<Rightarrow> 'a::linorder regex \<Rightarrow> 'a::linorder regex" where
  "rderiv c None = None" |
  "rderiv c Any = (Const \<epsilon>)"|
  "rderiv c (Const (a#w)) = (if a = c then (Const w) else None)" |
  "rderiv c (Const \<epsilon>) = None"|
  "rderiv c (Union r1 r2) = re_union (rderiv c r1) (rderiv c r2)" |
  "rderiv c (Inter r1 r2) = re_inter (rderiv c r1) (rderiv c r2)"|
  "rderiv c (Concat r1 r2) = (re_union (re_concat (rderiv c r1) r2)  (re_concat (vu r1) (rderiv c r2)))" |
  "rderiv c (Star r) = re_concat (rderiv c r) (re_star r)"|
  "rderiv c (Range l u) = (if (l\<le>c \<and> c \<le> u) then (Const \<epsilon>) else None)"|
  "rderiv c (Comp r) = re_comp (rderiv c r)"|
  "rderiv c (Diff r1 r2) = re_diff (rderiv c r1) (rderiv c r2)"

lemma "c > u \<Longrightarrow> rderiv c (Range l u) = None"
  by auto

lemma [simp]: "c < l \<Longrightarrow> rderiv c (Range l u) = None"
  by auto

lemma [simp]: "l \<le> c \<Longrightarrow> c \<le> u \<Longrightarrow> rderiv c (Range l u) = (Const \<epsilon>)"
  by auto

lemma vu_null_iff: "lang (vu r) = null (lang r)"
  unfolding Regular.null_def 
  by (induct r) (simp_all add: re_union_correct re_concat_correct re_inter_correct re_star_correct 
      concat_def re_diff_correct  nullability)

lemma rderiv_correct: "lang (rderiv a r) = deriv a (lang r)"
proof(induction r arbitrary: a)
  case None
  then show ?case 
    by (simp add: deriv_empty)
next
  case (Const x)  
  then show ?case 
  proof(cases x)
    case Nil
    then show ?thesis 
      by (simp add: deriv_def)
  next
    case (Cons a list)
    then show ?thesis 
      by (simp add: deriv_const)
  qed
next
  case (Union r1 r2)
  then show ?case 
    by (simp add: deriv_union re_union_correct)
next
  case (Concat r1 r2)
  then show ?case  
    by (simp add: deriv_concat vu_null_iff re_concat_correct re_union_correct)
next
  case (Inter r1 r2)
  then show ?case 
    by (auto simp add: deriv_inter re_inter_correct)
next
  case (Star r)
  then show ?case 
    by (simp add: deriv_star re_star_correct re_union_correct re_concat_correct)
next
  case Any
  then show ?case 
    by (auto simp add: deriv_def)
next
  case (Range l u)
  then show ?case 
    by(auto simp add: deriv_def)
next 
  case (Comp r)
  then show ?case
    by (auto simp add: deriv_def re_comp_correct)
next 
  case (Diff r1 r2)
  then show ?case 
    by (auto simp add: deriv_def re_diff_correct)
qed

primrec rderivw:: "'a::linorder word \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where
  "rderivw \<epsilon> r = r" |
  "rderivw (a#u) r = rderivw u (rderiv a r)"

lemma derivw_nullable_contains: 
  assumes "nullable (rderivw w r)"
  shows "w \<in> (lang r)"
  using assms
proof (induct w arbitrary: r)
  case Nil
  then show ?case 
    by (auto simp add: nullability)
next
  case (Cons a w)
  then have "\<epsilon> \<in> lang (rderivw w (rderiv a r))"
    by (auto simp add: nullability)
  then have "nullable (rderivw w (rderiv a r))"
    by (simp add: nullability)
  then have "a # w \<in> lang r"
    using Cons(1) by (metis deriv_correct rderiv_correct)
  then show ?case  
    by auto
qed

lemma contains_derivw_nullable:
  assumes "w \<in> (lang r)"
  shows "nullable (rderivw w r)"
  using assms
proof (induct w arbitrary: r)
  case Nil
  then show ?case 
    by (auto simp add: nullability)
next
  case (Cons a w)
  have "a # w \<in> lang r"
    using Cons by (auto simp add: nullability)
  then have "\<epsilon> \<in> lang (rderivw w (rderiv a r))"
    using Cons(1) by (auto simp add: nullability deriv_correct rderiv_correct)
  then show ?case 
    by (auto simp add: nullability)
qed

theorem derivative_correctness: "w \<in> (lang r) \<longleftrightarrow> nullable (rderivw w r)"
  by (auto simp add: contains_derivw_nullable derivw_nullable_contains)

end