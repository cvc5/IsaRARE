theory Strings
  imports Core "strings/RegEx" "strings/Words"  "HOL-Library.List_Lexorder"
begin

no_notation List.length ("\<bar>_\<bar>")
unbundle no abs_syntax



section "Standard model for the SMT-LIB Theory of String"

subsection "Definition of Unicode characters"

text "The standard defines two sorts, String and RegLan. 
In the standard model, the domain of these sorts are fixed as the set of all words over the 
alphabet of unicode code points from 0 to 196607, and the powerset of this set, respectively.
We define the set of unicode code points as the subsets of integers from 0 up to 196607.
Words as lists over this alphabet (type) and regular languages as regular expression over the
alphabet, equipped with a function that maps expression to actual languages."


typedef uc_chr = "{(0::nat)..(196607)}" morphisms as_nat chr by auto
setup_lifting type_definition_uc_chr


lemma [code abstype]: "chr (as_nat x) = x" by (rule as_nat_inverse)
code_datatype chr



instantiation uc_chr::one begin  
lift_definition one_chr::uc_chr is "1" by auto
instance ..
end 

instantiation uc_chr::zero begin 
lift_definition zero_chr::uc_chr is "0" by auto
instance ..
end

instantiation uc_chr::equal begin
lift_definition equal_uc_chr :: "uc_chr \<Rightarrow> uc_chr \<Rightarrow> bool"
  is "\<lambda> a b. a = b" .
instance apply(standard; transfer)
  by (auto)
end

instantiation uc_chr::linorder begin
lift_definition less_eq_uc_chr::"uc_chr \<Rightarrow> uc_chr \<Rightarrow> bool" is "\<lambda> a b. a \<le> b" .
lift_definition less_uc_chr::"uc_chr \<Rightarrow> uc_chr\<Rightarrow> bool" is "\<lambda> a b. a < b" .

instance apply(standard) 
  using less_uc_chr.rep_eq less_eq_uc_chr.rep_eq apply auto
  using as_nat_inject by auto
end



lemma[simp]: "x\<in>{(0::nat)..(196607)} \<Longrightarrow> as_nat (chr x) = x" 
  by (simp add: chr_inverse)

lemma[simp]: "x < 196608 \<and> y < 196608 \<Longrightarrow> chr x \<le> chr y \<longleftrightarrow> x \<le> y"
  apply (auto)
  by (simp_all add: eq_onp_same_args less_eq_uc_chr.abs_eq)

lemma[simp]: "x < 196608 \<and> y < 196608 \<Longrightarrow> chr x < chr y \<longleftrightarrow> x < y"
  apply (auto)
  by (simp_all add: eq_onp_same_args less_uc_chr.abs_eq)

lemma[simp]: "x < 196608 \<and> y < 196608 \<Longrightarrow> chr y = chr x \<longleftrightarrow> x = y" 
  apply(auto)
  by (simp add: chr_inject)




type_synonym uc_word = "uc_chr word"
type_synonym uc_regex = "uc_chr regex"

definition UC:: "uc_word set" where "UC = {w. True}"


subsection "Interpretation of the SMT-LIB theory of strings symbols"

text "In the following, we interpret all symbols of the SMT-LIB theory of strings.
The interpretations are based on primitive functions implemented on lists and regular expressions.
Note that the symbols are not identical to the one state in the SMT-LIB theory due to syntactic
restrictions of Isabelle/HOL. However, there is a one to one mapping between the symbols used here
and the symbols used in SMT-LIB. This mapping is specified in 'spec.json'."


abbreviation str_concat:: "uc_word \<Rightarrow> uc_word  \<Rightarrow> uc_word" where 
  "(str_concat) u v \<equiv> u\<cdot>v" 

abbreviation str_len:: "uc_word \<Rightarrow> int" ("\<bar>_\<bar>") where  
  "str_len w \<equiv> of_nat (length w)"

abbreviation str_at:: "uc_word \<Rightarrow> int \<Rightarrow> uc_word" where 
  "str_at w i \<equiv> if i \<ge> 0 then w[(nat i); (nat i+1)] else \<epsilon>"

abbreviation str_substr:: "uc_word \<Rightarrow> int \<Rightarrow> int \<Rightarrow> uc_word" where 
  "str_substr w m n \<equiv> if (n \<ge> 0 \<and> 0\<le>m \<and> ((nat m) \<le> (length w)-1)) then  w[(nat m);(nat (m+n))] else \<epsilon>"

abbreviation str_prefixof:: "uc_word \<Rightarrow> uc_word \<Rightarrow> bool" where 
  "str_prefixof \<equiv> prefix"

abbreviation str_suffixof:: "uc_word \<Rightarrow> uc_word \<Rightarrow> bool" where 
  "str_suffixof \<equiv> suffix"

abbreviation str_contains:: "uc_word \<Rightarrow> uc_word \<Rightarrow> bool" where 
  "str_contains \<equiv> Words.contains"


(* This is a corrected version of str.indexof, the original one is not well-defined (see model proof below)*)
abbreviation str_indexof:: "uc_word \<Rightarrow> uc_word \<Rightarrow> int \<Rightarrow> int" where 
  "str_indexof w v i \<equiv> (if i\<ge>0 \<and>  (str_contains (str_substr w i \<bar>w\<bar>) v) \<and> i\<le>\<bar>w\<bar> then Int.int (indexof_nat w v (Int.nat i)) else -1)"

abbreviation str_replace:: "uc_word \<Rightarrow> uc_word \<Rightarrow> uc_word \<Rightarrow> uc_word" where 
  "str_replace \<equiv> replace"

(* str_replace_all added by Jibiana Jakpor. TODO: Prove that it matches SMT-LIB spec. *)
fun str_replace_all ::  "uc_word \<Rightarrow> uc_word \<Rightarrow> uc_word \<Rightarrow> uc_word" where
"str_replace_all s \<epsilon> t' = s" |
"str_replace_all \<epsilon> t t' = \<epsilon>" |
"str_replace_all s t t' = (if (str_contains s t = False) then s else
  (let u1 = (take (nat (str_indexof s t 0)) s); 
       u2 = drop (length u1 + length t) s in
       u1\<cdot>t'\<cdot> (str_replace_all u2 t t')))"


abbreviation str_in_re:: "uc_word \<Rightarrow> uc_regex \<Rightarrow> bool" where 
  "str_in_re w r \<equiv> nullable (rderivw w r)"

(* Not an SMT-LIB symbol interpretation but a predicate pulled from the Model Proofs section to be
   used in str_replace_re.
 *)
abbreviation shortest_word where
  "shortest_word w P \<equiv> P w \<and> (\<forall>w'. P w' \<longrightarrow> \<bar>w\<bar> \<le> \<bar>w'\<bar>)"

(* str_replace_re added by Jibiana Jakpor. This definition mirrors the SMT-LIB specification. *)
function  str_replace_re :: "uc_word \<Rightarrow> uc_regex \<Rightarrow> uc_word \<Rightarrow> uc_word" where
  "(\<not> (\<exists>s. str_contains w s \<and> str_in_re s L)) \<Longrightarrow> str_replace_re w L w2 = w" |
"\<exists>s.  str_contains w s \<and> str_in_re s L \<Longrightarrow> str_replace_re w L w2 = 
  (let u1 = (THE u1'. (shortest_word u1' (\<lambda>u. \<exists>w1 u2. (str_in_re w1 L \<and> u \<cdot> w1 \<cdot> u2 = w))));
   w1 = (THE w1'. shortest_word w1' (\<lambda>w1''. \<exists>u2'. u1 \<cdot> w1'' \<cdot> u2' = w \<and> str_in_re w1'' L));  
  u2 = THE u2'. u1 \<cdot> w1 \<cdot> u2' = w   in 
    (u1 \<cdot> w2 \<cdot> u2) )"
  apply auto
  apply atomize_elim
  apply auto
  done

termination by lexicographic_order

abbreviation str_replace_re_all:: "uc_word \<Rightarrow> uc_regex \<Rightarrow> uc_word \<Rightarrow> uc_word" where 
  "str_replace_re_all \<equiv> undefined"

abbreviation str_to_re:: "uc_word \<Rightarrow> uc_regex" where 
  "str_to_re w \<equiv> regex.Const w"

abbreviation re_none:: "uc_regex" where 
  "re_none \<equiv> regex.None"

abbreviation re_allchar:: "uc_regex" where 
  "re_allchar \<equiv> regex.Any"

abbreviation re_all::"uc_regex" where
  "re_all \<equiv> re_star re_allchar"

abbreviation re_concat:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where 
  "re_concat \<equiv> RegEx.re_concat"

abbreviation re_union:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where
  "re_union  \<equiv> RegEx.re_union"

abbreviation re_inter:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where 
  "re_inter  \<equiv> RegEx.re_inter"

abbreviation re_star:: "uc_regex \<Rightarrow>uc_regex" where 
  "re_star \<equiv> RegEx.re_star"

abbreviation re_plus:: "uc_regex \<Rightarrow> uc_regex" where 
  "re_plus r \<equiv> RegEx.re_plus r"

fun re_range:: "uc_word \<Rightarrow> uc_word \<Rightarrow> uc_regex" where 
  "re_range (l#\<epsilon>) (u#\<epsilon>) = RegEx.re_range l u"|
  "re_range _ _ = RegEx.None"

abbreviation re_opt::"uc_regex \<Rightarrow> uc_regex" where 
  "re_opt r \<equiv> re_union (Const \<epsilon>) r"

abbreviation re_comp::"uc_regex \<Rightarrow> uc_regex" where
  "re_comp \<equiv> RegEx.re_comp"

abbreviation re_diff:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where
  "re_diff \<equiv> RegEx.re_diff"

abbreviation re_pow::"nat \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where
  "re_pow n r \<equiv> RegEx.re_pow r n"

abbreviation re_loop:: "nat \<Rightarrow> nat \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where 
  "re_loop a b r \<equiv> RegEx.re_loop r a b"

(* String-Integer-Conversion *)

fun chr_to_code::"uc_chr \<Rightarrow> int" where "chr_to_code c = int (as_nat c)"

fun chr_to_digit::"uc_chr \<Rightarrow> int" where
  "chr_to_digit c = (let v = chr_to_code c in
  if v = 48 then 0 else 
  if v = 49 then 1 else 
  if v = 50 then 2 else 
  if v = 51 then 3 else 
  if v = 52 then 4 else 
  if v = 53 then 5 else 
  if v = 54 then 6 else 
  if v = 55 then 7 else 
  if v = 56 then 8 else 
  if v = 57 then 9 else -1
)"

fun digit_to_chr::"int \<Rightarrow> uc_chr" where
  "digit_to_chr d = (
  if d = 0 then (chr 48) else
  if d = 1 then (chr 49) else
  if d = 2 then  (chr 50) else
  if d = 3 then  (chr 51) else
  if d = 4 then  (chr 52) else
  if d = 5 then  (chr 53) else
  if d = 6 then  (chr 54) else
  if d = 7 then  (chr 55) else
  if d = 8 then  (chr 56) else
  if d = 9 then  (chr 57) else (chr 0)
)"


fun nat_digit_to_chr::"nat \<Rightarrow> uc_chr" where
  "nat_digit_to_chr d = (
  if d = 0 then (chr 48) else
  if d = 1 then (chr 49) else
  if d = 2 then  (chr 50) else
  if d = 3 then  (chr 51) else
  if d = 4 then  (chr 52) else
  if d = 5 then  (chr 53) else
  if d = 6 then  (chr 54) else
  if d = 7 then  (chr 55) else
  if d = 8 then  (chr 56) else
  if d = 9 then  (chr 57) else (chr 0)
)"



fun chr_is_digit::"uc_chr \<Rightarrow> bool" where
  "chr_is_digit x = (chr_to_digit x \<ge> 0)"



fun is_digit::"uc_word \<Rightarrow> bool" where
  "is_digit (x#\<epsilon>) = chr_is_digit x"|
  "is_digit _ = False"



fun to_code::"uc_word \<Rightarrow> int" where
  "to_code (x#\<epsilon>) = chr_to_code x" |
  "to_code _ = -1"


fun from_code:: "int \<Rightarrow> uc_word" where 
  "from_code n = (if 0\<le> n \<and> n \<le> 196607 then [(chr (nat n))] else \<epsilon>)"


fun digs_to_int::"int list \<Rightarrow> int" where
  "digs_to_int (x#\<epsilon>) = x"|  
  "digs_to_int (x#xs) = (((10::int)^(length xs))*x)+digs_to_int xs"|
  "digs_to_int \<epsilon> = -1"


fun nat_pos::"nat \<Rightarrow> nat" where 
  "nat_pos n = (let d = (n div 10) in if d = 0 then 1 else 1+(nat_pos d))"


fun nat_to_digs::"nat \<Rightarrow> int list" where 
  "nat_to_digs x = (if x\<le>9 then [(int x)] else (nat_to_digs (x div 10))@[(int (x mod 10))])"


primrec all_digits::"int list \<Rightarrow> bool" where 
  "all_digits \<epsilon> = True" |
  "all_digits (x#xs) = (0 \<le> x \<and> x\<le>9 \<and> all_digits xs)"

primrec all_digit_chrs::"uc_word \<Rightarrow> bool" where
  "all_digit_chrs \<epsilon> = True" |
  "all_digit_chrs (a#w) = (chr_is_digit a \<and> (all_digit_chrs w))"


fun to_int::"uc_word \<Rightarrow> int" where
  "to_int \<epsilon> = -1" |
  "to_int (a#\<epsilon>) = (chr_to_digit a)" |
  "to_int w = (let n = (chr_to_digit (last w)) in let r= (to_int (butlast w)) in if n \<ge> 0 \<and> r \<ge> 0 then 10*r + n else -1)"

fun from_nat::"nat \<Rightarrow> uc_word" where
  "from_nat n = (if (n \<le> 9) then [(nat_digit_to_chr n)] else (from_nat (n div 10))@[(nat_digit_to_chr (n mod 10))])"

fun from_int::"int \<Rightarrow> uc_word" where 
  "from_int i = (if i<0 then \<epsilon> else from_nat (nat i))"

(* Operators specific to cvc5. Added by Jibiana Jakpor. *)
abbreviation str_rev :: "uc_word \<Rightarrow> uc_word" where
"str_rev \<equiv> rev"

definition uc_chr_to_lower :: "uc_chr \<Rightarrow> uc_chr" where
"uc_chr_to_lower si \<equiv> (let x = as_nat si in
  chr (x + (if 65 \<le> x \<and> x \<le> 90 then 32 else 0))
  )"

definition str_to_lower :: "uc_word \<Rightarrow> uc_word" where
"str_to_lower w \<equiv> map uc_chr_to_lower w"

definition uc_chr_to_upper :: "uc_chr \<Rightarrow> uc_chr" where
"uc_chr_to_upper si \<equiv> (let x = as_nat si in
  chr (x - (if 97 \<le> x \<and> x \<le> 122 then 32 else 0)))"

definition str_to_upper :: "uc_word \<Rightarrow> uc_word" where
"str_to_upper w \<equiv> map uc_chr_to_upper w"

lemma str_to_upper_cons:
  fixes a :: "uc_chr" and s :: "uc_word"
  shows "str_to_upper (a # s) = (uc_chr_to_upper a) # (str_to_upper s)"
  by (simp add: str_to_upper_def)

lemma uc_chr_to_lower_upper:
  fixes c :: "uc_chr"
  shows "uc_chr_to_lower (uc_chr_to_upper c) = uc_chr_to_lower c"
proof (cases "97 \<le> as_nat c \<and> as_nat c \<le> 122")
  case True
  define c' where c'_def: "c' = (uc_chr_to_upper c)"
  have upper_range: "65 \<le> as_nat c' \<and> as_nat c' \<le> 90" using True c'_def uc_chr_to_upper_def
    by auto
  have upper_val: "as_nat c' = as_nat c - 32" using c'_def True c'_def uc_chr_to_upper_def 
    by auto
  define d where d_def: "d = uc_chr_to_lower c'"
  then have d_def2: "d = uc_chr_to_lower (uc_chr_to_upper c)" using d_def c'_def 
    by auto
  have lower_upper_val: "as_nat d = as_nat c' + 32" using c'_def True d_def uc_chr_to_lower_def upper_range 
    by auto
  have "as_nat d = as_nat c" using upper_val lower_upper_val upper_range 
    by linarith
  hence "c = d" using as_nat_inverse 
    by metis
  have "uc_chr_to_lower c = c" using True uc_chr_to_lower_def 
    by (simp add: as_nat_inverse)
  then show ?thesis using d_def2 \<open>c=d\<close> 
    by order
next
  case False
  then show ?thesis using uc_chr_to_lower_def uc_chr_to_upper_def as_nat_inverse by auto
qed

lemma str_to_lower_cons:
  fixes a :: "uc_chr" and s :: "uc_word"
  shows "str_to_lower (a # s) = (uc_chr_to_lower a) # (str_to_lower s)"
  by (simp add: str_to_lower_def)

lemma uc_chr_to_upper_lower:
  fixes c :: "uc_chr"
  shows "uc_chr_to_upper (uc_chr_to_lower c) = uc_chr_to_upper c"
proof (cases "65 \<le> as_nat c \<and> as_nat c \<le> 90")
  case True
  define c' where c'_def: "c' = (uc_chr_to_lower c)"
  have lower_range: "97 \<le> as_nat c' \<and> as_nat c' \<le> 122" using True c'_def uc_chr_to_lower_def
    by auto
  have lower_val: "as_nat c' = as_nat c + 32" using c'_def True c'_def uc_chr_to_lower_def 
    by auto
  define d where d_def: "d = uc_chr_to_upper c'"
  then have d_def2: "d = uc_chr_to_upper (uc_chr_to_lower c)" using d_def c'_def 
    by auto
  have upper_lower_val: "as_nat d = as_nat c' - 32" using c'_def True d_def uc_chr_to_lower_def 
    by (simp add: as_nat_inverse lower_val uc_chr_to_upper_def)
  have "as_nat d = as_nat c" using lower_val upper_lower_val lower_range 
    by linarith
  hence "c = d" using as_nat_inverse 
    by metis
  have "uc_chr_to_upper c = c" using True uc_chr_to_upper_def 
    by (simp add: as_nat_inverse)
  then show ?thesis using d_def2 \<open>c=d\<close> 
    by order
next
  case False
  then show ?thesis using uc_chr_to_lower_def uc_chr_to_upper_def as_nat_inverse by auto
qed

subsection "Model Proofs"

text "We shows that our interpretation of the symbols satisfy all conditions stated by the SMT-LIB theory 
of strings."

abbreviation smallest_set where
  "smallest_set K P \<equiv> P K \<and> (\<forall>K'. P K' \<longrightarrow> K \<subseteq> K')"

abbreviation smallest_int where
  "smallest_int n P \<equiv> P n \<and> (\<forall>n'. P n' \<longrightarrow> n \<le> n')"

(* abbreviation shortest_word where
  "shortest_word w P \<equiv> P w \<and> (\<forall>w'. P w' \<longrightarrow> \<bar>w\<bar> \<le> \<bar>w'\<bar>)" 
  defined above
*)

theorem "UNIV = UC"  
  by (simp add: UC_def)

subsubsection "Lexicographic order"

theorem lexord_strict:"v < w \<longleftrightarrow> (v, w) \<in> lexord {(a, b). a<b}" 
  by (simp add: list_less_def)

theorem lexord:"v \<le> w \<longleftrightarrow> (v, w) \<in> lexord {(a, b). a<b} \<or> v = w" 
  by (simp add: list_le_def list_less_def)

subsubsection "Length"

text "Some lemmas about string length used later on"


lemma length_int_nat: "\<bar>w\<bar> = int (length w)" 
  by auto

lemma length_int_nat_le: "m \<ge> 0 \<Longrightarrow> m \<le> \<bar>w\<bar> \<longleftrightarrow> (nat m) \<le> (length w)"
  by auto

lemma length_int_nat_sub: "m \<ge> 0 \<Longrightarrow> m \<le> \<bar>w\<bar> \<Longrightarrow> int ((length w) - (nat m)) = (\<bar>w\<bar> - m)"
  by auto

lemma length_int_nat_min: "m \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> int (min (nat m) (nat n)) = min m n"
  by auto

lemma length_int_nat_sub_min:
  assumes "\<bar>w\<bar> \<ge> m"
    and "n \<ge> 0"
    and "m \<ge> 0"
  shows "int (min (nat n) ((length w)-nat m)) = (min n (\<bar>w\<bar>- m))"
  using assms by auto

lemma of_nat_nat_inv: "x \<ge> 0 \<Longrightarrow> of_nat (nat x) = x" 
  by auto


subsubsection "Substrings (str.at, str.substr)"

theorem str_at:"str_at w n = str_substr w n 1" 
  by (simp split: if_splits add: diff_nat_eq_if)

lemma substr_factor_equal:
  assumes "0 \<le> m"
    and "m < \<bar>w\<bar>"
    and "0 < n"
  shows "str_substr w m n = (w[nat m; nat m + nat n])"
  using assms diff_nat_eq_if by auto
(*
theorem str_substr1_old:
  assumes "0 \<le> m" and "m < \<bar>w\<bar>" and "0 < n"
  shows "\<exists>!v. str_substr w m n = v \<and> (\<exists>x y. w =  x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and>  \<bar>v\<bar> = min n (\<bar>w\<bar> - m))"
proof -
  from assms have "nat m < (length w) \<and> nat m \<le> nat m + nat n" by auto
  then have "\<exists>!v. (w[nat m; nat m + nat n]) = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = nat m \<and>
               (length v) = min ((nat m + nat n)-nat m) ((length w)-nat m))" 
    using factorization by metis
  then have "\<exists>!v. (w[nat m; nat m + nat n]) = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> (length v) = min (nat n) ((length w)-nat m))" 
    by (metis add_diff_cancel_left' assms(1) int_nat_eq)
  then have "\<exists>!v. str_substr w m n = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> (length v) = min (nat n) ((length w)-nat m))" 
    using assms substr_factor_equal by presburger
  then have "\<exists>!v. str_substr w m n = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = int (min (nat n) ((length w)-nat m)))" 
    by simp
  then have "\<exists>!v. str_substr w m n = v \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = (min n (\<bar>w\<bar>- m)))" 
    using length_int_nat_sub_min assms by auto
  then show ?thesis 
    by blast
qed
*)

theorem str_substr11_aux:
  assumes "0 \<le> m" and "m < \<bar>w\<bar>" and "0 < n"
  assumes "v = str_substr w m n"
  shows "(\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = min n (\<bar>w\<bar> - m))"
proof -
  have v_factor: "v = (w[nat m; nat m + nat n])"
    using assms substr_factor_equal by blast

  from assms have "nat m < (length w) \<and> nat m \<le> nat m + nat n" by auto
  then have "(\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = nat m \<and>
               (length v) = min ((nat m + nat n)-nat m) ((length w)-nat m))" 
    using factorization v_factor by metis
  then have "(\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> (length v) = min (nat n) ((length w)-nat m))" 
    by (metis add_diff_cancel_left' assms(1) int_nat_eq)
  then have "(\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = int (min (nat n) ((length w)-nat m)))"
    by simp
  then have "\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = (min n (\<bar>w\<bar>- m))" 
    using length_int_nat_sub_min assms by auto
  then show ?thesis
    using assms(4) by force
qed

theorem str_substr_exists:
  assumes "0 \<le> m" and "m < \<bar>w\<bar>" and "0 < n"
  shows "\<exists>v. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = min n (\<bar>w\<bar> - m))"
  using str_substr11_aux assms
  by fastforce

theorem str_substr1_aux:
  assumes "0 \<le> m" and "m < \<bar>w\<bar>" and "0 < n"
  shows "(\<exists>x y. w = x\<cdot>(str_substr w m n)\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>str_substr w m n\<bar> = min n (\<bar>w\<bar> - m))"
  using str_substr11_aux assms by auto

theorem str_substr1_1:
  assumes "0 \<le> m" and "m < \<bar>w\<bar>" and "0 < n"
  shows "\<exists>!v. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = min n (\<bar>w\<bar> - m))"
proof (rule ex_ex1I)
  show "\<exists>v x y. w = str_concat x (str_concat v y) \<and> int (length x) = m \<and>
          int (length v) = min n (int (length w) - m)"
    using str_substr_exists assms by blast
next
  fix v y
  assume "\<exists>x y. w = str_concat x (str_concat v y) \<and> int (length x) = m \<and>
            int (length v) = min n (int (length w) - m)"
  moreover
  assume "\<exists>x ya. w = str_concat x (str_concat y ya) \<and> int (length x) = m \<and>
            int (length y) = min n (int (length w) - m)"
  ultimately
  show "v = y"
    using assms by (metis append_eq_append_conv of_nat_eq_iff) 
qed

theorem str_substr1_2:
  assumes "0 \<le> m" and "m < \<bar>w\<bar>" and "0 < n"
  shows "str_substr w m n = (THE v. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = min n (\<bar>w\<bar> - m)))"
  using theI_unique[OF str_substr1_1[OF assms], of "str_substr w m n"]
    str_substr1_aux[OF assms] by auto

theorem str_substr2:
  assumes "\<not>(0 \<le> m \<and> (m <  \<bar>w\<bar>) \<and> 0 < n)"
  shows "str_substr w m n = \<epsilon>"
proof -
  from assms have "0 > m \<or> m \<ge> \<bar>w\<bar> \<or> 0 \<ge> n" by auto
  then show ?thesis by fastforce
qed


subsubsection "Factors (str.prefixof, str.suffixof, str.contains)"

theorem str_prefix[simp]: "str_prefixof v w \<longleftrightarrow> (\<exists>x. w = v\<cdot>x)"   by (simp add: prefix_def)

theorem str_suffix[simp]: "str_suffixof v w \<longleftrightarrow> (\<exists>x. w = x\<cdot>v)"   by (simp add: suffix_def)

theorem str_contains: "str_contains w v \<longleftrightarrow> (\<exists>x y. w = x\<cdot>v\<cdot>y)" 
  by (auto simp add: contains_iff_factor sublist_def)


subsubsection "Searching and replacing (str.indexof, str.replace variants)"


text "The SMT-LIB standard states the following theorems

str_contains v w \<Longrightarrow> \<exists>n. str_indexof w v i = n \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. n' < n \<longrightarrow> (\<exists>x' y'. w = x'\<cdot>v\<cdot>y' \<and> i \<le> n' \<and> n = \<bar>x'\<bar>)) and
\<not>str_contains v w \<Longrightarrow> str_indexof w v i = -1 and

However, they are inconsistent. We find counterexamples.

- if i\<le>\<bar>w\<bar> no such n exists 
  - Example: (indexof 'ab' \<epsilon> 3 = n) but no n wa and words x y satisfy 'ab' = x\<cdot>\<epsilon>\<cdot>y \<and> \<bar>x\<bar>=n \<and> n\<ge>3
- if (str_contains v w) but not str_contains (str_substr w i \<bar>w\<bar>) v, then no such n exists
  - Example: (indexof 'ab' 'a' 1 = n) but no n and words x y satisfy 'ab' = x\<cdot>'a'\<cdot>y \<and> \<bar>x\<bar> = n \<and> n\<ge>1

To be consistent, we need (str_contains (str_substr w i \<bar>w\<bar>) v)  instad of 
(str_contains v w), and additionally need the premise i\<le>\<bar>w\<bar>.
If either of these premises is not met, or i<0, the the function must evaluate to -1.
"

theorem str_indexof1:
  assumes "i\<ge>0" and "i\<le> \<bar>w\<bar>" and "str_contains (str_substr w i \<bar>w\<bar>) v"
  shows "\<exists>n. str_indexof w v i = n \<and> smallest_int n (\<lambda>n. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = \<bar>x\<bar>))" 
proof -
  have "nat i \<le> length w"
    using assms(2) nat_le_iff
    by auto
  moreover
  have "sublist v (drop (nat i) w)"
    by (smt (verit, best) assms(3) contains_iff_factor dual_order.refl factor.elims(1) 
        factor_suffix nat_add_distrib nat_int sublist_Nil_left sublist_Nil_right trans_le_add2)
  ultimately
  have "smallest_int (indexof_nat w v (Int.nat i)) (\<lambda>n. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (Int.nat i) \<le> n \<and> n = length x))"
    using str_indexof_nat1[of "Int.nat i" w v] by auto
  then show ?thesis
   by (metis assms nat_int nat_le_iff)
qed

theorem str_indexof2: 
  assumes "i<0 \<or> i>\<bar>w\<bar> \<or> \<not> str_contains (str_substr w i \<bar>w\<bar>) v" 
  shows "str_indexof w v i = -1" 
proof -
  {
    assume "i<0"
    then have ?thesis
      by auto
  }
  moreover
  {
    assume "\<not> str_contains (str_substr w i \<bar>w\<bar>) v" 
    then have ?thesis
      using assms indexof_if_not_contains''' by presburger
  }
  moreover
  {
    assume "i>\<bar>w\<bar>"
    then have ?thesis
      using assms by auto 
  }
  ultimately show ?thesis 
    using assms by metis
qed

theorem str_replace1:
  assumes "str_contains w v"
  shows "\<exists>x y. str_replace w v u = x\<cdot>u\<cdot>y \<and> w = x\<cdot>v\<cdot>y \<and> (\<forall> x'. (\<exists>y'. w=x'\<cdot>v\<cdot>y') \<longrightarrow> \<bar>x\<bar> \<le> \<bar>x'\<bar>)"
  using replace_first_factor 
  by (metis assms of_nat_mono)


theorem str_replace2: 
  assumes "\<not> str_contains w v"
  shows "str_replace w v u = w" 
  using assms replace_id_if_not_contains by blast

(* TODO: Add replace_all, replace_re, replace_all_re! *)


subsubsection "Regular languages"

text "We represent regular languages using regular expression accompanied by a `lang` function that
maps expression to languages."

text "We first who that this `lang` operator maps into the power set of all unicode strings"

theorem re_lang_unicode: "range (lang::(uc_chr regex \<Rightarrow> uc_chr word set)) \<subseteq> Pow UC"
  using UC_def by force

theorem str_to_re: "lang (str_to_re w) = {w}" by auto

theorem str_in_re: "str_in_re w R \<longleftrightarrow> w \<in> (lang R)" 
  by (auto simp add: derivw_nullable_contains contains_derivw_nullable)


paragraph "Regular Operators"

theorem re_none: "lang re_none = {}" by auto

theorem re_allchar: "lang re_allchar = {w. \<bar>w\<bar> = 1}" by auto

theorem re_all: "lang re_all = UC"
  using UC_def star_any_is_univ by auto

theorem re_concat: "lang (re_concat r e) = {x\<cdot>y|x y. x \<in> lang r \<and> y \<in> lang e}" 
  by (simp add: Regular.concat_def re_concat_correct)

theorem re_union: "lang (re_union r e) = {w|w. w \<in> lang r \<or> w \<in> lang e}" 
  by (simp add: Un_def re_union_correct)

theorem re_inter: "lang (re_inter r1 r2) = {w|w. w\<in> lang r1 \<and> w \<in> lang r2}" 
  by (auto simp add:  re_inter_correct)

lemma Star_smallest:
  assumes "w \<in> (pow (lang r) n)"
  assumes "\<epsilon> \<in> K'"
  assumes "{x \<cdot> y |x y. x \<in> lang r \<and> y \<in> K'} \<subseteq> K'"
  shows "w \<in> K'"
  using assms
proof (induction n arbitrary: w)
  case 0
  then show ?case
    by (simp add: star_all_pows star_of_empty)
next
  case (Suc n)
  from Suc(2) have "\<exists>u v. w = u \<cdot> v \<and> u \<in> (lang r) \<and> v \<in> pow (lang r) n"
    by (simp add: Regular.concat_def)
  then obtain u v where u_v_p: "w = u \<cdot> v" "u \<in> lang r" "v \<in> pow (lang r) n"
    by auto
  then have "v \<in> K'"
    using Suc(1)[of v] Suc(3) Suc(4) by auto
  then show ?case
    using u_v_p Suc by auto
qed

abbreviation smallest where
  "smallest K P \<equiv> P K \<and> (\<forall>K'. P K' \<longrightarrow> K \<subseteq> K')"

theorem re_star: "smallest (lang (Star r)) (\<lambda>K. \<epsilon> \<in> K \<and> {x\<cdot>y | x y. x \<in> lang r \<and> y \<in> K} \<subseteq> K)"
proof -
  have "\<epsilon> \<in> lang (r\<^sup>\<star>)"
    by simp
  moreover
  have "{x \<cdot> y |x y. x \<in> lang r \<and> y \<in> lang (r\<^sup>\<star>)} \<subseteq> lang (r\<^sup>\<star>)"
    by (auto simp add: concat_containment re_star_correct star_subsumes)
  moreover
  have "(\<forall>K'. \<epsilon> \<in> K' \<and> {x \<cdot> y |x y. x \<in> lang r \<and> y \<in> K'} \<subseteq> K' \<longrightarrow> lang (r\<^sup>\<star>) \<subseteq> K')"
    using Star_smallest by (auto simp add: star_def)
  ultimately
  show ?thesis
    by auto
qed

theorem re_plus: "lang (re_plus r) = lang (re_concat r (re_star r))"  
  by auto

theorem re_range1: "\<bar>l\<bar> = 1 \<and> \<bar>u\<bar> = 1 \<Longrightarrow> lang (re_range l u) = {v| v. l \<le> v \<and>  v\<le>u \<and> \<bar>v\<bar> = 1}" 
  apply(cases \<open>(l, u)\<close> rule: re_range.cases)
  apply (auto split: if_splits)
  apply (metis (no_types, lifting) Cons_less_Cons length_0_conv length_Suc_conv linorder_not_le)
  by (meson Cons_le_Cons dual_order.trans)

theorem re_range2: "\<bar>l\<bar> \<noteq> 1 \<or> \<bar>u\<bar> \<noteq> 1 \<Longrightarrow> lang (re_range l u) = {}" 
  by (cases \<open>(l, u)\<close> rule:re_range.cases) (auto split: if_splits)

theorem re_comp: "lang (re_comp r) = UNIV - (lang r)"
  by (simp add: Compl_eq_Diff_UNIV re_comp_correct)

theorem re_diff: "lang (re_diff r1 r2) = lang r1 - lang r2" 
  by (simp add: re_diff_correct)

theorem re_pow1: "lang (re_pow 0 r) = {\<epsilon>}" 
  by auto

theorem re_pow2: "\<forall>n. re_pow (Suc n) r =  re_concat r (re_pow n r)" 
  by simp

theorem re_loop1: 
  assumes "a \<le> b"
  shows "lang (re_loop a b r) = (\<Union>x\<in>{a..b}. (lang (re_pow x r)))"
  using re_loop_iff1[of a b] using assms atLeastAtMost_iff by fastforce

theorem re_loop2: "a > b \<Longrightarrow> lang (re_loop a b r) = {}" 
  by (simp add: re_loop_None_if)

subsubsection "String Number Conversions"


lemma chr_digit_inv: "i\<in>{0..9} \<Longrightarrow> chr_to_digit (digit_to_chr i) =  i"
  apply(auto) 
  by presburger


theorem is_digit: "is_digit x \<longleftrightarrow> (\<exists>c. x=(c#\<epsilon>) \<and> 48 \<le> as_nat c \<and> as_nat c \<le> 57)"
  apply(cases \<open>x\<close> rule: is_digit.cases)
    apply simp_all
  subgoal for x
    apply (cases "as_nat x = (48::nat)")
     apply simp_all
    apply (cases "as_nat x = (49::nat)")
     apply simp_all
    apply (cases "as_nat x = (50::nat)")
     apply simp_all
    apply (cases "as_nat x = (51::nat)")
     apply simp_all
    apply (cases "as_nat x = (52::nat)")
     apply simp_all
    apply (cases "as_nat x = (53::nat)")
     apply simp_all
    apply (cases "as_nat x = (54::nat)")
     apply simp_all
    apply (cases "as_nat x = (55::nat)")
     apply simp_all
    apply (cases "as_nat x = (56::nat)")
     apply simp_all
    apply (cases "as_nat x = (57::nat)")
     apply simp_all
    apply (cases "as_nat x \<ge> (48::nat)")
    apply presburger
    apply (cases "as_nat x \<ge> (57::nat)")
     apply presburger
    apply blast
    done
  done

theorem to_code1: "\<bar>w\<bar> \<noteq> 1 \<Longrightarrow> to_code w = -1"
  apply(cases \<open>w\<close> rule: to_code.cases) by auto

theorem to_code2: "w = [c] \<Longrightarrow> to_code w = int (as_nat c)"
  apply(cases \<open>w\<close> rule: to_code.cases) by auto

theorem from_code1: "0 \<le> n \<Longrightarrow> n \<le> 196607 \<Longrightarrow> from_code n = [(chr (nat n))]"
  by auto

theorem from_code2: "n<0 \<or>  196607 < n \<Longrightarrow> from_code n = \<epsilon>"
  by auto


lemma is_digit_iff_conv_positive:"\<not>(chr_is_digit c) \<longleftrightarrow> chr_to_digit c = -1"
  apply(auto)
  by (smt (verit) linordered_nonzero_semiring_class.zero_le_one zero_le_numeral)

lemma to_int_chr_iff:"to_int [c] \<ge> 0 \<longleftrightarrow> chr_is_digit c"
  by (auto split: if_splits simp add: Let_def)

theorem to_int1': "length w = n \<Longrightarrow> to_int w = -1 \<longleftrightarrow> w = \<epsilon> \<or> (\<exists>c \<in> set w. \<not>chr_is_digit c)"
proof (induction n arbitrary: w rule: less_induct)
  case (less n)
  show ?case
  proof (cases w)
    case Nil
    then show ?thesis
      by simp
  next
    case (Cons a w'')
    note outer_Cons = Cons
    show ?thesis
    proof (cases w'')
      case Nil
      then show ?thesis  
        using outer_Cons
        by (metis is_digit_iff_conv_positive length_pos_if_in_set less_numeral_extra(3)
            list.set_intros(1) list.size(3) set_ConsD to_int.simps(2))
    next
      case (Cons a' w')
      have "((if 0 \<le> chr_to_digit (last (a # a' # w')) \<and> 0 \<le> (to_int (butlast (a # a' # w'))) then 
               10 * (to_int (butlast (a # a' # w'))) + chr_to_digit (last (a # a' # w')) 
              else - 1) = - 1)
            \<longleftrightarrow> (\<exists>c\<in>set (a # a' # w'). \<not> chr_is_digit c)"
      proof (cases "0 \<le> chr_to_digit (last (a # a' # w')) \<and> 0 \<le> (to_int (butlast (a # a' # w')))")
        case True
        have "\<forall>c\<in>set (butlast (a # a' # w')). chr_is_digit c"
          by (metis True diff_less in_set_butlastD length_butlast length_pos_if_in_set less.IH
              less.prems less_minus_one_simps(1) less_numeral_extra(1) linorder_not_le local.Cons
              outer_Cons)
        moreover
        have "chr_is_digit (last (a # a' # w'))"
          using True chr_is_digit.simps by presburger
        ultimately
        have b: "(\<forall>c\<in>set (a # a' # w'). chr_is_digit c)"
          using append_butlast_last_id[of "a # a' # w'"]
          by (metis list.discI rotate1.simps(2) set_ConsD set_rotate1)
        then have b: "\<not>(\<exists>c\<in>set (a # a' # w'). \<not> chr_is_digit c)"
          by auto
        then show ?thesis
          using True by presburger
      next
        case False
        then have "(\<exists>c\<in>set (a # a' # w'). \<not> chr_is_digit c)"
          by (smt (verit, ccfv_SIG) One_nat_def butlast.simps(2) chr_is_digit.elims(1) diff_less 
              in_set_butlastD last_in_set length_butlast length_greater_0_conv less(2) less.IH lessI 
              list.discI list.set_intros(1) local.Cons outer_Cons to_int.elims)
        then show ?thesis
          using False by presburger
      qed
      then show ?thesis 
        unfolding outer_Cons Cons
        by (smt (verit, del_insts) to_int.simps(1) to_int.simps(3))
    qed
  qed
qed

theorem to_int1:"w = \<epsilon> \<or> w = u\<cdot>[c]\<cdot>v \<and> \<not>chr_is_digit c \<Longrightarrow> to_int w = -1"
  using to_int1' by auto


theorem to_int2: "w=[c] \<Longrightarrow> chr_is_digit c \<Longrightarrow> to_int w = chr_to_digit c"
  by (auto simp add: Let_def)


theorem to_int3: "w=u\<cdot>v \<Longrightarrow> \<bar>v\<bar>=1 \<Longrightarrow> to_int u \<ge> 0 \<Longrightarrow> to_int v \<ge> 0 \<Longrightarrow> to_int w = 10*(to_int u) + (to_int v)"
proof -
  assume a1:"w=u\<cdot>v"
  assume a2:"\<bar>v\<bar>=1"
  assume a3:"to_int u \<ge> 0"
  assume a4:"to_int v \<ge> 0"

  from a1 a2 have p:"\<exists>c. w = u\<cdot>[c]"
    by (simp add: length_Suc_conv)
  then obtain c where c_def:"w = u\<cdot>[c]" by fastforce

  from p a1 a2 have u_def:"v = [c]"  by (simp add: c_def)
  then have "to_int [c] \<ge> 0"  using a4 by blast
  then have c_digit: "chr_is_digit c" using to_int_chr_iff u_def a3 by blast

  from a3  have u:"u \<noteq> \<epsilon>"  by fastforce
  then have w_len:"\<bar>w\<bar>>1" using c_def by auto
  then have x:"\<bar>u\<cdot>[c]\<bar>>1"  using c_def by blast
  then have x:"(\<forall>a. u\<cdot>[c] \<noteq> a#\<epsilon>) \<and>  u\<cdot>[c] \<noteq> \<epsilon>"  by simp


  from a1 u_def have "to_int w  = to_int (u\<cdot>[c])" by simp
  also have "... = (let n = (chr_to_digit (last (u\<cdot>[c]))) in let r= (to_int (butlast (u\<cdot>[c]))) in if n \<ge> 0 \<and> r \<ge> 0 then 10*r + n else -1)"
    using x to_int.elims   by metis
  also have "... = (let n = (chr_to_digit c) in let r= (to_int u) in if n \<ge> 0 \<and> r \<ge> 0 then 10*r + n else -1)"
    by simp
  also have "... = 10*(to_int u) + (chr_to_digit c)" using c_digit by (simp add: a3)

  finally show ?thesis 
    using to_int.simps(2) u_def  by presburger
qed

lemma chr_nat_digit_inv:fixes r::nat shows "r < 10 \<Longrightarrow> chr_to_digit (nat_digit_to_chr r) = (int r) \<and> (int r) \<ge> 0"
  by (auto)

theorem from_nat:"0 \<le> n \<Longrightarrow> from_nat n = w \<Longrightarrow> to_int w = int n" 
proof (induct n arbitrary: w rule: less_induct )
  case ih:(less x)
  then show ?case proof (cases "x<10")
    case True
    then show ?thesis proof -
      assume c1:"x<10"
      then have x:"from_nat x = [(nat_digit_to_chr x)]" by auto
      then have "w = [(nat_digit_to_chr x)]" using ih by auto
      then have "to_int w = to_int [(nat_digit_to_chr x)]" by simp
      also have "... = chr_to_digit (nat_digit_to_chr x)" by simp
      finally have "... = int x" using c1 by fastforce
      then show ?thesis  using x ih by force
    qed
  next
    case False
    then show ?thesis proof -
      assume "\<not>x<10"
      then have c2:"9 < x" by auto

      then have "\<exists>m r. x = 10*m + r \<and> m > 0 \<and> r < 10" by presburger
      then obtain m r where n_eq:"x = 10*m +r \<and> m > 0 \<and> r < 10" by blast
      moreover have r_eq:"r = x mod 10" using calculation by simp
      ultimately have m_eq: "m = x div 10"  by auto

      from c2 have "from_nat x = (from_nat (x div 10))@[(nat_digit_to_chr (x mod 10))]" by auto
      then have from_nat_x_eq:"from_nat x = (from_nat m)@[(nat_digit_to_chr r)]" using r_eq m_eq by auto

      have m_not_eps:"from_nat m \<noteq> \<epsilon>"
        by (metis from_nat.elims self_append_conv2 snoc_eq_iff_butlast) 
      have "[(nat_digit_to_chr r)] \<noteq> \<epsilon>" by simp
      have r_conv:"chr_to_digit (nat_digit_to_chr r) = int r \<and> (int r) \<ge> 0" using n_eq chr_nat_digit_inv
        by blast

      have m_leq_x:"m<x"
        by (simp add: n_eq)

      have "to_int w = to_int ((from_nat m)@[(nat_digit_to_chr r)])" using from_nat_x_eq ih by auto
      also have  "... = (let a = (chr_to_digit  (nat_digit_to_chr r)) in let b= (to_int (from_nat m)) in if a \<ge> 0 \<and> b \<ge> 0 then 10*b + a else -1)" using  m_not_eps to_int.elims r_conv  
        by (smt (verit, best) One_nat_def ih.hyps length_Cons less_imp_le_nat list.size(3) m_leq_x n_eq of_nat_0_le_iff of_nat_1 to_int.simps(2) to_int3)
      also have  "... = (let a = (chr_to_digit  (nat_digit_to_chr r)) in let b= int m in if a \<ge> 0 \<and> b \<ge> 0 then 10*b + a else -1)" using ih.hyps n_eq by fastforce
      also have "... =  (let a = (int r) in let b= int m in if b \<ge> 0 \<and> b \<ge> 0 then 10*b + a else -1)" using chr_nat_digit_inv  r_conv by presburger
      also have "... =  (let a = (int r) in let b= int m in 10*b + a)" by auto
      also have "... =  10*(int m) + (int r)" by auto

      finally show ?thesis using n_eq 
        by simp
    qed
  qed    
qed

theorem from_int1: "n\<ge>0 \<Longrightarrow> from_int n = w \<Longrightarrow> to_int w = n" 
  apply(cases n)
  using from_nat apply force
  by simp

theorem from_int2: "n<0 \<Longrightarrow> from_int n = \<epsilon>" by auto

end
