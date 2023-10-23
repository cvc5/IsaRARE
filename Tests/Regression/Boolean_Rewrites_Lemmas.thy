theory Boolean_Rewrites_Lemmas
  imports "HOL-CVC.Dsl_Nary_Ops"
begin
declare[[show_types]]
lemma bool_or_taut_lemma:
 "foldr (\<or>) xss (w \<or> foldr (\<or>) yss (\<not> w \<or> foldr (\<or>) zss False)) = True"
  by (metis (mono_tags, lifting) foldr_or_neutral)

lemma bool_and_conf_lemma:
 "foldr (\<and>) xss (w \<and> foldr (\<and>) yss (\<not> w \<and> foldr (\<and>) zss True)) = False"
  by (metis (mono_tags, opaque_lifting) foldr_and_neutral)

lemma bool_and_dup_lemma:
  "foldr (\<and>) xss (b \<and> foldr (\<and>) yss (b \<and> foldr (\<and>) zss True)) = foldr (\<and>) xss (b \<and> foldr (\<and>) yss (foldr (\<and>) zss True))"
   apply auto[1]
   apply (metis(full_types))
  by (metis(full_types))

lemma bool_and_flatten_lemma:
  "foldr (\<and>) xss ((b \<and> foldr (\<and>) yss True) \<and> foldr (\<and>) zss True) = foldr (\<and>) xss (b \<and> foldr (\<and>) yss (foldr (\<and>) zss True))"
  by (metis(full_types) foldr_and_neutral)

lemma bool_or_dup_lemma:
  "foldr (\<or>) xss (b \<or> foldr (\<or>) yss (b \<or> foldr (\<or>) zss False)) = foldr (\<or>) xss (b \<or> foldr (\<or>) yss (foldr (\<or>) zss False))"
    apply auto[1]
   apply (metis(full_types))
  by (metis(full_types))

lemma bool_or_flatten_lemma:
 "foldr (\<or>) xss ((b \<or> foldr (\<or>) yss False) \<or> foldr (\<or>) zss False) = foldr (\<or>) xss (b \<or> foldr (\<or>) yss (foldr (\<or>) zss False))"
  by (metis(full_types) foldr_or_neutral)

lemma bool_or_true_lemma:
 "foldr (\<or>) xss (True \<or> foldr (\<or>) yss False) = True"
  by simp

lemma bool_or_false_lemma:
 "foldr (\<or>) xss (False \<or> foldr (\<or>) yss False) = foldr (\<or>) xss (foldr (\<or>) yss False)"
  by simp

lemma bool_and_true_lemma:
 "foldr (\<and>) xss (True \<and> foldr (\<and>) yss True) = foldr (\<and>) xss (foldr (\<and>) yss True)"
  by simp

lemma bool_and_false_lemma:
 "foldr (\<and>) xss (False \<and> foldr (\<and>) yss True) = False"
  by simp

end