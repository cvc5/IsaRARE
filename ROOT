session "IsaRARE" (main) = "HOL-CVC" +
 description
  "IsaRARE transforms rewrite rules in the RARE language into Isabelle lemmas"
 sessions
  "HOL-Library"
  "Word_Lib"
 theories
  IsaRARE (global)

session "IsaRARE-Tests" in "Tests" = "IsaRARE" +
  theories
  "IsaRARE_Tests"

session "IsaRARE-Results" in "Tests/Regression" = "HOL-CVC" +
theories
  "EUF_Rewrites"
  "Set_Rewrites"
  "Array_Rewrites"
  "Arith_Rewrites"
  "String_Rewrites"
  "Bitvector_Rewrites"

session "IsaRARE-Results-Autoproven" in "Tests/Regression/Autoproven" = "HOL-CVC" +
theories
  "EUF_Rewrites_Autoproven"
  "Set_Rewrites_Autoproven"
  "Array_Rewrites_Autoproven"
  "Arith_Rewrites_Autoproven"
  "String_Rewrites_Autoproven"
  "Bitvector_Rewrites_Autoproven"
