chapter IsaRARE
    
session IsaRARE = "HOL-CVC" +
 description
  "IsaRARE transforms rewrite rules in the RARE language into Isabelle lemmas"
 sessions
  "HOL-Library"
  "Word_Lib"
 theories
  IsaRARE (global)

session "IsaRARE-Tests" in Tests = IsaRARE +
theories
  "IsaRARE_Tests"

session "IsaRARE-Results" in "Tests/Regression" = "HOL-CVC" +
theories
  "Boolean_Rewrites"
  "UF_Rewrites"
  "Builtin_Rewrites"
  "Set_Rewrites"
  "Array_Rewrites"
