chapter IsaRARE
    
session IsaRARE = "HOL-CVC" +
 description
  "IsaRARE transforms rewrite rules in the RARE language into Isabelle lemmas"
  options [document = pdf, document_output = "output"]
 sessions
  "HOL-Library"
  "Word_Lib"
 theories [document = true]
  IsaRARE (global)
  document_files
    "root.tex"

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
