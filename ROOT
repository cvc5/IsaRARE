session "IsaRARE" (main) = "HOL-CVC" +
 description
  "IsaRARE transforms rewrite rules in the RARE language into Isabelle lemmas"
 options [document = pdf, document_output = "output",quick_and_dirty]
 sessions
  "HOL-Library"
  "Word_Lib"
 theories
  IsaRARE (global)
 document_files
    "root.tex"

session "IsaRARE-Tests" in "Tests" = "IsaRARE" +
  description
   "Runs IsaRARE on RARE rules from various theories that can be found in Tests/Regressions/."
  sessions
  "HOL-Library"
  "Word_Lib"
  theories
  "IsaRARE_Tests"

session "IsaRARE-Results" in "Tests/Regression" = "HOL-CVC" +
theories
  "EUF_Rewrites"
  "Set_Rewrites"
  "Array_Rewrites"
  "Arith_Rewrites"
  "String_Rewrites"
  "Bitvector_Rewrites_Proven"

session "IsaRARE-Results-Autoproven" in "Tests/Regression/Autoproven" = "HOL-CVC" +
theories
  "EUF_Rewrites_Autoproven"
  "Set_Rewrites_Autoproven"
  "Array_Rewrites_Autoproven"
  "Arith_Rewrites_Autoproven"
  "String_Rewrites_Autoproven"
  "Bitvector_Rewrites_Autoproven"
