theory IsaRARE
  imports "HOL.SMT" "HOL-CVC.Smtlib_String" "HOL-CVC.SMT_CVC" "HOL-CVC.Dsl_Nary_Ops" "HOL-CVC.SMT_Word"
  keywords "parse_rare_file" "parse_rare" :: diag
begin

section \<open>Introduction\<close>

text\<open>IsaRARE is a tool that transforms rewrite rules in the RARE language into Isabelle lemmas.\<close>


section \<open>Components\<close>

ML_file \<open>src/isarare_config.ML\<close>
ML_file \<open>src/parse_rare.ML\<close>
ML_file \<open>src/rare_impl_assump.ML\<close>
ML_file \<open>src/rare_lists.ML\<close>
ML_file \<open>src/write_rewrite_as_lemma.ML\<close>





(*
Note: IsaRARE can currently not deal with line breaks in rewrite rules
*)

ML \<open>
 open Parse_RARE
 open Write_Rewrite_as_Lemma

 fun print_item string_of (modes, arg) = Toplevel.keep (fn state =>
   Print_Mode.with_modes modes (fn () => writeln (string_of state (hd arg))) ())

 (*TODO: Can I use: Library.cat_lines?*)
 fun string_of_rewrite ctxt s
  = (Write_Rewrite_as_Lemma.write_thy (Parse_RARE.parse_rewrites ctxt [s]) "THEORY_NAME" "IMPORTING_THEORIES" ctxt)

 fun print_rewrite (cs:string) (t:Toplevel.transition) :  Toplevel.transition =
  Toplevel.keep (fn toplevel => (fn state =>
   Print_Mode.with_modes [] (fn () => writeln (string_of_rewrite state cs)) ()) (Toplevel.context_of toplevel)) t

 val _ =
  Outer_Syntax.command \<^command_keyword>\<open>parse_rare\<close> "parse a single rule in rare format (provided as a string) and output lemma"
    ( Parse.string >> print_rewrite);

val ISARARE_HOME = OS.FileSys.getDir()

 val semi = Scan.option \<^keyword>\<open>;\<close>; (*TODO: Do not need?*)
val x = OS.Process.getEnv

 val _ =  Outer_Syntax.local_theory \<^command_keyword>\<open>parse_rare_file\<close> "parse file in rare format and output lemmas. <rare_file, import theories, target_theory>"
    (((Parse.string -- Parse.string)  -- Parse.string)
    >> (fn ((file_name,theory_imports),theory_name) => fn lthy =>
  let
          (*Built new path*)
          val file_path = Path.explode file_name
          val new_theory_name = theory_name ^ ".thy"
          val ctxt = Local_Theory.target_of lthy
          val res_path = Path.append (Path.dir file_path) (Path.basic new_theory_name)

          (*Calculate result*)
          (*val lines = raw_explode ( hd  (Bytes.contents (Bytes.read file_path))) ;*)
          val lines = Bytes.split_lines (Bytes.read file_path)
          val res =  (Write_Rewrite_as_Lemma.write_thy (Parse_RARE.parse_rewrites ctxt lines) theory_name theory_imports ctxt)
          val _ = (Output.writeln res)

          val _ =
           Bytes.write
            res_path (Bytes.string res)
          val _ = @{print} ("done writing to file", res_path)
 in  lthy
 end))
\<close>

lemmas cvc_arith_rewrite_defs = SMT.z3div_def


section \<open>Options\<close>

declare[[IsaRARE_verbose = true]] (*Get additional information*)
declare[[IsaRARE_debug = true]] (*Get debugging information*)
declare[[IsaRARE_implAssump = true]] (*Turn implicit assumption generation on or off (Warning this is an expert option: Lemmas might not be provable without the assumptions) *)
declare[[IsaRARE_listsAsVar = false]] (*When turned on list parameters are parsed as if they were variables (Warning this is an expert option: Lemmas might be proven but corresponding RARE rule is not correct) *)
declare[[IsaRARE_proofStrategy = "Full"]] (*Turn on specific strategies for proof printed, e.g. strings*)
declare [[ML_print_depth=10000]]


(*Test*)
(*TODO: Get current directory*)
(*parse_rare_file "$IsaRARE_HOME/Tests/mixed_rewrites" "" "Mixed_Rewrites"

*)

section \<open>Test\<close>

declare[[IsaRARE_proofStrategy = "Minimum"]]
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/boolean_rewrites" "Boolean_Rewrites_Lemmas" "Boolean_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/uf_rewrites" "" "UF_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/builtin_rewrites" "" "Builtin_Rewrites"

declare[[IsaRARE_proofStrategyTheory = "Arith"]]
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/arith_rewrites" "Arith_Rewrites_Lemmas" "Arith_Rewrites"


declare[[IsaRARE_proofStrategy = "Full"]]

(*TODO: Documentation adding new operators to parser*)

(*TODO: Documentation new_nary operators*)

end