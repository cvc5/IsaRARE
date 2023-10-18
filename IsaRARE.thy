theory IsaRARE
  imports "HOL.SMT" "HOL-CVC.Smtlib_String" "HOL-CVC.SMT_CVC" "HOL-CVC.Dsl_Nary_Ops" "HOL-CVC.SMT_Word"
  keywords "parse_rare_file" "parse_rare" :: diag
begin
ML_file \<open>$ISABELLE_HOME/src/HOL/CVC/ML/SMT_string.ML\<close> (*TODO: Should be in session*)

ML_file \<open>isarare_config.ML\<close>
ML_file \<open>parse_rare.ML\<close>
ML_file \<open>rare_impl_assump.ML\<close>
ML_file \<open>rare_lists.ML\<close>
ML_file \<open>write_rewrite_as_lemma.ML\<close>

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



val semi = Scan.option \<^keyword>\<open>;\<close>; (*TODO: Do not need?*)

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

declare[[IsaRARE_verbose = true]] (*Get additional information*)
declare[[IsaRARE_debug = true]] (*Get debugging information*)
declare[[IsaRARE_implAssump = true]] (*Turn implicit assumption generation on or off (Warning this is an expert option: Lemmas might not be provable without the assumptions) *)
declare[[IsaRARE_listsAsVar = false]] (*When turned on list parameters are parsed as if they were variables (Warning this is an expert option: Lemmas might be proven but corresponding RARE rule is not correct) *)
declare [[ML_print_depth=10000]]


(*Test*)
(*TODO: Get current directory*)
(*(define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)*)
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/boolean_rewrites" "Boolean_Rewrites_Lemmas" "Boolean_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/uf_rewrites" "" "UF_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/builtin_rewrites" "" "Builtin_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/set_rewrites" "" "Set_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/arith_rewrites" "Arith_Rewrites_Lemmas" "Arith_Rewrites"
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/array_rewrites" "" "Array_Rewrites"
declare[[IsaRARE_proofStrategy = "Strings"]]
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/string_rewrites" "" "String_Rewrites"
declare[[IsaRARE_proofStrategy = "None"]]
parse_rare_file "~/Sources/IsaRARE/Tests/Regression/bv_rewrites" "" "Bitvector_Rewrites"

(*(define-rule bv-comp-eliminate ((x ?BitVec) (y ?BitVec)) (bvcomp x y) (ite (= x y) (bv 1 1) (bv 0 1)))
*)
(* [Rule_Type DEFINE_RULE_STAR, Rule_Name "bv_concat_flatten",
   Par ([S [Sym "zs", Sym "?BitVec"], S [Sym "ys", Sym "?BitVec"], S [Sym "s", Sym "?BitVec"], S [Sym "xs", Sym "?BitVec"]],
        [S [Sym "zs", Sym "?BitVec"], S [Sym "ys", Sym "?BitVec"], S [Sym "xs", Sym "?BitVec"]]),
   Let_Defs NONE, Context_Expr NONE, Match (S [Sym "concat", Sym "xs", S [Sym "concat", Sym "s", Sym "ys"], Sym "zs"]),
   Target (S [Sym "concat", Sym "xs", Sym "s", Sym "ys", Sym "zs"])]


 "\<forall>(xs::_ cvc_ListVar) s (ys::_ cvc_ListVar) zs::_ cvc_ListVar.
     x_c1 = word_cat (word_cat (word_cat (concat_smt2 xs) s) (concat_smt2 ys)) (concat_smt2 zs) \<and>
     x_c0 = word_cat (word_cat (concat_smt2 xs) x_c0) (concat_smt2 zs) \<and>
     x_c0 = x_c1")

*)





(*TODO: Documentation adding new operators to parser*)

(*TODO: Documentation new_nary operators*)

end