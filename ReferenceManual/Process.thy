(*<*)
theory Process
  imports ImplAss
begin


ML_file \<open>../src/process_rare.ML\<close>

(*>*)

section \<open>Process AST and Transformation into Isabelle Term\<close>


subsubsection \<open> Test Processing \<close>

lemma test: "\<forall>x. x = x"
  by simp

lemma test2: "\<forall>x. x = x"
  by simp

declare[[show_markup]]

ML\<open>
val ctxt = Context.the_local_context ()

  val term = @{term "\<And>x. x"}
  val _ = @{print}("term",term)

  val term2 = @{term "\<forall>x. x"}
  val _ = @{print}("term2",term2)

  val term3 = term2 |> (fn Const ("HOL.All", _) $ x => x )
  val _ = @{print}("term3",term3)

  val test2 = Term.dest_abs_global term3
  val _ = @{print}("test2",test2)

  val ((par,res),r) =  Variable.dest_all term ctxt
  val _ = @{print}("res",res)
  val _ = @{print}("par",par)
  val _ = @{print}("r",r)

  val test = Variable.dest_abs (Abs ("x", @{typ "bool"}, Bound 0)) ctxt
  val _ = @{print}("test",test)

\<close>


ML \<open>
fun hackish_string_of_term ctxt =
Print_Mode.setmp [] (Syntax.string_of_term ctxt)
#> YXML.content_of
#> Sledgehammer_Util.simplify_spaces

val ctxt = Context.the_local_context ()

val x =  (Goal_Display.string_of_goal ctxt @{thm "refl"}) |> YXML.content_of
val _ = @{print}("x",x)

val y =  Thm.string_of_thm ctxt @{thm "refl"} |> YXML.content_of
val _ = @{print}("y",y)
(*|> Thm.forall_elim (Thm.cterm_of ctxt @{term "x"})*)
val z1 = @{thm test}|> Thm.cconcl_of  |> Thm.term_of
val _ = @{print}("z1",z1)

val t = (Term.add_free_names (Thm.prop_of @{thm test2}) ["w"])
val _ = @{print}("t",t)

(*val z = @{thm test} |> Thm.generalize (Names.empty,Names.make_set ["0"]) 0 |> Thm.cconcl_of  |> Thm.term_of
val _ = @{print}("z",z)*)


val parsed = Parse_RARE.parse_rewrites ctxt [(1,"(define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)")]

val processed_smtlibTerm = Process_RARE.process_rule ctxt (hd parsed)
val parsed = Parse_RARE.parse_rewrites ctxt [(1,"(define-cond-rule ite-neg-branch ((c Bool) (x Bool) (y Bool)) (= (not y) x) (ite c x y) (= c x))")]
val processed_smtlibTerm = Process_RARE.process_rule ctxt (hd parsed)
val _ = @{print}("processed_smtlibTerm",processed_smtlibTerm)


\<close>




end