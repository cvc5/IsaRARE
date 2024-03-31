(*<*)
theory WriteThy
  imports Process
begin


ML_file \<open>../src/write_theory.ML\<close>

(*>*)
subsubsection \<open> Test Processing \<close>

declare[[show_markup]]
ML \<open>

val ctxt = Context.the_local_context ()
val parsed = Parse_RARE.parse_rewrites ctxt [(1,"(define-rule bool-double-not-elim ((t Bool)) (not (not t)) t)")]
val processed_smtlibTerm = Process_RARE.process_rule ctxt (hd parsed)
val written = Write_Theory.write_thy ctxt [processed_smtlibTerm] "" ""

val _ = @{print} written
\<close>


end