

(*TODO*)

fun rare_type_parser (SMTLIB.Sym "?", _) = SOME dummyT |
    rare_type_parser (SMTLIB.Sym "?BitVec", []) = SOME (Type (\<^type_name>\<open>word\<close>, [dummyT]))

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_term_parser rare_term_parser)
)
val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser rare_type_parser))



