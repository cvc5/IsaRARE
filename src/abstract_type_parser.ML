(*  Title:      IsaRARE/parse_rare.ML
    Author:     Hanna Lachnitt, Stanford University

Additional type and term parser for RARE for its features that extend SMT-LIB
*)


fun rare_type_parser (SMTLIB.Sym "?Array", [])
      = SOME (Type(\<^type_name>\<open>fun\<close>,[dummyT,Type(\<^type_name>\<open>option\<close>,[dummyT])]))
  | rare_type_parser (SMTLIB.Sym "?Set", []) = SOME (Type(\<^type_name>\<open>Set.set\<close>,[dummyT]))
  | rare_type_parser (SMTLIB.Sym "?", []) = SOME (dummyT)
 (*  | rare_type_parser (SMTLIB.Sym "Type", []) = SOME (dummyT)
  | rare_type_parser (SMTLIB.Sym x, []) = SOME (dummyT)
  | rare_type_parser (SMTLIB.Sym "@T1", []) = SOME (dummyT) *)
  | rare_type_parser _ = NONE

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser rare_type_parser))

(*
fun mk_test (t1, t2) = (Const (\<^const_name>\<open>Word.word_cat\<close>, dummyT --> dummyT --> dummyT))  $ t1 $ t2

fun bv_term_parser (SMTLIB.Sym "concat", t::ts) = 
      SOME (mk_lassoc (curry mk_test) t ts)

fun mk_concat (t, u) =
  let
    val T = fastype_of t
    val _ = @{print}("fastype_of t",fastype_of t)
    val U = fastype_of u

    (*TODO: If one of them is not concrete we need to use LENGTH('a) here. But how to add the extra restriction that LENGTH('c) = LENGTH('a) + LENGTH('b)?*)
    (*val TU = Word_Lib.dest_wordT T + Word_Lib.dest_wordT U
          |> Word_Lib.mk_wordT*)
    val TU = (TVar (("?a", serial ()), []))
  in Const (\<^const_name>\<open>Word.word_cat\<close>, T --> U --> TU) $ t $ u end;

  | bv_term_parser (SMTLIB.Sym "extract", [t1,t2,t3]) =
    let 
       val T1 = fastype_of t1
       val T2 = fastype_of t2

       val t1' = if T1 = \<^typ>\<open>Int.int\<close> then Const ( \<^const_name>\<open>nat\<close>, T1 -->  \<^typ>\<open>Nat.nat\<close>) $ t1 else t1
       val t2' = if T2 = \<^typ>\<open>Int.int\<close> then Const ( \<^const_name>\<open>nat\<close>, T2 -->  \<^typ>\<open>Nat.nat\<close>) $ t2 else t2
    in SOME (Const (\<^const_name>\<open>SMT_Word.smt_extract\<close>, @{typ nat} --> @{typ nat} --> dummyT --> dummyT) $ t1' $ t2' $ t3)
    end
*)
