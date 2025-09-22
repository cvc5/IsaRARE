

(* Overwrites the original parser (in TODO) for some operators *)

fun is_concrete_numeral n =
  HOLogic.dest_numeral n |> mk_wordT
    handle TERM(_) => dummyT

fun is_concrete_bitwidth w =
  dest_wordT w |> K w
    handle TERM(_) => dummyT

(*At some point TU should also be tested? Then, we cannot just test for SMTLIB.Num i*)
fun mk_extract i j u T =
 let
  val I = HOLogic.mk_number \<^typ>\<open>nat\<close> i
  val J = HOLogic.mk_number \<^typ>\<open>nat\<close> j

  val TU = i - j + 1 |> Word_Lib.mk_wordT
 in
   Const (\<^const_name>\<open>SMT_Word.smt_extract\<close>, @{typ nat} --> @{typ nat} --> T --> TU) $ I $ J $ u
 end

fun
(* RARE only *)
bv_rare_term_parser (SMTLIB.Sym "bv", [int,base]) =
let
       val _ = @{print}("T1",int)
in
  SOME (Const (\<^const_name>\<open>Word.Word\<close>,\<^typ>\<open>Int.int\<close>--> dummyT) $ int) 
end |
bv_rare_term_parser (SMTLIB.Sym "bvsize", [t1]) =
  let
       val _ = @{print}("T1",t1)

    val T = fastype_of t1
  in
    SOME (Const ( \<^const_name>\<open>of_nat\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Int.int\<close>) $
        (* (Const ( \<^const_name>\<open>size\<close>, is_concrete_bitwidth T --> \<^typ>\<open>Nat.nat\<close>) $ t1))*)
         (Const ( \<^const_name>\<open>size\<close>, dummyT --> \<^typ>\<open>Nat.nat\<close>) $ t1))

  end |
(* SMT-LIB 3 operators *)
bv_rare_term_parser (SMTLIB.Sym "extract", [t1,t2,t3]) =
    let 
       val T1 = fastype_of t1
       val T2 = fastype_of t2
       val _ = @{print}("T1",T1)
       val t1' = if T1 = \<^typ>\<open>Int.int\<close> then Const ( \<^const_name>\<open>nat\<close>, T1 -->  \<^typ>\<open>Nat.nat\<close>) $ t1 else t1
       val t2' = if T2 = \<^typ>\<open>Int.int\<close> then Const ( \<^const_name>\<open>nat\<close>, T2 -->  \<^typ>\<open>Nat.nat\<close>) $ t2 else t2
    in SOME (Const (\<^const_name>\<open>SMT_Word.smt_extract\<close>, @{typ nat} --> @{typ nat} --> dummyT --> dummyT) $ t1' $ t2' $ t3)
    end |
bv_rare_term_parser (SMTLIB.Sym "zero_extend", [t1, t2]) = (*This should push t1 0's before t2, solution above uses ucast, should I do too?*)
  let
       val _ = @{print}("T1",t1)
       val _ = @{print}("T1",t2)

    val TU = dummyT (*TODO: If known add concrete bitwidth*)
  in (SOME (Const (\<^const_name>\<open>Word.cast\<close>, dummyT  --> dummyT)  $ t2 ) |> @{print}) end
 |
 bv_rare_term_parser (SMTLIB.Sym "bvshl", [t1, t2]) = 

      SOME (Const (\<^const_name>\<open>semiring_bit_operations_class.push_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> dummyT --> dummyT) $ (Const ( \<^const_name>\<open>unsigned\<close>, dummyT --> \<^typ>\<open>Nat.nat\<close> ) $ t2) $ t1)
  | bv_rare_term_parser (SMTLIB.Sym "bvlshr", [t1, t2]) = 

      SOME (Const (\<^const_name>\<open>semiring_bit_operations_class.drop_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> dummyT --> dummyT) $ (Const ( \<^const_name>\<open>unsigned\<close>, dummyT --> \<^typ>\<open>Nat.nat\<close> ) $ t2) $ t1)
  | bv_rare_term_parser (SMTLIB.Sym "bvashr", [t1, t2]) = 
      SOME (Const (\<^const_name>\<open>signed_drop_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> dummyT --> dummyT) $ (Const ( \<^const_name>\<open>unsigned\<close>, dummyT --> \<^typ>\<open>Nat.nat\<close> ) $ t2) $ t1)
   | bv_rare_term_parser (SMTLIB.Sym "concat", [t1, t2]) = 
let
  val _ = @{print}("t1",t1)
in
      SOME (Const (\<^const_name>\<open>word_cat\<close>,dummyT --> dummyT --> dummyT) $ t1 $ t2)
end
 
   |
bv_rare_term_parser _ = NONE

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_term_parser bv_rare_term_parser)
)

(*val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser rare_type_parser))*)


