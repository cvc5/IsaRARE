(*  Title:      IsaRARE/rare_impl_assms.ML
    Author:     Hanna Lachnitt, Stanford University

This file provides functionality to add implicit assumptions to a SMTLIB Tree:

 Some operators have restrictions on the values they are defined on in SMTLIB, that their
 corresponding operator in Isabelle does not have. This is particularly
 often the case for the theory of bit-vectors. E.g., extract i j s is restricted to values
 0 \<le> i \<le> j \<le> size s and the bid-width of the output is size(i) + 1 - j. 

get_implicit_assms needs as input the term it is supposed to add assumptions for and a list of
parameters. It outputs a tuple (ts,t) where t is the transformed conclusion (with sharing) and
ts is the list of additional assumptions needed for t.

This also implements a sharing algorithm.

A lot of assumptions might be collected several times,
so we use a data structure to make sure we don't have them double.
*)

signature RARE_IMPL_ASSMS =
sig
  exception IMPL_ASSMS of string
  val process : Proof.context -> SMTLIB.tree -> Parse_RARE.par list -> SMTLIB.tree list * SMTLIB.tree
end;

structure RARE_Impl_Assms: RARE_IMPL_ASSMS =
struct

exception IMPL_ASSMS of string

(* Utils *)

fun debug_msg_implAssms ctxt msg =
  (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> ("Implicit assumption module: " ^ msg)))

fun find_term term sharingTable = 
let
  val str_term = term |> SMTLIB.str_of |> ATP_Util.hash_string |> Int.toString
in
  case Symtab.lookup sharingTable str_term of
   NONE =>
     let
       val new_name = "_c" ^ Library.string_of_int (Symtab.size sharingTable) |> SMTLIB.Sym
       val updatedSharingTable = Symtab.update_new (str_term,new_name) sharingTable
     in
       (new_name,updatedSharingTable)
     end |
   (SOME x) => (x,sharingTable)
end

fun add_implAss termList implAssTable =
let
  val str_list = termList |> (map (fn x => x |> SMTLIB.str_of |> ATP_Util.hash_string |> Int.toString))
in fold (fn t => fn tab => Symtab.update t tab) (ListPair.zip (str_list,termList)) implAssTable end

fun mk_assms_size t1 = SMTLIB.S [SMTLIB.Sym "bvsize", t1]
fun mk_assm_equal t1 t2 = SMTLIB.S [SMTLIB.Sym "=", t1, t2]
fun mk_assm_size var width = mk_assm_equal (mk_assms_size var) width
fun mk_assm_leq t1 t2 = SMTLIB.S [SMTLIB.Sym "<=", t1, t2]
fun mk_assm_leq_0 t1 = mk_assm_leq (SMTLIB.Num 0) t1
fun mk_assm_plus t1 t2 = SMTLIB.S [SMTLIB.Sym "+", t1, t2]


(* Processing *)

(* binary operators where the only assumption needed is that the bit-width of the result is the
 width of the first argument *)
val size_of_fst_arg = ["bvshl","bvlshr","bvashr"]
(* binary operators where the only assumption needed is that the first argument is a positive
 number*)
val pos_fst_arg = ["rotate_left","rotate_right"]
(* binary operators where two assumptions are needed:
1. is that the first argument is a positive number
2. is that the bit-width of the result is the first argument plus the width of second argument *)
val pos_fst_arg_size_sum = ["zero_extend","sign_extend"]


val needs_assms = size_of_fst_arg @ pos_fst_arg @ pos_fst_arg_size_sum @ 
  ["@bv","bv","extract","concat","repeat" ]

fun assms_by_operator (SMTLIB.S [SMTLIB.Sym "bv", value, width]) new_name = 
  [
   mk_assm_size new_name width,
   mk_assm_leq value (SMTLIB.S [SMTLIB.Sym "pow2", width])
  ] |
assms_by_operator (SMTLIB.S [SMTLIB.Sym "extract", i, j, t1]) new_name =
  [
   mk_assm_leq_0 j,
   mk_assm_leq j i,
   mk_assm_size new_name (SMTLIB.S [SMTLIB.Sym "+", SMTLIB.Num 1, SMTLIB.S [SMTLIB.Sym "-", i, j]]),
   SMTLIB.S [SMTLIB.Sym "<", i, SMTLIB.S [SMTLIB.Sym "bvsize", t1]]
  ] |
assms_by_operator (SMTLIB.S [SMTLIB.Sym operator,t1,t2]) new_name =
  if List.exists (curry (op =) operator) size_of_fst_arg
  then [mk_assm_equal (mk_assms_size new_name) (mk_assms_size t1)]
  else if List.exists (curry (op =) operator) pos_fst_arg
  then [mk_assm_leq_0 t1]
  else if List.exists (curry (op =) operator) pos_fst_arg_size_sum
  then [mk_assm_leq_0 t1,mk_assm_equal (mk_assms_size new_name) (mk_assm_plus t1 (mk_assms_size t2))]
  else []   (*TODO: error*)|
 assms_by_operator _ _ = [] (*TODO: error*)

(*
There is no way treating concat like the other operators.

We have found a way to at least being able to use lists in concat terms. Let's say xs is a list
variable. A xs could have 0 to n elements. However, we want to make sure that not all arguments of a
concat could be empty lists. Usually, (i.e., for other operators) we don't care since that would
mean that the result is the identity element of that operator. concat does not have an identity
element though.

During list processing the xs used in a concat will be transformed from a bit-vector list to a list
of bool lists by adding the operator XYZ.

However, it might still appear in the rest of the rewrite where it is still a bit-vector! The
casting actually needs to be restricted by an implicit assumption even if xs's type is not an
abstract type because XYZ has a variable bit-width for its result type.

So, every potential element xss of xs will get transformed into a list of booleans xss' by
applying the operator XYZ.

For that we have to exchange the operator concat to XYZ and give a new name to every list variable.
We add the assumption that that new name is equal to the operator XYZ in front of
that list variable


Then, for each such list variable we need to include the implicit assumption:

- The length of each list xss is not 0 (we don't have bit-vectors of size 0). For this we have
to add a special operator

- Each conversion that is going to be added is correct. So for every xss if it had bit-width n
before now the list xss' has n elements.

And since we don't have xss we have to do all of this by introducing operators on xs
and making sure that that xs actually is transformed into xs'. We have to introduce a new subterm
(that will be binarised eventually).

For the whole term:

- The length of the concat term is the length of every non-list argument + the length of each list
 argument (which is the length of
each xss summed up)

Note: xs will get binarised. We need to make sure that the type of (concat ys zs) is correct.


(concat xs ys zs) = (concat xs (concat ys zs))

However, since we added: length (XYZ ys) = size(ys), our concat function will fail if 
(concat (XYZ ys) (XYZ zs)) = length (XYZ xs) + length (XYZ ys) is not correct.

We can also add this here but that would include binarizing the term

*)
fun process_concat (implAssTable,sharingTable) xs = ([],(implAssTable,sharingTable) )

fun traverse ctxt (implAssTable,sharingTable) (t as (SMTLIB.S (SMTLIB.Sym x::xs))) = 
let
  val _ = @{print}("sdf",x)
  val (traversed_children,(implAssTable,sharingTable)) = traverse_children ctxt ([],(implAssTable,sharingTable)) xs
  val t' = (SMTLIB.S (SMTLIB.Sym x::traversed_children))
in
 if x = "concat"
 then (debug_msg_implAssms ctxt ("Found concat term, special handeling ");
       process_concat (implAssTable,sharingTable) traversed_children)
 else if Library.member (op =) needs_assms x
 then
   let
     val _ = debug_msg_implAssms ctxt ("Found operator that needs implicit assumption: " ^ x)
     val (new_name,sharingTable) = find_term t' sharingTable
     val implAssTable = add_implAss [mk_assm_equal new_name t] implAssTable
     val implAssTable = add_implAss (assms_by_operator t' new_name) implAssTable
     val _ = debug_msg_implAssms ctxt ("Found operator " ^ x);
   in ([t'],(implAssTable,sharingTable)) end
 else ([t'],(implAssTable,sharingTable))
end |
traverse _ (implAssTable,sharingTable) _ = ([],(implAssTable,sharingTable))
and
 traverse_children ctxt (children,(implAssTable,sharingTable)) [] = (children,(implAssTable,sharingTable)) |
 traverse_children ctxt (children,(implAssTable,sharingTable)) (x::xs) =
   let
     val _ = @{print}("taverse child",x)
     val (child,(implAssTable,sharingTable)) = traverse ctxt (implAssTable,sharingTable) x
   in
     traverse_children ctxt (child @ children,(implAssTable,sharingTable)) xs 
   end


fun process ctxt t params = 
let
  val ([t'],(implAssTable,sharingTable)) = traverse ctxt (Symtab.empty,Symtab.empty) t
  val ass = Symtab.dest implAssTable |> map snd
in (ass,t')  end

end
