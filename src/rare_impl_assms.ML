(*  Title:      IsaRARE/rare_impl_assms.ML
    Author:     Hanna Lachnitt, Stanford University

This file provides functionality to add implicit assumptions to a SMTLIB Tree:

 Some operators have restrictions on the values they are defined on in SMTLIB that their
 corresponding operator in Isabelle does not have. This is particularly
 often the case for the theory of bit-vectors. E.g., extract i j s is restricted to values
 0 \<le> i \<le> j \<le> size s and the bid-width of the output is size(i) + 1 - j. 

get_implicit_assms needs as input the term it is supposed to add assumptions for and a list of
parameters. It outputs a tuple (ts,t) where t is the transformed conclusion (with sharing) and
ts is the list of additional assumptions needed for t.

This also implements a sharing algorithm.

A lot of assumptions might be collected several times,
so we use a datastructure to make sure we don't have them double.
*)

signature RARE_IMPL_ASSMS =
sig
  exception IMPL_ASSMS of string
  val get_implicit_assms : SMTLIB.tree -> (SMTLIB.tree * SMTLIB.tree) list ->
    SMTLIB.tree list * SMTLIB.tree
end;

structure RARE_Impl_Assms: RARE_IMPL_ASSMS =
struct

exception IMPL_ASSMS of string

fun debug_msg_implAssms ctxt msg =
  (IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> ("Implicit assumption module: " ^ msg)))

fun find_term term sharingTable = 
let
  (*TODO: Find out correctness guarantee of this hash function, otherwise just use SMTLIB.str_of *)
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
  (*TODO: Find out correctness guarantee of this hash function, otherwise just use SMTLIB.str_of *)
  val str_list = termList |> (map (fn x => x |> SMTLIB.str_of |> ATP_Util.hash_string |> Int.toString))
in fold (fn t => fn tab => Symtab.update t tab) (ListPair.zip (str_list,termList)) implAssTable end

fun assm_size var bit_width = SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym "bvsize", var],bit_width]
fun assm_equal t1 t2 = SMTLIB.S [SMTLIB.Sym "=", t1, t2]

local 

 fun traverse_tree ctxt _ implAssTable sharingTable (t as (SMTLIB.S [SMTLIB.Sym "bv", value, width])) = 
 let
   val _ = debug_msg_implAssms ctxt "Found bit-vector constant"
   val (t',sharingTable) = find_term t sharingTable
   val _ = debug_msg_implAssms ctxt ("Sharing results in: " ^ SMTLIB.str_of t')

   val assms = [assm_size t' width, assm_equal t' t, SMTLIB.S [SMTLIB.Sym "<=", SMTLIB.S [SMTLIB.Sym "pow2", value], width]]
   val implAssTable = add_implAss assms implAssTable

  in (t',implAssTable,sharingTable) end  |
 traverse_tree ctxt params implAssTable sharingTable (t as (SMTLIB.S [SMTLIB.Sym "extract", i, j, t1])) = 
  let
   val (i',implAssTable,sharingTable) = traverse_tree ctxt params implAssTable sharingTable i
   val (j',implAssTable,sharingTable) = traverse_tree ctxt params implAssTable sharingTable j
   val (t1',implAssTable,sharingTable) = traverse_tree ctxt params implAssTable sharingTable t1

   val new_t = (SMTLIB.S [SMTLIB.Sym "extract", i', j', t1'])

   val _ = debug_msg_implAssms ctxt "Found bit-vector extract term"
   val (t',sharingTable) = find_term new_t sharingTable
   val _ = debug_msg_implAssms ctxt ("Sharing results in: " ^ SMTLIB.str_of t')

   val assms =
    [  assm_equal t' new_t, 
      SMTLIB.S [SMTLIB.Sym "<=", SMTLIB.Num 0, j'],
      SMTLIB.S [SMTLIB.Sym "<=", j', i'],
      SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym "bvsize", t'],
        SMTLIB.S [SMTLIB.Sym "+", SMTLIB.Num 1, SMTLIB.S [SMTLIB.Sym "-", i', j']]],
      SMTLIB.S [SMTLIB.Sym "<", i, SMTLIB.S [SMTLIB.Sym "bvsize", t1]]
      ]

   val implAssTable = add_implAss assms implAssTable
  in (t',implAssTable,sharingTable) end



in 
fun get_implicit_assms t params =
let
  val emptyTable = Symtab.empty
  val sharingTable = Symtab.empty

in
 ([],t)
end
end


(*I need this to be incooperated in the other function and called on terms that are added to implicit assumptions as well*)
val merge_sets = Library.union (fn (a,b) => (a = b))
val merge_subterms = Library.union (fn ((_,b),(_,d)) => (b = d))

fun get_implicit_assump2 (SMTLIB.S [SMTLIB.Sym "bv", i, j]) assms subterms list_param =
 let
   val _ = @{print}("is this happening", (i,j))

   val new_term = (SMTLIB.S [SMTLIB.Sym "bv", i, j])
   val new_var = case List.find (fn (_,b) => new_term = b) subterms of
                  NONE =>  "_c" ^ Library.string_of_int (length subterms) |> SMTLIB.Sym |
                  SOME (x,_) => x
   val subterms = merge_subterms [(new_var,new_term)] subterms

   val add_assms =
    [
 
      SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym "bvsize", new_var],j],
      SMTLIB.S [SMTLIB.Sym "=", new_var, (SMTLIB.S [SMTLIB.Sym "bv", i, j])]

      ] |> Library.distinct (fn (a,b) => (a = b))

   val assms = merge_sets add_assms assms
  in (assms,subterms,new_var)
  end |

get_implicit_assump2 (SMTLIB.S [SMTLIB.Sym "extract", i, j, t]) assms subterms list_param =
  let
   val (assms, subterms, new_body) = get_implicit_assump2 t assms subterms list_param
   val new_term = (SMTLIB.S [SMTLIB.Sym "extract", i, j, new_body])
   val new_var = case List.find (fn (_,b) => new_term = b) subterms of
                  NONE =>  "_c" ^ Library.string_of_int (length subterms) |> SMTLIB.Sym |
                  SOME (x,_) => x
   val subterms = merge_subterms [(new_var,new_term)] subterms

   val add_assms =
    [
      SMTLIB.S [SMTLIB.Sym "<=", SMTLIB.Num 0, j],
      SMTLIB.S [SMTLIB.Sym "<=", j, i],
      SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym "bvsize", new_var],
        SMTLIB.S [SMTLIB.Sym "+", SMTLIB.Num 1, SMTLIB.S [SMTLIB.Sym "-", i, j]]],
      SMTLIB.S [SMTLIB.Sym "=", new_var, (SMTLIB.S [SMTLIB.Sym "extract", i, j, new_body])],
      SMTLIB.S [SMTLIB.Sym "<", i, SMTLIB.S [SMTLIB.Sym "bvsize", new_body]]
      ] |> Library.distinct (fn (a,b) => (a = b))

   val assms = merge_sets add_assms assms
  in (assms,subterms,new_var)
  end |
 get_implicit_assump2 (SMTLIB.S ((SMTLIB.Sym "concat")::ts1)) assms subterms list_param =
   let

   (*First we binarize*)
   fun mk_bin [x] = x |
       mk_bin (x1::x2::xs) = SMTLIB.S [(SMTLIB.Sym "concat"),x1,mk_bin (x2::xs)]

   val ts = (mk_bin ts1)
   val _ = @{print}("new ts with operator",ts)


   (*Now we are going through the binarized term building up a new term by adding smt_concats before lists giving them a new name
     collecting assumptions
    *)

   (*Makes assumptions necessary for a single subterm (smt_concat xss);
     namely
      - length xss > 0
      - each xs in xss has length > 0
      - (smt_concat xss)'s new id c1 is equal to the sum of the elements in xss
     *)
   fun mk_assms_for_list list_name list_with_smt_concat_id =
        [ SMTLIB.S[SMTLIB.Sym "=",list_with_smt_concat_id,SMTLIB.S[SMTLIB.Sym "smt_concat",list_name]],
          SMTLIB.S[SMTLIB.Sym ">",SMTLIB.S[SMTLIB.Sym "length",list_name],SMTLIB.Num 0],
          SMTLIB.S[SMTLIB.Sym "list_length_0", list_name],
          SMTLIB.S[SMTLIB.Sym "=",SMTLIB.S[SMTLIB.Sym "length",list_name], SMTLIB.S[SMTLIB.Sym "sum_length",list_name]]
         ]


   (*For a child of a concat we need to figure out if it is:
      1. a list
         Then, we want to change the term to SMTLIB.S [SMTLIB.Sym "smt_concat", x1] give it a new name, add the assumptions above
      2. not a list
         We want to call get_implicit_assump2 on it to figure out if it needs to be replaced by a subterm

      Return the new set of subterms, new set of assumptions, also for convenience return the new set of ids
   *)
   fun get_sub x1 subt ass =
   let
    val _ = @{print}("Get sub with ", x1)

     val x1_is_List = (case List.find (fn b => x1 = b) (map (fn x=> case x of (SMTLIB.S[SMTLIB.Sym b, _]) => SMTLIB.Sym b) list_param) of
                  NONE => false |
                  SOME x => true)
   in
    if x1_is_List
    then
      let
        val x1' = SMTLIB.S [SMTLIB.Sym "smt_concat", x1]
        val x1_id = (case List.find (fn (_,b) => x1' = b) subt of
                           NONE =>  "_c" ^ Library.string_of_int (length subt) |> SMTLIB.Sym |
                           SOME (x,_) => x)
        val ass = mk_assms_for_list x1 x1_id
      in
         (x1_id,ass,[(x1_id,x1')])
      end
    else 
      let
       val (assms, subt', new_body) = get_implicit_assump2 x1 ass subt list_param
      in
        (new_body,assms,subt')
      end
   end


   fun process_concat (SMTLIB.S [(SMTLIB.Sym "concat"), x1, SMTLIB.S [(SMTLIB.Sym "concat"),x2,xs]]) subt ass = 
       let
            val _ = @{print}("Process nested concat", (SMTLIB.S [(SMTLIB.Sym "concat"), x1, SMTLIB.S [(SMTLIB.Sym "concat"),x2,xs]]))

          val (x1',ass_x1, subt_x1) = get_sub x1 subt ass
          val ass = merge_sets ass_x1 ass
          val subt = merge_subterms subt_x1 subt
            val _ = @{print}("Got subfor x1 now x1'", x1')



          val (last_id,ass',subt') = process_concat (SMTLIB.S [(SMTLIB.Sym "concat"),x2,xs]) subt ass
          val ass = merge_sets ass' ass
          val subt = merge_subterms subt' subt

          val new_term = (SMTLIB.S [(SMTLIB.Sym "concat"), x1', last_id])
          val new_var = case List.find (fn (_,b) => new_term = b) subt of
                           NONE =>  "_c" ^ Library.string_of_int (length subt) |> SMTLIB.Sym |
                           SOME (x,_) => x
          val subt = merge_subterms [(new_var,new_term)] subt

          val new_assms = [SMTLIB.S[SMTLIB.Sym "=",new_var,new_term],
                           SMTLIB.S[SMTLIB.Sym "=",SMTLIB.S[SMTLIB.Sym "bvsize",new_var],
                             SMTLIB.S [SMTLIB.Sym "+",SMTLIB.S[SMTLIB.Sym "bvsize", x1'],SMTLIB.S[SMTLIB.Sym "bvsize", last_id]]]
                           
                           ]
          val ass = merge_sets new_assms ass
       in
          (new_var,ass,subt)
       end
   | process_concat (SMTLIB.S [(SMTLIB.Sym "concat"), x1, x2]) subt ass = 
        let
          val (x1',ass_x1, subt_x1) = get_sub x1 subt ass
          val ass = merge_sets ass_x1 ass
          val subt = merge_subterms subt_x1 subt

          val (x2',ass_x2, subt_x2) = get_sub x2 subt ass
          val ass = merge_sets ass_x2 ass
          val subt = merge_subterms subt_x2 subt

          val new_term = (SMTLIB.S [(SMTLIB.Sym "concat"), x1', x2'])
          val new_var = case List.find (fn (_,b) => new_term = b) subt of
                           NONE =>  "_c" ^ Library.string_of_int (length subt) |> SMTLIB.Sym |
                           SOME (x,_) => x
          val subt = merge_subterms [(new_var,new_term)] subt

          val new_assms = [SMTLIB.S[SMTLIB.Sym "=",new_var,new_term],
                          SMTLIB.S[SMTLIB.Sym "=",SMTLIB.S[SMTLIB.Sym "bvsize",new_var],
                             SMTLIB.S [SMTLIB.Sym "+",SMTLIB.S[SMTLIB.Sym "bvsize", x1'],SMTLIB.S[SMTLIB.Sym "bvsize", x2']]]
                           
                           ]
          val ass = merge_sets new_assms ass

        in
          (new_var,ass,subt)
        end

   val (new_var,ass,subt) = process_concat ts subterms assms
   val assms = merge_sets ass assms
   val subterms = merge_subterms subt subterms

   val _ = @{print}("assms ",assms)




 (*|
       process_concat ((SMTLIB.Sym "concat") :: x1 :: xs) subt ass = 
        let
          val (x1',ass_x1, subt_x1) = get_sub x1 subt ass
          val ass = merge_sets ass_x1 ass
          val subt = merge_sets subt_x1 subt

          val (new_ass,new_sub,last_id) = (process_concat xs subt ass)
          val ass = merge_sets new_ass ass
          val subt = merge_sets new_sub subt

          
          val new_term = ((SMTLIB.Sym "concat") :: x1' :: [x2'])
          val new_var = case List.find (fn (_,b) => new_term = b) subterms of
                           NONE =>  "_c" ^ Library.string_of_int (length subterms) |> SMTLIB.Sym |
                           SOME (x,_) => x

          val new_assms = [SMTLIB.S[SMTLIB.Sym "=",SMTLIB.S[SMTLIB.Sym "length",new_var],SMTLIB.S [SMTLIB.Sym "+",x1',x2']],
                           SMTLIB.S[SMTLIB.Sym "=",new_var,new_term]
                           ]
          val ass = merge_sets new_assms ass
        in 
          (new_ass,new_sub,last_id) :: processed xs subt ass
        end*)







(*
    fun listify [] = [] |
    listify (t::tss) = 
      let
        val (assms, subterms, new_t') = get_implicit_assump2 t assms subterms list_param (*TODO merge with rest?*)
        val t_is_List = (case List.find (fn b => new_t' = b) (map (fn x=> case x of (SMTLIB.S[SMTLIB.Sym b, _]) => SMTLIB.Sym b) list_param) of
                  NONE => false |
                  SOME x => true)
        val new_t'' =
        (if t_is_List then SMTLIB.S [SMTLIB.Sym "smt_concat", new_t']
         else new_t')
        val (new_ass',new_sub',new_termi') =
        (if t_is_List then
                        let
                           val new_var = case List.find (fn (_,b) => new_t'' = b) subterms of
                           NONE =>  "_c" ^ Library.string_of_int (length subterms) |> SMTLIB.Sym |
                           SOME (x,_) => x
                           val new_sub' = [(new_var,new_t'')]

                        in
                        ([SMTLIB.S[SMTLIB.Sym ">",SMTLIB.S[SMTLIB.Sym "length",new_t'],SMTLIB.Num 0],
                            SMTLIB.S[SMTLIB.Sym "list_length_0", new_t'],
                            SMTLIB.S[SMTLIB.Sym "=",new_var, new_t''],
                            SMTLIB.S[SMTLIB.Sym "=",SMTLIB.S[SMTLIB.Sym "bvsize",new_var], SMTLIB.S[SMTLIB.Sym "sum_length",new_t']] (*foldr (+) (map length xss) 0 *)
                           ],new_sub',[new_var])
                        end
         else ([],[],[new_t']))
        val _ = @{print}("termi'",new_termi')

      in (new_t'',new_ass',new_sub',new_termi')::listify tss end

   val l = (listify ts)
   val listi = map (fn (a,b,c,_) => a) l
   val assi = map (fn (a,b,c,_) => b) l
   val subi = map (fn (a,b,c,_) => c) l
   val termi = (map hd (filter (fn x => length x>0)  (map (fn (a,b,c,d) => d) l)))
   val assms = merge_sets (List.concat assi) assms
   val _ = @{print}("assi",assi)
   val _ = @{print}("termi",termi)

   val _ = @{print}("concat assi", (List.concat assi))

   fun he [] = subterms|
       he (x::xs) = merge_subterms x (he xs)
    val subterms = he subi

   (*If it is a list we need to replace it by a smt_concat term*)
    val new_term = (SMTLIB.S ((SMTLIB.Sym "concat")::listi))
    val new_var = case List.find (fn (_,b) => new_term = b) subterms of
                  NONE =>  "_c" ^ Library.string_of_int (length subterms) |> SMTLIB.Sym |
                  SOME (x,_) => x
    val subterms = merge_subterms [(new_var,new_term)] subterms

(*(S [Sym "concat", Sym "xs", S [Sym "concat", Sym "s", Sym "ys"], Sym "zs"])*)
(*(S [Sym "concat", S[Sym "smt_concat", Sym "xs"], S [Sym "concat", Sym "s", Sym "ys"], Sym "zs"])*)

    val add_assms =
       [ SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym "bvsize", new_var],
                                   SMTLIB.S (SMTLIB.Sym "+" :: (map (fn q => SMTLIB.S [SMTLIB.Sym "bvsize", q]) termi))],
       SMTLIB.S [SMTLIB.Sym "=", new_var, (SMTLIB.S ((SMTLIB.Sym "concat")::listi))
       ]] |> Library.distinct (fn (a,b) => (a = b))
val _ = @{print}("add_assms",add_assms)

    val assms = merge_sets add_assms assms*)
   in
    (assms,subterms,new_var)
   end |
 get_implicit_assump2 (SMTLIB.S [SMTLIB.Sym operator, i, t]) assms subterms list_param =
  if not (Library.member (op =) ["concat","repeat","zero_extend","sign_extend","rotate_left","rotate_right","bvshl","bvlshr","bvashr"] operator)
   then normal_case (SMTLIB.S [SMTLIB.Sym operator, i, t]) assms subterms list_param
  else if operator = "bvshl" orelse operator = "bvlshr" orelse operator = "bvashr" then (*TODO: Don't add whole term*)
  let
    val (assms, subterms, new_t') = get_implicit_assump2 t assms subterms list_param(*TODO: Save assumptions*)
    val (assms, subterms, new_i') = get_implicit_assump2 i assms subterms list_param

    val new_var_i' = case List.find (fn (_,b) => new_i' = b) subterms of
                  NONE =>  "_c" ^ Library.string_of_int (length subterms) |> SMTLIB.Sym |
                  SOME (x,_) => x
    val subterms = merge_subterms [(new_var_i',new_i')] subterms

    val new_term = (SMTLIB.S [SMTLIB.Sym operator, new_var_i', new_t'])
    val new_var2 = case List.find (fn (_,b) => new_term = b) subterms of
                  NONE =>  "_c" ^ Library.string_of_int (length subterms) |> SMTLIB.Sym |
                  SOME (x,_) => x
    val subterms = merge_subterms [(new_var2,new_term)] subterms

    val add_assms =
       [ SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym "bvsize", new_t'],SMTLIB.S [SMTLIB.Sym "bvsize", new_var_i']],
         SMTLIB.S [SMTLIB.Sym "=", new_var_i' ,new_i'],
         SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym "bvsize", new_var2] ,SMTLIB.S [SMTLIB.Sym "bvsize", new_var_i']],
         SMTLIB.S [SMTLIB.Sym "=", new_var2 ,new_term]
       ] |> Library.distinct (fn (a,b) => (a = b))

    val assms = merge_sets add_assms assms
   in
    (assms,subterms,new_var2)
   end
  else if operator = "rotate_left" orelse operator = "rotate_right"
   then
    let
     val (assms, subterms, new_body) = get_implicit_assump2 t assms subterms list_param
    in
     (merge_sets [SMTLIB.S [SMTLIB.Sym "<=", SMTLIB.Num 0, i]] assms,subterms,(SMTLIB.S [SMTLIB.Sym operator, i, new_body]))
    end
  else 
   let
    val (assms, subterms, new_body) = get_implicit_assump2 t assms subterms list_param
    val new_term = (SMTLIB.S [SMTLIB.Sym operator, i, new_body])
    val new_var = case List.find (fn (_,b) => new_term = b) subterms of
                  NONE =>  "_c" ^ Library.string_of_int (length subterms) |> SMTLIB.Sym |
                  SOME (x,_) => x
    val subterms = merge_subterms [(new_var,new_term)] subterms

    val add_assms =
      if operator = "repeat"
      then [
        SMTLIB.S [SMTLIB.Sym "<=", SMTLIB.Num 0, i],
        SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym "bvsize", new_var],
          SMTLIB.S [SMTLIB.Sym "*", SMTLIB.S [SMTLIB.Sym "bvsize", new_body], i]],
        SMTLIB.S [SMTLIB.Sym "=", new_var, (SMTLIB.S [SMTLIB.Sym operator, i, new_body])]
        ] |> Library.distinct (fn (a,b) => (a = b))
      else if operator = "zero_extend" orelse operator = "sign_extend"
      then [
        SMTLIB.S [SMTLIB.Sym "<=", SMTLIB.Num 0, i],
        SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym "bvsize", new_var],
          SMTLIB.S [SMTLIB.Sym "+", SMTLIB.S [SMTLIB.Sym "bvsize", new_body], i]],
        SMTLIB.S [SMTLIB.Sym "=", new_var, (SMTLIB.S [SMTLIB.Sym operator, i, new_body])]
        ] |> Library.distinct (fn (a,b) => (a = b))
      else []

    val assms = merge_sets add_assms assms
  in
   (assms,subterms,new_var)
  end |
 get_implicit_assump2 (SMTLIB.S ts) assms subterms list_param = normal_case (SMTLIB.S ts) assms subterms list_param |
 get_implicit_assump2 x assms ids list_param = (assms,ids,x)
and
normal_case (SMTLIB.S ts) assms subterms list_param =
 let
  fun fold_get_implicit assms' subterms' (t::ts) new_term = 
   let
    val (assms', subterms', t') = get_implicit_assump2 t assms' subterms' list_param
   in
    fold_get_implicit assms' subterms' ts (new_term @ [t'])
   end |
  fold_get_implicit assms' subterms' [] new_term = (assms',subterms',new_term)
    val (assms,subterms,new_term) = fold_get_implicit assms subterms ts []
 in
  (assms,subterms,(SMTLIB.S new_term))
 end |
normal_case _ _ _ _ = raise IMPL_ASSMS("Error while getting implicit assumptions")

end
