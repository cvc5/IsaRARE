(*  Title:      IsaRARE/rare_lists.ML
    Author:     Hanna Lachnitt, Stanford University
*)

signature RARE_LISTS =
sig
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string
  val rare_lists : SMTLIB.tree list -> int -> term -> Proof.context -> term
end;

structure RARE_Lists: RARE_LISTS =
struct
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string


(*TODO decrease m instead of giving two arguments*)
fun mk_nary ((Const (operator_name,operator_typ)) $ (Bound m1) $ (Bound m2)) lvars _ _ _ =
  let
   val var1_is_in_list = List.find (fn a => m1 = a) lvars
   val var2_is_in_list = List.find (fn a => m2 = a) lvars

   fun neutral_for_operator "HOL.conj" = Const (\<^const_name>\<open>HOL.True\<close>, \<^typ>\<open>HOL.bool\<close>) |
      neutral_for_operator "HOL.disj" = Const (\<^const_name>\<open>HOL.False\<close>, \<^typ>\<open>HOL.bool\<close>) |
      neutral_for_operator "Groups.plus_class.plus" = Const (\<^const_name>\<open>Groups.zero\<close>, \<^typ>\<open>Int.int\<close>) |
      neutral_for_operator "Orderings.ord_class.less_eq" = Const (\<^const_name>\<open>Groups.zero\<close>, \<^typ>\<open>Int.int\<close>) |
      neutral_for_operator "Groups.times_class.times" = Const (\<^const_name>\<open>Groups.one\<close>, \<^typ>\<open>Int.int\<close>) |
      neutral_for_operator "Smtlib_String.smtlib_re_concat" = Free ("{''''}", \<^typ>\<open>RegLan\<close>) |
      neutral_for_operator "Smtlib_String.smtlib_re_union" = Free ("{''''}", \<^typ>\<open>RegLan\<close>) |
      neutral_for_operator "Smtlib_String.smtlib_re_inter" = Free ("UNIV", \<^typ>\<open>RegLan\<close>) |
      neutral_for_operator "Smtlib_String.smtlib_str_concat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) |
      neutral_for_operator "Word.word_cat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) | (*TODO*)
      neutral_for_operator "Bit_Operations.semiring_bit_operations_class.xor" =  Const (\<^const_name>\<open>Groups.zero\<close>, dummyT) |
      neutral_for_operator l = (@{print}("neutral_for_operator", l);Free ("PutInNeutral",dummyT))

    val T = (dummyT --> dummyT --> dummyT) --> dummyT --> dummyT --> dummyT

    val new_operator =
      if var1_is_in_list = NONE andalso var2_is_in_list = NONE
        then Const (operator_name,operator_typ)
      else if var1_is_in_list = NONE (* \<^typ>\<open>(T \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>*)
        then Const(\<^const_name>\<open>cvc_list_right\<close>,T ) $ Const (operator_name,dummyT)
      else if var2_is_in_list = NONE (* \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a \<Rightarrow> 'a\<close>*)
        then Const(\<^const_name>\<open>cvc_list_left\<close>,T) $ Const (operator_name,dummyT)
      else (* \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar
          \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a \<Rightarrow> 'a\<close>*)
      Const(\<^const_name>\<open>cvc_list_both\<close>,T) $ Const (operator_name,dummyT) $ (neutral_for_operator (fst (operator_name,dummyT)))

   val new_term = 
    (if (var1_is_in_list = NONE andalso var2_is_in_list = NONE) orelse (operator_name <> "Word.word_cat")
     then (new_operator $ (Bound m1) $ (Bound m2))
     else
     let
      fun mk_concat_smt m' = Const ("SMT_Word.concat_smt2",dummyT) $ (Bound m')
     in
      if var1_is_in_list = NONE
      then (Const (operator_name,dummyT) $ (Bound m1) $ mk_concat_smt m2)
      else if var2_is_in_list = NONE
      then (Const (operator_name,dummyT) $ mk_concat_smt m1 $ (Bound m2))
      else (Const (operator_name,dummyT) $ mk_concat_smt m1 $ mk_concat_smt m2)
    end
)

(*
A term

(concat s ys) needs to be parsed to:

(concat s (concat_smt ys::'b::len word))

and we need to add assumptions for it

*)
  in 
   (new_operator $ (Bound m1) $ (Bound m2))
  end |
 mk_nary ((Const (operator_name,_)) $ (Bound m1) $ l2) lvars lists n m =
  let 
   val var1_is_in_list = List.find (fn a => m1 = a) lvars
   val T = (dummyT --> dummyT --> dummyT) --> dummyT --> dummyT --> dummyT

  val new_operator =
     if var1_is_in_list = NONE
     then Const (operator_name,dummyT) (* \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow>'a \<Rightarrow> 'a\<close>*)
     else Const (\<^const_name>\<open>cvc_list_left\<close>,T)
        $ Const (operator_name,dummyT)

 val new_term = 
  (if (var1_is_in_list = NONE) orelse (operator_name <> "Word.word_cat")
   then (new_operator $ (Bound m1) $ (mk_nary l2 lvars lists n m))
   else
   let
   fun mk_concat_smt m' = Const ("SMT_Word.concat_smt2",dummyT) $ (Bound m')
   in
    (Const (operator_name,dummyT) $ mk_concat_smt m1 $ l2)
  end)


  in 
   (new_operator $ (Bound m1) $ (mk_nary l2 lvars lists n m))
  end |
 mk_nary ((Const (operator_name,_)) $ l1 $ (Bound m2)) lvars lists n m =
  let
   val var2_is_in_list = List.find (fn a => m2 = a) lvars
   val T = (dummyT --> dummyT --> dummyT) --> dummyT --> dummyT --> dummyT

   val new_operator =
     if var2_is_in_list = NONE
     then Const (operator_name,dummyT)(* \<^typ>\<open>('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>*)
     else Const (\<^const_name>\<open>cvc_list_right\<close>,T)
        $ Const (operator_name,dummyT)
 val new_term = 
  (if (var2_is_in_list = NONE) orelse (operator_name <> "Word.word_cat")
   then (new_operator $ (mk_nary l1 lvars lists n m) $ (Bound m2))
   else
   let
   fun mk_concat_smt m' = Const ("SMT_Word.concat_smt2",dummyT) $ (Bound m')
   in
    (Const (operator_name,dummyT) $  l1 $ mk_concat_smt m2)
  end)


  in  
   (new_operator $ (mk_nary l1 lvars lists n m) $ (Bound m2))
  end |
 mk_nary (Const ("HOL.All", Type (t1,[Type(t2a,[_,t2b2]),t3])) $ (Abs (name, typ,l2))) lvars lists n m= (*TODO also need to change Const*)
  let
   val var1_is_in_list = List.find (fn a => name = a) lists
   val (new_typ,new_lvars) = if var1_is_in_list = NONE
                             then (typ,lvars)  
                             else (Type("Dsl_Nary_Ops.cvc_ListVar",[typ]),(m-n)::lvars)
   (*TODO: If list appears in a concat it should not be made a ListVar here? *)
(*For now change SMT_Word.concat_smt to take bool list ListVar instead of bool list list *)
   (*TODO: make list here if var1_is_in_list*)
  in
   (Const ("HOL.All", Type (t1,[Type(t2a,[new_typ,t2b2]),t3])) $ (Abs (name, new_typ,mk_nary l2 new_lvars lists (n+1) m)))
  end |
mk_nary (l1 $ l2) lvars lists n m = ((mk_nary l1 lvars lists n m) $ (mk_nary l2 lvars lists n m)) |
mk_nary l1 _ _ _ _ = l1





fun rare_lists list_param nr_pars term ctxt =
let 
    val list_param2 = map (fn (SMTLIB.S [SMTLIB.Sym name, SMTLIB.Sym _]) => name ) list_param
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("list_param2 ", list_param2))

    val nary_term = mk_nary term [] list_param2 0 (nr_pars - 1)
    val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "After adding list operators: " ) [] 
in 
    nary_term
end

end
