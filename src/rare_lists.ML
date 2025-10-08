(*  Title:      IsaRARE/rare_lists.ML
    Author:     Hanna Lachnitt, Stanford University
*)

signature RARE_LISTS =
sig
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string
  val rare_lists : REWRITE_RULE_AST.par list -> term -> Proof.context -> term
end;

structure RARE_Lists: RARE_LISTS =
struct
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string

fun neutral_for_operator "HOL.conj" = Const (\<^const_name>\<open>HOL.True\<close>, \<^typ>\<open>HOL.bool\<close>) |
neutral_for_operator "HOL.disj" = Const (\<^const_name>\<open>HOL.False\<close>, \<^typ>\<open>HOL.bool\<close>) |
neutral_for_operator "Groups.plus_class.plus" = Const (\<^const_name>\<open>Groups.zero\<close>,dummyT) |
neutral_for_operator "Orderings.ord_class.less_eq" = Const (\<^const_name>\<open>Groups.zero\<close>, dummyT) |
neutral_for_operator "Groups.times_class.times" = Const (\<^const_name>\<open>Groups.one\<close>,dummyT) |
neutral_for_operator "Smtlib_String.smtlib_re_concat" = Free ("{[]}", \<^typ>\<open>RegLan\<close>) |
neutral_for_operator "Smtlib_String.smtlib_re_union" = Free ("{}", \<^typ>\<open>RegLan\<close>) |
neutral_for_operator "Smtlib_String.smtlib_re_inter" = Free ("UNIV", \<^typ>\<open>RegLan\<close>) |
neutral_for_operator "Smtlib_String.smtlib_str_concat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) |
neutral_for_operator "Word.word_cat" = Const (\<^const_name>\<open>List.Nil\<close>, \<^typ>\<open>String.string\<close>) | (*TODO*)
neutral_for_operator "Bit_Operations.semiring_bit_operations_class.xor" =  Const (\<^const_name>\<open>Groups.zero\<close>, dummyT) |
neutral_for_operator l = (@{print}("neutral_for_operator", l);Free ("PutInNeutral",dummyT))

 (* \<^typ>\<open>(T \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a Dsl_Nary_Ops.cvc_ListVar \<Rightarrow> 'a\<close>*)
val dummyBinFunT = (dummyT --> dummyT --> dummyT) --> dummyT --> dummyT --> dummyT

fun var_is_list_par v list = List.exists (curry (op =) v) list

fun new_operator v1_list v2_list op_name op_typ =
(@{print}("original op",(op_name,op_typ));
  if not v1_list andalso not v2_list
   then Const (op_name,op_typ)
  else if not v1_list
   then Const(\<^const_name>\<open>cvc_list_right\<close>,dummyBinFunT) $ Const (op_name,dummyT)
  else if not v2_list
   then Const(\<^const_name>\<open>cvc_list_left\<close>,dummyBinFunT) $ Const (op_name,dummyT)
  else Const(\<^const_name>\<open>cvc_list_both\<close>,dummyBinFunT) $ Const (op_name,dummyT) $ (neutral_for_operator (fst (op_name,dummyT)))
)

(*TODO decrease m instead of giving two arguments*)
fun mk_nary ((Const (op_name,op_typ)) $ (Bound m1) $ (Bound m2)) _ lists _ _ =
  let
   val m1_list = var_is_list_par m1 lists
   val m2_list = var_is_list_par m2 lists
   val new_op = new_operator m1_list m2_list op_name op_typ
   val _ = @{print}("new op",(new_op));
  in 
   (new_op $ (Bound m1) $ (Bound m2))
  end |
mk_nary ((Const (op_name,op_typ)) $ (Bound m1) $ l2) param_names lists n m =
  let 
   val _ = @{print}("m1",(m1));
   val _ = @{print}("l2",(l2));

   val m1_list = var_is_list_par m1 lists |> @{print}
   val new_op = new_operator m1_list false op_name op_typ 
   val _ = @{print}("new op",(new_op));

  in 
   (new_op $ (Bound m1) $ (mk_nary l2 param_names lists n m))
  end |
mk_nary ((Const (op_name,op_typ)) $ l1 $ (Bound m2)) param_names lists n m =
  let
   val m2_list = var_is_list_par m2 lists |> @{print}
   val new_op = new_operator false m2_list op_name op_typ 
   val _ = @{print}("new op",(new_op));

  in  
   (new_op $ (mk_nary l1 param_names lists n m) $ (Bound m2))
  end |
mk_nary (Const ("HOL.All", Type (t1,[Type(t2a,[new_typ,t2b2]),t3])) $ (Abs (name, typ,l2))) param_names lists n m =
  let
   val name_list = var_is_list_par name param_names
   val (new_typ,new_lvars) = if not name_list
                             then (typ,lists)
                             else if (fst (dest_Type new_typ) = "Word.word")
                             then (Type("Dsl_Nary_Ops.cvc_ListVar",[dummyT]),(m-n)::lists)
                             else (Type("Dsl_Nary_Ops.cvc_ListVar",[typ]),(m-n)::lists)
   val _ = @{print}("add new enntry",(name,m-n));

  in
   (Const ("HOL.All", Type (t1,[Type(t2a,[new_typ,t2b2]),t3])) $ (Abs (name, new_typ,mk_nary l2 param_names new_lvars (n+1) m)))
  end |
mk_nary (l1 $ l2) lvars lists n m = ((mk_nary l1 lvars lists n m) $ (mk_nary l2 lvars lists n m)) |
mk_nary l1 _ _ _ _ = l1





fun rare_lists params term ctxt =
let 
  val param_names =
    map_filter (fn (REWRITE_RULE_AST.Par _) => NONE |
               (REWRITE_RULE_AST.ListPar (SMTLIB.S[SMTLIB.Sym name,_])) => SOME name)
    params
  val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> ("The following list parameters were found: ", param_names))
  val nary_term = mk_nary term param_names [] 0 (length params-1)
  val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print> ("The term after adding lists: ", nary_term))
in 
    nary_term
end

end
