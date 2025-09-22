(*  Title:      IsaRARE/process_rare.ML
    Author:     Hanna Lachnitt, Stanford University

*)

signature PROCESS_RARE =
sig
  type rewrite_rule_term =
  {
    params : (string * typ) list,
    concl : term
  }
  type rewrite_rule_lemma =
  {
    rule_name : string,
    rule_body : rewrite_rule_term list
  }
  val process_rule : Proof.context -> Parse_RARE.rewrite_rule -> rewrite_rule_lemma


  (*val process_tree : Parse_RARE.rewrite_rule -> thm 
  val combine_tree : Parse_RARE.rewrite_rule -> SMTLIB.tree*)
end;

structure Process_RARE: PROCESS_RARE =
struct

open Parse_RARE

type rewrite_rule_term =
{
  params : (string * typ) list,
  concl : term
}

type rewrite_rule_lemma =
{
  rule_name : string,
  rule_body : rewrite_rule_term list
}

(* Type Re-inference *)

fun generalize_types ctxt t =
let
  (*Don't erase simple types here.*)
  (*val erase_types = map_types (fn x => dummyT)*)
  (* use schematic type variables *)
  val ctxt = ctxt |> Proof_Context.set_mode Proof_Context.mode_pattern
  val infer_types = singleton (Type_Infer_Context.infer_types ctxt)
in
  t |> infer_types
end

fun let_tree tree NONE = tree |
    let_tree tree (SOME []) = tree |
    let_tree tree (SOME ((n,v)::lets)) = SMTLIB.S [SMTLIB.Sym "let", SMTLIB.S [n,v], let_tree tree (SOME lets)]


fun quant_tree [] tree = tree |
    quant_tree params tree = SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S (map (fn (Par p) => p | (ListPar p) => p) params), tree]

fun eliminate_context t (SMTLIB.S ts) = (SMTLIB.S (map (eliminate_context t) ts)) |
    eliminate_context t (SMTLIB.Sym "_") = t |
    eliminate_context t x = x

fun combine_tree (rule as ({rule_type=DEFINE_RULE, precondition=NONE, context_expr = NONE, ...} : rewrite_rule)) =
   SMTLIB.S [SMTLIB.Sym "=", #match rule, #target rule] |
 combine_tree (rule as ({rule_type=DEFINE_COND_RULE, precondition=(SOME p), context_expr = NONE, ...} : rewrite_rule)) = 
    SMTLIB.S [SMTLIB.Sym "implies", p, SMTLIB.S [SMTLIB.Sym "=", #match rule, #target rule]] |
 combine_tree (rule as ({rule_type=DEFINE_RULE_STAR, precondition=NONE, context_expr = NONE, ...} : rewrite_rule)) = 
    SMTLIB.S [SMTLIB.Sym "=", #match rule, #target rule] |
 combine_tree (rule as ({rule_type=DEFINE_RULE_STAR, precondition=NONE, context_expr = (SOME c), ...} : rewrite_rule)) = 
    SMTLIB.S [SMTLIB.Sym "=", #match rule, eliminate_context (#target rule) c] |
 combine_tree ({rule_name, ...} : rewrite_rule) = raise PARSE("Rule " ^ rule_name ^ " has wrong type and could not be processed!")

(*In case we want to print one lemma per type seperateLemmasForTypes*)
(*params might contain schematic types*)
(*We have to re-infer types after each such parameter gets a new type, so params gets smaller and changes every iteration*)
val smtlib_types = [@{typ "HOL.bool"},@{typ "Int.int"},@{typ "Real.real"},@{typ "String.string"}] (*TODO: Make this for complex types, should be easy*)

fun match_types _ term [] = ([term] : term list) |
 match_types ctxt term (par::params)  =
let
  val par_possible_types = filter (fn t => Type.could_unify (par |> snd |> @{print},t|> @{print})) smtlib_types
  val _ = @{print}("explode_params",par_possible_types)

  fun not_processed_yet p = List.exists (curry (op =) (fst p|> @{print})) (map fst params |> @{print})|> @{print}

  (*Add each type to term and recursively call function*)
  fun process_term [] term = [(generalize_types ctxt term,[])] | (*Maybe only add if no gradual types in it*)
    process_term (new_type::ts) term =
    let

      val term_with_new_type = map_types (fn t => if t = (snd par) then new_type else t) term
      val _ = @{print}("term_with_new_type",term_with_new_type)

      val term_with_new_type' = generalize_types ctxt term_with_new_type

     
    in
      if not (term_with_new_type' = term)
      then
       let
      val _ = @{print}("term_with_new_type'",term_with_new_type')

       fun get_body (Const ("HOL.All", _) $ x) params' params2' = (*Could have this check if all foralls are from parameters, currently nothing else is allowed in RARE*)
           let val (param,new_term) = Term.dest_abs_global x
           in
             get_body new_term (if not_processed_yet param then (param::params') else params') (param::params')
           end |                                
         get_body x params' params2' = (x,params',params2')

     val (term_without_quant,new_params,new_params2) = get_body term_with_new_type' [] [] (*I should delete the params that I already processed, otherwise params never gets smaller*)
      val _ = @{print}("term_without_quant",term_without_quant)
      val _ = @{print}("new_params",new_params)
      val _ = @{print}("new_params2",new_params2)
      in
       (term_with_new_type',new_params) :: process_term ts term end
    else process_term ts term end

  val res_process = process_term par_possible_types term
  val _ = @{print}("all possible new terms",res_process)

  fun call_match [] = [] |
  call_match ((nt,np)::nts) =
    let
      val tt = (match_types ctxt nt np : term list) (*TODO: I also want params to be updated, maybe its type is already found*)
    in
      tt @ call_match nts
    end
  val res_rec = call_match res_process
  val _ = @{print}("finished processing term recursively ",res_rec)

in
  res_rec
end


fun process_rule ctxt (rule as ({rule_name, params, let_defs, ...} : rewrite_rule)) =
   let
     val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "Processing rule " ^ rule_name) []

     (*Combine body according to rule*)
     val body = combine_tree rule
     val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "Combined body " ^ SMTLIB.str_of body) []

     (*Add implicit assumptions*)
     val (implAss,body') = RARE_Impl_Assms.process ctxt body params
     val body_with_implAss = SMTLIB.S [SMTLIB.Sym "implies", SMTLIB.S ([SMTLIB.Sym "and"]@implAss), body']
     val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "Added impl ass " ^ SMTLIB.str_of body_with_implAss) []
     val body_with_implAss = body

     (*Add lets*)
     val let_body = let_tree body_with_implAss let_defs

     (*Add quantifiers*)
     val quant_rule = quant_tree params let_body

     val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "Rule as SMTLIB tree: " ^ SMTLIB.str_of quant_rule) []

     (*Transform to Isabelle term*)
     (*First the tree is transformed without considering lists*)
     val cx = SMTLIB_Proof.empty_context ctxt Symtab.empty Symtab.empty
     val term = SMTLIB_Proof.term_of quant_rule cx |> fst
     val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Transformed into Isabelle term:  ", term))

     (*Add lists*)
     val term = RARE_Lists.rare_lists params term ctxt
     val _ = @{print}("yyy term",term)

     (*Finally, types are reinferred to allow gradual types*)
     val term_gen_types = term |> generalize_types ctxt
     val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("After re-inference of types:  ", term_gen_types))
     val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("params:  ", params))

     (*If we don't care about lemmas potentially being to general we are done, we merely 
     separate body and parameters from each other. Otherwise, we try to match all available
     SMT-LIB types.*)

     fun get_body (Const ("HOL.All", _) $ x) params = (*Could have this check if all foralls are from parameters, currently nothing else is allowed in RARE*)
           let val (param,new_term) = Term.dest_abs_global x in get_body new_term (param::params) end |                                
         get_body x params = (x,params)

     val (term_without_quant,new_params) = get_body term_gen_types []
     val _ = @{print}("new_params",new_params)
     val _ = @{print}("term_without_quant",term_without_quant)

     val tems =
     if not (Config.get ctxt IsaRARE_Config.seperateLemmasForTypes)
     then [({params= new_params,concl=term_without_quant} : rewrite_rule_term)]
     else
      let
         val temp = if new_params = [] then @{typ "int"} else  hd new_params |> snd
         val temp2 = Type.could_unify (temp, @{typ "int"})
         val _ = @{print}("temp2",temp2)
         val temp2 = Type.could_unify (temp, @{typ "string"})
         val _ = @{print}("temp2",temp2)
         val temp2 = Type.could_unify (temp, @{typ "real"})
         val _ = @{print}("temp2",temp2)
         val _ = @{print}("temp3",(Term.strip_all_body term_gen_types))

         fun temp (Const ("HOL.All", _) $ Abs (_, _,t)) = temp t |
             temp t = t
         val _ = @{print}("temp3",(temp term_gen_types))

         val ttt = match_types ctxt (term_gen_types) (rev new_params) 
         val _ = @{print}("ttt",ttt)

        val xs = map (fn t => get_body t []) ttt |> Library.distinct (op =)
             val _ = @{print}("xs",xs)

         fun mk_rewrite_rule_term [] = [] |
             mk_rewrite_rule_term ((c,q)::ts) =
             ({params= q,concl=c} : rewrite_rule_term) :: mk_rewrite_rule_term ts
      in mk_rewrite_rule_term xs end

   in
    ({rule_name=rule_name,rule_body=tems}:rewrite_rule_lemma)
   end




end;