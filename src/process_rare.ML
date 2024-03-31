(*  Title:      IsaRARE/process_rare.ML
    Author:     Hanna Lachnitt, Stanford University

*)

signature PROCESS_RARE =
sig
  type rewrite_rule_term =
  {
    rule_name : string,
    params : (string * typ) list,
    concl : term
  }
  val process_rule : Proof.context -> Parse_RARE.rewrite_rule -> rewrite_rule_term


  (*val process_tree : Parse_RARE.rewrite_rule -> thm 
  val combine_tree : Parse_RARE.rewrite_rule -> SMTLIB.tree*)
end;

structure Process_RARE: PROCESS_RARE =
struct

open Parse_RARE

type rewrite_rule_term =
{
  rule_name : string,
  params : (string * typ) list,
  concl : term
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
  t  |> infer_types
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


 fun process_rule ctxt (rule as ({rule_name, params, let_defs, ...} : rewrite_rule)) =
   let
     val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "Processing rule " ^ rule_name) []

     (*Combine body according to rule*)
     val body = combine_tree rule
     val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "Combined body " ^ SMTLIB.str_of body) []

     (*Add implicit assumptions*)
     (*val (implAss,body') = RARE_Impl_Assms.process ctxt body params
     val body_with_implAss = SMTLIB.S [SMTLIB.Sym "implies", SMTLIB.S ([SMTLIB.Sym "and"]@implAss), body']
     val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "Added impl ass " ^ SMTLIB.str_of body_with_implAss) []*)
     val body_with_implAss = body

     (*Add lets*)
     val let_body = let_tree body_with_implAss let_defs
     (*Add quantifiers*)
     val quant_rule = quant_tree params let_body

     val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "Rule as SMTLIB tree: " ^ SMTLIB.str_of quant_rule) []

     (*Transform to Isabelle term*)
     val cx = SMTLIB_Proof.empty_context ctxt Symtab.empty Symtab.empty
     val term = SMTLIB_Proof.term_of quant_rule cx |> fst
     (*Separate parameters and body*)
     fun get_body (Const ("HOL.All", _) $ x) params =
     let 
       val (param,new_term) = Term.dest_abs_global x
     in
       get_body new_term (param::params)
     end |                                
         get_body x params = (x,params)

     val (term_without_quant,new_params) = get_body term []
     val _ = @{print}("new_params",new_params)
     val _ = @{print}("term_without_quant",term_without_quant)

       (*TODO: Reorder params if necessary *)

     (*Add lists*)


(* (*First the tree is parsed without considering lists*)
   val cx = empty_context ctxt Symtab.empty Symtab.empty
   val term = SMTLIB_Proof.term_of smtlib_tree cx |> fst
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("After parsing to Isabelle terms (before adding list operators): ",term)) (* Syntax.pretty_term ctxt *)

   (*Then, the whole term is traversed to make terms lists and introduce corresponding operators*)
   val nary_term = if (Config.get ctxt IsaRARE_Config.listsAsVar)
      then term else RARE_Lists.rare_lists list_param nr_pars term ctxt
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("After adding list operators: ",  nary_term))

   (*val str_body = hackish_string_of_term ctxt nary_term*)

   (*Finally, types are reinferred to allow gradual types*)

   val term_gen_types = nary_term |> generalize_types ctxt
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("After re-inference of types:  ", term_gen_types))
*)
   in
    ({rule_name=rule_name,params= new_params,concl=term_without_quant}:rewrite_rule_term)
   end




end;