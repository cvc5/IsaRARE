(*  Title:      IsaRARE/write_rewrite_as_lemma.ML
    Author:     Hanna Lachnitt, Stanford University

Diagnostic tools for IsaRARE.
*)
(*TODO: I still don't like the name of this file*)

(*
This file offers the functionality to transform a rewrite_tree to a lemma

Adding implicit assumptions:

 Some operators have restrictions on the values they take in SMTLIB. This is particularly the case
 for the theory of bitvectors. E.g., extract i j s is restricted to values 0 \<le> i \<le> j \<le> size s and
 the bidwith of the output is size(i) + 1 - j. 

Binarisation of n-ary operators in rare rules:
 TODO

Type inference:
 Since dummy types were added during parsing IsaRARE has to re-generalize types.



*)

signature WRITE_REWRITE_AS_LEMMA =
sig
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string

  val write_lemma: Parse_RARE.rewrite_tree -> Proof.context -> string list (*TODO: Change order of context such that it is the same for parse_rewrite and this*)
  val write_thy: Parse_RARE.rewrite_tree list -> string -> string -> Proof.context -> string
end;

open SMTLIB_Proof
open Parse_RARE
open RARE_Impl_Assump
open RARE_Lists

structure Write_Rewrite_as_Lemma: WRITE_REWRITE_AS_LEMMA =
struct
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string

(* Utilities *)

fun hackish_string_of_term ctxt =
 Print_Mode.setmp [] (Syntax.string_of_term ctxt)
  #> YXML.content_of

fun hackish_string_of_type ctxt =
 Print_Mode.setmp [] (Syntax.string_of_typ ctxt)
  #> YXML.content_of


(* Writing Utility Functions *)

(* Theory *)
fun write_file_header theory_name theory_imports 
 = Library.cat_lines
  ["theory " ^ theory_name,
   "  imports \"HOL-CVC.Dsl_Nary_Ops\" " ^ theory_imports,
   "begin\n",
   "(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!",
   "All that remains to do is to prove any lemma whose provided proof fails.",
   "If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)\n\n"]

val write_file_footer = "end"

(* Lemma *)
fun write_lemma_header name
 = Library.cat_lines
   ["named_theorems rewrite_" ^ name ^ " \<open>automatically_generated\<close>\n",
    "lemma [rewrite_" ^ name ^ "]:"]

fun write_body body param ctxt =
  let
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Writing body "))

   val str_body = hackish_string_of_term ctxt body
  
   val a = String.isPrefix "\<forall>" str_body

   fun wth_forall ("."::" "::xs) = xs |
       wth_forall ("."::"\n"::" "::" "::" "::xs) = xs |
       wth_forall ("."::xs) = xs | 
       wth_forall (_::xs) = wth_forall xs |
       wth_forall xs = xs

   val temp = if a then raw_explode str_body |> wth_forall else raw_explode str_body
   val goal = temp |> filter (fn x => not (x = "?")) |> implode

   val goal' = "NO_MATCH cvc_a (undefined " ^ space_implode " " (rev param) ^ ") \<Longrightarrow> "
  in
   "  shows \"" ^ goal' ^ goal ^ "\""
  end

fun write_auto lists name ctxt =
 if lists = []
 then
  (if  IsaRARE_Config.getStrategy ctxt = IsaRARE_Config.Strings
   then "    by (simp add: cvc_string_rewrite_defs)\n"
   else  "  by auto\n\n")
 else
  let
   fun write_cases xs = if xs = [] then ""
     else map (fn str => "  apply (cases " ^ str ^ ")\n") xs |> foldl1 (String.^)
   fun write_subgoal xs = if xs = [] then "" else map (fn str => str ^ "s ") xs |> foldl1 (String.^)

   fun write_induct []= "" |
       write_induct (x::xs) =  "    apply (induction " ^ x ^ "s arbitrary: " ^ x ^ ")\n" ^ 
                               "    apply simp_all\n"
                               ^ write_induct xs

   val tactic = write_cases lists ^ "  subgoal for " ^ write_subgoal lists ^ "\n" ^
               "    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)\n" ^ 
               write_induct lists ^
               (if  IsaRARE_Config.getStrategy ctxt = IsaRARE_Config.Strings
               then "    apply (simp_all add: cvc_string_rewrite_defs)\n"
               else "") ^
               "    apply (simp_all add: cvc_rewrites_fold)\n" ^
               "    by (simp_all add: " ^ name ^  "_lemma)\n" ^
               "  done\n\n"
  in
    Library.cat_lines [tactic]
  end


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

fun parse_tree smtlib_tree list_param nr_pars ctxt =
 let

  val smtlib_tree =
   if (Config.get ctxt IsaRARE_Config.implAssump)
    then
    let
      val (implicit_assumptions,_,new_tree) = get_implicit_assump smtlib_tree [] [] list_param
      val implicit_assumptions2 = SMTLIB.S ([SMTLIB.Sym "and"] @ implicit_assumptions)
      val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Generated the following set of implicit assumptions: ", implicit_assumptions2))
    in
    case new_tree of
      SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S param,SMTLIB.S [SMTLIB.Sym "let", SMTLIB.S lets, body]] => 
      if implicit_assumptions = []
      then smtlib_tree
      else (SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S param,SMTLIB.S [SMTLIB.Sym "let", SMTLIB.S lets, 
            SMTLIB.S [SMTLIB.Sym "=>",implicit_assumptions2, body]]]) |
      SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S param,body] =>
        if implicit_assumptions = []
        then smtlib_tree
        else (SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S param, SMTLIB.S [SMTLIB.Sym "=>",implicit_assumptions2, body]]) |
      _ => raise WRITE_LEMMA_FROM_DSL_REWRITE("Error when adding implicit assumptions")
    end
    else smtlib_tree 

   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Tree after potentially adding assumptions: ", smtlib_tree))

   (*First the tree is parsed without considering lists*)
   val cx = empty_context ctxt Symtab.empty Symtab.empty
   val term = SMTLIB_Proof.term_of smtlib_tree cx |> fst
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("After parsing to Isabelle terms (before adding list operators): ", Syntax.pretty_term ctxt term))

   (*Then, the whole term is traversed to make terms lists and introduce corresponding operators*)
   val nary_term = if (Config.get ctxt IsaRARE_Config.listsAsVar)
      then term else RARE_Lists.rare_lists list_param nr_pars term ctxt
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("After adding list operators: ",  nary_term))

   (*val str_body = hackish_string_of_term ctxt nary_term*)

   (*Finally, types are reinferred to allow gradual types*)

   val term_gen_types = nary_term |> generalize_types ctxt
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("After re-inference of types:  ", term_gen_types))

  in
   (term_gen_types,ctxt)
  end

local

 fun write_pars res ctxt = 
  let
   val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Writing parameters  "))

   fun write_params [] = "" |
       write_params [Const (str,typ)] = str ^ ":: \"" ^ hackish_string_of_type ctxt typ ^ "\"" |
       write_params (Const (str,typ)::ps) = str ^ ":: \"" ^ hackish_string_of_type ctxt typ ^ "\"" ^ " and " ^ write_params ps |
       write_params _ = raise WRITE_LEMMA_FROM_DSL_REWRITE("Problem while writing parameter")

   fun delete_question_mark l = l |> filter (fn x => not (x = "?"))

   fun temp ("w"::"o"::"r"::"d"::ts) = (":"::":"::"l"::"e"::"n"::" ":: "w"::"o"::"r"::"d"::ts) |
       temp (t::ts) = t :: temp ts|
       temp [] = []

  fun test (Const ("HOL.All", _) $ Abs (str, typ,((Const ("HOL.All", typ1) $ t1)))) =
    let
      val new_type = implode ( (hackish_string_of_type ctxt typ |> raw_explode |> delete_question_mark)) (*LENGTH thing should happen in parser eventually*)
    in
       str ^ "::\"" ^ new_type ^ "\"" ^ " and " ^ test ((Const ("HOL.All", typ1) $ t1))
    end |
  test (Const ("HOL.All", _) $ Abs (str, typ,ts)) = str ^ "::\"" ^  (implode ( (hackish_string_of_type ctxt typ |> raw_explode |> delete_question_mark)))  ^ "\"" |
  test x = (@{print}("x",x);"")
  in
   if size (test res) = 0 then "" else "  fixes " ^ test res
  end


  (*Would the use of Pure.all change this all?!*)
  fun quant_letify_tree tree param (NONE) = SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S (rev param), tree] |
   quant_letify_tree tree param (SOME lets) = (@{print}("lets",lets);SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S (rev param),
                                               SMTLIB.S [SMTLIB.Sym "let", SMTLIB.S lets, tree]])
 in

 fun write_lemma (Rewrite_Rule ((Rule_Type DEFINE_RULE)::(Rule_Name name):: [Par (param,list_param), Let_Defs ld, Match m, Target t])) ctxt =
   let
    val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "Processing normal rule with the name " ^ name) []
    val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("param are  ", param))

    (*Build up smtlib tree*)
    val smtlib_tree_body = SMTLIB.S [SMTLIB.Sym "=", m, t]
    val smtlib_tree = quant_letify_tree smtlib_tree_body param ld
    val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("Tree is  ", smtlib_tree))

    (*Get term of smtlib_tree*)
    val (res,ctxt) = parse_tree smtlib_tree list_param (length param) ctxt
    (*Get components of term for printing*)
    val list_param2 = map (fn (SMTLIB.S [SMTLIB.Sym name, SMTLIB.Sym typ]) => name) list_param
    val param2 = map (fn (SMTLIB.S [SMTLIB.Sym name, _]) => name) param
    val _ =  IsaRARE_Config.debug_msg_raw ctxt (fn () => \<^print>  ("get list params and param  ", list_param2))
(*("param are  ",
 [S [Sym "x", Sym "?BitVec"], S [Sym "c", S [Sym "_", Sym "BitVec", Num 1]]])*)

   in
    [write_lemma_header name, write_pars res ctxt, write_body res param2 ctxt, write_auto list_param2 name ctxt]
   end |                                                
  write_lemma (Rewrite_Rule ((Rule_Type DEFINE_COND_RULE)::(Rule_Name name)::[Par (param,list_param), Let_Defs ld, Precondition ass, Match m, Target t])) ctxt =
   let
    val _ = IsaRARE_Config.debug_msg ctxt (fn _ => "Processing conditional rule with the name " ^ name) []

    val smtlib_tree_body = SMTLIB.S [SMTLIB.Sym "implies", ass, SMTLIB.S [SMTLIB.Sym "=", m, t]]
    val smtlib_tree = quant_letify_tree smtlib_tree_body param ld
    val (res,ctxt) = parse_tree smtlib_tree list_param (length param) ctxt
    val list_param2 = map (fn (SMTLIB.S [SMTLIB.Sym name, SMTLIB.Sym typ]) => name) list_param
    val param2 = map (fn (SMTLIB.S [SMTLIB.Sym name, SMTLIB.Sym typ]) => name) param

   in 
     [write_lemma_header name, write_pars res ctxt, write_body res param2 ctxt, write_auto list_param2 name ctxt]
   end |
  write_lemma (Rewrite_Rule ((Rule_Type DEFINE_STAR_RULE)::(Rule_Name name)::[Par (param,list_param), Let_Defs ld, Context_Expr context_expr, Match m, Target t])) ctxt =
   let (*TODO*)
     fun eliminate_context (SMTLIB.S ts) = (SMTLIB.S (map eliminate_context ts)) |
         eliminate_context (SMTLIB.Sym "_") = t |
         eliminate_context x = x
 
     val t = case context_expr of
             NONE => t |
             SOME ce => eliminate_context ce

     val smtlib_tree_body = SMTLIB.S [SMTLIB.Sym "=", m, t]
     val smtlib_tree = quant_letify_tree smtlib_tree_body param ld
     val (res,ctxt) = parse_tree smtlib_tree list_param (length param) ctxt
     val list_param2 = map (fn (SMTLIB.S [SMTLIB.Sym name, SMTLIB.Sym typ]) => name) list_param
    val param2 = map (fn (SMTLIB.S [SMTLIB.Sym name, SMTLIB.Sym typ]) => name) param

   in
     [write_lemma_header name, write_pars res ctxt, write_body res param2 ctxt, write_auto list_param2 name ctxt]
   end |
  write_lemma rwr _ = (@{print}("rwr",rwr);raise WRITE_LEMMA_FROM_DSL_REWRITE ("Could not write rewrite rule to lemma, has wrong form"))
end

local
  fun write_lemmas_h [] _ = [] |
      write_lemmas_h (c::cs) ctxt = (write_lemma c ctxt) @ write_lemmas_h cs ctxt
in 
  fun write_thy cs theory_name theory_imports ctxt
    = write_file_header theory_name theory_imports ^ Library.cat_lines ( write_lemmas_h cs ctxt) ^ write_file_footer
end

end;