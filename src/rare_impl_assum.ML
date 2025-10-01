(*  Title:      IsaRARE/rare_impl_assum.ML
    Author:     Hanna Lachnitt, Stanford University

This file provides functionality to implicit assumptions to a SMTLIB Tree:

 Some operators have restrictions on the values they take in SMTLIB. This is particularly the case
 for the theory of bitvectors. E.g., extract i j s is restricted to values 0 \<le> i \<le> j \<le> size s and
 the bidwith of the output is size(i) + 1 - j. 

*)
signature RARE_IMPL_ASSUM =
sig
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string
  fun get_implicit_assump = SMTLIB.tree ->
      SMTLIB.tree list ->
        (SMTLIB.tree * SMTLIB.tree) list ->
          SMTLIB.tree list *
          (SMTLIB.tree * SMTLIB.tree) list * SMTLIB.tree
end;

structure RARE_Impl_Assum: RARE_IMPL_ASSUM =
struct
  exception WRITE_LEMMA_FROM_DSL_REWRITE of string


(*I need this to be incooperated in the other function and called on terms that are added to implicit assumptions as well*)
val merge_sets = Library.union (fn (a,b) => (a = b))
val merge_subterms = Library.union (fn ((_,b),(_,d)) => (b = d))

fun get_implicit_assump (SMTLIB.S [SMTLIB.Sym "extract", i, j, t]) assms subterms =
  let
   val (assms, subterms, new_body) = get_implicit_assump t assms subterms
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
 get_implicit_assump (SMTLIB.S [SMTLIB.Sym operator, i, t]) assms subterms =
  if not (Library.member (op =) ["concat","repeat","zero_extend","sign_extend","rotate_left","rotate_right"] operator)
   then normal_case (SMTLIB.S [SMTLIB.Sym operator, i, t]) assms subterms
  else if operator = "concat" then
   let
    val (assms, subterms, new_i') = get_implicit_assump i assms subterms
    val (assms, subterms, new_t') = get_implicit_assump t assms subterms

    val new_term = (SMTLIB.S [SMTLIB.Sym operator, new_i', new_t'])
    val new_var = case List.find (fn (_,b) => new_term = b) subterms of
                  NONE =>  "_c" ^ Library.string_of_int (length subterms) |> SMTLIB.Sym |
                  SOME (x,_) => x
    val subterms = merge_subterms [(new_var,new_term)] subterms

    val add_assms =
       [ SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym "bvsize", new_var],
         SMTLIB.S [SMTLIB.Sym "+", SMTLIB.S [SMTLIB.Sym "bvsize", new_i'], SMTLIB.S [SMTLIB.Sym "bvsize", new_t']]],
       SMTLIB.S [SMTLIB.Sym "=", new_var, (SMTLIB.S [SMTLIB.Sym operator, new_i', new_t'])
       ]] |> Library.distinct (fn (a,b) => (a = b))

    val assms = merge_sets add_assms assms
   in
    (assms,subterms,new_var)
   end
  else if operator = "rotate_left" orelse operator = "rotate_right"
   then
    let
     val (assms, subterms, new_body) = get_implicit_assump t assms subterms
    in
     (merge_sets [SMTLIB.S [SMTLIB.Sym "<=", SMTLIB.Num 0, i]] assms,subterms,(SMTLIB.S [SMTLIB.Sym operator, i, new_body]))
    end
  else 
   let
    val (assms, subterms, new_body) = get_implicit_assump t assms subterms
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
 get_implicit_assump (SMTLIB.S ts) assms subterms = normal_case (SMTLIB.S ts) assms subterms |
 get_implicit_assump x assms ids = (assms,ids,x)
and
normal_case (SMTLIB.S ts) assms subterms =
 let
  fun fold_get_implicit assms' subterms' (t::ts) new_term = 
   let
    val (assms', subterms', t') = get_implicit_assump t assms' subterms'
   in
    fold_get_implicit assms' subterms' ts (new_term @ [t'])
   end |
  fold_get_implicit assms' subterms' [] new_term = (assms',subterms',new_term)
    val (assms,subterms,new_term) = fold_get_implicit assms subterms ts []
 in
  (assms,subterms,(SMTLIB.S new_term))
 end |
normal_case _ _ _ = raise WRITE_LEMMA_FROM_DSL_REWRITE("Error while getting implicit assumptions")

end
