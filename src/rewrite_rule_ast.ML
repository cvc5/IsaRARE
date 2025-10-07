(*  Title:      IsaRARE/rewrite_rule_ast.ML
    Author:     Hanna Lachnitt, Stanford University

    This file contains the signature and an implementation for the notion of
    "AST of a rewrite rule". This AST is later given semantics through a shallow 
    embedding into Isabelle.
*)

signature REWRITE_RULE_AST =
sig
    datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
    datatype par = Par of SMTLIB.tree | ListPar of SMTLIB.tree

    type rewrite_rule =
         {
           rule_type : rule_type,
           rule_name : string,
           params : par list,
           let_defs : (SMTLIB.tree * SMTLIB.tree) list option,
           precondition : SMTLIB.tree option,
           match : SMTLIB.tree,
           target : SMTLIB.tree,
           context_expr : SMTLIB.tree option
         }

end;

structure REWRITE_RULE_AST: REWRITE_RULE_AST =
struct

  datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
  datatype par = Par of SMTLIB.tree | ListPar of SMTLIB.tree

  type rewrite_rule =
  {
    rule_type : rule_type,
    rule_name : string,
    params : par list,
    let_defs : (SMTLIB.tree * SMTLIB.tree) list option,
    precondition : SMTLIB.tree option,
    match : SMTLIB.tree,
    target : SMTLIB.tree,
    context_expr : SMTLIB.tree option
  }

end;
