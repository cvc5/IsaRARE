(*  Title:      IsaRARE/alf_parser.ML
    Author:     Hanna Lachnitt, Stanford University

    AST for Eunoia rules.
*)

signature ALF_AST =
sig
    datatype alf_rule_type = ALF_AXIOM | ALF_RULE

    datatype par = Par of SMTLIB.tree | ListPar of SMTLIB.tree
    
    type eunoia_rule =
    {
      rule_type : alf_rule_type,
      rule_name : string,
      params : par list,
      premises : SMTLIB.tree list,
      (* TODO: change this to just SMTLIB.tree *)
      conclusion : SMTLIB.tree list
    }

end;

structure ALF_AST: ALF_AST =
struct

  datatype alf_rule_type = ALF_AXIOM | ALF_RULE

  datatype par = Par of SMTLIB.tree | ListPar of SMTLIB.tree

  type eunoia_rule =
  {
    rule_type : alf_rule_type,
    rule_name : string,
    params : par list,
    premises : SMTLIB.tree list,
    conclusion : SMTLIB.tree list
  }

end;
