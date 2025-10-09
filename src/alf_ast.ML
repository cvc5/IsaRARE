(*  Title:      IsaRARE/alf_parser.ML
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mallku Soldevila, Universidade Federal de Minas Gerais

    AST for Eunoia rules.
*)

signature ALF_AST =
sig

    (* AST representation of Eunoia rules used to represent RARE rules:
       - no premises
       - no side-conditions
       - only args and conclusions *)
    type eunoia_rule =
    {
      rule_name : string,
      (* TODO: sharing this with REWRITE_RULE_AST *)
      args : REWRITE_RULE_AST.par list,
      conclusion : SMTLIB.tree
    }

    (* TODO: would not be required *)
    datatype alf_rule_type = ALF_AXIOM | ALF_RULE
end;

structure ALF_AST: ALF_AST =
struct

  type eunoia_rule =
  {
    rule_name : string,
    (* TODO: sharing this with REWRITE_RULE_AST *)
    args : REWRITE_RULE_AST.par list,
    conclusion : SMTLIB.tree
  }
    
  (* TODO: would not be required *)
  datatype alf_rule_type = ALF_AXIOM | ALF_RULE

end;
