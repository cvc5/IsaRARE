(*<*)
theory Parsing
  imports Config
begin


ML_file \<open>../src/parse_rare.ML\<close>

(*>*)

section \<open>Parsing\<close>


text \<open>

IsaRARE is used to increase trust in SMT rewrite rules. Therefore, we want our parser to be as
transparent and readable as possible. Furthermore, since we don't expect huge files as input to
IsaRARE we did not implement the parser to be mostly efficient but instead focus on extensibility.

We especially want it to be easy for SMT developers who have no or little Isabelle knowledge to
adapt the parser, to cater to their custom rewrite format as long as that format is build on
SMT-LIB. Thus, the architecture of the parser is split up in two components.

First, a lexer separates the rewrite rules from each other.
Each rule starts with an opening parenthesis "(" and closes with a matching
closing parenthesis ")". There can be nested parenthesis in the rule. It also takes care of
comments, line breaks, extra white space and empty lines. The lexer does not already build up an
AST though. The idea is that the user now only has to write a single rule parser that takes as input
a string and does not has to care about the outer structure of the file.

Second, the parser actually transforms a string into our custom AST
@{ML_type Parse_RARE.rewrite_rule}. User could parse the string in any way they want but our
solution for RARE rules use separate component parsers. We explain how to write a component
parser and how to combine them in section XYZ.

Most exceptions that functions in this structure throw are of the type
@{ML_text "exception PARSE of string" }. This is usually done by calling 
@{ML_text "raise_lexer_error"} or @{ML_text "raise_parser_error"} which will include the line
number in which the error occurred.

\<close>

subsection \<open> Intermediate Datatype for Rewrite Rules\label{sec:parsing:AST} \<close>

text \<open>

The signature contains the @{ML_text "rewrite_rule"} used to store rewrites rules in an inter-
mediate format.

@{ML_text
"
  datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
  datatype par = Par of SMTLIB.tree | ListPar of SMTLIB.tree

  type rewrite_rule =
  {
    rule_type : rule_type,
    rule_name : string,
    params : par list,
    let_defs : SMTLIB.tree list option,
    precondition : SMTLIB.tree option,
    match : SMTLIB.tree,
    target : SMTLIB.tree,
    context_expr : SMTLIB.tree option
  }
"}

Most of the components are self explanatory. Not all objects of type @{ML_text "rewrite_rule"} are
valid rules. E.g., if @{ML_text "rule_type"} is @{ML_text "DEFINE_RULE"} there precondition should
be @{ML_text "NONE"}. However, we felt it is unnecessary to have three different types for this
with all the implications for functions using them. The parser will complain if it is supposed to
read in an invalid rule.

Rewrite rules can be printed with @{ML_def "Parse_RARE.pretty_rewrite_rule"} or
@{ML_def "Parse_RARE.str_of"}.

\<close>


subsection \<open> Lexing a RARE file \<close>

text \<open>

The lexer discards comments and excessive white space. It separates the rules from each other and
makes sure each rule is a single string even if it stretched over several lines. To do that some-
what efficiently it processes the file line by line and only expands a line when needed.

It outputs a list of (int,string) tuples where the first element is the line number the rule starts
in and the second is the read in rule. This is so that during parsing, an error can be given with
the correct line number of the original file.

Note: the lexer might occasionally in very special situations add an extra white space. This is
because line breaks inside of a rule are replaced by white spaces. If the user was to introduce
a line break inside of an expression (which we discourage) this could happen. E.g., 

\begin{lstlisting}[language=rare]
(define-rule* bv-neg-add
((x ?BitVec) (y ?BitVec) (zs ?BitVec :list))
(bvneg (
bvadd x y zs))
(bvneg (bvadd y zs))
(bvadd (bvneg x) _))
\end{lstlisting}

would add a white space between the opening parenthesis and the bvadd. In this case this space 
would then be ignored by the SMT-LIB parser.

\<close>

subsection \<open> Parsing RARE rules \<close>

text \<open>

In a first step a RARE rule is parsed in into @{ML_type Parse_RARE.rewrite_rule} which is shown in
Section \ref{sec:parsing:AST}.

While rule type and rule name are directly parsed in, the parameters and expressions are given
to SMTLIB.parse to efficiently reuse its capabilities. We use the Scan library
(\path{src/Pure/General/scan.ML}) to combine our component parsers. We allow white space
between all components that we describe in the following:

\begin{enumerate}
\item Opening parenthesis
\item Rule type:
 Simple matching on the prefix of the string list. If it is "(define-rule" we set the type to
 DEFINE_RULE and so on.
\item Rule name:
 When the name is parsed in dashes are changed to underscores since they are not allowed in Isabelle
 lemma names. 
\item Parameter list:
 The parameters list has to be in parenthesis even if there are no parameters. Each parameter is
 checked on having an annotation. The only annotation RARE has is :list. We have to delete this
 annotation from the token before we give it to the SMT-LIB parser. Then, we convert it in a
 Par if it had no annotation or ListPar if it had to save its status.
\item Let definitions:
 We check if the next token starts with a "def". In that case we parse it in as a TODO (make this a list of tuples?)
\item Expressions: We then parse all following tokens always requiring white space between them.
 All of them are converted to SMT-LIB. Then, the content of this list of expressions is matched to
 the rule components based on the rule type. E.g., for a define-cond-rule we expect there to be
 exactly three expressions that are in order precondition, match and target.

\<close>

subsection \<open>Parsing ALF\<close>

text \<open> 
The general way to declare a proof rule in ALF is:

\begin{lstlisting}[language=rare]
(declare-rule <symbol> (<typed-param>*) <assumption>? <premises>? <arguments>? <reqs>? :conclusion <term>)
where
<assumption>    ::= :assumption <term>
<premises>      ::= :premises (<term>*) | :premise-list <term> <term>
<arguments>     ::= :args (<term>*)
<reqs>          ::= :requires ((<term> <term>)*)
\end{lstlisting}

For RARE rules we use a more restricted grammar though. We don't allow reqs or arguments and only
allow :premises and not :premise-list. The grammar for ALFRARE is:

begin{lstlisting}[language=rare]
(declare-rule <symbol> (<typed-param>*) <premises>? :conclusion <term>)
where
<premises>      ::= :premises (<term>*)
\end{lstlisting}



\<close>



subsection \<open> Write your own rewrite parser \<close>

text \<open>

To write your own parser you basically just have to provide a function with the
following signature @{ML_text "Proof.context -> (int * string) list -> rewrite_rule list"}, where
the integer is the original line numbers where the rule started that is given as a string. The line
number is usually only helpful for error messages. 

For errors you can use our function @{ML_text "raise_parser_error"} that outputs the line
automatically for you and then appends your custom error message.

While you can process the string list however you like we provide some functions that might
help you. Most of these require you to expand a string into a string list of single characters
with @{ML_text "raw_explode"}.

General: We use Isabelle's Scan. library for our RARE parser.

@{ML_text "get_smtlib_term"} transforms a string list into an SMT-LIB term if
possible

@{ML_text "parse_next_term"} takes a string list and cuts off the first token (expects an opening
parenthesis as a first character, so make sure to permit white space with the white space parser
first if needed). This token can have nested parenthesis inside. It returns NONE if it could not
find the token, otherwise it returns the token and the rest of the string list after the token is
parsed.



\<close>


subsection \<open> Parsing Test \<close>

declare[[IsaRARE_debug = true]]
declare[[IsaRARE_verbose = true]]

subsubsection \<open> Test Lexer \<close>
ML \<open>

val file_name = "~/Sources/IsaRARE/Tests/Regression/bv_rewrites_proven"
val file_path = Path.explode file_name
val new_theory_name = "Parsing" ^ ".thy"
val ctxt = Context.the_local_context ()
     
val lines = Bytes.split_lines (Bytes.read file_path)
val res = Parse_RARE.lex_rewrites ctxt lines
val _ = @{print}("after lexing",res)

\<close>

subsubsection \<open> Test Parser \<close>

ML \<open>

val file_name = "~/Sources/IsaRARE/Tests/Regression/bv_rewrites_proven"
val file_path = Path.explode file_name
val new_theory_name = "Parsing" ^ ".thy"
val ctxt = Context.the_local_context ()
     
val lines = Bytes.split_lines (Bytes.read file_path)
val lexed = Parse_RARE.lex_rewrites ctxt lines

val parsed = Parse_RARE.parse_rewrites ctxt lexed
val _ = @{print}("after parsing ",map Parse_RARE.str_of parsed)
\<close>

subsubsection \<open> ALF Parser Test \<close>

declare[[IsaRARE_ruleFormat = "ALF"]]

ML \<open>

val file_name = "~/Sources/IsaRARE/Tests/Regression/ParserTest/alf_rewrites"
val file_path = Path.explode file_name
val new_theory_name = "Parsing" ^ ".thy"
val ctxt = Context.the_local_context ()
     
val lines = Bytes.split_lines (Bytes.read file_path)
val lexed = Parse_RARE.lex_rewrites ctxt lines

val parsed = Parse_RARE.parse_rewrites ctxt lexed
val _ = @{print}("after parsing ",map Parse_RARE.str_of parsed)
\<close>


(*
Testing
 :|-- (fn t => fn cs => ((@{print} ("Parse "  ^ ",remaining: " ^ implode cs );(t,cs))))
*)
(*<*)
end
(*>*)