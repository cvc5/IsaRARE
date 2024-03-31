(*<*)
theory BVTermParser
  imports Parsing "HOL-CVC.SMT_CVC_Word"
begin


ML_file \<open>../src/bv_parser.ML\<close>

(*>*)

text \<open>
RARE specific:

\begin{enumerate}
\item For (bv v n), we check if n is a constant. If so we use it as bit-size. Otherwise, we use a
dummy type. The implicit assumption we added will make sure that Isabelle has to infer the right
type.
\item 
\end{enumerate}



\<close>


end
