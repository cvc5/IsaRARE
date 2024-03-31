(*<*)
theory ImplAss
  imports Parsing
begin


ML_file \<open>../src/rare_impl_assms.ML\<close>

(*>*)

section \<open>Adding Implicit Assumptions\<close>


text \<open>

We never need to add the assumption that the bitwidth is $> 0$ since Isabelle words have the same
assumption. 

This is slightly simplified since we don't know LENGTH('a) yet so we have to use bvsize instead

Notice that we usually would not need to traverse e.g., v in (bv v n) or i in extract. However, we
are not in SMT-LIB2. 

\begin{tabular}{c | c | p{10cm}}
term & translated term & Assumptions needed \\
\hline
  (bv v n) &
  ((Word.word $\bar{v}$)::'a::len word) &
  LENGTH('a) = $\bar{n}$ \newline
  $\bar{v} < {2^{\bar{n}}}$ \\
\hline
  (bvsize n) &
  LENGTH(n::'a::len word) &
  none \\
\end{tabular}

TODO: bvashr non-smtlib

\begin{tabular}{c | c | p{10cm}}
term & translated term & Assumptions needed \\
\hline
  (extract i j t) &
  ((smt\_extract $\bar{i}$ $\bar{j}$ ($\bar{t}$::'a::len word))::'b::len word) &
  $\bar{i} <= LENGTH('a)$ \newline
  $\bar{i} <= \bar{j}$ \newline
  $0 <= \bar{j}$ \newline
  $LENGTH('b) = 1+(\bar{i}-\bar{j})$ \\
\hline
  (bvshl s t) & TODO & none \\
\hline
  (bvshr s t) & TODO & none \\
\hline
  (rotate_left s t) & TODO & none \\
\hline
  (rotate_right s t) & TODO & none \\
\hline
  concat & TODO & TODO \\
\hline
  repeat & TODO & TODO \\

\hline
  (zero_extend t) & TODO & none \\
\hline
  (sign_extend s t) & TODO & none \\


\hline
  (bvnot t) & TODO & none \\
\hline
  (bvand s t) & TODO & none \\
\hline
  (bvor s t) & TODO & none \\
\hline
  (bvnand s t) & TODO & none \\
\hline
  (bvnor s t) & TODO & none \\
\hline
  (bvxor s t) & TODO & none \\
\hline
  (bvxnor s t) & TODO & none \\
\hline
  (bvcomp s t) & TODO & none \\
\hline
  (bvneg s t) & TODO & none \\
\hline
  (bvadd s t) & TODO & none \\
\hline
  (bvmul s t) & TODO & none \\
\hline
  (bvudiv s t) & TODO & none \\
\hline
  (bvurem s t) & TODO & none \\
\hline
  (bvsub s t) & TODO & none \\
\hline
  (bvsdiv s t) & TODO & none \\
\hline
  (bvsrem s t) & TODO & none \\
\hline
  (bvsmod s t) & TODO & none \\
\hline
  (bvult s t) & TODO & none \\
\hline
  (bvule s t) & TODO & none \\
\hline
  (bvugt s t) & TODO & none \\
\hline
  (bvuge s t) & TODO & none \\
\hline
  (bvslt s t) & TODO & none \\
\hline
  (bvsle s t) & TODO & none \\
\hline
  (bvsgt s t) & TODO & none \\
\hline
  (bvsge s t) & TODO & none \\
\hline
  (bvite s t) & TODO & none \\





\end{tabular}




\begin{lstlisting}

fun concat_smt2 :: "(bool list) cvc_ListVar  \<Rightarrow> 'b::len  word" where
  "concat_smt2 (ListVar xss) = (THE x :: 'b::len word. length xss > 0 \<and> list_length_0 xss
 \<and> LENGTH('b) = foldr (+) (map length xss) 0 \<and> x = of_bl (foldr (append) xss []))"

\end{lstlisting}




\<close>

end