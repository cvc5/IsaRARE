theory Core
  imports Main
begin

fun ite:: "bool \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where "ite a B C = (if a then B else C)"

end