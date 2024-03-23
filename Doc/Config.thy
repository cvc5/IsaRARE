(*<*)
theory Config
  imports Manual
begin
(*>*)

section \<open>Config\<close>

text \<open>
For an explanation of what the options do please consult the user manual. Here we describe how a
developer can add a new option to IsaRARE.

All config functionalities can be found in \path{src/config}.
\<close>

ML_file \<open>../src/isarare_config.ML\<close>


subsection \<open>Adding a proof strategy or proof strategy theory \<close>


text \<open>

To add a new strategy extend one of these datatypes:

@{ML_text "
  datatype proof_strategy = None | Minimum | Full | TACAS_Autoprove 
  datatype proof_strategy_theory = All | Strings | Arith | BV
"}

Then, add a tuple to @{ML_text "str_to_proof_strategy"}, where the first entry is the
string your option should be printed at and the second is the option itself.

All done! You can now use your option and set it like you would set any of the other ones with:

@{verbatim "declare[[IsaRARE_proofStrategy = \"Minimum\"]]"}

Access the value for the strategy in ML for a given Context ctxt (that is where the "current" state
of the option is set, in this case the one where parse\_smt is called in) by writing:

@{ML_text "IsaRARE_Config.getStrategy ctxt"}. 

you can then compare if the strategy is set to your new option by comparing this to it directly.

@{ML_text "IsaRARE_Config.getStrategy ctxt = IsaRARE_Config.Minimum"}. 

\<close>

subsection \<open>Adding a new option \<close>

text \<open>

To create a new option choose which type the option should have. In this example,
it is a boolean so we are creating a flag:

@{ML_text
"val verbose = Attrib.setup_config_bool \<^binding>\<open>IsaRARE_verbose\<close> (K false)"
}

\path{$ISABELLE_HOME/src/Pure/Isar/attrib.ML} has some more types to choose from.
You have to set the default value. In this case the variable is always false by default but
for a string you could choose the empty string etc.

Now you can set your option with

@{verbatim "declare[[IsaRARE_verbose = true]]"}

and check its value with

@{ML_text "(Config.get ctxt verbose)"}
\<close>

(*<*)
end
(*>*)