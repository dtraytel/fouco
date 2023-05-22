theory Binary_Tree_Input0
imports "../Prelim"
  Complex_Main
  "~~/src/HOL/Library/BNF_Axiomatization"
begin

type_synonym 'a F = "rat * 'a * 'a"
composition_bnf F: "'a F"
type_synonym bd_type_F = nat
abbreviation "F_bd \<equiv> natLeq"

end
