theory Stream_Input4
imports Stream_More_Corec_Upto3 "~~/src/HOL/Library/FSet"
begin

type_synonym 'a K4 = "'a fset"
composition_bnf (open) K4: "'a K4"

abbreviation (input) "K4_map \<equiv> fimage"
abbreviation (input) "K4_rel \<equiv> rel_fset"
abbreviation (input) "K4_set \<equiv> fset"
abbreviation "bd_K4 \<equiv> natLeq"
type_synonym bd_type_K4 = nat

end
