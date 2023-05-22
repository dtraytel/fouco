theory Tree_Input0
imports "../Prelim"
begin

type_synonym 'a F = "nat * 'a list"
composition_bnf F: "'a F"
type_synonym bd_type_F = nat
abbreviation "F_bd \<equiv> natLeq"

end
