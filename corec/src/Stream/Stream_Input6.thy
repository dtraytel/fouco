theory Stream_Input6
imports Stream_More_Corec_Upto5
begin

type_synonym 'a K6 = "'a * 'a"
composition_bnf (open) K6: "'a * 'a"

abbreviation "K6_map \<equiv> \<lambda>f. f ** f"
abbreviation "K6_rel \<equiv> \<lambda>R. rel_prod R R"
abbreviation "K6_set \<equiv> \<lambda>x. Basic_BNFs.fsts x \<union> Basic_BNFs.snds x"
abbreviation "bd_K6 \<equiv> natLeq"
type_synonym bd_type_K6 = nat

end
