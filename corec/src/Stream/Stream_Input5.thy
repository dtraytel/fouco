theory Stream_Input5
imports Stream_More_Corec_Upto4
begin

type_synonym 'a K5 = "'a * 'a"
composition_bnf (open) K5: "'a * 'a"

abbreviation "K5_map \<equiv> \<lambda>f. f ** f"
abbreviation "K5_rel \<equiv> \<lambda>R. rel_prod R R"
abbreviation "K5_set \<equiv> \<lambda>x. Basic_BNFs.fsts x \<union> Basic_BNFs.snds x"
abbreviation "bd_K5 \<equiv> natLeq"
type_synonym bd_type_K5 = nat

end
