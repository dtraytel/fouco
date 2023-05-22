theory Stream_Input1
imports Stream_More_Corec_Upto0
begin

type_synonym 'a K1 = "'a * 'a"
composition_bnf (open) K1: "'a * 'a"
thm K1.set_map
abbreviation "K1_map \<equiv> \<lambda>f. f ** f"
abbreviation "K1_rel \<equiv> \<lambda>R. rel_prod R R"
abbreviation "K1_set \<equiv> \<lambda>x. Basic_BNFs.fsts x \<union> Basic_BNFs.snds x"
abbreviation "bd_K1 \<equiv> natLeq"
type_synonym bd_type_K1 = nat

end
