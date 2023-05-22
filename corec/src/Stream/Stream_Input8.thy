theory Stream_Input8
imports Stream_More_Corec_Upto7
begin

type_synonym 'a K8 = "'a * 'a"
composition_bnf (open) K8: "'a * 'a"

abbreviation "K8_map \<equiv> \<lambda>f. f ** f"
abbreviation "K8_rel \<equiv> \<lambda>R. rel_prod R R"
abbreviation "K8_set \<equiv> \<lambda>x. Basic_BNFs.fsts x \<union> Basic_BNFs.snds x"
abbreviation "bd_K8 \<equiv> natLeq"
type_synonym bd_type_K8 = nat

end
