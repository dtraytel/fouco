theory Binary_Tree_Input2
imports Binary_Tree_More_Corec_Upto1
begin

type_synonym 'a K2 = "'a * 'a"
composition_bnf (open) K2: "'a * 'a"

abbreviation "K2_map \<equiv> \<lambda>f. f ** f"
abbreviation "K2_rel \<equiv> \<lambda>R. rel_prod R R"
abbreviation "K2_set \<equiv> \<lambda>x. Basic_BNFs.fsts x \<union> Basic_BNFs.snds x"
abbreviation "bd_K2 \<equiv> natLeq"
type_synonym bd_type_K2 = nat

end
