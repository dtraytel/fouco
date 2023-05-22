theory Stream_Input9
imports Stream_More_Corec_Upto8
begin

type_synonym 'a K9 = "nat * 'a"
composition_bnf (open) K9: "nat * 'a"

abbreviation "K9_map \<equiv> \<lambda>f. id ** f"
abbreviation "K9_rel \<equiv> \<lambda>R. rel_prod op = R"
abbreviation "K9_set \<equiv> \<lambda>x. Basic_BNFs.snds x"
abbreviation "bd_K9 \<equiv> natLeq"
type_synonym bd_type_K9 = nat


end
