theory Stream_Op_Input4
imports Stream_FreeAlg4
begin

abbreviation "PLS4 \<equiv> \<oo>\<pp>4 o Abs_\<Sigma>4 o Inl o Abs_\<Sigma>3 o Inl o Abs_\<Sigma>2 o Inl o Abs_\<Sigma>1 o Inr :: 'a \<Sigma>\<Sigma>4 K1 \<Rightarrow> 'a \<Sigma>\<Sigma>4"
abbreviation "PRD4 \<equiv> \<oo>\<pp>4 o Abs_\<Sigma>4 o Inl o Abs_\<Sigma>3 o Inl o Abs_\<Sigma>2 o Inr :: 'a \<Sigma>\<Sigma>4 K2 \<Rightarrow> 'a \<Sigma>\<Sigma>4"
abbreviation "EXP4 \<equiv> \<oo>\<pp>4 o Abs_\<Sigma>4 o Inl o Abs_\<Sigma>3 o Inr :: 'a \<Sigma>\<Sigma>4 K3 \<Rightarrow> 'a \<Sigma>\<Sigma>4"
abbreviation "SUP4 \<equiv> \<oo>\<pp>4 o Abs_\<Sigma>4 o Inr :: 'a \<Sigma>\<Sigma>4 K4 \<Rightarrow> 'a \<Sigma>\<Sigma>4"

lemma PLS4_transfer[transfer_rule]:
  "(K1_rel (\<Sigma>\<Sigma>4_rel R) ===> \<Sigma>\<Sigma>4_rel R) PLS4 PLS4"
  by transfer_prover

lemma PRD4_transfer[transfer_rule]:
  "(K2_rel (\<Sigma>\<Sigma>4_rel R) ===> \<Sigma>\<Sigma>4_rel R) PRD4 PRD4"
  by transfer_prover

lemma EXP4_transfer[transfer_rule]:
  "(K3_rel (\<Sigma>\<Sigma>4_rel R) ===> \<Sigma>\<Sigma>4_rel R) EXP4 EXP4"
  by transfer_prover

lemma SUP4_transfer[transfer_rule]:
  "(K4_rel (\<Sigma>\<Sigma>4_rel R) ===> \<Sigma>\<Sigma>4_rel R) SUP4 SUP4"
  by transfer_prover

definition fMax where
  "fMax F = (if F = {||} then 0 :: nat else Max (fset F))"

definition \<rho>4 :: "('a \<times> 'a F) K4 \<Rightarrow> 'a \<Sigma>\<Sigma>4 F" where
  "\<rho>4 F = (fMax ((fst o snd) |`| F), K4_as_\<Sigma>\<Sigma>4 ((snd o snd) |`| F))"
 
lemma \<rho>4_transfer[transfer_rule]:
  "(K4_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>4_rel R)) \<rho>4 \<rho>4"
  unfolding rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def \<rho>4_def[abs_def]
  by transfer_prover

end