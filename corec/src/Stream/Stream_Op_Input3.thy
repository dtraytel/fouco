theory Stream_Op_Input3
imports Stream_FreeAlg3
begin

abbreviation "PLS3 \<equiv> \<oo>\<pp>3 o Abs_\<Sigma>3 o Inl o Abs_\<Sigma>2 o Inl o Abs_\<Sigma>1 o Inr :: 'a \<Sigma>\<Sigma>3 K1 \<Rightarrow> 'a \<Sigma>\<Sigma>3"
abbreviation "PRD3 \<equiv> \<oo>\<pp>3 o Abs_\<Sigma>3 o Inl o Abs_\<Sigma>2 o Inr :: 'a \<Sigma>\<Sigma>3 K2 \<Rightarrow> 'a \<Sigma>\<Sigma>3"
abbreviation "EXP3 \<equiv> \<oo>\<pp>3 o Abs_\<Sigma>3 o Inr :: 'a \<Sigma>\<Sigma>3 K3 \<Rightarrow> 'a \<Sigma>\<Sigma>3"

lemma PLS3_transfer[transfer_rule]:
  "(K1_rel (\<Sigma>\<Sigma>3_rel R) ===> \<Sigma>\<Sigma>3_rel R) PLS3 PLS3"
  by transfer_prover

lemma PRD3_transfer[transfer_rule]:
  "(K2_rel (\<Sigma>\<Sigma>3_rel R) ===> \<Sigma>\<Sigma>3_rel R) PRD3 PRD3"
  by transfer_prover

lemma EXP3_transfer[transfer_rule]:
  "(K3_rel (\<Sigma>\<Sigma>3_rel R) ===> \<Sigma>\<Sigma>3_rel R) EXP3 EXP3"
  by transfer_prover

definition exp :: "nat \<Rightarrow> nat" where "exp n = 2 ^ n"

primrec \<rho>3 :: "('a \<times> 'a F) K3 \<Rightarrow> 'a \<Sigma>\<Sigma>3 F" where
  "\<rho>3 (I a_m_a') =
    (let a = I (fst a_m_a') ; m = fst (snd a_m_a') ; a' = snd (snd a_m_a')
    in (exp m, PRD3 (leaf3 a', K3_as_\<Sigma>\<Sigma>3 a)))"

lemma I_transfer[transfer_rule]:
  "(R ===> K3_rel R) I I"
  by auto

lemma rec_K3_transfer[transfer_rule]: "((R ===> S) ===> K3_rel R ===> S) rec_K3 rec_K3"
  apply (rule rel_funI)+
  apply (rename_tac x y)
  apply (case_tac x)
  apply (case_tac y)
  apply (auto elim: rel_funE)
  done

lemma \<rho>3_transfer[transfer_rule]:
  "(K3_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>3_rel R)) \<rho>3 \<rho>3"
  unfolding rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def \<rho>3_def[abs_def] Let_def
  by transfer_prover



end