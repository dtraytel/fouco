theory Stream_Op_Input9
imports Stream_FreeAlg9
begin

abbreviation "MERGE9 \<equiv> \<oo>\<pp>9 o Abs_\<Sigma>9 o Inl o Abs_\<Sigma>8 o Inr :: 'a \<Sigma>\<Sigma>9 K8 \<Rightarrow> 'a \<Sigma>\<Sigma>9"
abbreviation "TIMES9 \<equiv> \<oo>\<pp>9 o Abs_\<Sigma>9 o Inr :: 'a \<Sigma>\<Sigma>9 K9 \<Rightarrow> 'a \<Sigma>\<Sigma>9"

lemma PRD9_transfer[transfer_rule]:
  "(K9_rel (\<Sigma>\<Sigma>9_rel R) ===> \<Sigma>\<Sigma>9_rel R) TIMES9 TIMES9"
  by transfer_prover

definition \<rho>9 :: "('a \<times> 'a F) K9 \<Rightarrow> 'a \<Sigma>\<Sigma>9 F" where
  "\<rho>9 m_b_n_b' =
    (let m = fst m_b_n_b' ; b_n_b' = snd m_b_n_b' ;
      b = fst b_n_b' ; n = fst (snd b_n_b') ; b' = snd (snd b_n_b')
    in (m * n, TIMES9 (m, leaf9 b')))"

lemma \<rho>9_transfer[transfer_rule]:
  "(K9_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>9_rel R)) \<rho>9 \<rho>9"
  unfolding Let_def \<rho>9_def[abs_def] rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def
  by transfer_prover

end