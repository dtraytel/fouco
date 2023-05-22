theory Stream_Op_Input7
imports Stream_FreeAlg7
begin

abbreviation "INTERLEAVE7 \<equiv> \<oo>\<pp>7 o Abs_\<Sigma>7 o Inl o Abs_\<Sigma>6 o Inr :: 'a \<Sigma>\<Sigma>7 K6 \<Rightarrow> 'a \<Sigma>\<Sigma>7"
abbreviation "INV7 \<equiv> \<oo>\<pp>7 o Abs_\<Sigma>7 o Inr :: 'a \<Sigma>\<Sigma>7 K7 \<Rightarrow> 'a \<Sigma>\<Sigma>7"

lemma INTERLEAVE7_transfer[transfer_rule]:
  "(K6_rel (\<Sigma>\<Sigma>7_rel R) ===> \<Sigma>\<Sigma>7_rel R) INTERLEAVE7 INTERLEAVE7"
  by transfer_prover

lemma EXP7_transfer[transfer_rule]:
  "(K7_rel (\<Sigma>\<Sigma>7_rel R) ===> \<Sigma>\<Sigma>7_rel R) INV7 INV7"
  by transfer_prover

primrec \<rho>7 :: "('a \<times> 'a F) K7 \<Rightarrow> 'a \<Sigma>\<Sigma>7 F" where
  "\<rho>7 (I a_m_a') =
    (let a = I (fst a_m_a') ; m = fst (snd a_m_a') ; a' = (snd (snd a_m_a'))
    in (1 - m, INV7 (I (leaf7 a'))))"

lemma I_transfer[transfer_rule]:
  "(R ===> K7_rel R) I I"
  by auto

lemma rec_K7_transfer[transfer_rule]: "((R ===> S) ===> K7_rel R ===> S) rec_K7 rec_K7"
  apply (rule rel_funI)+
  apply (rename_tac x y)
  apply (case_tac x)
  apply (case_tac y)
  apply (auto elim: rel_funE)
  done

lemma \<rho>7_transfer[transfer_rule]:
  "(K7_rel (rel_prod R (F_rel R)) ===> F_rel (\<Sigma>\<Sigma>7_rel R)) \<rho>7 \<rho>7"
  unfolding rel_pre_J_def id_apply vimage2p_def BNF_Comp.id_bnf_comp_def \<rho>7_def[abs_def] Let_def
  by transfer_prover



end