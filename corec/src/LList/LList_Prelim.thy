header{* Preliminaries *}

theory LList_Prelim
imports LList_Incremental
  "~~/src/HOL/Library/Lattice_Syntax"
  "~~/src/HOL/Library/Cardinal_Notations"
keywords "composition_bnf" :: thy_decl
begin

notation BNF_Def.convol ("<_ , _>")

declare [[bnf_note_all]]

subsection{* Preliminaries *}

interpretation lifting_syntax .

lemma map_sum_transfer[transfer_rule]:
  "((R ===> T) ===> (S ===> U) ===> rel_sum R S ===> rel_sum T U) map_sum map_sum"
  unfolding rel_fun_def rel_sum_def by (auto split: sum.splits)

lemma convol_transfer[transfer_rule]:
  "((R ===> S) ===> (R ===> T) ===> R ===> rel_prod S T) BNF_Def.convol BNF_Def.convol"
  unfolding rel_prod_def rel_fun_def convol_def by auto

lemma id_bnf_comp_transfer[transfer_rule]:
  "(R ===> R) BNF_Comp.id_bnf_comp BNF_Comp.id_bnf_comp"
  unfolding BNF_Comp.id_bnf_comp_def rel_fun_def by blast



lemma Grp_transfer[transfer_rule]: "\<lbrakk>bi_unique R; bi_unique S\<rbrakk> \<Longrightarrow>
  (rel_set R ===> (R ===> S) ===> R ===> S ===> op =) BNF_Def.Grp BNF_Def.Grp"
  unfolding Grp_def[abs_def] rel_set_def rel_fun_def bi_unique_def by metis

lemma conversep_tansfer[transfer_rule]:
  "((A ===> B ===> op =) ===> B ===> A ===> op =) conversep conversep"
  unfolding rel_fun_def conversep.simps bi_total_def by metis

lemma relcompp_tansfer[transfer_rule]: "bi_total B \<Longrightarrow>
  ((A ===> B ===> op =) ===> (B ===> C ===> op =) ===> A ===> C ===> op =) op OO op OO"
  unfolding rel_fun_def relcompp.simps bi_total_def by metis

ML {*
fun composition_bnf (inline_opt, (b, str)) lthy =
  let
    val T = Syntax.read_typ lthy str;
    fun qualify b' = if length (Binding.dest b' |> #2) <= 2 then b
      else Binding.qualify true (Binding.name_of b) b';
    val inline = (case inline_opt of true => BNF_Def.Dont_Inline | _ => BNF_Def.Do_Inline);
    val ((bnf, (_, _)), (_, lthy')) =
      BNF_Comp.bnf_of_typ inline qualify (distinct op = o flat) [] [] T
        ((BNF_Comp.empty_comp_cache, BNF_Comp.empty_unfolds), lthy)
  in
    BNF_Def.note_bnf_thms BNF_Def.Note_All I b bnf lthy' |> snd
  end;

val _ =
  Outer_Syntax.local_theory @{command_spec "composition_bnf"} "define BNF by composition"
    ((Parse.opt_keyword "open" >> not) --
      (BNF_Util.parse_binding_colon -- Parse.typ) >> composition_bnf);
*}

(* Products: *)
abbreviation map_prod_abbr (infix "**" 80) where "f ** g \<equiv> map_prod f g"

lemma fst_o_Pair: "fst o (\<lambda> a. Pair a b) = id"
by (rule ext, auto)

lemma snd_o_Pair: "snd o Pair a = id"
by (rule ext, auto)

lemma fst_snd_cong:
assumes "fst o f = fst o g" and "snd o f = snd o g"
shows "f = g"
using assms unfolding comp_def fun_eq_iff
by (metis (lifting) prod_eqI)

declare fst_convol[simp]   declare snd_convol[simp]

lemma convol_comp[simp]: "<f1 o g, f2 o g> = <f1,f2> o g"
unfolding comp_def fun_eq_iff
by (metis fst_convol o_def snd_convol surjective_pairing)

lemma convol_comp_id1[simp]: "<g, f2 o g> = <id,f2> o g"
using convol_comp[of id] by simp

lemma convol_comp_id2[simp]: "<f1 o g, g> = <f1,id> o g"
using convol_comp[of _ _ id] by simp

(* Sums: *)
lemma map_sum_Inl[simp]:
"map_sum f1 f2 \<circ> Inl = Inl o f1"
unfolding map_sum_def comp_def by (rule ext) auto

lemma map_sum_Inr[simp]:
"map_sum f1 f2 \<circ> Inr = Inr o f2"
unfolding map_sum_def comp_def by (rule ext) auto

lemma sum_comp_cases:
assumes "f o Inl = g o Inl" and "f o Inr = g o Inr"
shows "f = g"
proof(rule ext)
  fix a show "f a = g a"
  using assms unfolding comp_def fun_eq_iff by (cases a) auto
qed

lemma eq_o_InrI: "\<lbrakk>g o Inl = h; case_sum h f = g\<rbrakk> \<Longrightarrow> f = g o Inr"
  by (auto simp: fun_eq_iff split: sum.splits)

lemma case_sum_comp[simp]:
"case_sum (h o f1) (h o f2) = h o case_sum f1 f2"
apply (rule ext) by (case_tac x, auto)

lemma case_sum_Inl_Inr[simp]:
"case_sum (Inl o f1) (Inr o f2) = map_sum f1 f2"
unfolding map_sum_def apply (rule ext) by (case_tac x, auto)

lemma case_sum_Inl_Inr1[simp]:
"case_sum Inl (Inr o f) = map_sum id f"
unfolding map_sum_def apply (rule ext) by (case_tac x, auto)

lemma case_sum_Inl_Inr2[simp]:
"case_sum (Inl o f) Inr = map_sum f id"
unfolding map_sum_def apply (rule ext) by (case_tac x, auto)

lemma case_sum_triv[simp]: "case_sum Inl Inr = id"
unfolding map_sum_def apply (rule ext) by (case_tac x, auto)

lemma case_sum_Inl_Inr_L[simp]: "case_sum (f o Inl) (f o Inr) = f"
by (metis case_sum_expand_Inr')

lemma symp_iff: "symp R \<longleftrightarrow> R = R^--1"
  by (metis antisym conversep.cases conversep_le_swap predicate2I symp_def)

lemma transp_iff: "transp R \<longleftrightarrow> R OO R \<le> R"
  by (metis predicate2D relcompp.relcompI transpI transp_relcompp_less_eq)

lemma equivp_inf: "\<lbrakk>equivp R; equivp S\<rbrakk> \<Longrightarrow> equivp (R \<sqinter> S)"
  unfolding equivp_def inf_fun_def inf_bool_def by metis

lemma vimage2p_rel_prod: "BNF_Def.vimage2p (<f1, g1>) (<f2, g2>) (rel_prod R S) =
  BNF_Def.vimage2p f1 f2 R \<sqinter> BNF_Def.vimage2p g1 g2 S"
  unfolding vimage2p_def rel_prod_def convol_def by auto

end