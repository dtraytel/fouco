theory Tree_Lib
imports "../Tree/Tree_Behavior_BNF" "../Tree/Tree_More_Corec_Upto2"
begin

(* todo: make them defs eventually: *)
type_synonym tree = J
abbreviation "val xs \<equiv> fst (dtor_J xs)"
abbreviation "sub xs \<equiv> snd (dtor_J xs)"
abbreviation "Node n ts \<equiv> ctor_J (n, ts)"
code_datatype ctor_J
declare J.dtor_ctor[code]

definition tmap where
  "tmap f = corec_J (\<lambda>xs. (f (val xs), map Inr (sub xs)))"

lemma head_tmap[simp]: "val (tmap f xs) = f (val xs)"
  unfolding tmap_def corec_J_def J.dtor_corec BNF_Comp.id_bnf_comp_def map_pre_J_def by simp

lemma tail_tmap[simp]: "sub (tmap f xs) = map (tmap f) (sub xs)"
  unfolding tmap_def corec_J_def J.dtor_corec BNF_Comp.id_bnf_comp_def map_pre_J_def by simp

lemma tmap_code[code]: "tmap f xs = Node (f (val xs)) (map (tmap f) (sub xs))"
  by (metis J.ctor_dtor prod.collapse head_tmap tail_tmap)

section {* Abbreviations *}
          
abbreviation "NODE0 \<equiv> gg0  :: 'a \<Sigma>\<Sigma>0 F \<Rightarrow> 'a \<Sigma>\<Sigma>0"
abbreviation "LEAF0 \<equiv> leaf0"
abbreviation GUARD0 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>0" where "GUARD0 \<equiv> LEAF0"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END0 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>0" where "END0 xs \<equiv> LEAF0 (Inl xs)"
abbreviation CONT0 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>0" where "CONT0 a \<equiv> LEAF0 (Inr a)"

abbreviation "NODE1 \<equiv> gg1  :: 'a \<Sigma>\<Sigma>1 F \<Rightarrow> 'a \<Sigma>\<Sigma>1"
abbreviation "LEAF1 \<equiv> leaf1"
abbreviation GUARD1 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>1" where "GUARD1 \<equiv> LEAF1"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END1 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>1" where "END1 xs \<equiv> LEAF1 (Inl xs)"
abbreviation CONT1 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>1" where "CONT1 a \<equiv> LEAF1 (Inr a)"

abbreviation "NODE2 \<equiv> gg2  :: 'a \<Sigma>\<Sigma>2 F \<Rightarrow> 'a \<Sigma>\<Sigma>2"
abbreviation "LEAF2 \<equiv> leaf2"
abbreviation GUARD2 :: "'a F \<Rightarrow> 'a F \<Sigma>\<Sigma>2" where "GUARD2 \<equiv> LEAF2"
(* local ("inside") end and continuation: within the upto-corecursive definition of a function f,
END immediately an element of J, while CONT calls f corecursively  *)
abbreviation END2 :: "J \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>2" where "END2 xs \<equiv> LEAF2 (Inl xs)"
abbreviation CONT2 :: "'a \<Rightarrow> (J + 'a) \<Sigma>\<Sigma>2" where "CONT2 a \<equiv> LEAF2 (Inr a)"

end