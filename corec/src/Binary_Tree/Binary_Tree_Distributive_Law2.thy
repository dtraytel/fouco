header {* Distributive law for the sum of 2 *}

(* This is similar to Distributive_Law, but assumes a distributive law \<Lambda>2 over (SpK,\<Sigma>\<Sigma>2,F)
instead of (S,\<Sigma>\<Sigma>2,F): *)

theory Binary_Tree_Distributive_Law2
imports Binary_Tree_Integrate_New_Op2
begin

(* We assume (S,\<Sigma>\<Sigma>,F)-distributive law, where:
 -- S is the syntactic signature and T is its term extension (free algebra extension)
 -- F is the behavior functor  *)

(*
(* Distributive law: *)
consts \<Lambda>2 :: "('a \<times> 'a F) SpK \<Rightarrow> 'a \<Sigma>\<Sigma>2 F"

axiomatization where
  \<Lambda>2_natural: "\<Lambda>2 o SpKmap (f ** Fmap f) = Fmap (T1_map f) o \<Lambda>2"

*)


end