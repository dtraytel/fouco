header {* Distributive law for the sum of 2 *}

(* This is similar to Distributive_Law, but assumes a distributive law \<Lambda>_step over (SpK,\<Sigma>\<Sigma>_step,F)
instead of (S,\<Sigma>\<Sigma>_step,F): *)

theory Distributive_Law_step
imports Integrate_New_Op_step
begin

(* We assume (S,\<Sigma>\<Sigma>,F)-distributive law, where:
 -- S is the syntactic signature and T is its term extension (free algebra extension)
 -- F is the behavior functor  *)

(*
(* Distributive law: *)
consts \<Lambda>_step :: "('a \<times> 'a F) SpK \<Rightarrow> 'a \<Sigma>\<Sigma>_step F"

axiomatization where
  \<Lambda>_step_natural: "\<Lambda>_step o SpKmap (f ** Fmap f) = Fmap (T1_map f) o \<Lambda>_step"

*)


end