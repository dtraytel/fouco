header {* Distributive law for the sum of 2 *}

(* This is similar to Distributive_Law, but assumes a distributive law \<Lambda>1 over (SpK,\<Sigma>\<Sigma>1,F)
instead of (S,\<Sigma>\<Sigma>1,F): *)

theory Stream_Distributive_Law1
imports Stream_Integrate_New_Op1
begin

(* We assume (S,\<Sigma>\<Sigma>,F)-distributive law, where:
 -- S is the syntactic signature and T is its term extension (free algebra extension)
 -- F is the behavior functor  *)

(*
(* Distributive law: *)
consts \<Lambda>1 :: "('a \<times> 'a F) SpK \<Rightarrow> 'a \<Sigma>\<Sigma>1 F"

axiomatization where
  \<Lambda>1_natural: "\<Lambda>1 o SpKmap (f ** Fmap f) = Fmap (T1_map f) o \<Lambda>1"

*)


end