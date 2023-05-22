header {* Distributive law for the sum of 2 *}

(* This is similar to Distributive_Law, but assumes a distributive law \<Lambda>8 over (SpK,\<Sigma>\<Sigma>8,F)
instead of (S,\<Sigma>\<Sigma>8,F): *)

theory Stream_Distributive_Law8
imports Stream_Integrate_New_Op8
begin

(* We assume (S,\<Sigma>\<Sigma>,F)-distributive law, where:
 -- S is the syntactic signature and T is its term extension (free algebra extension)
 -- F is the behavior functor  *)

(*
(* Distributive law: *)
consts \<Lambda>8 :: "('a \<times> 'a F) SpK \<Rightarrow> 'a \<Sigma>\<Sigma>8 F"

axiomatization where
  \<Lambda>8_natural: "\<Lambda>8 o SpKmap (f ** Fmap f) = Fmap (T1_map f) o \<Lambda>8"

*)


end