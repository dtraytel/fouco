header {* Distributive law for the sum of 2 *}

(* This is similar to Distributive_Law, but assumes a distributive law \<Lambda>5 over (SpK,\<Sigma>\<Sigma>5,F)
instead of (S,\<Sigma>\<Sigma>5,F): *)

theory Stream_Distributive_Law5
imports Stream_Integrate_New_Op5
begin

(* We assume (S,\<Sigma>\<Sigma>,F)-distributive law, where:
 -- S is the syntactic signature and T is its term extension (free algebra extension)
 -- F is the behavior functor  *)

(*
(* Distributive law: *)
consts \<Lambda>5 :: "('a \<times> 'a F) SpK \<Rightarrow> 'a \<Sigma>\<Sigma>5 F"

axiomatization where
  \<Lambda>5_natural: "\<Lambda>5 o SpKmap (f ** Fmap f) = Fmap (T1_map f) o \<Lambda>5"

*)


end