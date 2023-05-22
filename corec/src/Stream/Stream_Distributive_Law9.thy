header {* Distributive law for the sum of 2 *}

(* This is similar to Distributive_Law, but assumes a distributive law \<Lambda>9 over (SpK,\<Sigma>\<Sigma>9,F)
instead of (S,\<Sigma>\<Sigma>9,F): *)

theory Stream_Distributive_Law9
imports Stream_Integrate_New_Op9
begin

(* We assume (S,\<Sigma>\<Sigma>,F)-distributive law, where:
 -- S is the syntactic signature and T is its term extension (free algebra extension)
 -- F is the behavior functor  *)

(*
(* Distributive law: *)
consts \<Lambda>9 :: "('a \<times> 'a F) SpK \<Rightarrow> 'a \<Sigma>\<Sigma>9 F"

axiomatization where
  \<Lambda>9_natural: "\<Lambda>9 o SpKmap (f ** Fmap f) = Fmap (T1_map f) o \<Lambda>9"

*)


end