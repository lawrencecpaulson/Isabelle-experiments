section \<open>Alternative defn of Aleph that's defined on all sets, not just ordinals\<close>

theory ALEPH imports
  "HOL-ex.Sketch_and_Explore" "ZFC_in_HOL.ZFC_Typeclasses"
   
begin

thm inj_on_of_nat
lemma Nats_infinite: "\<not> finite (\<nat> :: 'a::semiring_char_0 set)"
  by (metis Nats_def finite_imageD infinite_UNIV_char_0 inj_on_of_nat)

end
