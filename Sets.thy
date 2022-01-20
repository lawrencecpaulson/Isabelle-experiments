section \<open>Set theory experiments\<close>

theory Sets imports
  "ZFC_in_HOL.ZFC_Typeclasses" 
  "HOL-ex.Sketch_and_Explore"
   
begin


lemma "(UNIV :: V set) \<notin> range elts"
  using mem_not_refl by blast

lemma "ON \<notin> range elts"
  using big_ON by fastforce

text \<open>Every small, embeddable HOL type is in bijection with a ZF set. Example, the reals:\<close>
lemma "\<exists>f R. bij_betw f (UNIV::real set) (elts R)"
proof -
  obtain V_of:: "real \<Rightarrow> V" where "inj V_of"
    by (metis ZFC_Typeclasses.embeddable_class.ex_inj)
  moreover
  obtain R where "range (V_of) = elts R"
    by (meson replacement small small_iff)
  ultimately show ?thesis
    by (metis inj_on_imp_bij_betw)
qed


end
