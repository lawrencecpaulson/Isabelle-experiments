section \<open>Set theory experiments\<close>

theory Sets imports "ZFC_in_HOL.ZFC_Typeclasses" "HOL-Complex_Analysis.Complex_Analysis" 
  "HOL-ex.Sketch_and_Explore"
   
begin

thm real_non_denum
theorem complex_non_denum: "\<nexists>f :: nat \<Rightarrow> complex. surj f"
  by (metis (full_types) Re_complex_of_real comp_surj real_non_denum surj_def)

lemma uncountable_UNIV_complex: "uncountable (UNIV :: complex set)"
  using complex_non_denum unfolding uncountable_def by auto

lemma "(UNIV :: V set) \<notin> range elts"
  using mem_not_refl by blast

lemma "ON \<notin> range elts"
  using big_ON by fastforce

definition V_of :: "'a::embeddable \<Rightarrow> V"
  where "V_of \<equiv> SOME f. inj f"

lemma inj_V_of: "inj V_of"
  unfolding V_of_def by (metis embeddable_class.ex_inj some_eq_imp)

declare inv_f_f [OF inj_V_of, simp]

lemma infinite_V_of: "infinite (UNIV::'a set) \<Longrightarrow> infinite (range (V_of::'a::embeddable\<Rightarrow>V))"
  using finite_imageD inj_V_of by blast

lemma countable_V_of: "countable (range (V_of::'a::countable\<Rightarrow>V))"
  by blast

definition "Real_set \<equiv> ZFC_in_HOL.set (range (V_of::real\<Rightarrow>V))"
    
lemma V_of_real: "bij_betw V_of (UNIV::real set) (range (V_of::real\<Rightarrow>V))"
  by (metis V_of_def embeddable_class.ex_inj inj_on_imp_bij_betw someI_ex)

lemma V_of_Real_set: "bij_betw V_of (UNIV::real set) (elts Real_set)"
  by (simp add: Real_set_def V_of_real)

lemma infinite_Real_set: "infinite (elts Real_set)"
  using V_of_Real_set bij_betw_finite infinite_UNIV_char_0 by blast

lemma uncountable_Real_set: "uncountable (elts Real_set)"
  using V_of_Real_set countable_iff_bij uncountable_UNIV_real by blast

definition "Complex_set \<equiv> ZFC_in_HOL.set (range (V_of::complex\<Rightarrow>V))"
    
lemma V_of_complex: "bij_betw V_of (UNIV::complex set) (range (V_of::complex\<Rightarrow>V))"
  by (metis V_of_def embeddable_class.ex_inj inj_on_imp_bij_betw someI_ex)

lemma V_of_Complex_set: "bij_betw V_of (UNIV::complex set) (elts Complex_set)"
  by (simp add: Complex_set_def V_of_complex)

lemma uncountable_Complex_set: "uncountable (elts Complex_set)"
  using V_of_Complex_set countableI_bij2 uncountable_UNIV_complex by blast

lemma infinite_Complex_set: "infinite (elts Complex_set)"
  by (simp add: uncountable_Complex_set uncountable_infinite)

definition "C_Continuum \<equiv> vcard Real_set"

lemma Complex_vcard: "C_Continuum = vcard Complex_set"
proof -
  define emb1 where "emb1 \<equiv> V_of o complex_of_real o inv V_of"
  have "elts Real_set \<approx> elts Complex_set"
  proof (rule lepoll_antisym)
    show "elts Real_set \<lesssim> elts Complex_set"
      unfolding lepoll_def
    proof (intro conjI exI)
      show "inj_on emb1 (elts Real_set)"
        unfolding emb1_def Real_set_def
        by (simp add: inj_V_of inj_compose inj_of_real inj_on_imageI)
      show "emb1 ` elts Real_set \<subseteq> elts Complex_set"
        by (simp add: emb1_def Real_set_def Complex_set_def image_subset_iff)
    qed
  define emb2 where "emb2 \<equiv> (\<lambda>z. (V_of (Re z), V_of (Im z))) o inv V_of"
    have "elts Complex_set \<lesssim> elts Real_set \<times> elts Real_set"
      unfolding lepoll_def
    proof (intro conjI exI)
      show "inj_on emb2 (elts Complex_set)"
        unfolding emb2_def Complex_set_def inj_on_def
        by (simp add: complex.expand inj_V_of inj_eq)
      show "emb2 ` elts Complex_set \<subseteq> elts Real_set \<times> elts Real_set"
        by (simp add: emb2_def Real_set_def Complex_set_def image_subset_iff)
    qed
    also have "...  \<approx> elts Real_set"
      by (metis infinite_Real_set infinite_times_eqpoll_self)
    finally show "elts Complex_set \<lesssim> elts Real_set" .
  qed
  then show ?thesis
    by (simp add: C_Continuum_def cardinal_cong)
qed

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
