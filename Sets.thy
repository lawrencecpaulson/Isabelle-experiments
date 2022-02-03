section \<open>Set theory experiments\<close>

theory Sets imports "ZFC_in_HOL.ZFC_Typeclasses" "HOL-Complex_Analysis.Complex_Analysis" 
  "HOL-ex.Sketch_and_Explore"
   
begin

subsection \<open>For the libraries\<close>

thm real_non_denum
theorem complex_non_denum: "\<nexists>f :: nat \<Rightarrow> complex. surj f"
  by (metis (full_types) Re_complex_of_real comp_surj real_non_denum surj_def)

lemma uncountable_UNIV_complex: "uncountable (UNIV :: complex set)"
  using complex_non_denum unfolding uncountable_def by auto

thm countable_iff_le_Aleph0
lemma finite_iff_less_Aleph0: "finite (elts x) \<longleftrightarrow> vcard x < \<omega>"
proof
  show "finite (elts x) \<Longrightarrow> vcard x < \<omega>"
    by (metis Card_\<omega> Card_def finite_lesspoll_infinite infinite_\<omega> lesspoll_imp_Card_less)
  show "vcard x < \<omega> \<Longrightarrow> finite (elts x)"
    by (meson Ord_\<omega> Ord_cardinal Ord_mem_iff_lt cardinal_eqpoll eqpoll_finite_iff finite_Ord_omega)
qed

lemma countable_infinite_vcard: "countable (elts x) \<and> infinite (elts x) \<longleftrightarrow> vcard x = \<aleph>0"
  by (metis Aleph_0 countable_iff_le_Aleph0 dual_order.refl finite_iff_less_Aleph0 less_V_def)

lemma vcard_set_image: "inj_on f (elts x) \<Longrightarrow> vcard (ZFC_in_HOL.set (f ` elts x)) = vcard x"
  by (simp add: cardinal_cong)

lemma subset_smaller_vcard:
  assumes "\<kappa> \<le> vcard x" "Card \<kappa>"
  obtains y where "y \<le> x" "vcard y = \<kappa>"
proof -
  obtain \<phi> where \<phi>: "bij_betw \<phi> (elts (vcard x)) (elts x)"
    using cardinal_eqpoll eqpoll_def by blast
  show thesis
  proof
    let ?y = "ZFC_in_HOL.set (\<phi> ` elts \<kappa>)"
    show "?y \<le> x"
      by (meson \<phi> assms bij_betwE set_image_le_iff small_elts vsubsetD) 
    show "vcard ?y = \<kappa>"
      by (metis vcard_set_image Card_def assms bij_betw_def bij_betw_subset \<phi> less_eq_V_def)
  qed
qed

thm Card_lt_csucc_iff
lemma csucc_le_Card_iff: "\<lbrakk>Card \<kappa>'; Card \<kappa>\<rbrakk> \<Longrightarrow> csucc \<kappa>' \<le> \<kappa> \<longleftrightarrow> \<kappa>' < \<kappa>"
  by (metis Card_csucc Card_is_Ord Card_lt_csucc_iff Ord_not_le)

subsection \<open>Making the embedding explicit (possibly add to the AFP entry?\<close>

definition V_of :: "'a::embeddable \<Rightarrow> V"
  where "V_of \<equiv> SOME f. inj f"

lemma inj_V_of: "inj V_of"
  unfolding V_of_def by (metis embeddable_class.ex_inj some_eq_imp)

declare inv_f_f [OF inj_V_of, simp]

lemma inv_V_of_image_eq [simp]: "inv V_of ` (V_of ` X) = X"
  by (auto simp: image_comp)

lemma infinite_V_of: "infinite (UNIV::'a set) \<Longrightarrow> infinite (range (V_of::'a::embeddable\<Rightarrow>V))"
  using finite_imageD inj_V_of by blast

lemma countable_V_of: "countable (range (V_of::'a::countable\<Rightarrow>V))"
  by blast

lemma elts_set_V_of: "small X \<Longrightarrow> elts (ZFC_in_HOL.set (V_of ` X)) \<approx> X"
  by (metis inj_V_of inj_eq inj_on_def inj_on_image_eqpoll_self replacement set_of_elts small_iff)

subsection \<open>The cardinality of the continuum\<close>

definition "Real_set \<equiv> ZFC_in_HOL.set (range (V_of::real\<Rightarrow>V))"
definition "Complex_set \<equiv> ZFC_in_HOL.set (range (V_of::complex\<Rightarrow>V))"
definition "C_continuum \<equiv> vcard Real_set"

lemma V_of_Real_set: "bij_betw V_of (UNIV::real set) (elts Real_set)"
  by (simp add: Real_set_def bij_betw_def inj_V_of)

lemma uncountable_Real_set: "uncountable (elts Real_set)"
  using V_of_Real_set countable_iff_bij uncountable_UNIV_real by blast
    
lemma V_of_Complex_set: "bij_betw V_of (UNIV::complex set) (elts Complex_set)"
  by (simp add: Complex_set_def bij_betw_def inj_V_of)

lemma uncountable_Complex_set: "uncountable (elts Complex_set)"
  using V_of_Complex_set countableI_bij2 uncountable_UNIV_complex by blast

lemma Complex_vcard: "C_continuum = vcard Complex_set"
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
      by (simp add: infinite_times_eqpoll_self uncountable_Real_set uncountable_infinite)
    finally show "elts Complex_set \<lesssim> elts Real_set" .
  qed
  then show ?thesis
    by (simp add: C_continuum_def cardinal_cong)
qed

subsection \<open>Cardinality of an arbitrary HOL set\<close>

definition gcard :: "'a::embeddable set \<Rightarrow> V" 
  where "gcard X \<equiv> vcard (ZFC_in_HOL.set (V_of ` X))"

lemma Card_gcard [iff]: "Card (gcard X)"
  by (simp add: Card_def gcard_def)

lemma gcard_eq_vcard [simp]: "gcard (elts x) = vcard x"
  by (metis cardinal_cong elts_set_V_of gcard_def small_elts)

lemma gcard_eqpoll: "small X \<Longrightarrow> elts (gcard X) \<approx> X"
  by (metis cardinal_eqpoll elts_set_V_of eqpoll_trans gcard_def)

lemma countable_iff_g_le_Aleph0: "small X \<Longrightarrow> countable X \<longleftrightarrow> gcard X \<le> \<aleph>0"
  by (metis inv_V_of_image_eq countable_iff_le_Aleph0 countable_image elts_of_set gcard_def replacement)

lemma countable_imp_g_le_Aleph0: "countable X \<Longrightarrow> gcard X \<le> \<aleph>0"
  by (meson countable countable_iff_g_le_Aleph0)

lemma finite_iff_g_le_Aleph0: "small X \<Longrightarrow> finite X \<longleftrightarrow> gcard X < \<aleph>0"
  by (metis Aleph_0 elts_set_V_of eqpoll_finite_iff finite_iff_less_Aleph0 gcard_def)

lemma finite_imp_g_le_Aleph0: "finite X \<Longrightarrow> gcard X < \<aleph>0"
  by (meson finite_iff_g_le_Aleph0 finite_imp_small)

lemma countable_infinite_gcard: "countable X \<and> infinite X \<longleftrightarrow> gcard X = \<aleph>0"
proof -
  have "gcard X = \<omega>"
    if "countable X" and "infinite X"
    using that countable countable_imp_g_le_Aleph0 finite_iff_g_le_Aleph0 less_V_def by auto
  moreover have "countable X" if "gcard X = \<omega>"
    by (metis Aleph_0 inv_V_of_image_eq countable_image countable_infinite_vcard elts_of_set finite.emptyI gcard_def that)
  moreover have False if "gcard X = \<omega>" and "finite X"
    by (metis Aleph_0 dual_order.irrefl finite_iff_g_le_Aleph0 finite_imp_small that)
  ultimately show ?thesis
    by auto
qed

lemma uncountable_gcard: "small X \<Longrightarrow> uncountable X \<longleftrightarrow> gcard X > \<aleph>0"
  by (simp add: Ord_not_le countable_iff_g_le_Aleph0 gcard_def)

lemma uncountable_gcard_ge: "small X \<Longrightarrow> uncountable X \<longleftrightarrow> gcard X \<ge> \<aleph>1"
  by (simp add: uncountable_gcard csucc_le_Card_iff one_V_def)

lemma subset_smaller_gcard:
  assumes \<kappa>: "\<kappa> \<le> gcard X" "Card \<kappa>" and "small X"
  obtains Y where "Y \<subseteq> X" "gcard Y = \<kappa>"
  using subset_smaller_vcard [OF \<kappa> [unfolded gcard_def]]
  by (metis \<open>small X\<close> elts_of_set gcard_def less_eq_V_def replacement set_of_elts subset_imageE)

lemma lepoll_imp_gcard_le:
  assumes "Y \<subseteq> X" "small X" shows "gcard Y \<le> gcard X"
  unfolding gcard_def
  by (metis assms elts_of_set image_mono lepoll_imp_Card_le replacement smaller_than_small subset_imp_lepoll)

lemma V_of_image_times: "V_of ` (X \<times> Y) \<approx> (V_of ` X) \<times> (V_of ` Y)"
proof -
  have "V_of ` (X \<times> Y) \<approx> X \<times> Y"
    by (meson inj_V_of inj_eq inj_onI inj_on_image_eqpoll_self)
  also have "... \<approx> (V_of ` X) \<times> (V_of ` Y)"
    by (metis eqpoll_sym inj_V_of inj_eq inj_onI inj_on_image_eqpoll_self times_eqpoll_cong)
  finally show ?thesis .
qed

lemma G: 
  assumes "small X" "small Y" 
  shows "gcard (X \<times> Y) = gcard X \<otimes> gcard Y"
  using assms
  apply (simp add: gcard_def)
  using V_of_image_times [of X Y]
sledgehammer [isar_proofs, timeout = 77]
  sorry


subsection \<open>Wetzel's property\<close>

definition Wetzel :: "(complex \<Rightarrow> complex) set \<Rightarrow> bool"
  where "Wetzel \<equiv> \<lambda>F. (\<forall>f\<in>V_of_image_times. f analytic_on UNIV) \<and> (\<forall>z. countable((\<lambda>f. f z) ` V_of_image_times))"

proposition Erdos_Wetzel_nonCH:
  assumes W: "Wetzel V_of_image_times" and NCH: "C_continuum > \<aleph>1" and "small V_of_image_times"
  shows "countable V_of_image_times"
proof -
  have "\<exists>z0. gcard ((\<lambda>f. f z0) ` V_of_image_times) \<ge> \<aleph>1" if "uncountable V_of_image_times"
  proof -
    have "gcard V_of_image_times \<ge> \<aleph>1"
      using \<open>small V_of_image_times\<close> that uncountable_gcard_ge by blast 
    then obtain F' where "F' \<subseteq> V_of_image_times" and F': "gcard F' = \<aleph>1"
      by (meson Card_Aleph Ord_1 subset_smaller_gcard \<open>small V_of_image_times\<close>)
    then obtain \<phi> where \<phi>: "bij_betw \<phi> (elts (\<aleph>1)) F'"
      by (metis TC_small eqpoll_def gcard_eqpoll)
    define AB where "AB \<equiv> {(\<alpha>,\<beta>). \<alpha> < \<beta>} \<inter> (elts (\<aleph>1) \<times> elts (\<aleph>1))"
    have "gcard AB = \<aleph>1"
    proof (rule antisym)
      have "small AB"
        unfolding AB_def by (metis inf_le2 small_Times small_iff smaller_than_small)
      have "gcard (elts (\<aleph>1) \<times> elts (\<aleph>1)) = vcard (\<aleph>1 \<otimes> \<aleph>1)"
        by (metis G \<open>gcard F' = \<omega>1\<close> cardinal_idem gcard_def gcard_eq_vcard small_elts)
      also have "... = \<aleph>1 \<otimes> \<aleph>1"
        by (simp add: cmult_def)
      also have "\<dots> = \<aleph>1"
        by (simp add: InfCard_csquare_eq InfCard_def le_csucc one_V_def)
      finally show "gcard AB \<le> \<omega>1"
        by (metis AB_def inf_le2 lepoll_imp_gcard_le small_Times small_elts)
      have "elts (\<aleph>1) \<lesssim> AB"
        sorry
      then show "\<omega>1 \<le> gcard AB"
        apply (intro lepoll_imp_gcard_le)
        using lepoll_imp_gcard_le
    obtain z0 where "gcard ((\<lambda>f. f z0) ` F') = \<aleph>1"
      sorry
    then show ?thesis
      by (metis \<open>F' \<subseteq> V_of_image_times\<close> assms(3) image_mono lepoll_imp_gcard_le replacement)
  qed
  with W show ?thesis
    unfolding Wetzel_def
    by (metis Aleph_0 Aleph_succ Card_\<omega> countable_imp_g_le_Aleph0 leD less_csucc one_V_def order_le_less_trans)
qed



proposition Erdos_Wetzel_CH:
  assumes CH: "C_continuum = \<aleph>1"
  obtains V_of_image_times where "Wetzel V_of_image_times" and "uncountable V_of_image_times"
  sorry


theorem Erdos_Wetzel: "C_continuum = \<aleph>1 \<longleftrightarrow> (\<exists>V_of_image_times. Wetzel V_of_image_times \<and> uncountable V_of_image_times)"
  by (metis C_continuum_def Erdos_Wetzel_CH Erdos_Wetzel_nonCH Ord_\<omega>1 Ord_cardinal Ord_linear2 TC_small cardinal_idem countable_iff_le_Aleph0 countable_iff_less_\<omega>1 order_le_less uncountable_Real_set)



subsection \<open>random junk\<close>

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
