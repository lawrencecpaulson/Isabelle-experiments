section \<open>Set theory experiments\<close>

theory Sets imports
  "HOL-ex.Sketch_and_Explore" "HOL-Complex_Analysis.Complex_Analysis" "ZFC_in_HOL.ZFC_Typeclasses"
   
begin

subsection \<open>For the libraries\<close>


subsubsection \<open>HOL\<close>

thm card_Union_le_sum_card (*RENAME*)
lemma card_Union_le_sum_cardXXXX:
  fixes U :: "'a set set"
  shows "card (\<Union>U) \<le> sum card U"
  by (metis Union_upper card.infinite card_Union_le_sum_card finite_subset zero_le)

subsubsection \<open>Analysis\<close>

lemma Rats_closure_real: "closure \<rat> = (UNIV::real set)"
proof -
  have "\<And>x::real. x \<in> closure \<rat>"
    by (metis closure_approachable dist_real_def rational_approximation)
  then show ?thesis by auto
qed

lemma fsigma_UNIV [iff]: "fsigma (UNIV :: 'a::real_inner set)"
proof -
  have "(UNIV ::'a set) = (\<Union>i. cball 0 (of_nat i))"
    by (auto simp: real_arch_simple)
  then show ?thesis
    by (metis closed_cball fsigma.intros)
qed

lemma holomorphic_countable_zeros:
  assumes S: "f holomorphic_on S" "open S" "connected S" and "fsigma S"
      and "\<not> f constant_on S"
    shows "countable {z\<in>S. f z = 0}"
proof -
  obtain F::"nat \<Rightarrow> complex set" 
      where F: "range F \<subseteq> Collect compact" and Seq: "S = (\<Union>i. F i)"
    using \<open>fsigma S\<close> by (meson fsigma_Union_compact)
  have fin: "finite {z \<in> F i. f z = 0}" for i
    using holomorphic_compact_finite_zeros assms F Seq Union_iff by blast
  have "{z \<in> S. f z = 0} = (\<Union>i. {z \<in> F i. f z = 0})"
    using Seq by auto
  with fin show ?thesis
    by (simp add: countable_finite)
qed

lemma holomorphic_countable_equal:
  assumes "f holomorphic_on S" "g holomorphic_on S" "open S" "connected S" and "fsigma S"
    and eq: "uncountable {z\<in>S. f z = g z}"
  shows "S \<subseteq> {z\<in>S. f z = g z}"
proof -
  obtain z where z: "z\<in>S" "f z = g z"
    using eq not_finite_existsD uncountable_infinite by blast
  have "(\<lambda>x. f x - g x) holomorphic_on S"
    by (simp add: assms holomorphic_on_diff)
  then have "(\<lambda>x. f x - g x) constant_on S"
    using holomorphic_countable_zeros assms by force
  with z have "\<And>x. x\<in>S \<Longrightarrow> f x - g x = 0"
    unfolding constant_on_def by force
  then show ?thesis
    by auto
qed

lemma holomorphic_countable_equal_UNIV:
  assumes fg: "f holomorphic_on UNIV" "g holomorphic_on UNIV"
    and eq: "uncountable {z. f z = g z}"
  shows "f=g"
  using holomorphic_countable_equal [OF fg] eq by fastforce

thm real_non_denum
theorem complex_non_denum: "\<nexists>f :: nat \<Rightarrow> complex. surj f"
  by (metis (full_types) Re_complex_of_real comp_surj real_non_denum surj_def)

lemma uncountable_UNIV_complex: "uncountable (UNIV :: complex set)"
  using complex_non_denum unfolding uncountable_def by auto

subsubsection \<open>ZFC in HOL\<close>

thm countable_iff_le_Aleph0
lemma finite_iff_less_Aleph0: "finite (elts x) \<longleftrightarrow> vcard x < \<omega>"
proof
  show "finite (elts x) \<Longrightarrow> vcard x < \<omega>"
    by (metis Card_\<omega> Card_def finite_lesspoll_infinite infinite_\<omega> lesspoll_imp_Card_less)
  show "vcard x < \<omega> \<Longrightarrow> finite (elts x)"
    by (meson Ord_\<omega> Ord_cardinal Ord_mem_iff_lt cardinal_eqpoll eqpoll_finite_iff finite_Ord_omega)
qed

lemma cadd_left_commute: "j \<oplus> (i \<oplus> k) = i \<oplus> (j \<oplus> k)"
  using cadd_assoc cadd_commute by force

lemmas cadd_ac = cadd_assoc cadd_commute cadd_left_commute

thm Card_lt_csucc_iff
lemma csucc_lt_csucc_iff: "\<lbrakk>Card \<kappa>'; Card \<kappa>\<rbrakk> \<Longrightarrow> (csucc \<kappa>' < csucc \<kappa>) = (\<kappa>' < \<kappa>)"
  by (metis Card_csucc Card_is_Ord Card_lt_csucc_iff Ord_not_less)

lemma csucc_le_csucc_iff: "\<lbrakk>Card \<kappa>'; Card \<kappa>\<rbrakk> \<Longrightarrow> (csucc \<kappa>' \<le> csucc \<kappa>) = (\<kappa>' \<le> \<kappa>)"
  by (metis Card_csucc Card_is_Ord Card_lt_csucc_iff Ord_not_less)

lemma Card_Un [simp,intro]:
  assumes "Card(x)" "Card(y)" shows "Card(x \<squnion> y)"
  by (metis Card_is_Ord Ord_linear_le assms sup.absorb2 sup.orderE)


lemma csucc_0 [simp]: "csucc 0 = 1"
  by (simp add: finite_csucc one_V_def)

thm Card_Aleph
lemma InfCard_Aleph [simp, intro]:
  assumes "Ord \<alpha>"
  shows "InfCard(Aleph \<alpha>)"
  unfolding InfCard_def
  by (metis Aleph_0 Aleph_increasing Card_Aleph antisym_conv1 assms in_succ_iff nless_le zero_in_succ)

thm InfCard_csquare_eq
corollary Aleph_csquare_eq [simp]: "Ord \<alpha> \<Longrightarrow> \<aleph>\<alpha> \<otimes> \<aleph>\<alpha> = \<aleph>\<alpha>"
  using InfCard_csquare_eq by auto

lemma small_Times_iff: "small (X \<times> Y) \<longleftrightarrow> small X \<and> small Y \<or> X={} \<or> Y={}"  (is "_ = ?rhs")
proof
  assume *: "small (X \<times> Y)"
  { have "small X \<and> small Y" if "x \<in> X" "y \<in> Y" for x y
    proof -
      have "X \<subseteq> fst ` (X \<times> Y)" "Y \<subseteq> snd ` (X \<times> Y)"
        using that by auto
      with that show ?thesis
        by (metis * replacement smaller_than_small)
    qed    }
  then show ?rhs
    by (metis equals0I)
next
  assume ?rhs
  then show "small (X \<times> Y)"
    by auto
qed

lemma lepoll_small:
  assumes "A \<lesssim> B" "small B"
  shows "small A"
    by (meson assms lepoll_iff replacement smaller_than_small)

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

thm vcard_disjoint_sup
lemma vcard_sup: "vcard (x \<squnion> y) \<le> vcard x \<oplus> vcard y"
proof -
  have "elts (x \<squnion> y) \<lesssim> elts (x \<Uplus> y)"
    unfolding lepoll_def
  proof (intro exI conjI)
    let ?f = "\<lambda>z. if z \<in> elts x then Inl z else Inr z"
    show "inj_on ?f (elts (x \<squnion> y))"
      by (simp add: inj_on_def)
    show "?f ` elts (x \<squnion> y) \<subseteq> elts (x \<Uplus> y)" thm add.left_commute
      by force
  qed
  then show ?thesis
    using cadd_ac
    by (metis cadd_def cardinal_cong cardinal_idem lepoll_imp_Card_le vsum_0_eqpoll)
qed

lemma elts_cmult: "elts (\<kappa>' \<otimes> \<kappa>) \<approx> elts \<kappa>' \<times> elts \<kappa>"
  by (simp add: cmult_def elts_vcard_VSigma_eqpoll)

lemma vcard_Sup_le_cmult:
  assumes "small U" and \<kappa>: "\<And>x. x \<in> U \<Longrightarrow> vcard x \<le> \<kappa>"
  shows "vcard (\<Squnion>U) \<le> vcard (set U) \<otimes> \<kappa>"
proof -
  have "\<exists>f. f \<in> elts x \<rightarrow> elts \<kappa> \<and> inj_on f (elts x)" if "x \<in> U" for x
    using \<kappa> [OF that] by (metis cardinal_le_lepoll image_subset_iff_funcset lepoll_def)
  then obtain \<phi> where \<phi>: "\<And>x. x \<in> U \<Longrightarrow> (\<phi> x) \<in> elts x \<rightarrow> elts \<kappa> \<and> inj_on (\<phi> x) (elts x)"
    by metis
  define u where "u \<equiv> \<lambda>y. @x. x \<in> U \<and> y \<in> elts x"
  have u: "u y \<in> U \<and> y \<in> elts (u y)" if "y \<in> \<Union>(elts ` U)" for y
    unfolding u_def by (metis (mono_tags, lifting)that someI2_ex UN_iff)  
  define \<psi> where "\<psi> \<equiv> \<lambda>y. (u y, \<phi> (u y) y)"
  have U: "elts (vcard (set U)) \<approx> U"
    by (metis \<open>small U\<close> cardinal_eqpoll elts_of_set)
  have "elts (\<Squnion>U) = \<Union>(elts ` U)"
    using \<open>small U\<close> by blast
  also have "\<dots> \<lesssim> U \<times> elts \<kappa>"
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on \<psi> (\<Union> (elts ` U))"
      using \<phi> u by (smt (verit) \<psi>_def inj_on_def prod.inject)
    show "\<psi> ` \<Union> (elts ` U) \<subseteq> U \<times> elts \<kappa>"
      using \<phi> u by (auto simp: \<psi>_def)
  qed
  also have "\<dots>  \<approx> elts (vcard (set U) \<otimes> \<kappa>)"
    using U elts_cmult eqpoll_sym eqpoll_trans times_eqpoll_cong by blast
  finally have "elts (\<Squnion> U) \<lesssim> elts (vcard (set U) \<otimes> \<kappa>)" .
  then show ?thesis
    by (simp add: cmult_def lepoll_cardinal_le)
qed


thm Card_lt_csucc_iff
lemma csucc_le_Card_iff: "\<lbrakk>Card \<kappa>'; Card \<kappa>\<rbrakk> \<Longrightarrow> csucc \<kappa>' \<le> \<kappa> \<longleftrightarrow> \<kappa>' < \<kappa>"
  by (metis Card_csucc Card_is_Ord Card_lt_csucc_iff Ord_not_le)

lemma cadd_InfCard_le:
  assumes "\<alpha> \<le> \<kappa>" "\<beta> \<le> \<kappa>" "InfCard \<kappa>"
  shows "\<alpha> \<oplus> \<beta> \<le> \<kappa>"
  using assms by (metis InfCard_cdouble_eq cadd_le_mono)

lemma cmult_InfCard_le:
  assumes "\<alpha> \<le> \<kappa>" "\<beta> \<le> \<kappa>" "InfCard \<kappa>"
  shows "\<alpha> \<otimes> \<beta> \<le> \<kappa>"
  using assms
  by (metis InfCard_csquare_eq cmult_le_mono)

lemma vcard_Aleph [simp]: "Ord \<alpha> \<Longrightarrow> vcard (\<aleph>\<alpha>) = \<aleph>\<alpha>"
  by (simp add: Card_cardinal_eq)

lemma omega_le_Aleph [simp]: "Ord \<alpha> \<Longrightarrow> \<omega> \<le> \<aleph>\<alpha>"
  using InfCard_def by auto

subsection \<open>Making the embedding explicit (possibly add to the AFP entry?)\<close>

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

lemma V_of_image_times: "V_of ` (X \<times> Y) \<approx> (V_of ` X) \<times> (V_of ` Y)"
proof -
  have "V_of ` (X \<times> Y) \<approx> X \<times> Y"
    by (meson inj_V_of inj_eq inj_onI inj_on_image_eqpoll_self)
  also have "\<dots> \<approx> (V_of ` X) \<times> (V_of ` Y)"
    by (metis eqpoll_sym inj_V_of inj_eq inj_onI inj_on_image_eqpoll_self times_eqpoll_cong)
  finally show ?thesis .
qed

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

lemma Complex_vcard: "vcard Complex_set = C_continuum"
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
    also have "\<dots>  \<approx> elts Real_set"
      by (simp add: infinite_times_eqpoll_self uncountable_Real_set uncountable_infinite)
    finally show "elts Complex_set \<lesssim> elts Real_set" .
  qed
  then show ?thesis
    by (simp add: C_continuum_def cardinal_cong)
qed

subsection \<open>Cardinality of an arbitrary HOL set (add to the AFP entry?)\<close>

definition gcard :: "'a::embeddable set \<Rightarrow> V" 
  where "gcard X \<equiv> vcard (ZFC_in_HOL.set (V_of ` X))"

lemma gcard_big_0: "\<not> small X \<Longrightarrow> gcard X = 0"
  by (metis elts_eq_empty_iff elts_of_set gcard_def inv_V_of_image_eq replacement vcard_0)

lemma gcard_empty_0 [simp]: "gcard {} = 0"
  by (metis gcard_def image_is_empty vcard_0 zero_V_def)

lemma gcard_single_1 [simp]: "gcard {x} = 1"
  by (simp add: gcard_def)

lemma gcard_finite_set: "\<lbrakk>finite X; a \<notin> X\<rbrakk> \<Longrightarrow> gcard (insert a X) = succ (gcard X)" 
  by (simp add: gcard_def inj_V_of inj_image_mem_iff finite_csucc vcard_finite_set)

lemma gcard_eq_card: "finite X \<Longrightarrow> gcard X = ord_of_nat (card X)"
  by (induction X rule: finite_induct) (auto simp add: gcard_finite_set)

lemma Card_gcard [iff]: "Card (gcard X)"
  by (simp add: Card_def gcard_def)

lemma gcard_eq_vcard [simp]: "gcard (elts x) = vcard x"
  by (metis cardinal_cong elts_set_V_of gcard_def small_elts)

lemma gcard_eqpoll: "small X \<Longrightarrow> elts (gcard X) \<approx> X"
  by (metis cardinal_eqpoll elts_set_V_of eqpoll_trans gcard_def)

lemma gcard_image_le: 
  assumes "small A"
  shows "gcard (f ` A) \<le> gcard A"
proof -
  have "(V_of ` f ` A) \<lesssim> (V_of ` A)"
    by (metis Int_UNIV_left image_lepoll inj_V_of inj_on_Int inj_on_image_lepoll_1 inj_on_image_lepoll_2)
  then show ?thesis
    by (simp add: assms gcard_def lepoll_imp_Card_le)
qed

lemma gcard_image: "inj_on f A \<Longrightarrow> gcard (f ` A) = gcard A"
  by (metis dual_order.antisym gcard_big_0 gcard_image_le small_image_iff the_inv_into_onto)

lemma lepoll_imp_gcard_le:
  assumes "A \<lesssim> B" "small B"
  shows "gcard A \<le> gcard B"
proof -
  have "elts (ZFC_in_HOL.set (V_of ` A)) \<approx> A" "elts (ZFC_in_HOL.set (V_of ` B)) \<approx> B"
    by (meson assms elts_set_V_of lepoll_small)+
  with \<open>A \<lesssim> B\<close> show ?thesis
  unfolding gcard_def
  by (meson lepoll_imp_Card_le eqpoll_sym lepoll_iff_leqpoll lepoll_trans)
qed

lemma subset_imp_gcard_le:
  assumes "A \<subseteq> B" "small B"
  shows "gcard A \<le> gcard B"
  by (simp add: assms lepoll_imp_gcard_le subset_imp_lepoll)

lemma gcard_le_lepoll: "\<lbrakk>gcard A \<le> \<alpha>; small A\<rbrakk> \<Longrightarrow> A \<lesssim> elts \<alpha>"
  by (meson eqpoll_sym gcard_eqpoll lepoll_trans1 less_eq_V_def subset_imp_lepoll)

lemma gcard_Union_le_cmult:
  assumes "small U" and \<kappa>: "\<And>x. x \<in> U \<Longrightarrow> gcard x \<le> \<kappa>" and sm: "\<And>x. x \<in> U \<Longrightarrow> small x"
  shows "gcard (\<Union>U) \<le> gcard U \<otimes> \<kappa>"
proof -
  have "\<exists>f. f \<in> x \<rightarrow> elts \<kappa> \<and> inj_on f x" if "x \<in> U" for x
    using \<kappa> [OF that] gcard_le_lepoll by (smt (verit) Pi_iff TC_small imageI lepoll_def subset_eq)
  then obtain \<phi> where \<phi>: "\<And>x. x \<in> U \<Longrightarrow> (\<phi> x) \<in> x \<rightarrow> elts \<kappa> \<and> inj_on (\<phi> x) x"
    by metis
  define u where "u \<equiv> \<lambda>y. @x. x \<in> U \<and> y \<in> x"
  have u: "u y \<in> U \<and> y \<in>  (u y)" if "y \<in> \<Union>( U)" for y
    unfolding u_def using that by (fast intro!: someI2)
  define \<psi> where "\<psi> \<equiv> \<lambda>y. (u y, \<phi> (u y) y)"
  have U: "elts (gcard U) \<approx> U"
    by (simp add: gcard_eqpoll)
   have "\<Union>U \<lesssim> U \<times> elts \<kappa>"
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj_on \<psi> (\<Union> U)"
      using \<phi> u by (smt (verit) \<psi>_def inj_on_def prod.inject)
    show "\<psi> ` \<Union> U \<subseteq> U \<times> elts \<kappa>"
      using \<phi> u by (auto simp: \<psi>_def)
  qed
  also have "\<dots>  \<approx> elts (gcard U \<otimes> \<kappa>)"
    using U elts_cmult eqpoll_sym eqpoll_trans times_eqpoll_cong by blast
  finally have " (\<Union>U) \<lesssim> elts (gcard U \<otimes> \<kappa>)" .
  then show ?thesis
    by (metis cardinal_idem cmult_def gcard_eq_vcard lepoll_imp_gcard_le small_elts)
qed

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
  assumes \<kappa>: "\<kappa> \<le> gcard X" "Card \<kappa>"
  obtains Y where "Y \<subseteq> X" "gcard Y = \<kappa>"
proof (cases "small X")
  case True
  with  subset_smaller_vcard [OF \<kappa> [unfolded gcard_def]] show ?thesis
    by (metis elts_of_set gcard_def less_eq_V_def replacement set_of_elts subset_image_iff that)
next
  case False
  with assms show ?thesis
    by (metis antisym gcard_big_0 le_0 order_refl that)
qed

lemma Real_gcard: "gcard (UNIV::real set) = C_continuum"
  by (metis C_continuum_def Real_set_def gcard_def)

lemma Complex_gcard: "gcard (UNIV::complex set) = C_continuum"
  by (metis Complex_set_def Complex_vcard gcard_def)


lemma gcard_Times [simp]: "gcard (X \<times> Y) = gcard X \<otimes> gcard Y"
proof (cases "small X \<and> small Y")
  case True
  have "V_of ` (X \<times> Y) \<approx> (V_of ` X) \<times> (V_of ` Y)"
    by (metis V_of_image_times)
  also have "\<dots> \<approx> elts (vcard (ZFC_in_HOL.set (V_of ` X))) \<times> elts (vcard (ZFC_in_HOL.set (V_of ` Y)))"
    by (metis True cardinal_eqpoll eqpoll_sym replacement set_of_elts small_iff times_eqpoll_cong)
  also have "\<dots> \<approx> elts (vtimes (vcard (ZFC_in_HOL.set (V_of ` X))) (vcard (ZFC_in_HOL.set (V_of ` Y))))"
    using elts_VSigma by auto
  finally show ?thesis
    using True cardinal_cong by (simp add: gcard_def cmult_def)
next
  case False
  have "gcard (X \<times> Y) = 0"
    by (metis False Times_empty gcard_big_0 gcard_empty_0 small_Times_iff)
  then show ?thesis
    by (metis False cmult_0 cmult_commute gcard_big_0)
qed


subsection \<open>Wetzel's property\<close>

lemma less_succ_self: "x < succ x"
  by (simp add: less_eq_V_def order_neq_le_trans subset_insertI)

definition Wetzel :: "(complex \<Rightarrow> complex) set \<Rightarrow> bool"
  where "Wetzel \<equiv> \<lambda>F. (\<forall>f\<in>F. f analytic_on UNIV) \<and> (\<forall>z. countable((\<lambda>f. f z) ` F))"


proposition Erdos_Wetzel_nonCH:
  assumes W: "Wetzel F" and NCH: "C_continuum > \<aleph>1" and "small F"
  shows "countable F"
proof -
  have "\<exists>z0. gcard ((\<lambda>f. f z0) ` F) \<ge> \<aleph>1" if "uncountable F"
  proof -
    have "gcard F \<ge> \<aleph>1"
      using \<open>small F\<close> that uncountable_gcard_ge by blast 
    then obtain F' where "F' \<subseteq> F" and F': "gcard F' = \<aleph>1"
      by (meson Card_Aleph Ord_1 subset_smaller_gcard \<open>small F\<close>)
    then obtain \<phi> where \<phi>: "bij_betw \<phi> (elts (\<aleph>1)) F'"
      by (metis TC_small eqpoll_def gcard_eqpoll)
    define S where "S \<equiv> \<lambda>\<alpha> \<beta>. {z. \<phi> \<alpha> z = \<phi> \<beta> z}"
    have co_S: "gcard (S \<alpha> \<beta>) \<le> \<aleph>0" if "\<alpha> \<in> elts \<beta>" "\<beta> \<in> elts (\<aleph>1)" for \<alpha> \<beta>
    proof -
      have "\<phi> \<alpha> holomorphic_on UNIV" "\<phi> \<beta> holomorphic_on UNIV"
        using W \<open>F' \<subseteq> F\<close> unfolding Wetzel_def
        by (meson Ord_\<omega>1 Ord_trans \<phi> analytic_imp_holomorphic bij_betwE subsetD that)+
      moreover have "\<phi> \<alpha> \<noteq> \<phi> \<beta>"
        by (metis Ord_\<omega>1 Ord_in_Ord Ord_trans OrdmemD \<phi> bij_betw_imp_inj_on inj_on_def less_V_def that)
      ultimately have "countable (S \<alpha> \<beta>)"
        using holomorphic_countable_equal_UNIV unfolding S_def by blast
      then show ?thesis
        using countable_imp_g_le_Aleph0 by blast
    qed
    define SS where "SS \<equiv> \<Squnion>\<beta> \<in> elts(\<aleph>1). \<Squnion>\<alpha> \<in> elts \<beta>. S \<alpha> \<beta>"
    have F'_eq: "F' =  \<phi> ` elts \<omega>1"
      using \<phi> bij_betw_imp_surj_on by auto
    have \<section>: "\<And>x xa. xa \<in> elts \<omega>1 \<Longrightarrow> gcard (\<Union>\<alpha>\<in>elts xa. S \<alpha> xa) \<le> \<omega>"
      by (metis Aleph_0 TC_small co_S countable_UN countable_iff_g_le_Aleph0 less_\<omega>1_imp_countable)
    have "gcard SS \<le> gcard ((\<lambda>\<beta>. \<Union>\<alpha>\<in>elts \<beta>. S \<alpha> \<beta>) ` elts \<omega>1) \<otimes> \<aleph>0"
      apply (simp add: SS_def)
      by (metis (no_types, lifting) "\<section>" TC_small gcard_Union_le_cmult imageE)
    also have "...  \<le> \<aleph>1"
    proof (rule cmult_InfCard_le)
      show "gcard ((\<lambda>\<beta>. \<Union>\<alpha>\<in>elts \<beta>. S \<alpha> \<beta>) ` elts \<omega>1) \<le> \<omega>1"
        using gcard_image_le by fastforce
    qed auto
    finally have "gcard SS \<le> \<aleph>1" .
    with NCH obtain z0 where "z0 \<notin> SS"
      by (metis Complex_gcard UNIV_eq_I less_le_not_le)
    then have "inj_on (\<lambda>x. \<phi> x z0) (elts \<omega>1)"
      apply (simp add: SS_def S_def inj_on_def)
      by (metis Ord_\<omega>1 Ord_in_Ord Ord_linear)
    then have "gcard ((\<lambda>f. f z0) ` F') = \<aleph>1"
      by (smt (verit) F' F'_eq gcard_image imageE inj_on_def)
    then show ?thesis
      by (metis TC_small \<open>F' \<subseteq> F\<close> image_mono subset_imp_gcard_le)
  qed
  with W show ?thesis
    unfolding Wetzel_def
    by (metis Aleph_0 Aleph_succ Card_\<omega> countable_imp_g_le_Aleph0 leD less_csucc one_V_def order_le_less_trans)
qed


lemma Rats_closure_real2: "closure (\<rat>\<times>\<rat>) = (UNIV::real set)\<times>(UNIV::real set)"
  by (simp add: Rats_closure_real closure_Times)

proposition Erdos_Wetzel_CH:
  assumes CH: "C_continuum = \<aleph>1"
  obtains F where "Wetzel F" and "uncountable F"
proof -
  define D where "D \<equiv> {z. Re z \<in> \<rat> \<and> Im z \<in> \<rat>}"
  have "D = (\<Union>x\<in>\<rat>. \<Union>y\<in>\<rat>. {Complex x y})"
    using complex.collapse by (force simp: D_def)
  with countable_rat have "countable D"
    by blast
  have "\<exists>w. Re w \<in> \<rat> \<and> Im w \<in> \<rat> \<and> cmod (w - z) < e" if "e > 0" for z and e::real
  proof -
    obtain x y where "x\<in>\<rat>" "y\<in>\<rat>" and xy: "dist (x,y) (Re z, Im z) < e"
      using \<open>e > 0\<close> Rats_closure_real2 by (force simp: closure_approachable)
    moreover have "dist (x,y) (Re z, Im z) = cmod (Complex x y - z)"
      by (simp add: norm_complex_def norm_prod_def dist_norm)
    ultimately show "\<exists>w. Re w \<in> \<rat> \<and> Im w \<in> \<rat> \<and> cmod (w - z) < e"
      by (metis complex.sel)
  qed
  then have "closure D = UNIV"
    by (auto simp: D_def closure_approachable dist_complex_def)
  obtain \<zeta> where \<zeta>: "bij_betw \<zeta> (elts (\<aleph>1)) (UNIV::complex set)"
    by (metis Complex_gcard TC_small assms eqpoll_def gcard_eqpoll)
  obtain f where f: "inj_on f (elts (\<aleph>1))" and anf: "\<And>\<beta>. \<beta> \<in> elts (\<aleph>1) \<Longrightarrow> f \<beta> analytic_on UNIV"
    and D: "\<And>\<alpha> \<beta>. \<lbrakk>\<beta> \<in> elts (\<aleph>1); \<alpha> \<in> elts \<beta>\<rbrakk> \<Longrightarrow> f \<beta> (\<zeta> \<alpha>) \<in> D"
    sorry
  show ?thesis
    sorry
qed


theorem Erdos_Wetzel: "C_continuum = \<aleph>1 \<longleftrightarrow> (\<exists>F. Wetzel F \<and> uncountable F)"
  by (metis Complex_vcard Erdos_Wetzel_CH Erdos_Wetzel_nonCH TC_small antisym_conv1 gcard_eq_vcard small_elts uncountable_Complex_set uncountable_gcard_ge)



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