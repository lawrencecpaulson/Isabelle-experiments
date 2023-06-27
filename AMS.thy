section \<open>Abstract Metric Spaces\<close>

theory AMS
  imports
    "HOL-Analysis.Analysis" "HOL-Library.Equipollence"
    "HOL-ex.Sketch_and_Explore"
begin


(*HOL Light's FORALL_POS_MONO_1_EQ*)
lemma Inter_eq_Inter_inverse_Suc:
  assumes "\<And>r' r. r' < r \<Longrightarrow> A r' \<subseteq> A r"
  shows "(\<Inter>\<epsilon>\<in>{0<..}. A \<epsilon>) = (\<Inter>n. A(inverse(Suc n)))"
proof 
  have "x \<in> A \<epsilon>"
    if x: "\<forall>n. x \<in> A (inverse (Suc n))" and "\<epsilon>>0" for x and \<epsilon> :: real
  proof -
    obtain n where "inverse (Suc n) < \<epsilon>"
      using \<open>\<epsilon>>0\<close> reals_Archimedean by blast
    with assms x show ?thesis
      by blast
  qed
  then show "(\<Inter>n. A(inverse(Suc n))) \<subseteq> (\<Inter>\<epsilon>\<in>{0<..}. A \<epsilon>)"
    by auto    
qed auto

thm shrink_range (*Abstract_Topology_2*)
lemma card_eq_real_subset:
  fixes a b::real
  assumes "a < b" and S: "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> x \<in> S"
  shows "S \<approx> (UNIV::real set)"
proof (rule lepoll_antisym)
  show "S \<lesssim> (UNIV::real set)"
    by (simp add: subset_imp_lepoll)
  define f where "f \<equiv> \<lambda>x. (a+b) / 2 + (b-a) / 2 * (x / (1 + \<bar>x\<bar>))"
  show "(UNIV::real set) \<lesssim> S"
    unfolding lepoll_def
  proof (intro exI conjI)
    show "inj f"
      unfolding inj_on_def f_def
      by (smt (verit, ccfv_SIG) real_shrink_eq \<open>a<b\<close> divide_eq_0_iff mult_cancel_left times_divide_eq_right)
    have pos: "(b-a) / 2 > 0"
      using \<open>a<b\<close> by auto
    have *: "a < (a + b) / 2 + (b - a) / 2 * x \<longleftrightarrow> (b - a) > (b - a) * -x"
            "(a + b) / 2 + (b - a) / 2 * x < b \<longleftrightarrow> (b - a) * x < (b - a)" for x
      by (auto simp: field_simps)
    show "range f \<subseteq> S"
      using shrink_range [of UNIV] \<open>a < b\<close>
      unfolding subset_iff f_def greaterThanLessThan_iff image_iff
      by (smt (verit, best) S * mult_less_cancel_left2 mult_minus_right)
  qed
qed

  
(*NEEDS LEPOLL (Used nowhere in Analysis) *)
lemma card_lepoll_quasi_components_of_topspace: "quasi_components_of X \<lesssim> topspace X"
  unfolding lepoll_def
  by (metis bot.extremum image_empty inj_on_empty inj_on_iff_surj quasi_components_of_def)

(*NEEDS first_countable
lemma first_countable_mtopology:
   "first_countable mtopology"
oops
  GEN_TAC THEN REWRITE_TAC[first_countable; TOPSPACE_MTOPOLOGY] THEN
  X_GEN_TAC `x::A` THEN DISCH_TAC THEN
  EXISTS_TAC `{ mball m (x::A,r) | rational r \<and> 0 < r}` THEN
  REWRITE_TAC[FORALL_IN_GSPEC; OPEN_IN_MBALL; EXISTS_IN_GSPEC] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{f x | S x \<and> Q x} = f ` {x \<in> S. Q x}`] THEN
  SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_RATIONAL; COUNTABLE_RESTRICT] THEN
  REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN
  X_GEN_TAC `U::A=>bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `x::A`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r::real` THEN STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC \<circ> SPEC `r::real` \<circ> MATCH_MP RATIONAL_APPROXIMATION_BELOW) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q::real` THEN
  REWRITE_TAC[REAL_SUB_REFL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CENTRE_IN_MBALL] THEN
  TRANS_TAC SUBSET_TRANS `mball m (x::A,r)` THEN
  ASM_SIMP_TAC[MBALL_SUBSET_CONCENTRIC; REAL_LT_IMP_LE]);;

lemma metrizable_imp_first_countable:
   "metrizable_space X \<Longrightarrow> first_countable X"
oops
  REWRITE_TAC[FORALL_METRIZABLE_SPACE; FIRST_COUNTABLE_MTOPOLOGY]);;
*)


context Metric_space
begin


subsection\<open>Size bounds on connected or path-connected spaces\<close>

lemma connected_space_imp_card_ge_alt:
  assumes "connected_space X" "completely_regular_space X" "closedin X S" "S \<noteq> {}" "S \<noteq> topspace X"
  shows "(UNIV::real set) \<lesssim> topspace X"
proof -
  have "S \<subseteq> topspace X"
    using \<open>closedin X S\<close> closedin_subset by blast
  then obtain a where "a \<in> topspace X" "a \<notin> S"
    using \<open>S \<noteq> topspace X\<close> by blast
  have "(UNIV::real set) \<lesssim> {0..1::real}"
    using card_eq_real_subset 
    by (meson atLeastAtMost_iff eqpoll_imp_lepoll eqpoll_sym less_eq_real_def zero_less_one)
  also have "\<dots> \<lesssim> topspace X"
  proof -
    obtain f where contf: "continuous_map X euclidean f"
      and fim: "f ` (topspace X) \<subseteq> {0..1::real}"
      and f0: "f a = 0" and f1: "f ` S \<subseteq> {1}"
      using \<open>completely_regular_space X\<close>
      unfolding completely_regular_space_def
      by (metis Diff_iff \<open>a \<in> topspace X\<close> \<open>a \<notin> S\<close> \<open>closedin X S\<close> continuous_map_in_subtopology)
    have "\<exists>y\<in>topspace X. x = f y" if "0 \<le> x" and "x \<le> 1" for x
    proof -
      have "connectedin euclidean (f ` topspace X)"
        using \<open>connected_space X\<close> connectedin_continuous_map_image connectedin_topspace contf by blast
      moreover have "\<exists>y. 0 = f y \<and> y \<in> topspace X"
        using \<open>a \<in> topspace X\<close> f0 by auto
      moreover have "\<exists>y. 1 = f y \<and> y \<in> topspace X"
        using \<open>S \<subseteq> topspace X\<close> \<open>S \<noteq> {}\<close> f1 by fastforce
      ultimately show ?thesis
        using that by (fastforce simp: is_interval_1 simp flip: is_interval_connected_1)
    qed
    then show ?thesis
      unfolding lepoll_iff using atLeastAtMost_iff by blast
  qed
  finally show ?thesis .
qed


lemma connected_space_imp_card_ge_gen:
  assumes "connected_space X" "normal_space X" "closedin X S" "closedin X T" "S \<noteq> {}" "T \<noteq> {}" "disjnt S T"
  shows "(UNIV::real set) \<lesssim> topspace X"
proof -
  have "(UNIV::real set) \<lesssim> {0..1::real}"
    by (metis atLeastAtMost_iff card_eq_real_subset eqpoll_imp_lepoll eqpoll_sym less_le_not_le zero_less_one)
  also have "\<dots>\<lesssim> topspace X"
  proof -
    obtain f where contf: "continuous_map X euclidean f"
       and fim: "f ` (topspace X) \<subseteq> {0..1::real}"
       and f0: "f ` S \<subseteq> {0}" and f1: "f ` T \<subseteq> {1}"
      using assms by (metis continuous_map_in_subtopology normal_space_iff_Urysohn)
    have "\<exists>y\<in>topspace X. x = f y" if "0 \<le> x" and "x \<le> 1" for x
    proof -
      have "connectedin euclidean (f ` topspace X)"
        using \<open>connected_space X\<close> connectedin_continuous_map_image connectedin_topspace contf by blast
      moreover have "\<exists>y. 0 = f y \<and> y \<in> topspace X"
        using \<open>closedin X S\<close> \<open>S \<noteq> {}\<close> closedin_subset f0 by fastforce
      moreover have "\<exists>y. 1 = f y \<and> y \<in> topspace X"
        using \<open>closedin X T\<close> \<open>T \<noteq> {}\<close> closedin_subset f1 by fastforce
      ultimately show ?thesis
        using that by (fastforce simp: is_interval_1 simp flip: is_interval_connected_1)
    qed
    then show ?thesis
      unfolding lepoll_iff using atLeastAtMost_iff by blast
  qed
  finally show ?thesis .
qed

lemma connected_space_imp_card_ge:
  assumes "connected_space X" "normal_space X" "t1_space X" and nosing: "\<not> (\<exists>a. topspace X \<subseteq> {a})"
  shows "(UNIV::real set) \<lesssim> topspace X"
proof -
  obtain a b where "a \<in> topspace X" "b \<in> topspace X" "a \<noteq> b"
    by (metis nosing singletonI subset_iff)
  then have "{a} \<noteq> topspace X"
    by force
  with connected_space_imp_card_ge_alt assms show ?thesis
    by (metis \<open>a \<in> topspace X\<close> closedin_t1_singleton insert_not_empty normal_imp_completely_regular_space_A)
qed

lemma connected_space_imp_infinite_gen:
   "\<lbrakk>connected_space X; t1_space X; \<nexists>a. topspace X \<subseteq> {a}\<rbrakk> \<Longrightarrow> infinite(topspace X)"
  by (metis connected_space_discrete_topology finite_t1_space_imp_discrete_topology)

lemma connected_space_imp_infinite:
   "\<lbrakk>connected_space X; Hausdorff_space X; \<nexists>a. topspace X \<subseteq> {a}\<rbrakk> \<Longrightarrow> infinite(topspace X)"
  by (simp add: Hausdorff_imp_t1_space connected_space_imp_infinite_gen)

lemma connected_space_imp_infinite_alt:
  assumes "connected_space X" "regular_space X" "closedin X S" "S \<noteq> {}" "S \<noteq> topspace X"
  shows "infinite(topspace X)"
proof -
  have "S \<subseteq> topspace X"
    using \<open>closedin X S\<close> closedin_subset by blast
  then obtain a where a: "a \<in> topspace X" "a \<notin> S"
    using \<open>S \<noteq> topspace X\<close> by blast
  have "\<exists>\<Phi>. \<forall>n. (disjnt (\<Phi> n) S \<and> a \<in> \<Phi> n \<and> openin X (\<Phi> n)) \<and> \<Phi>(Suc n) \<subset> \<Phi> n"
  proof (rule dependent_nat_choice)
    show "\<exists>T. disjnt T S \<and> a \<in> T \<and> openin X T"
      by (metis Diff_iff a \<open>closedin X S\<close> closedin_def disjnt_iff)
    fix V n
    assume \<section>: "disjnt V S \<and> a \<in> V \<and> openin X V"
    then obtain U C where U: "openin X U" "closedin X C" "a \<in> U" "U \<subseteq> C" "C \<subseteq> V"
      using \<open>regular_space X\<close> by (metis neighbourhood_base_of neighbourhood_base_of_closedin)
    with assms have "U \<subset> V"
      by (metis "\<section>" \<open>S \<subseteq> topspace X\<close> connected_space_clopen_in disjnt_def empty_iff inf.absorb_iff2 inf.orderE psubsetI subset_trans)
    with U show "\<exists>U. (disjnt U S \<and> a \<in> U \<and> openin X U) \<and> U \<subset> V"
      using "\<section>" disjnt_subset1 by blast
  qed
  then obtain \<Phi> where \<Phi>: "\<And>n. disjnt (\<Phi> n) S \<and> a \<in> \<Phi> n \<and> openin X (\<Phi> n)"
    and \<Phi>sub: "\<And>n. \<Phi> (Suc n) \<subset> \<Phi> n" by metis
  then have "decseq \<Phi>"
    by (simp add: decseq_SucI psubset_eq)
  have "\<forall>n. \<exists>x. x \<in> \<Phi> n \<and> x \<notin> \<Phi>(Suc n)"
    by (meson \<Phi>sub psubsetE subsetI)
  then obtain f where fin: "\<And>n. f n \<in> \<Phi> n" and fout: "\<And>n. f n \<notin> \<Phi>(Suc n)"
    by metis
  have "range f \<subseteq> topspace X"
    by (meson \<Phi> fin image_subset_iff openin_subset subset_iff)
  moreover have "inj f"
    by (metis Suc_le_eq \<open>decseq \<Phi>\<close> decseq_def fin fout linorder_injI subsetD)
  ultimately show ?thesis
    using infinite_iff_countable_subset by blast
qed

lemma path_connected_space_imp_card_ge:
  assumes "path_connected_space X" "Hausdorff_space X" and nosing: "\<not> (\<exists>x. topspace X \<subseteq> {x})"
  shows "(UNIV::real set) \<lesssim> topspace X"
proof -
  obtain a b where "a \<in> topspace X" "b \<in> topspace X" "a \<noteq> b"
    by (metis nosing singletonI subset_iff)
  then obtain \<gamma> where \<gamma>: "pathin X \<gamma>" "\<gamma> 0 = a" "\<gamma> 1 = b"
    by (meson \<open>a \<in> topspace X\<close> \<open>b \<in> topspace X\<close> \<open>path_connected_space X\<close> path_connected_space_def)
  let ?Y = "subtopology X (\<gamma> ` (topspace (subtopology euclidean {0..1})))"
  have "(UNIV::real set) \<lesssim>  topspace ?Y"
  proof (intro compact_Hausdorff_or_regular_imp_normal_space connected_space_imp_card_ge)
    show "connected_space ?Y"
      using \<open>pathin X \<gamma>\<close> connectedin_def connectedin_path_image by auto
    show "Hausdorff_space ?Y \<or> regular_space ?Y"
      using Hausdorff_space_subtopology \<open>Hausdorff_space X\<close> by blast
    show "t1_space ?Y"
      using Hausdorff_imp_t1_space \<open>Hausdorff_space X\<close> t1_space_subtopology by blast
    show "compact_space ?Y"
      by (simp add: \<open>pathin X \<gamma>\<close> compact_space_subtopology compactin_path_image)
    have "a \<in> topspace ?Y" "b \<in> topspace ?Y"
      using \<gamma> pathin_subtopology by fastforce+
    with \<open>a \<noteq> b\<close> show "\<nexists>x. topspace ?Y \<subseteq> {x}"
      by blast
  qed
  also have "\<dots> \<lesssim> \<gamma> ` {0..1}"
    by (simp add: subset_imp_lepoll)
  also have "\<dots> \<lesssim> topspace X"
    by (meson \<gamma> path_image_subset_topspace subset_imp_lepoll)
  finally show ?thesis .
qed

lemma connected_space_imp_uncountable:
  assumes "connected_space X" "regular_space X" "Hausdorff_space X" "\<not> (\<exists>a. topspace X \<subseteq> {a})"
  shows "\<not> countable(topspace X)"
proof
  assume coX: "countable (topspace X)"
  with \<open>regular_space X\<close> have "normal_space X"
    using countable_imp_Lindelof_space regular_Lindelof_imp_normal_space by blast
  then have "(UNIV::real set) \<lesssim> topspace X"
    by (simp add: Hausdorff_imp_t1_space assms connected_space_imp_card_ge)
  with coX show False
    using countable_lepoll uncountable_UNIV_real by blast
qed

lemma path_connected_space_imp_uncountable:
  assumes "path_connected_space X" "t1_space X" and nosing: "\<not> (\<exists>a. topspace X \<subseteq> {a})"
  shows "\<not> countable(topspace X)"
proof 
  assume coX: "countable (topspace X)"
  obtain a b where "a \<in> topspace X" "b \<in> topspace X" "a \<noteq> b"
    by (metis nosing singletonI subset_iff)
  then obtain \<gamma> where "pathin X \<gamma>" "\<gamma> 0 = a" "\<gamma> 1 = b"
    by (meson \<open>a \<in> topspace X\<close> \<open>b \<in> topspace X\<close> \<open>path_connected_space X\<close> path_connected_space_def)
  then have "\<gamma> ` {0..1} \<lesssim> topspace X"
    by (meson path_image_subset_topspace subset_imp_lepoll)
  define \<A> where "\<A> \<equiv> ((\<lambda>a. {x \<in> {0..1}. \<gamma> x \<in> {a}}) ` topspace X) - {{}}"
  have \<A>01: "\<A> = {{0..1}}"
  proof (rule real_Sierpinski_lemma)
    show "countable \<A>"
      using \<A>_def coX by blast
    show "disjoint \<A>"
      by (auto simp: \<A>_def disjnt_iff pairwise_def)
    show "\<Union>\<A> = {0..1}"
      using \<open>pathin X \<gamma>\<close> path_image_subset_topspace by (fastforce simp: \<A>_def Bex_def)
    fix C
    assume "C \<in> \<A>"
    then obtain a where "a \<in> topspace X" and C: "C = {x \<in> {0..1}. \<gamma> x \<in> {a}}" "C \<noteq> {}"
      by (auto simp: \<A>_def)
    then have "closedin X {a}"
      by (meson \<open>t1_space X\<close> closedin_t1_singleton)
    then have "closedin (top_of_set {0..1}) C"
      using C \<open>pathin X \<gamma>\<close> closedin_continuous_map_preimage pathin_def by fastforce
    then show "closed C \<and> C \<noteq> {}"
      using C closedin_closed_trans by blast
  qed auto
  then have "{0..1} \<in> \<A>"
    by blast
  then have "\<exists>a \<in> topspace X. {0..1} \<subseteq> {x. \<gamma> x = a}"
    using \<A>_def image_iff by auto
  then show False
    using \<open>\<gamma> 0 = a\<close> \<open>\<gamma> 1 = b\<close> \<open>a \<noteq> b\<close> atLeastAtMost_iff zero_less_one_class.zero_le_one by blast
qed



subsection\<open>Lavrentiev extension etc\<close>

lemma (in Metric_space) convergent_eq_zero_oscillation_gen:
  assumes "mcomplete" and fim: "f ` (topspace X \<inter> S) \<subseteq> M"
  shows "(\<exists>l. limitin mtopology f l (atin_within X a S)) \<longleftrightarrow>
         M \<noteq> {} \<and>
         (a \<in> topspace X
            \<longrightarrow> (\<forall>\<epsilon>>0. \<exists>U. openin X U \<and> a \<in> U \<and>
                           (\<forall>x \<in> (S \<inter> U) - {a}. \<forall>y \<in> (S \<inter> U) - {a}. d (f x) (f y) < \<epsilon>)))"
proof (cases "M = {}")
  case True
  with limitin_mspace show ?thesis
    by blast
next
  case False
  show ?thesis
  proof (cases "a \<in> topspace X")
    case True
    let ?R = "\<forall>\<epsilon>>0. \<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>)"
    show ?thesis
    proof (cases "a \<in> X derived_set_of S")
      case True
      have ?R
        if "limitin mtopology f l (atin_within X a S)" for l
      proof (intro strip)
        fix \<epsilon>::real
        assume "\<epsilon>>0"
        with that \<open>a \<in> topspace X\<close> 
        obtain U where U: "openin X U" "a \<in> U" "l \<in> M"
          and Uless: "\<forall>x\<in>U - {a}. x \<in> S \<longrightarrow> f x \<in> M \<and> d (f x) l < \<epsilon>/2"
          unfolding limitin_metric eventually_within_imp eventually_atin
          using half_gt_zero by blast
        show "\<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>)"
        proof (intro exI strip conjI)
          fix x y
          assume x: "x \<in> S \<inter> U - {a}" and y: "y \<in> S \<inter> U - {a}"
          then have "d (f x) l < \<epsilon>/2" "d (f y) l < \<epsilon>/2" "f x \<in> M" "f y \<in> M"
            using Uless by auto
          then show "d (f x) (f y) < \<epsilon>"
            using triangle' \<open>l \<in> M\<close> by fastforce
        qed (auto simp add: U)
      qed
      moreover have "\<exists>l. limitin mtopology f l (atin_within X a S)" 
        if R [rule_format]: ?R
      proof -
        define F where "F \<equiv> \<lambda>U. mtopology closure_of f ` (S \<inter> U - {a})"
        define \<C> where "\<C> \<equiv> F ` {U. openin X U \<and> a \<in> U}"
        have \<C>_clo: "\<forall>C \<in> \<C>. closedin mtopology C"
          by (force simp add: \<C>_def F_def)
        moreover have sub_mcball: "\<exists>C a. C \<in> \<C> \<and> C \<subseteq> mcball a \<epsilon>" if "\<epsilon>>0" for \<epsilon>
        proof -
          obtain U where U: "openin X U" "a \<in> U" 
            and Uless: "\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>"
            using R [OF \<open>\<epsilon>>0\<close>] by blast
          then obtain b where b: "b \<noteq> a" "b \<in> S" "b \<in> U"
            using True by (auto simp add: in_derived_set_of)
          have "U \<subseteq> topspace X"
            by (simp add: U(1) openin_subset)
          have "f b \<in> M"
            using b \<open>openin X U\<close> by (metis Int_iff fim image_eqI openin_subset subsetD)
          moreover
          have "mtopology closure_of f ` ((S \<inter> U) - {a}) \<subseteq> mcball (f b) \<epsilon>"
          proof (rule closure_of_minimal)
            have 1: "\<And>y. \<lbrakk>y \<in> S; y \<in> U; y \<noteq> a\<rbrakk> \<Longrightarrow> f y \<in> M \<and> d (f b) (f y) \<le> \<epsilon>"
              using \<open>U \<subseteq> topspace X\<close> fim Uless b by (force simp add: subset_iff) 
            then show "f ` (S \<inter> U - {a}) \<subseteq> mcball (f b) \<epsilon>"
              by (force simp: \<open>f b \<in> M\<close>)
          qed auto
          ultimately show ?thesis
            using U by (auto simp add: \<C>_def F_def)
        qed
        moreover have "\<Inter>\<F> \<noteq> {}" if "finite \<F>" "\<F> \<subseteq> \<C>" for \<F>
        proof -
          obtain \<G> where sub: "\<G> \<subseteq> {U. openin X U \<and> a \<in> U}" and eq: "\<F> = F ` \<G>" and "finite \<G>"
            by (metis (no_types, lifting) \<C>_def \<open>\<F> \<subseteq> \<C>\<close> \<open>finite \<F>\<close> finite_subset_image)
          then have "U \<subseteq> topspace X" if "U \<in> \<G>" for U
            using openin_subset that by auto
          then have "T \<subseteq> mtopology closure_of T" 
            if "T \<in> (\<lambda>U. f ` (S \<inter> U - {a})) ` \<G>" for T
            using that fim by (fastforce simp add: intro!: closure_of_subset)
          moreover
          have ain: "a \<in> \<Inter> (insert (topspace X) \<G>)" "openin X (\<Inter> (insert (topspace X) \<G>))"
            using True in_derived_set_of sub \<open>finite \<G>\<close> by (fastforce intro!: openin_Inter)+
          then obtain y where "y \<noteq> a" "y \<in> S" and y: "y \<in> \<Inter> (insert (topspace X) \<G>)"
            by (meson \<open>a \<in> X derived_set_of S\<close> sub in_derived_set_of) 
          then have "f y \<in> \<Inter>\<F>"
            using eq that ain fim by (auto simp add: F_def image_subset_iff in_closure_of)
          then show ?thesis by blast
        qed
        ultimately have "\<Inter>\<C> \<noteq> {}"
          using \<open>mcomplete\<close> mcomplete_fip by metis
        then obtain b where "b \<in> \<Inter>\<C>"
          by auto
        then have "b \<in> M"
          using sub_mcball \<C>_clo mbounded_alt_pos mbounded_empty metric_closedin_iff_sequentially_closed by force
        have "limitin mtopology f b (atin_within X a S)"
        proof (clarsimp simp: limitin_metric \<open>b \<in> M\<close>)
          fix \<epsilon> :: real
          assume "\<epsilon> > 0"
          then obtain U where U: "openin X U" "a \<in> U" and subU: "U \<subseteq> topspace X"
            and Uless: "\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>/2"
            by (metis R half_gt_zero openin_subset) 
          then obtain x where x: "x \<in> S" "x \<in> U" "x \<noteq> a" and fx: "f x \<in> mball b (\<epsilon>/2)"
            using \<open>b \<in> \<Inter>\<C>\<close> 
            apply (simp add: \<C>_def F_def closure_of_def del: divide_const_simps)
            by (metis Diff_iff Int_iff centre_in_mball_iff in_mball openin_mball singletonI zero_less_numeral)
          moreover
          have "d (f y) b < \<epsilon>" if "y \<in> U" "y \<noteq> a" "y \<in> S" for y
          proof -
            have "d (f x) (f y) < \<epsilon>/2"
              using Uless that x by force
            moreover have "d b (f x)  < \<epsilon>/2"
              using fx by simp
            ultimately show ?thesis
              using triangle [of b "f x" "f y"] subU that \<open>b \<in> M\<close> commute fim fx by fastforce
          qed
          ultimately show "\<forall>\<^sub>F x in atin_within X a S. f x \<in> M \<and> d (f x) b < \<epsilon>"
            apply (simp add: eventually_atin eventually_within_imp del: divide_const_simps)
            by (smt (verit, del_insts) Diff_iff Int_iff U fim imageI insertI1 openin_subset subsetD)
        qed
        then show ?thesis ..
      qed
      ultimately
      show ?thesis
        by (meson True \<open>M \<noteq> {}\<close> in_derived_set_of)
    next
      case False
      have "(\<exists>l. limitin mtopology f l (atin_within X a S))"
        by (metis \<open>M \<noteq> {}\<close> False derived_set_of_trivial_limit equals0I limitin_trivial topspace_mtopology)
      moreover have "\<forall>e>0. \<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < e)"
        by (metis Diff_iff False IntE True in_derived_set_of insert_iff)
      ultimately show ?thesis
        using limitin_mspace by blast
    qed
  next
    case False
    then show ?thesis
      by (metis derived_set_of_trivial_limit ex_in_conv in_derived_set_of limitin_mspace limitin_trivial topspace_mtopology)
  qed
qed

lemma (in Metric_space) gdelta_in_points_of_convergence_within:
  assumes "mcomplete"
    and f: "continuous_map (subtopology X S) mtopology f \<or> t1_space X \<and> f ` S \<subseteq> M"
  shows "gdelta_in X {x \<in> topspace X. \<exists>l. limitin mtopology f l (atin_within X x S)}"
proof -
  have fim: "f ` (topspace X \<inter> S) \<subseteq> M"
    using continuous_map_image_subset_topspace f by fastforce
  show ?thesis
  proof (cases "M={}")
    case True
    then show ?thesis
      by (smt (verit) Collect_cong empty_def empty_iff gdelta_in_empty limitin_mspace)
  next
    case False
    define A where "A \<equiv> {x \<in> topspace X. \<forall>\<epsilon>>0. \<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>xa\<in>S \<inter> U - {x}. \<forall>y\<in>S \<inter> U - {x}. d (f xa) (f y) < \<epsilon>)}"
    have "gdelta_in X A"
      using f 
    proof (elim disjE conjE)
      assume cm: "continuous_map (subtopology X S) mtopology f"
      define B where "B \<equiv> topspace X \<inter> (\<Inter>n. \<Union>{U. openin X U \<and> (\<forall>x \<in> S\<inter>U. \<forall>y \<in> S\<inter>U. d (f x) (f y) < inverse(Suc n))})"
      have "gdelta_in X B"
        unfolding B_def gdelta_in_def
        by (intro relative_to_inc countable_intersection_of_Inter countable_intersection_of_inc) auto
      moreover have "A=B"
      proof -
        have *: "\<exists>T. (openin X T \<and> (\<forall>x y. x \<in> S \<longrightarrow> x \<in> T \<longrightarrow> y \<in> S \<longrightarrow> y \<in> T \<longrightarrow> d (f x) (f y) < \<epsilon>)) \<and> a \<in> T" 
          if "openin X U" "a \<in> U" "a \<in> topspace X" "\<epsilon> > 0"
            and U: "\<And>x y. x \<in> S \<and> x \<in> U \<and> x\<noteq>a \<and> y \<in> S \<and> y \<in> U \<and> y \<noteq> a \<Longrightarrow> d (f x) (f y) < \<epsilon>"
          for U a and \<epsilon>::real
        proof (cases "a \<in> S")
          case True
          then obtain V where "openin X V" "a \<in> V" and V: "\<forall>x. x \<in> S \<and> x \<in> V \<longrightarrow> f a \<in> M \<and> f x \<in> M \<and> d (f a) (f x) < \<epsilon>"
            using \<open>a \<in> topspace X\<close> \<open>\<epsilon> > 0\<close> cm   
            by (force simp add: continuous_map_to_metric openin_subtopology_alt Ball_def)
          show ?thesis
          proof (intro exI conjI strip)
            show "openin X (U \<inter> V)"
              using \<open>openin X V\<close> that by blast
            show "a \<in> U \<inter> V"
              by (simp add: \<open>a \<in> V\<close> that)
            show "\<And>x y. \<lbrakk>x \<in> S; x \<in> U \<inter> V; y \<in> S; y \<in> U \<inter> V\<rbrakk> \<Longrightarrow> d (f x) (f y) < \<epsilon>"
              by (metis Int_iff U V commute)
          qed
        next
          case False then show ?thesis
            using U that by blast
        qed
        show ?thesis
        proof (intro equalityI subsetI)
          fix x
          assume x: "x \<in> A"
          then have "x \<in> topspace X"
            using A_def by blast
          show "x \<in> B"
          proof (clarsimp simp: B_def \<open>x \<in> topspace X\<close>)
            fix n
            obtain U where "openin X U \<and> x \<in> U \<and> (\<forall>xa\<in>S \<inter> U - {x}. \<forall>y\<in>S \<inter> U - {x}. d (f xa) (f y) < inverse (1 + real n))"
              using x by (force simp: A_def)
            show "\<exists>U. openin X U \<and> (\<forall>x\<in>S \<inter> U. \<forall>y\<in>S \<inter> U. d (f x) (f y) < inverse (1 + real n)) \<and> x \<in> U"

              sorry
          qed
        next
          fix x
          assume x: "x \<in> B"
          then have "x \<in> topspace X"
            using B_def by blast
          show "x \<in> A"
          proof (clarsimp simp: A_def \<open>x \<in> topspace X\<close>)
            fix \<epsilon> :: real
            assume "\<epsilon> > 0"
            then obtain n where "inverse (Suc n) < \<epsilon>"
              using reals_Archimedean by blast
            with x 
            show "\<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>xa\<in>S \<inter> U - {x}. \<forall>y\<in>S \<inter> U - {x}. d (f xa) (f y) < \<epsilon>)"
              apply (simp add: B_def)
              by (smt (verit, ccfv_threshold) DiffD1)
          qed
        qed
      qed
      ultimately show ?thesis
        by metis
    next
      assume "t1_space X" "f ` S \<subseteq> M"
      define B where "B \<equiv> topspace X \<inter> (\<Inter>n. \<Union>{U. openin X U \<and> 
                           (\<exists>b \<in> topspace X. \<forall>x \<in> S\<inter>U - {b}. \<forall>y \<in> S\<inter>U - {b}. d (f x) (f y) < inverse(Suc n))})"
      have "gdelta_in X B"
        unfolding B_def gdelta_in_def
        by (intro relative_to_inc countable_intersection_of_Inter countable_intersection_of_inc) auto
      moreover have "A=B"
        sorry
      ultimately show ?thesis
        by metis
    qed
    then show ?thesis
      by (simp add: A_def convergent_eq_zero_oscillation_gen False fim \<open>mcomplete\<close> cong: conj_cong)
  qed
qed

oops
  GEN_REWRITE_TAC id [EXTENSION] THEN
  REWRITE_TAC[IN_INTER; INTERS_GSPEC; IN_ELIM_THM] THEN
  REWRITE_TAC[IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `a::A` THEN ASM_CASES_TAC `(a::A) \<in> topspace X` THEN
  ASM_REWRITE_TAC[] THEN
  W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand) FORALL_POS_MONO_1_EQ \<circ> rand \<circ> snd) THEN
  (ANTS_TAC THENL
    [MESON_TAC[REAL_LT_TRANS]; DISCH_THEN(SUBST1_TAC \<circ> SYM)]) THEN
  REWRITE_TAC[IN_INTER; IN_DELETE; IN_ELIM_THM] THENL
   [EQ_TAC THENL [DISCH_TAC; MESON_TAC[]] THEN
    X_GEN_TAC `e::real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `e::real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `U::A=>bool` STRIP_ASSUME_TAC) THEN


    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [CONTINUOUS_MAP_TO_METRIC]) THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `a::A`) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `e::real`) THEN
    ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_ALT; EXISTS_IN_GSPEC; IN_INTER] THEN
    REWRITE_TAC[IN_MBALL; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `v::A=>bool` THEN STRIP_TAC THEN
    EXISTS_TAC `U \<inter> v::A=>bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN
    MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x::A = a` THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `y::A = a` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[MDIST_SYM];
    EQ_TAC THENL [ASM_METIS_TAC[]; DISCH_TAC] THEN
    X_GEN_TAC `e::real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `e::real`) THEN
    ASM_REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM;
                    LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`U::A=>bool`; `b::A`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `b::A = a` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [t1_space]) THEN
    DISCH_THEN(MP_TAC \<circ> SPECL [`a::A`; `b::A`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v::A=>bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `U \<inter> v::A=>bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN ASM SET_TAC[]]);;



lemma gdelta_in_points_of_convergence_within:
  assumes Y: "completely_metrizable_space Y"
    and f: "continuous_map (subtopology X S) Y f \<or> t1_space X \<and> f ` S \<subseteq> topspace Y"
  shows "gdelta_in X {x \<in> topspace X. \<exists>l. limitin Y f l (atin_within X x S)}"
  using assms
  unfolding completely_metrizable_space_def
  by (smt (verit, del_insts) Collect_cong Metric_space.gdelta_in_points_of_convergence_within Metric_space.topspace_mtopology)



lemma Lavrentiev_extension_gen:
  assumes "S \<subseteq> topspace X" and Y: "completely_metrizable_space Y" 
    and contf: "continuous_map (subtopology X S) Y f"
  obtains U g where "gdelta_in X U" "S \<subseteq> U" 
            "continuous_map (subtopology X (X closure_of S \<inter> U)) Y g" 
             "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  define U where "U \<equiv> {x \<in> topspace X. \<exists>l. limitin Y f l (atin_within X x S)}"
  have "S \<subseteq> U"
    using that contf limit_continuous_map_within subsetD [OF \<open>S \<subseteq> topspace X\<close>] 
    by (fastforce simp: U_def)
  then have "S \<subseteq> X closure_of S \<inter> U"
    by (simp add: \<open>S \<subseteq> topspace X\<close> closure_of_subset)
  moreover
  have "\<And>t. t \<in> X closure_of S \<inter> U - S \<Longrightarrow> \<exists>l. limitin Y f l (atin_within X t S)"
    using U_def by blast
  moreover have "regular_space Y"
    by (simp add: Y completely_metrizable_imp_metrizable_space metrizable_imp_regular_space)
  ultimately
  obtain g where g: "continuous_map (subtopology X (X closure_of S \<inter> U)) Y g" 
    and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    using continuous_map_extension_pointwise_alt assms by blast 
  show thesis
  proof
    show "gdelta_in X U"
      by (simp add: U_def Y contf gdelta_in_points_of_convergence_within)
    show "continuous_map (subtopology X (X closure_of S \<inter> U)) Y g"
      by (simp add: g)
  qed (use \<open>S \<subseteq> U\<close> gf in auto)
qed

lemma Lavrentiev_extension:
  assumes "S \<subseteq> topspace X" 
    and X: "metrizable_space X \<or> topspace X \<subseteq> X closure_of S" 
    and Y: "completely_metrizable_space Y" 
    and contf: "continuous_map (subtopology X S) Y f"
  obtains U g where "gdelta_in X U" "S \<subseteq> U" "U \<subseteq> X closure_of S"
            "continuous_map (subtopology X U) Y g"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  obtain U g where "gdelta_in X U" "S \<subseteq> U" 
    and contg: "continuous_map (subtopology X (X closure_of S \<inter> U)) Y g" 
    and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
    using Lavrentiev_extension_gen Y assms(1) contf by blast
  define V where "V \<equiv> X closure_of S \<inter> U"
  show thesis
  proof
    show "gdelta_in X V"
      by (metis V_def X \<open>gdelta_in X U\<close> closed_imp_gdelta_in closedin_closure_of closure_of_subset_topspace gdelta_in_Int gdelta_in_topspace subset_antisym)
    show "S \<subseteq> V"
      by (simp add: V_def \<open>S \<subseteq> U\<close> assms(1) closure_of_subset)
    show "continuous_map (subtopology X V) Y g"
      by (simp add: V_def contg)
  qed (auto simp: gf V_def)
qed


subsection\<open>Embedding in products and hence more about completely metrizable spaces\<close>

lemma (in Metric_space) gdelta_homeomorphic_space_closedin_product:
  assumes S: "\<And>i. i \<in> I \<Longrightarrow> openin mtopology (S i)"
  obtains T where "closedin (prod_topology mtopology (powertop_real I)) T"
                  "subtopology mtopology (\<Inter>i \<in> I. S i) homeomorphic_space
                   subtopology (prod_topology mtopology (powertop_real I)) T"
proof (cases "I={}")
  case True
  then have top: "topspace (prod_topology mtopology (powertop_real I)) = (M \<times> {(\<lambda>x. undefined)})"
    by simp
  show ?thesis
  proof
    show "closedin (prod_topology mtopology (powertop_real I)) (M \<times> {(\<lambda>x. undefined)})"
      by (metis top closedin_topspace)
    have "subtopology mtopology (\<Inter>(S ` I)) homeomorphic_space mtopology"
      by (simp add: True product_topology_empty_discrete)
    also have "\<dots> homeomorphic_space (prod_topology mtopology (powertop_real {}))"
      by (metis PiE_empty_domain homeomorphic_space_sym prod_topology_homeomorphic_space_left topspace_product_topology)
    finally
    show "subtopology mtopology (\<Inter>(S ` I)) homeomorphic_space subtopology (prod_topology mtopology (powertop_real I)) (M \<times> {(\<lambda>x. undefined)})"
      by (smt (verit) True subtopology_topspace top)
  qed   
next
  case False
  have SM: "\<And>i. i \<in> I \<Longrightarrow> S i \<subseteq> M"
    using assms openin_mtopology by blast
  then have "(\<Inter>i \<in> I. S i) \<subseteq> M"
    using False by blast
  define dd where "dd \<equiv> \<lambda>i. if i\<notin>I \<or> S i = M then \<lambda>u. 1 else (\<lambda>u. INF x \<in> M - S i. d u x)"
  have [simp]: "bdd_below (d u ` A)" for u A
    by (meson bdd_belowI2 nonneg)
  have cont_dd: "continuous_map (subtopology mtopology (S i)) euclidean (dd i)" if "i \<in> I" for i
  proof -
    have "dist (Inf (d x ` (M - S i))) (Inf (d y ` (M - S i))) \<le> d x y" 
      if "x \<in> S i" "x \<in> M" "y \<in> S i" "y \<in> M" "S i \<noteq> M" for x y
    proof -
      have [simp]: "\<not> M \<subseteq> S i"
        using SM \<open>S i \<noteq> M\<close> \<open>i \<in> I\<close> by auto
      have "\<And>u. \<lbrakk>u \<in> M; u \<notin> S i\<rbrakk> \<Longrightarrow> Inf (d x ` (M - S i)) \<le> d x y + d y u"
        apply (clarsimp simp add: cInf_le_iff_less)
        by (smt (verit) DiffI triangle \<open>x \<in> M\<close> \<open>y \<in> M\<close>)
      then have "Inf (d x ` (M - S i)) - d x y \<le> Inf (d y ` (M - S i))"
        by (force simp add: le_cInf_iff)
      moreover
      have "\<And>u. \<lbrakk>u \<in> M; u \<notin> S i\<rbrakk> \<Longrightarrow> Inf (d y ` (M - S i)) \<le> d x u + d x y"
        apply (clarsimp simp add: cInf_le_iff_less)
        by (smt (verit) DiffI triangle'' \<open>x \<in> M\<close> \<open>y \<in> M\<close>)
      then have "Inf (d y ` (M - S i)) - d x y \<le> Inf (d x ` (M - S i))"
        by (force simp add: le_cInf_iff)
      ultimately show ?thesis
        by (simp add: dist_real_def abs_le_iff)
    qed
    then have *: "Lipschitz_continuous_map (submetric Self (S i)) euclidean_metric (\<lambda>u. Inf (d u ` (M - S i)))"
      unfolding Lipschitz_continuous_map_def by (force intro!: exI [where x=1])
    then show ?thesis
      using Lipschitz_continuous_imp_continuous_map [OF *]
      by (simp add: dd_def Self_def mtopology_of_submetric )
  qed 
  have dd_pos: "0 < dd i x" if "x \<in> S i" for i x
  proof (clarsimp simp add: dd_def)
    assume "i \<in> I" and "S i \<noteq> M"
    have opeS: "openin mtopology (S i)"
      by (simp add: \<open>i \<in> I\<close> assms)
    then obtain r where "r>0" and r: "\<And>y. \<lbrakk>y \<in> M; d x y < r\<rbrakk> \<Longrightarrow> y \<in> S i"
      by (meson \<open>x \<in> S i\<close> in_mball openin_mtopology subsetD)
    then have "\<And>y. y \<in> M - S i \<Longrightarrow> d x y \<ge> r"
      by (meson Diff_iff linorder_not_le)
    then have "Inf (d x ` (M - S i)) \<ge> r"
      by (meson Diff_eq_empty_iff SM \<open>S i \<noteq> M\<close> \<open>i \<in> I\<close> cINF_greatest set_eq_subset)
    with \<open>r>0\<close> show "0 < Inf (d x ` (M - S i))" by simp
  qed
  define f where "f \<equiv> \<lambda>x. (x, \<lambda>i\<in>I. inverse(dd i x))"
  define T where "T \<equiv> f ` (\<Inter>i \<in> I. S i)"
  show ?thesis
  proof
    show "closedin (prod_topology mtopology (powertop_real I)) T"
      unfolding closure_of_subset_eq [symmetric]
    proof
      show "T \<subseteq> topspace (prod_topology mtopology (powertop_real I))"
        using False SM by (auto simp: T_def f_def)

      have "(x,ds) \<in> T"
        if \<section>: "\<And>U. \<lbrakk>(x, ds) \<in> U; openin (prod_topology mtopology (powertop_real I)) U\<rbrakk> \<Longrightarrow> \<exists>y\<in>T. y \<in> U"
          and "x \<in> M" and ds: "ds \<in> I \<rightarrow>\<^sub>E UNIV" for x ds
      proof -
        have ope: "\<exists>x. x \<in> \<Inter>(S ` I) \<and> f x \<in> U \<times> V"
          if "x \<in> U" and "ds \<in> V" and "openin mtopology U" and "openin (powertop_real I) V" for U V
          using \<section> [of "U\<times>V"] that by (force simp add: T_def openin_prod_Times_iff)
        have x_in_INT: "x \<in> \<Inter>(S ` I)"
        proof clarify
          fix i
          assume "i \<in> I"
          show "x \<in> S i"
          proof (rule ccontr)
            assume "x \<notin> S i"
            have "openin (powertop_real I) {z \<in> topspace (powertop_real I). z i \<in> {ds i - 1 <..< ds i + 1}}"
            proof (rule openin_continuous_map_preimage)
              show "continuous_map (powertop_real I) euclidean (\<lambda>x. x i)"
                by (metis \<open>i \<in> I\<close> continuous_map_product_projection)
            qed auto
            then obtain y where "y \<in> S i" "y \<in> M" and dxy: "d x y < inverse (\<bar>ds i\<bar> + 1)"
                          and intvl: "inverse (dd i y) \<in> {ds i - 1 <..< ds i + 1}"
              using ope [of "mball x (inverse(abs(ds i) + 1))" "{z \<in> topspace(powertop_real I). z i \<in> {ds i - 1<..<ds i + 1}}"]
                    \<open>x \<in> M\<close> \<open>ds \<in> I \<rightarrow>\<^sub>E UNIV\<close> \<open>i \<in> I\<close>
              by (fastforce simp add: f_def)
            have "\<not> M \<subseteq> S i"
              using \<open>x \<notin> S i\<close> \<open>x \<in> M\<close> by blast
            have "inverse (\<bar>ds i\<bar> + 1) \<le> dd i y"
              using intvl \<open>y \<in> S i\<close> dd_pos [of y i]
              by (smt (verit, ccfv_threshold) greaterThanLessThan_iff inverse_inverse_eq le_imp_inverse_le)
            also have "\<dots> \<le> d x y"
              using \<open>i \<in> I\<close> \<open>\<not> M \<subseteq> S i\<close> \<open>x \<notin> S i\<close> \<open>x \<in> M\<close>
              apply (simp add: dd_def cInf_le_iff_less)
              using commute by force
            finally show False
              using dxy by linarith
          qed
        qed
        moreover have "ds = (\<lambda>i\<in>I. inverse (dd i x))"
        proof (rule PiE_ext [OF ds])
          fix i
          assume "i \<in> I"
          define e where "e \<equiv> \<bar>ds i - inverse (dd i x)\<bar>"
          { assume con: "e > 0"
            have "continuous_map (subtopology mtopology (S i)) euclidean (\<lambda>x. inverse (dd i x))" 
              using dd_pos cont_dd \<open>i \<in> I\<close> 
              by (fastforce simp:  intro!: continuous_map_real_inverse)
             then have "openin (subtopology mtopology (S i))
                         {z \<in> topspace (subtopology mtopology (S i)). 
                          inverse (dd i z) \<in> {inverse(dd i x) - e/2<..<inverse(dd i x) + e/2}}"
               using openin_continuous_map_preimage open_greaterThanLessThan open_openin by blast
             then obtain U where "openin mtopology U"
                  and U: "{z \<in> S i. inverse (dd i x) - e/2 < inverse (dd i z) \<and>
                           inverse (dd i z) < inverse (dd i x) + e/2}
                         = U \<inter> S i"
               using SM \<open>i \<in> I\<close>  by (auto simp: openin_subtopology)
             have "x \<in> U"
               using U x_in_INT \<open>i \<in> I\<close> con by fastforce
             have "ds \<in> {z \<in> topspace (powertop_real I). z i \<in> {ds i - e / 2<..<ds i + e/2}}"
               by (simp add: con ds)
             moreover
             have  "openin (powertop_real I) {z \<in> topspace (powertop_real I). z i \<in> {ds i - e / 2<..<ds i + e/2}}"
             proof (rule openin_continuous_map_preimage)
               show "continuous_map (powertop_real I) euclidean (\<lambda>x. x i)"
                 by (metis \<open>i \<in> I\<close> continuous_map_product_projection)
             qed auto
             ultimately obtain y where "y \<in> \<Inter>(S ` I) \<and> f y \<in> U \<times> {z \<in> topspace (powertop_real I). z i \<in> {ds i - e / 2<..<ds i + e/2}}"
               using ope \<open>x \<in> U\<close> \<open>openin mtopology U\<close> \<open>x \<in> U\<close>
               by presburger 
             with \<open>i \<in> I\<close> U 
             have False unfolding set_eq_iff f_def e_def by simp (smt (verit) field_sum_of_halves)
          }
          then show "ds i = (\<lambda>i\<in>I. inverse (dd i x)) i"
            using \<open>i \<in> I\<close> by (force simp: e_def)
        qed auto
        ultimately show ?thesis
          by (auto simp: T_def f_def)
      qed
      then show "prod_topology mtopology (powertop_real I) closure_of T \<subseteq> T"
        by (auto simp: closure_of_def)
    qed
    have eq: "(\<Inter>(S ` I) \<times> (I \<rightarrow>\<^sub>E UNIV) \<inter> f ` (M \<inter> \<Inter>(S ` I))) = (f ` \<Inter>(S ` I))"
      using False SM by (force simp: f_def image_iff)
    have "continuous_map (subtopology mtopology (\<Inter>(S ` I))) euclidean (dd i)" if "i \<in> I" for i
      by (meson INT_lower cont_dd continuous_map_from_subtopology_mono that)
    then have "continuous_map (subtopology mtopology (\<Inter>(S ` I))) (powertop_real I) (\<lambda>x. \<lambda>i\<in>I. inverse (dd i x))"
      using dd_pos by (fastforce simp: continuous_map_componentwise intro!: continuous_map_real_inverse)
    then have "embedding_map (subtopology mtopology (\<Inter>(S ` I))) (prod_topology (subtopology mtopology (\<Inter>(S ` I))) (powertop_real I)) f"
      by (simp add: embedding_map_graph f_def)
    moreover have "subtopology (prod_topology (subtopology mtopology (\<Inter>(S ` I))) (powertop_real I))
                     (f ` topspace (subtopology mtopology (\<Inter>(S ` I)))) =
                   subtopology (prod_topology mtopology (powertop_real I)) T"
      by (simp add: prod_topology_subtopology subtopology_subtopology T_def eq)
    ultimately
    show "subtopology mtopology (\<Inter>(S ` I)) homeomorphic_space subtopology (prod_topology mtopology (powertop_real I)) T"
      by (metis embedding_map_imp_homeomorphic_space)
  qed
qed


lemma gdelta_homeomorphic_space_closedin_product:
  assumes "metrizable_space X" and "\<And>i. i \<in> I \<Longrightarrow> openin X (S i)"
  obtains T where "closedin (prod_topology X (powertop_real I)) T"
                  "subtopology X (\<Inter>i \<in> I. S i) homeomorphic_space
                   subtopology (prod_topology X (powertop_real I)) T"
  using Metric_space.gdelta_homeomorphic_space_closedin_product
  by (metis assms metrizable_space_def)

lemma open_homeomorphic_space_closedin_product:
  assumes "metrizable_space X" and "openin X S"
  obtains T where "closedin (prod_topology X euclideanreal) T"
    "subtopology X S homeomorphic_space
                   subtopology (prod_topology X euclideanreal) T"
proof -
  obtain T where cloT: "closedin (prod_topology X (powertop_real {()})) T"
    and homT: "subtopology X S homeomorphic_space
                   subtopology (prod_topology X (powertop_real {()})) T"
    using gdelta_homeomorphic_space_closedin_product [of X "{()}" "\<lambda>i. S"] assms
    by auto
  have "prod_topology X (powertop_real {()}) homeomorphic_space prod_topology X euclideanreal"
    by (meson homeomorphic_space_prod_topology homeomorphic_space_refl homeomorphic_space_singleton_product)
  then obtain f where f: "homeomorphic_map (prod_topology X (powertop_real {()})) (prod_topology X euclideanreal) f"
    unfolding homeomorphic_space by metis
  show thesis
  proof
    show "closedin (prod_topology X euclideanreal) (f ` T)"
      using cloT f homeomorphic_map_closedness_eq by blast
    moreover have "T = topspace (subtopology (prod_topology X (powertop_real {()})) T)"
      by (metis cloT closedin_subset topspace_subtopology_subset)
    ultimately show "subtopology X S homeomorphic_space subtopology (prod_topology X euclideanreal) (f ` T)"
      by (smt (verit, best) closedin_subset f homT homeomorphic_map_subtopologies homeomorphic_space 
          homeomorphic_space_trans topspace_subtopology topspace_subtopology_subset)
  qed
qed

lemma completely_metrizable_space_gdelta_in_alt:
  assumes X: "completely_metrizable_space X" 
    and S: "(countable intersection_of openin X) S"
  shows "completely_metrizable_space (subtopology X S)"
proof -
  obtain \<U> where "countable \<U>" "S = \<Inter>\<U>" and ope: "\<And>U. U \<in> \<U> \<Longrightarrow> openin X U"
    using S by (force simp add: intersection_of_def)
  then have \<U>: "completely_metrizable_space (powertop_real \<U>)"
    by (simp add: completely_metrizable_space_euclidean completely_metrizable_space_product_topology)
  obtain C where "closedin (prod_topology X (powertop_real \<U>)) C"
                and sub: "subtopology X (\<Inter>\<U>) homeomorphic_space
                   subtopology (prod_topology X (powertop_real \<U>)) C"
    by (metis gdelta_homeomorphic_space_closedin_product  X completely_metrizable_imp_metrizable_space ope INF_identity_eq)
  moreover have "completely_metrizable_space (prod_topology X (powertop_real \<U>))"
    by (simp add: completely_metrizable_space_prod_topology X \<U>)
  ultimately have "completely_metrizable_space (subtopology (prod_topology X (powertop_real \<U>)) C)"
    using completely_metrizable_space_closedin by blast
  then show ?thesis
    using \<open>S = \<Inter>\<U>\<close> sub homeomorphic_completely_metrizable_space by blast
qed

lemma completely_metrizable_space_gdelta_in:
   "\<lbrakk>completely_metrizable_space X; gdelta_in X S\<rbrakk>
        \<Longrightarrow> completely_metrizable_space (subtopology X S)"
  by (simp add: completely_metrizable_space_gdelta_in_alt gdelta_in_alt)

lemma completely_metrizable_space_openin:
   "\<lbrakk>completely_metrizable_space X; openin X S\<rbrakk>
        \<Longrightarrow> completely_metrizable_space (subtopology X S)"
  by (simp add: completely_metrizable_space_gdelta_in open_imp_gdelta_in)


lemma (in Metric_space) locally_compact_imp_completely_metrizable_space:
  assumes "locally_compact_space mtopology"
  shows "completely_metrizable_space mtopology"
proof -
  obtain f :: "['a,'a] \<Rightarrow> real" and m' where
    "mcomplete_of m'" and fim: "f ` M \<subseteq> mspace m' "
    and clo: "mtopology_of m' closure_of f ` M = mspace m'"
    and d: "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> mdist m' (f x) (f y) = d x y"
    by (meson metric_completion)
  then have "embedding_map mtopology (mtopology_of m') f"
    unfolding mtopology_of_def
    by (metis Metric_space12.isometry_imp_embedding_map Metric_space12_mspace_mdist mdist_metric mspace_metric)
  then have hom: "mtopology homeomorphic_space subtopology (mtopology_of m') (f ` M)"
    by (metis embedding_map_imp_homeomorphic_space topspace_mtopology)
  have "locally_compact_space (subtopology (mtopology_of m') (f ` M))"
    using assms hom homeomorphic_locally_compact_space by blast
  moreover have "Hausdorff_space (mtopology_of m')"
    by (simp add: Metric_space.Hausdorff_space_mtopology mtopology_of_def)
  ultimately have "openin (mtopology_of m') (f ` M)"
    by (simp add: clo dense_locally_compact_openin_Hausdorff_space fim)
  then
  have "completely_metrizable_space (subtopology (mtopology_of m') (f ` M))"
    using \<open>mcomplete_of m'\<close> unfolding mcomplete_of_def mtopology_of_def
    by (metis Metric_space.completely_metrizable_space_mtopology Metric_space_mspace_mdist completely_metrizable_space_openin )
  then show ?thesis
    using hom homeomorphic_completely_metrizable_space by blast
qed

lemma locally_compact_imp_completely_metrizable_space:
  assumes "metrizable_space X" and "locally_compact_space X"
  shows "completely_metrizable_space X"
  by (metis Metric_space.locally_compact_imp_completely_metrizable_space assms metrizable_space_def)


lemma completely_metrizable_space_imp_gdelta_in:
  assumes X: "metrizable_space X" and "S \<subseteq> topspace X" 
    and XS: "completely_metrizable_space (subtopology X S)"
  shows "gdelta_in X S"
proof -
  obtain U f where "gdelta_in X U" "S \<subseteq> U" and U: "U \<subseteq> X closure_of S"
            and contf: "continuous_map (subtopology X U) (subtopology X S) f" 
            and fid: "\<And>x. x \<in> S \<Longrightarrow> f x = x"
    using Lavrentiev_extension[of S X "subtopology X S" id] assms by auto
  then have "f ` topspace (subtopology X U) \<subseteq> topspace (subtopology X S)"
    using continuous_map_image_subset_topspace by blast
  then have "f`U \<subseteq> S"
    by (metis \<open>gdelta_in X U\<close> \<open>S \<subseteq> topspace X\<close> gdelta_in_subset topspace_subtopology_subset)
  moreover 
  have "Hausdorff_space (subtopology X U)"
    by (simp add: Hausdorff_space_subtopology X metrizable_imp_Hausdorff_space)
  then have "\<And>x. x \<in> U \<Longrightarrow> f x = x"
    using U fid contf forall_in_closure_of_eq [of _ "subtopology X U" S "subtopology X U" f id]
    by (metis \<open>S \<subseteq> U\<close> closure_of_subtopology_open continuous_map_id continuous_map_in_subtopology id_apply inf.orderE subtopology_subtopology)
  ultimately have "U \<subseteq> S"
    by auto
  then show ?thesis
    using \<open>S \<subseteq> U\<close> \<open>gdelta_in X U\<close> by auto
qed

lemma completely_metrizable_space_eq_gdelta_in:
   "\<lbrakk>completely_metrizable_space X; S \<subseteq> topspace X\<rbrakk>
        \<Longrightarrow> completely_metrizable_space (subtopology X S) \<longleftrightarrow> gdelta_in X S"
  using completely_metrizable_imp_metrizable_space completely_metrizable_space_gdelta_in completely_metrizable_space_imp_gdelta_in by blast

lemma gdelta_in_eq_completely_metrizable_space:
   "completely_metrizable_space X
    \<Longrightarrow> gdelta_in X S \<longleftrightarrow> S \<subseteq> topspace X \<and> completely_metrizable_space (subtopology X S)"
  by (metis completely_metrizable_space_eq_gdelta_in gdelta_in_alt)



text\<open> Basic definition of the small inductive dimension relation ind t \<le> n.    \<close>
text\<open> We plan to prove most of the theorems in R^n so this is as good a         \<close>
text\<open> definition as any other, but the present stuff works in any X space.    \<close>


parse_as_infix("dimension_le",(12,"right"));;

let DIMENSION_LE_RULES,DIMENSION_LE_INDUCT,DIMENSION_LE_CASES =
  new_inductive_definition
  `\<forall>X n.-1 \<le> n \<and>
           (\<forall>v a. openin X v \<and> a \<in> v
                  \<Longrightarrow> \<exists>u. a \<in> u \<and> u \<subseteq> v \<and> openin X u \<and>
                          subtopology X (X frontier_of u)
                          dimension_le (n - 1))
            \<Longrightarrow> X dimension_le (n::int)"

lemma dimension_le_neighbourhood_base:
   "\<And>X n.
        X dimension_le n \<longleftrightarrow>
 -1 \<le> n \<and>
        neighbourhood_base_of
         (\<lambda>u. openin X u \<and>
              (subtopology X (X frontier_of u))
              dimension_le (n - 1)) X"
oops
  REPEAT GEN_TAC THEN SIMP_TAC[OPEN_NEIGHBOURHOOD_BASE_OF] THEN
  GEN_REWRITE_TAC LAND_CONV [DIMENSION_LE_CASES] THEN MESON_TAC[]);;

lemma dimension_le_bound:
   "\<And>X: Atopology n. X dimension_le n \<Longrightarrow>-1 \<le> n"
oops
  MATCH_MP_TAC DIMENSION_LE_INDUCT THEN SIMP_TAC[]);;

lemma dimension_le_mono:
   "\<And>X: Atopology m n. X dimension_le m \<and> m \<le> n \<Longrightarrow> X dimension_le n"
oops
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC DIMENSION_LE_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`X: Atopology`; `m::int`] THEN STRIP_TAC THEN
  X_GEN_TAC `n::int` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC id [DIMENSION_LE_CASES] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INT_LE_TRANS]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v::A=>bool`; `a::A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`v::A=>bool`; `a::A`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_INT_ARITH_TAC);;

lemma dimension_le_eq_empty:
   "\<And>X: Atopology. X dimension_le (-1) \<longleftrightarrow> topspace X = {}"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[DIMENSION_LE_CASES] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SUBGOAL_THEN `\<forall>X::A topology. \<not> (X dimension_le -- 2)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN DISCH_THEN(MP_TAC \<circ> MATCH_MP DIMENSION_LE_BOUND) THEN
    INT_ARITH_TAC;
    EQ_TAC THENL
     [DISCH_THEN(MP_TAC \<circ> SPEC `topspace X::A=>bool`) THEN
      REWRITE_TAC[OPEN_IN_TOPSPACE] THEN SET_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET) THEN
      ASM SET_TAC[]]]);;

lemma dimension_le_0_neighbourhood_base_of_clopen:
   "X dimension_le 0 \<longleftrightarrow>
        neighbourhood_base_of (\<lambda>u. closedin X u \<and> openin X u) X"
oops
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [DIMENSION_LE_NEIGHBOURHOOD_BASE] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[DIMENSION_LE_EQ_EMPTY; TOPSPACE_SUBTOPOLOGY] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  SIMP_TAC[FRONTIER_OF_SUBSET_TOPSPACE; SET_RULE
   `s \<subseteq> u \<Longrightarrow> u \<inter> s = s`] THEN
  MESON_TAC[FRONTIER_OF_EQ_EMPTY; OPEN_IN_SUBSET]);;

lemma dimension_le_subtopology:
   "\<And>X n s::A=>bool.
        X dimension_le n \<Longrightarrow> (subtopology X s) dimension_le n"
oops
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC DIMENSION_LE_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`X::A topology`; `n::int`] THEN STRIP_TAC THEN
  X_GEN_TAC `s::A=>bool` THEN GEN_REWRITE_TAC id [DIMENSION_LE_CASES] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`u':A=>bool`; `a::A`] THEN
  GEN_REWRITE_TAC (LAND_CONV \<circ> LAND_CONV) [OPEN_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u::A=>bool` THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`u::A=>bool`; `a::A`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `v::A=>bool` THEN STRIP_TAC THEN
  EXISTS_TAC `s \<inter> v::A=>bool` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN ASM_MESON_TAC[INTER_COMM];
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC
     `subtopology X s frontier_of (s \<inter> v):A=>bool`) THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `s \<subseteq> u \<and> s \<subseteq> t \<Longrightarrow> t \<inter> s = u \<inter> s`) THEN
    REWRITE_TAC[FRONTIER_OF_SUBSET_SUBTOPOLOGY] THEN
    REWRITE_TAC[FRONTIER_OF_CLOSURES; CLOSURE_OF_SUBTOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; INTER_ASSOC] THEN
    MATCH_MP_TAC(SET_RULE
     `t \<subseteq> u \<and> v \<subseteq> w
      \<Longrightarrow> s \<inter> t \<inter> s \<inter> v \<subseteq> u \<inter> w`) THEN
    CONJ_TAC THEN MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[]]);;

lemma dimension_le_subtopologies:
   "\<And>X n s t::A=>bool.
        s \<subseteq> t \<and>
        subtopology X t dimension_le n
        \<Longrightarrow> (subtopology X s) dimension_le n"
oops
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC \<circ>
    ISPEC `s::A=>bool` \<circ> MATCH_MP DIMENSION_LE_SUBTOPOLOGY) THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[SET_RULE `s \<subseteq> t \<Longrightarrow> t \<inter> s = s`]);;

lemma dimension_le_eq_subtopology:
   "\<And>X s::A=>bool n.
        (subtopology X s) dimension_le n \<longleftrightarrow>
 -1 \<le> n \<and>
        \<forall>v a. openin X v \<and> a \<in> v \<and> a \<in> s
              \<Longrightarrow> \<exists>u. a \<in> u \<and> u \<subseteq> v \<and> openin X u \<and>
                      subtopology X
                       ((subtopology X s frontier_of (s \<inter> u)))
                      dimension_le (n - 1)"
oops
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [DIMENSION_LE_CASES] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; OPEN_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(\<forall>v a t. (P t \<and> Q v t) \<and> R a v t \<Longrightarrow> S a v t) \<longleftrightarrow>
    (\<forall>t a v. Q v t \<Longrightarrow> P t \<and> R a v t \<Longrightarrow> S a v t)`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
  X_GEN_TAC `v::A=>bool` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
  X_GEN_TAC `a::A` THEN REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC(TAUT `(p \<Longrightarrow> (q \<longleftrightarrow> r)) \<Longrightarrow> (p \<Longrightarrow> q \<longleftrightarrow> p \<Longrightarrow> r)`) THEN
  STRIP_TAC THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT
    `p \<and> q \<and> (r \<and> s) \<and> t \<longleftrightarrow> s \<and> p \<and> q \<and> r \<and> t`] THEN
  ASM_REWRITE_TAC[UNWIND_THM2; IN_INTER] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `u::A=>bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u \<inter> v::A=>bool` THEN
  ASM_SIMP_TAC[IN_INTER; OPEN_IN_INTER] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  ASM_SIMP_TAC[SET_RULE `u \<subseteq> v \<Longrightarrow> u \<inter> v = u`;
               SET_RULE `u \<inter> s \<subseteq> v \<inter> s
                         \<Longrightarrow> s \<inter> u \<inter> v = s \<inter> u`] THEN
  POP_ASSUM_LIST(MP_TAC \<circ> end_itlist CONJ \<circ> rev) THEN
  ASM_SIMP_TAC[FRONTIER_OF_SUBSET_SUBTOPOLOGY;
               SET_RULE `v \<subseteq> u \<Longrightarrow> u \<inter> v = v`] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]);;

lemma homeomorphic_space_dimension_le:
   "\<And>X (Y:B topology) n.
        X homeomorphic_space Y
        \<Longrightarrow> (X dimension_le n \<longleftrightarrow> Y dimension_le n)"
oops
  lemma lemma:
   "\<And>n X (Y:B topology).
        X homeomorphic_space Y \<and> X dimension_le (n - 1)
        \<Longrightarrow> Y dimension_le (n - 1)"
oops
    INDUCT_TAC THENL
     [CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[DIMENSION_LE_EQ_EMPTY] THEN
      MESON_TAC[HOMEOMORPHIC_EMPTY_SPACE];
      REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ARITH `(x + y) - y::int = x`]] THEN
    MAP_EVERY X_GEN_TAC [`X::A topology`; `Y:B topology`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC[DIMENSION_LE_CASES] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [homeomorphic_space]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f::A=>B`; `g::B=>A`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`v::B=>bool`; `b::B`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`image (g::B=>A) v`; `(g::B=>A) b`]) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[HOMEOMORPHIC_MAPS_MAP; HOMEOMORPHIC_IMP_OPEN_MAP;
                    open_map; FUN_IN_IMAGE];
      DISCH_THEN(X_CHOOSE_THEN `u::A=>bool` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `image f u` THEN REPEAT CONJ_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[homeomorphic_maps; continuous_map]) THEN
      ASM SET_TAC[];
      REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[homeomorphic_maps; continuous_map]) THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[HOMEOMORPHIC_MAPS_MAP; HOMEOMORPHIC_MAP_OPENNESS_EQ];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `subtopology X (X frontier_of u::A=>bool)` THEN
      ASM_REWRITE_TAC[homeomorphic_space] THEN
      MAP_EVERY EXISTS_TAC [`f::A=>B`; `g::B=>A`] THEN
      MATCH_MP_TAC HOMEOMORPHIC_MAPS_SUBTOPOLOGIES THEN
      ASM_SIMP_TAC[FRONTIER_OF_SUBSET_TOPSPACE; SET_RULE
       `s \<subseteq> t \<Longrightarrow> t \<inter> s = s`] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC HOMEOMORPHIC_MAP_FRONTIER_OF THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; HOMEOMORPHIC_MAPS_MAP]])
in

  REPEAT STRIP_TAC THEN ASM_CASES_TAC `-1::int \<le> n` THENL
   [ALL_TAC; ASM_MESON_TAC[DIMENSION_LE_BOUND]] THEN
  SUBST1_TAC(INT_ARITH `n::int = (Suc n) - 1`) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP
   (INT_ARITH `-x::int \<le> y \<Longrightarrow> 0 \<le> y + x`)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n::num` THEN DISCH_THEN SUBST1_TAC THEN
  EQ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] lemma) THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SPACE_SYM]);;

lemma dimension_le_retraction_map_image:
   "\<And>X Y n r.
        retraction_map X Y r \<and> X dimension_le n
        \<Longrightarrow> Y dimension_le n"
oops
  GEN_REWRITE_TAC id [MESON[] `(\<forall>x y z. P x y z) \<longleftrightarrow> (\<forall>z x y. P x y z)`] THEN
  GEN_TAC THEN MATCH_MP_TAC HEREDITARY_IMP_RETRACTIVE_PROPERTY THEN
  REWRITE_TAC[DIMENSION_LE_SUBTOPOLOGY; HOMEOMORPHIC_SPACE_DIMENSION_LE]);;

lemma dimension_le_discrete_topology:
   "\<And>u::A=>bool. (discrete_topology u) dimension_le 0"
oops
  GEN_TAC THEN ONCE_REWRITE_TAC[DIMENSION_LE_CASES] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[OPEN_IN_DISCRETE_TOPOLOGY; DISCRETE_TOPOLOGY_FRONTIER_OF] THEN
  REWRITE_TAC[DIMENSION_LE_EQ_EMPTY; TOPSPACE_SUBTOPOLOGY; INTER_EMPTY] THEN
  SET_TAC[]);;

lemma zero_dimensional_imp_completely_regular_space:
   "X dimension_le 0 \<Longrightarrow> completely_regular_space X"
oops
  GEN_TAC THEN REWRITE_TAC[DIMENSION_LE_0_NEIGHBOURHOOD_BASE_OF_CLOPEN] THEN
  SIMP_TAC[OPEN_NEIGHBOURHOOD_BASE_OF] THEN DISCH_TAC THEN
  REWRITE_TAC[completely_regular_space; IN_DIFF] THEN
  MAP_EVERY X_GEN_TAC [`c::A=>bool`; `a::A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`topspace X - c::A=>bool`; `a::A`]) THEN
  ASM_SIMP_TAC[IN_DIFF; OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(X_CHOOSE_THEN `u::A=>bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(\<lambda>x. if x \<in> u then 0 else 1):A=>real` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; \<subseteq>; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[ENDS_IN_UNIT_REAL_INTERVAL]] THEN
  REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
  X_GEN_TAC `r::real=>bool` THEN DISCH_TAC THEN REWRITE_TAC[TAUT
    `(if p then a else b) \<in> r \<longleftrightarrow> p \<and> a \<in> r \<or> \<not> p \<and> b \<in> r`] THEN
  MAP_EVERY ASM_CASES_TAC [`(0::real) \<in> r`; `(1::real) \<in> r`] THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; OPEN_IN_EMPTY; OPEN_IN_TOPSPACE;
                  IN_GSPEC; TAUT `p \<or> \<not> p`] THEN
  ASM_REWRITE_TAC[GSYM -; GSYM \<inter>] THEN
  ASM_SIMP_TAC[OPEN_IN_TOPSPACE; OPEN_IN_INTER; OPEN_IN_DIFF]);;

lemma zero_dimensional_imp_regular_space:
   "X dimension_le 0 \<Longrightarrow> regular_space X"
oops
  MESON_TAC[COMPLETELY_REGULAR_IMP_REGULAR_SPACE;
            ZERO_DIMENSIONAL_IMP_COMPLETELY_REGULAR_SPACE]);;


subsection\<open> Theorems from Kuratowski's "Remark on an Invariance Theorem"\<close>
(* Fundamenta Mathematicae vol 37 (1950), pp. 251-252. The idea is that in suitable     *)
(* spaces, to show "number of components of the complement" (without         *)
(* distinguishing orders of infinity) is a homeomorphic invariant, it        *)
text\<open> suffices to show it for closed subsets. Kuratowski states the main result \<close>
text\<open> for a "locally connected continuum", and seems clearly to be implicitly   \<close>
text\<open> assuming that means metrizable. We call out the general topological       \<close>
text\<open> hypotheses more explicitly, which do not however include connectedness.   \<close>


lemma separation_by_closed_intermediates_count:
   "\<And>X s n.
        hereditarily normal_space X \<and>
        (\<exists>u. u HAS_SIZE n \<and>
             pairwise (separatedin X) u \<and>
             (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
             \<Union>u = topspace X - s)
        \<Longrightarrow>  \<exists>c. closedin X c \<and> c \<subseteq> s \<and>
                 \<forall>d. closedin X d \<and> c \<subseteq> d \<and> d \<subseteq> s
                     \<Longrightarrow> \<exists>u. u HAS_SIZE n \<and>
                             pairwise (separatedin X) u \<and>
                             (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
                             \<Union>u = topspace X - d"
oops
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `u:(A=>bool)->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `u:(A=>bool)->bool` \<circ>
    GEN_REWRITE_RULE id [HEREDITARILY_NORMAL_SEPARATION_PAIRWISE]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `f:(A=>bool)->(A=>bool)` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC
   `topspace X - \<Union>(image (f:(A=>bool)->(A=>bool)) u)` THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE; OPEN_IN_UNIONS;
               FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `c::A=>bool` THEN STRIP_TAC THEN
  EXISTS_TAC `image (\<lambda>s. (f:(A=>bool)->(A=>bool)) s - c) u` THEN
  REWRITE_TAC[PAIRWISE_IMAGE; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[pairwise; SEPARATED_IN_OPEN_SETS; OPEN_IN_DIFF] THEN
  MATCH_MP_TAC(TAUT `d \<and> c \<and> b \<and> (c \<Longrightarrow> a) \<Longrightarrow> a \<and> b \<and> c \<and> d`) THEN
  REPEAT CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[UNIONS_IMAGE; OPEN_IN_CLOSED_IN_EQ]) THEN
    REWRITE_TAC[UNIONS_IMAGE] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [pairwise]) THEN
    REWRITE_TAC[] THEN ASM SET_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [pairwise]) THEN
    ASM SET_TAC[]]);;

lemma separation_by_closed_intermediates_gen:
   "\<And>X s.
        hereditarily normal_space X \<and>
        \<not> connectedin X (topspace X - s)
        \<Longrightarrow>  \<exists>c. closedin X c \<and> c \<subseteq> s \<and>
                 \<forall>d. closedin X d \<and> c \<subseteq> d \<and> d \<subseteq> s
                     \<Longrightarrow> \<not> connectedin X (topspace X - d)"
oops
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`X::A topology`; `s::A=>bool`; `2`]
    SEPARATION_BY_CLOSED_INTERMEDIATES_COUNT) THEN
  REWRITE_TAC[MESON[HAS_SIZE_CONV `s HAS_SIZE 2`]
   `(\<exists>s. s HAS_SIZE 2 \<and> P s) \<longleftrightarrow> (\<exists>a b. (a \<noteq> b) \<and> P{a,b})`] THEN
  REWRITE_TAC[PAIRWISE_INSERT; UNIONS_2; FORALL_IN_INSERT; NOT_IN_EMPTY;
              IMP_CONJ; NOT_IN_EMPTY; PAIRWISE_EMPTY] THEN
  REWRITE_TAC[MESON[SEPARATED_IN_SYM]
   `(a \<noteq> b) \<and>
    ((b \<noteq> a) \<Longrightarrow> separatedin X a b \<and> separatedin X b a) \<and> Q \<longleftrightarrow>
    (a \<noteq> b) \<and> separatedin X a b \<and> Q`] THEN
  REWRITE_TAC[MESON[SEPARATED_IN_REFL]
   `(a \<noteq> b) \<and> separatedin X a b \<and>
    ((a \<noteq> {}) \<and> (b \<noteq> {})) \<and> a \<union> b = s \<longleftrightarrow>
    a \<union> b = s \<and> (a \<noteq> {}) \<and> (b \<noteq> {}) \<and> separatedin X a b`] THEN
  REWRITE_TAC[CONNECTED_IN_EQ_NOT_SEPARATED; IMP_IMP; SUBSET_DIFF] THEN
  SIMP_TAC[]);;

lemma separation_by_closed_intermediates_eq_count:
   "\<And>X s n.
        locally_connected_space X \<and> hereditarily normal_space X
        \<Longrightarrow> ((\<exists>u. u HAS_SIZE n \<and>
                  pairwise (separatedin X) u \<and>
                  (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
                  \<Union>u = topspace X - s) \<longleftrightarrow>
             (\<exists>c. closedin X c \<and> c \<subseteq> s \<and>
                  \<forall>d. closedin X d \<and> c \<subseteq> d \<and> d \<subseteq> s
                      \<Longrightarrow> \<exists>u. u HAS_SIZE n \<and>
                              pairwise (separatedin X) u \<and>
                              (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
                              \<Union>u = topspace X - d))"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC(ONCE_REWRITE_RULE [IMP_CONJ]
        SEPARATION_BY_CLOSED_INTERMEDIATES_COUNT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[HAS_SIZE_0; UNWIND_THM2; NOT_IN_EMPTY; UNIONS_0] THEN
    REWRITE_TAC[PAIRWISE_EMPTY] THEN SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `c::A=>bool` THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(LABEL_TAC "*") THEN
  ABBREV_TAC
   `u = {d::A=>bool | d \<in> connected_components_of
                           (subtopology X (topspace X - c)) \<and>
                     \<not> (d - s = {})}` THEN
  SUBGOAL_THEN `\<forall>t::A=>bool. t \<in> u \<Longrightarrow> openin X t` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `d::A=>bool` THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE) \<circ>
     CONJUNCT1) THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY; OPEN_IN_DIFF;
                 OPEN_IN_TOPSPACE] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    MATCH_MP_TAC LOCALLY_CONNECTED_SPACE_OPEN_SUBSET THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `\<forall>t::A=>bool. t \<in> u \<Longrightarrow> (t \<noteq> {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pairwise disjnt (u:(A=>bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MP_TAC(ISPEC
     `subtopology X (topspace X - c):A topology`
        PAIRWISE_DISJOINT_CONNECTED_COMPONENTS_OF) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] PAIRWISE_MONO) THEN
    REWRITE_TAC[SUBSET_RESTRICT];
    ALL_TAC] THEN
  SUBGOAL_THEN `finite(u:(A=>bool)->bool) \<and> card u < n`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[TAUT `p \<and> q \<longleftrightarrow> (p \<noteq>=> \<not> q)`] THEN
    REWRITE_TAC[NOT_LT] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CHOOSE_SUBSET_STRONG) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:(A=>bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `\<exists>t::A=>bool. t \<in> v` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[HAS_SIZE_0; HAS_SIZE];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC
     `(topspace X - s - \<Union>(v - {t})) insert
      image (\<lambda>d::A=>bool. d - s) (v - {t})`) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT
     `d \<and> c \<and> b \<and> (b \<and> c \<Longrightarrow> a) \<Longrightarrow> a \<and> b \<and> c \<and> d`) THEN
    REPEAT CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[UNIONS_IMAGE; OPEN_IN_CLOSED_IN_EQ]) THEN
      REWRITE_TAC[UNIONS_IMAGE; UNIONS_INSERT] THEN ASM SET_TAC[];
      REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      SUBGOAL_THEN `\<exists>a::A. a \<in> t \<and> (a \<notin> s)` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `a::A` THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `subtopology X (topspace X - c::A=>bool)`
         CONNECTED_COMPONENTS_OF_SUBSET) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPECL [`v:(A=>bool)->bool`; `{t::A=>bool}`]
        DIFF_UNIONS_PAIRWISE_DISJOINT) THEN
      ASM_REWRITE_TAC[SING_SUBSET; SET_RULE `s - {a} = s - {a}`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
      REWRITE_TAC[pairwise] THEN ASM SET_TAC[];
      MATCH_MP_TAC PAIRWISE_IMP THEN EXISTS_TAC
       `separatedin (subtopology X (topspace X - s):A topology)` THEN
      CONJ_TAC THENL [ALL_TAC; SIMP_TAC[SEPARATED_IN_SUBTOPOLOGY]] THEN
      MATCH_MP_TAC PAIRWISE_IMP THEN
      EXISTS_TAC `disjnt:(A=>bool)->(A=>bool)->bool` THEN CONJ_TAC THENL
       [REWRITE_TAC[PAIRWISE_INSERT; PAIRWISE_IMAGE] THEN
        REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; pairwise] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN ASM SET_TAC[];
        MATCH_MP_TAC(MESON[]
         `\<forall>P. (\<forall>x y. P x \<and> P y \<Longrightarrow> (R x y \<longleftrightarrow> Q x y)) \<and> (\<forall>x. x \<in> s \<Longrightarrow> P x)
          \<Longrightarrow> \<forall>x y. x \<in> s \<and> y \<in> s \<and> Q x y \<and> (x \<noteq> y) \<Longrightarrow> R x y`) THEN
        EXISTS_TAC
         `openin (subtopology X (topspace X - s):A topology)` THEN
        REWRITE_TAC[SEPARATED_IN_OPEN_SETS; FORALL_IN_INSERT] THEN
        REWRITE_TAC[FORALL_IN_IMAGE] THEN CONJ_TAC THENL
         [REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_SUBTOPOLOGY] THEN
          SIMP_TAC[SET_RULE `s \<inter> (s - t) = s - t`; SUBSET_DIFF] THEN
          REWRITE_TAC[SET_RULE `s - (s - t) = s \<inter> t`] THEN
          SUBGOAL_THEN
           `closedin (subtopology X (topspace X - c))
                      (\<Union>(v DELETE (t::A=>bool)))`
          MP_TAC THENL
           [MATCH_MP_TAC CLOSED_IN_UNIONS THEN CONJ_TAC THENL
             [ASM_MESON_TAC[FINITE_DELETE; HAS_SIZE]; ALL_TAC] THEN
            X_GEN_TAC `t':A=>bool` THEN STRIP_TAC THEN
            MATCH_MP_TAC CLOSED_IN_CONNECTED_COMPONENTS_OF THEN
            ASM SET_TAC[];
            REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
            MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]];
          X_GEN_TAC `t':A=>bool` THEN DISCH_TAC THEN
          REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EXISTS_TAC `t':A=>bool` THEN
          MATCH_MP_TAC(TAUT `p \<and> (p \<Longrightarrow> q) \<Longrightarrow> p \<and> q`) THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          DISCH_THEN(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]]];
      STRIP_TAC THEN
      FIRST_ASSUM(SUBST1_TAC \<circ> MATCH_MP (ARITH_RULE
       `(n \<noteq> 0) \<Longrightarrow> n = Suc(n - 1)`)) THEN
      REWRITE_TAC[HAS_SIZE_CLAUSES] THEN MATCH_MP_TAC(MESON[]
       `P s \<and> Q a s \<Longrightarrow> (\<exists>b t. P t \<and> Q b t \<and> insert a s = insert b t)`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN ASM SET_TAC[];
          RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
          ASM_SIMP_TAC[CARD_DELETE; HAS_SIZE; FINITE_DELETE]];
        REWRITE_TAC[SET_RULE
         `(y \<notin> f ` s) \<longleftrightarrow> \<forall>x. x \<in> s \<Longrightarrow> \<not> (f x = y)`] THEN
        GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
         `disjnt s t \<and> (s \<noteq> {}) \<Longrightarrow> (s \<noteq> t)`) THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        MATCH_MP_TAC SEPARATED_IN_IMP_DISJOINT THEN
        EXISTS_TAC `X::A topology` THEN
        RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC \<circ> SPEC `topspace X - \<Union>u::A=>bool`) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_UNIONS; CLOSED_IN_TOPSPACE];
    ASM_SIMP_TAC[CLOSED_IN_SUBSET; SET_RULE
     `c \<subseteq> u - s \<longleftrightarrow> c \<subseteq> u \<and> s \<inter> c = {}`] THEN
    REWRITE_TAC[INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM; IMP_CONJ] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    EXPAND_TAC "u" THEN REWRITE_TAC[UNIONS_GSPEC] THEN
    MP_TAC(ISPEC `subtopology X (topspace X - c):A topology`
        UNIONS_CONNECTED_COMPONENTS_OF) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
    ASM_SIMP_TAC[SET_RULE `s \<subseteq> u \<Longrightarrow> u - (u - s) = s`;
                 UNIONS_SUBSET; OPEN_IN_SUBSET] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:(A=>bool)->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `(v:(A=>bool)->bool) \<lesssim> (u:(A=>bool)->bool)` MP_TAC THENL
   [ALL_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC[CARD_LE_CARD; NOT_LE]] THEN
  MATCH_MP_TAC CARD_LE_RELATIONAL_FULL THEN
  EXISTS_TAC `\<lambda>(u::A=>bool) v. \<not> disjnt u v` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t::A=>bool`; `c1::A=>bool`; `c2::A=>bool`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `c1::A=>bool = c2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `connectedin X (t::A=>bool)` MP_TAC THENL
   [UNDISCH_TAC `(t::A=>bool) \<in> u` THEN EXPAND_TAC "u" THEN
    REWRITE_TAC[IN_ELIM_THM; IMP_CONJ_ALT] THEN DISCH_THEN(K ALL_TAC) THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP CONNECTED_IN_CONNECTED_COMPONENTS_OF) THEN
    SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
    REWRITE_TAC[CONNECTED_IN_EQ_NOT_SEPARATED_SUBSET]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`c1::A=>bool`; `\<Union>(v DELETE (c1::A=>bool))`] THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[SEPARATED_IN_UNIONS; FINITE_DELETE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
  REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[separatedin]);;

lemma separation_by_closed_intermediates_eq_gen:
   "\<And>X s.
        locally_connected_space X \<and> hereditarily normal_space X
        \<Longrightarrow> (\<not> connectedin X (topspace X - s) \<longleftrightarrow>
             \<exists>c. closedin X c \<and> c \<subseteq> s \<and>
                 \<forall>d. closedin X d \<and> c \<subseteq> d \<and> d \<subseteq> s
                     \<Longrightarrow> \<not> connectedin X (topspace X - d))"
oops
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`X::A topology`; `s::A=>bool`; `2`]
    SEPARATION_BY_CLOSED_INTERMEDIATES_EQ_COUNT) THEN
  REWRITE_TAC[MESON[HAS_SIZE_CONV `s HAS_SIZE 2`]
   `(\<exists>s. s HAS_SIZE 2 \<and> P s) \<longleftrightarrow> (\<exists>a b. (a \<noteq> b) \<and> P{a,b})`] THEN
  REWRITE_TAC[PAIRWISE_INSERT; UNIONS_2; FORALL_IN_INSERT; NOT_IN_EMPTY;
              IMP_CONJ; NOT_IN_EMPTY; PAIRWISE_EMPTY] THEN
  REWRITE_TAC[MESON[SEPARATED_IN_SYM]
   `(a \<noteq> b) \<and>
    ((b \<noteq> a) \<Longrightarrow> separatedin X a b \<and> separatedin X b a) \<and> Q \<longleftrightarrow>
    (a \<noteq> b) \<and> separatedin X a b \<and> Q`] THEN
  REWRITE_TAC[MESON[SEPARATED_IN_REFL]
   `(a \<noteq> b) \<and> separatedin X a b \<and>
    ((a \<noteq> {}) \<and> (b \<noteq> {})) \<and> a \<union> b = s \<longleftrightarrow>
    a \<union> b = s \<and> (a \<noteq> {}) \<and> (b \<noteq> {}) \<and> separatedin X a b`] THEN
  REWRITE_TAC[CONNECTED_IN_EQ_NOT_SEPARATED; IMP_IMP; SUBSET_DIFF] THEN
  SIMP_TAC[]);;

lemma kuratowski_component_number_invariance:
   "compact_space X \<and>
      Hausdorff_space X \<and>
      locally_connected_space X \<and>
      hereditarily normal_space X
      \<Longrightarrow> ((\<forall>s t n.
              closedin X s \<and> closedin X t \<and>
              (subtopology X s) homeomorphic_space (subtopology X t)
              \<Longrightarrow> (connected_components_of
                    (subtopology X (topspace X - s)) HAS_SIZE n \<longleftrightarrow>
                   connected_components_of
                    (subtopology X (topspace X - t)) HAS_SIZE n)) \<longleftrightarrow>
           (\<forall>s t n.
              (subtopology X s) homeomorphic_space (subtopology X t)
              \<Longrightarrow> (connected_components_of
                    (subtopology X (topspace X - s)) HAS_SIZE n \<longleftrightarrow>
                   connected_components_of
                    (subtopology X (topspace X - t)) HAS_SIZE n)))"
oops
  lemma lemma:
   "\<And>(R::A=>A->bool) (f::A=>B->bool).
          (\<forall>s t. R s t \<Longrightarrow> R t s)
          \<Longrightarrow> ((\<forall>s t n. R s t \<Longrightarrow> (f s HAS_SIZE n \<longleftrightarrow> f t HAS_SIZE n)) \<longleftrightarrow>
               (\<forall>n s t. R s t \<Longrightarrow> 1..n \<lesssim> f s \<Longrightarrow> 1..n \<lesssim> f t))"
oops
    REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
     `\<forall>s t n. R s t \<Longrightarrow> (1..n \<lesssim> (f::A=>B->bool) s \<longleftrightarrow> 1..n \<lesssim> f t)` THEN
    CONJ_TAC THENL [POP_ASSUM(K ALL_TAC); ASM_MESON_TAC[]] THEN
    REWRITE_TAC[HAS_SIZE; NUMSEG_CARD_LE] THEN EQ_TAC THENL
     [MESON_TAC[];
      REWRITE_TAC[ARITH_RULE `a = n \<longleftrightarrow> n \<le> a \<and> \<not> (n + 1 \<le> a)`] THEN
      MESON_TAC[]])
  and lemur = prove
   (`pairwise (separatedin (subtopology X (topspace X - s))) u \<and>
     (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
     \<Union>u = topspace(subtopology X (topspace X - s)) \<longleftrightarrow>
     pairwise (separatedin X) u \<and>
     (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
     \<Union>u = topspace X - s"
oops
    REWRITE_TAC[pairwise; SEPARATED_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    SET_TAC[])
in

  REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand) lemma \<circ> lhand \<circ> snd) THEN ANTS_TAC THENL
   [MESON_TAC[HOMEOMORPHIC_SPACE_SYM]; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand) lemma \<circ> rand \<circ> snd) THEN ANTS_TAC THENL
   [MESON_TAC[HOMEOMORPHIC_SPACE_SYM]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n::num` THEN
  REWRITE_TAC[CARD_LE_CONNECTED_COMPONENTS_ALT] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[lemur] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s::A=>bool`; `t::A=>bool`] THEN
  ONCE_REWRITE_TAC[SUBTOPOLOGY_RESTRICT] THEN
  ONCE_REWRITE_TAC[SET_RULE `s - t = s - s \<inter> t`] THEN
  MP_TAC(SET_RULE
   `topspace X \<inter> (s::A=>bool) \<subseteq> topspace X \<and>
    topspace X \<inter> (t::A=>bool) \<subseteq> topspace X`) THEN
  SPEC_TAC(`topspace X \<inter> (t::A=>bool)`,`t::A=>bool`) THEN
  SPEC_TAC(`topspace X \<inter> (s::A=>bool)`,`s::A=>bool`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand)
    SEPARATION_BY_CLOSED_INTERMEDIATES_EQ_COUNT \<circ> lhand \<circ> snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand)
    SEPARATION_BY_CLOSED_INTERMEDIATES_EQ_COUNT \<circ> rand \<circ> snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [homeomorphic_space]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; HOMEOMORPHIC_MAPS_MAP] THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`f::A=>A`; `g::A=>A`] THEN STRIP_TAC THEN
  X_GEN_TAC `c::A=>bool` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(LABEL_TAC "*") THEN EXISTS_TAC `image (f::A=>A) c` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology X (s::A=>bool)` THEN
    ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY; CLOSED_IN_COMPACT_SPACE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY]) THEN
    ASM SET_TAC[];
    X_GEN_TAC `d':A=>bool` THEN STRIP_TAC] THEN
  ABBREV_TAC `d = image (g::A=>A) d'` THEN
  SUBGOAL_THEN `closedin X (d::A=>bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "d" THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology X (t::A=>bool)` THEN
    ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY; CLOSED_IN_COMPACT_SPACE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c::A=>bool) \<subseteq> d \<and> d \<subseteq> s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC \<circ> SPEC `d::A=>bool`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[homeomorphic_space] THEN
  MAP_EVERY EXISTS_TAC [`f::A=>A`; `g::A=>A`] THEN
  SUBGOAL_THEN
   `subtopology X d::A topology = subtopology (subtopology X s) d \<and>
    subtopology X d':A topology = subtopology (subtopology X t) d'`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHIC_MAPS_SUBTOPOLOGIES] THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_MAPS_MAP] THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                              CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY]) THEN
  ASM SET_TAC[]);;




subsection\<open>A perfect set in common cases must have cardinality >= c\<close>


lemma card_ge_perfect_set:
   "(completely_metrizable_space X \<or>
         locally_compact_space X \<and> Hausdorff_space X) \<and>
        X derived_set_of s = s \<and> (s \<noteq> {})
        \<Longrightarrow> UNIV \<lesssim> s"
oops
  REWRITE_TAC[TAUT `(p \<or> q) \<and> r \<Longrightarrow> s \<longleftrightarrow>
                    (p \<Longrightarrow> r \<Longrightarrow> s) \<and> (q \<and> r \<Longrightarrow> s)`] THEN
  REWRITE_TAC[FORALL_AND_THM; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[GSYM FORALL_MCOMPLETE_TOPOLOGY] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS `(:num=>bool)` THEN
    SIMP_TAC[CARD_EQ_REAL; CARD_EQ_IMP_LE] THEN
    SUBGOAL_THEN `(s::A=>bool) \<subseteq> M` ASSUME_TAC THENL
     [ASM_MESON_TAC[DERIVED_SET_OF_SUBSET_TOPSPACE; TOPSPACE_MTOPOLOGY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `\<forall>x e. x \<in> s \<and> 0 < e
            \<Longrightarrow> \<exists>y z d. y \<in> s \<and> z \<in> s \<and> 0 < d \<and> d < e/2 \<and>
                        mcball y d \<subseteq> mcball x e \<and>
                        mcball z d \<subseteq> mcball x e \<and>
                        disjnt (mcball m (y::A,d)) (mcball z d)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`m::A metric`; `s::A=>bool`]
          DERIVED_SET_OF_INFINITE_MBALL) THEN
      ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `x::A`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC \<circ> SPEC `e / 4`)) THEN
      ASM_REWRITE_TAC[infinite; REAL_ARITH `0 < e / 4 \<longleftrightarrow> 0 < e`] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `x::A` \<circ> MATCH_MP
       (MESON[FINITE_RULES; FINITE_SUBSET]
         `\<not> finite s \<Longrightarrow> \<forall>a b c. \<not> (s \<subseteq> {a,b,c})`)) THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP (SET_RULE
       `(\<forall>b c. \<not> (s \<subseteq> {a,b,c}))
        \<Longrightarrow> \<exists>b c. b \<in> s \<and> c \<in> s \<and> (c \<noteq> a) \<and> (b \<noteq> a) \<and> (b \<noteq> c)`)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l::A` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r::A` THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      EXISTS_TAC `d l::A r / 3` THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [IN_MBALL])) THEN
      UNDISCH_TAC `\<not> (l::A = r)` THEN
      REWRITE_TAC[disjnt; \<subseteq>; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      ASM_SIMP_TAC[IN_MCBALL] THEN UNDISCH_TAC `(x::A) \<in> M` THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      REPEAT(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC METRIC_ARITH; ALL_TAC] THEN
      REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `y::A` THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [ALL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC METRIC_ARITH] THEN
      REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC \<circ> SPEC `e::real` \<circ> MATCH_MP
        (REAL_ARITH `x \<le> y / 3 \<Longrightarrow> \<forall>e. y < e/2 \<Longrightarrow> x < e / 6`)) THEN
      (ANTS_TAC THENL
        [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC METRIC_ARITH; ALL_TAC])
      THENL
       [UNDISCH_TAC `d x::A l < e / 4`;
        UNDISCH_TAC `d x::A r < e / 4`] THEN
      MAP_EVERY UNDISCH_TAC
       [`(x::A) \<in> M`; `(y::A) \<in> M`;
        `(l::A) \<in> M`; `(r::A) \<in> M`] THEN
      CONV_TAC METRIC_ARITH;
      REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC
     [`l::A=>real->A`; `r::A=>real->A`; `d::A=>real->real`] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `a::A` \<circ>
     REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    SUBGOAL_THEN
      `\<forall>b. \<exists>xe. xe 0 = (a::A,1) \<and>
                \<forall>n. xe(Suc n) = (if b n then r else l) (fst(xe n)) (snd(xe n)),
                                d (fst(xe n)) (snd(xe n))`
    MP_TAC THENL
     [GEN_TAC THEN
      W(ACCEPT_TAC \<circ> prove_recursive_functions_exist num_RECURSION \<circ>
          snd \<circ> dest_exists \<circ> snd);
      REWRITE_TAC[EXISTS_PAIR_FUN_THM; PAIR_EQ] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM]] THEN
    MAP_EVERY X_GEN_TAC
     [`x:(num=>bool)->num=>A`; `r:(num=>bool)->num=>real`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `mcomplete (submetric s::A metric)` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE THEN
      ASM_REWRITE_TAC[CLOSED_IN_CONTAINS_DERIVED_SET; TOPSPACE_MTOPOLOGY] THEN
      ASM SET_TAC[];
      REWRITE_TAC[MCOMPLETE_NEST_SING]] THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP MONO_FORALL \<circ> GEN `b::num=>bool` \<circ>
      SPEC `\<lambda>n. mcball (submetric s)
                       ((x:(num=>bool)->num=>A) b n,r b n)`) THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    SUBGOAL_THEN `(\<forall>b n. (x:(num=>bool)->num=>A) b n \<in> s) \<and>
                  (\<forall>b n. 0 < (r:(num=>bool)->num=>real) b n)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_LT_01] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\<forall>b n. (x:(num=>bool)->num=>A) b n \<in> M)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `b::num=>bool` THEN REWRITE_TAC[CLOSED_IN_MCBALL] THEN
      ASM_REWRITE_TAC[MCBALL_EQ_EMPTY; SUBMETRIC; IN_INTER] THEN
      ASM_SIMP_TAC[REAL_ARITH `0 < x \<Longrightarrow> \<not> (x < 0)`] THEN CONJ_TAC THENL
       [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
        REPEAT(CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
        ASM_REWRITE_TAC[MCBALL_SUBMETRIC_EQ] THEN ASM SET_TAC[];
        X_GEN_TAC `e::real` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`inverse 2`; `e::real`] REAL_ARCH_POW_INV) THEN
        ASM_REWRITE_TAC[REAL_POW_INV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n::num` THEN
        DISCH_TAC THEN EXISTS_TAC `(x:(num=>bool)->num=>A) b n` THEN
        MATCH_MP_TAC MCBALL_SUBSET_CONCENTRIC THEN
        TRANS_TAC REAL_LE_TRANS `inverse(2 ^ n)` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        SPEC_TAC(`n::num`,`n::num`) THEN
        MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[real_pow] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_INV_MUL] THEN
        GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `d < e/2 \<Longrightarrow> e \<le> i \<Longrightarrow> d \<le> inverse 2 * i`) THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[SKOLEM_THM; le_c; IN_UNIV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:(num=>bool)->A` THEN
      SIMP_TAC[SUBMETRIC; IN_INTER; FORALL_AND_THM] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [`b::num=>bool`; `c::num=>bool`] THEN
      GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[FUN_EQ_THM; NOT_FORALL_THM] THEN
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; TAUT `\<not> (p \<longleftrightarrow> q) \<longleftrightarrow> p \<longleftrightarrow> \<not> q`] THEN
      X_GEN_TAC `n::num` THEN REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC \<circ>
        GEN_REWRITE_RULE (BINDER_CONV \<circ> LAND_CONV) [INTERS_GSPEC]) THEN
      DISCH_THEN(fun th ->
       MP_TAC(SPEC `c::num=>bool` th) THEN MP_TAC(SPEC `b::num=>bool` th)) THEN
      ASM_REWRITE_TAC[TAUT `p \<Longrightarrow> \<not> q \<longleftrightarrow> \<not> (p \<and> q)`] THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP (SET_RULE
       `s = {a} \<and> t = {a} \<Longrightarrow> a \<in> s \<inter> t`)) THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; AND_FORALL_THM] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `Suc n`) THEN ASM_REWRITE_TAC[COND_SWAP] THEN
      SUBGOAL_THEN
       `(x:(num=>bool)->num=>A) b n = x c n \<and>
        (r:(num=>bool)->num=>real) b n = r c n`
       (CONJUNCTS_THEN SUBST1_TAC)
      THENL
       [UNDISCH_TAC `\<forall>m::num. m < n \<Longrightarrow> (b m \<longleftrightarrow> c m)` THEN
        SPEC_TAC(`n::num`,`p::num`) THEN
        INDUCT_TAC THEN ASM_SIMP_TAC[LT_SUC_LE; LE_REFL; LT_IMP_LE];
        COND_CASES_TAC THEN ASM_REWRITE_TAC[MCBALL_SUBMETRIC_EQ; IN_INTER] THEN
        ASM SET_TAC[]]];
    SUBGOAL_THEN
     `\<forall>X::A topology.
          locally_compact_space X \<and> Hausdorff_space X \<and>
          X derived_set_of topspace X = topspace X \<and> \<not> (topspace X = {})
          \<Longrightarrow> UNIV \<lesssim> topspace X`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC;
      MAP_EVERY X_GEN_TAC [`X::A topology`; `s::A=>bool`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> SPEC `subtopology X (s::A=>bool)`) THEN
      SUBGOAL_THEN `(s::A=>bool) \<subseteq> topspace X` ASSUME_TAC THENL
       [ASM_MESON_TAC[DERIVED_SET_OF_SUBSET_TOPSPACE]; ALL_TAC] THEN
      ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_SUBTOPOLOGY;
                   DERIVED_SET_OF_SUBTOPOLOGY; SET_RULE `s \<inter> s = s`;
                   SET_RULE `s \<subseteq> u \<Longrightarrow> u \<inter> s = s`] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC LOCALLY_COMPACT_SPACE_CLOSED_SUBSET THEN
      ASM_REWRITE_TAC[CLOSED_IN_CONTAINS_DERIVED_SET; SUBSET_REFL]] THEN
    TRANS_TAC CARD_LE_TRANS `(:num=>bool)` THEN
    SIMP_TAC[CARD_EQ_REAL; CARD_EQ_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `z::A`) THEN
    FIRST_ASSUM(MP_TAC \<circ> SPEC `z::A` \<circ> REWRITE_RULE[locally_compact_space]) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u::A=>bool`; `k::A=>bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `\<not> (u::A=>bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[];
      REPEAT(FIRST_X_ASSUM(K ALL_TAC \<circ> check (free_in `z::A`) \<circ> concl))] THEN
    SUBGOAL_THEN
     `\<forall>c. closedin X c \<and> c \<subseteq> k \<and> \<not> (X interior_of c = {})
          \<Longrightarrow> \<exists>d e. closedin X d \<and> d \<subseteq> k \<and>
                    \<not> (X interior_of d = {}) \<and>
                    closedin X e \<and> e \<subseteq> k \<and>
                    \<not> (X interior_of e = {}) \<and>
                    disjnt d e \<and> d \<subseteq> c \<and> e \<subseteq> (c::A=>bool)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_TAC `\<not> (X interior_of c::A=>bool = {})` THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `z::A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z::A) \<in> topspace X` ASSUME_TAC THENL
       [ASM_MESON_TAC[\<subseteq>; INTERIOR_OF_SUBSET_TOPSPACE]; ALL_TAC] THEN
      MP_TAC(ISPECL [`X::A topology`; `topspace X::A=>bool`]
            DERIVED_SET_OF_INFINITE_OPEN_IN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC \<circ> AP_TERM `\<lambda>s. (z::A) \<in> s`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `X interior_of c::A=>bool`) THEN
      ASM_SIMP_TAC[OPEN_IN_INTERIOR_OF; INTERIOR_OF_SUBSET_TOPSPACE;
                   SET_RULE `s \<subseteq> u \<Longrightarrow> u \<inter> s = s`] THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP (MESON[infinite; FINITE_SING; FINITE_SUBSET]
        `infinite s \<Longrightarrow> \<forall>a. \<not> (s \<subseteq> {a})`)) THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP (SET_RULE
       `(\<forall>a. \<not> (s \<subseteq> {a})) \<Longrightarrow> \<exists>a b. a \<in> s \<and> b \<in> s \<and> (a \<noteq> b)`)) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x::A) \<in> topspace X \<and> y \<in> topspace X`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[\<subseteq>; INTERIOR_OF_SUBSET_TOPSPACE]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC \<circ> SPECL [`x::A`; `y::A`] \<circ>
        REWRITE_RULE[Hausdorff_space]) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`v::A=>bool`; `w::A=>bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPEC `X::A topology`
        LOCALLY_COMPACT_HAUSDORFF_IMP_REGULAR_SPACE) THEN
      ASM_REWRITE_TAC[GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN] THEN
      REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN DISCH_THEN(fun th ->
        MP_TAC(SPECL [`X interior_of c \<inter> w::A=>bool`; `y::A`] th) THEN
        MP_TAC(SPECL [`X interior_of c \<inter> v::A=>bool`; `x::A`] th)) THEN
      ASM_SIMP_TAC[IN_INTER; OPEN_IN_INTER; OPEN_IN_INTERIOR_OF] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET_INTER] THEN
      MAP_EVERY X_GEN_TAC [`m::A=>bool`; `d::A=>bool`] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [`n::A=>bool`; `e::A=>bool`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`d::A=>bool`; `e::A=>bool`] THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[TAUT
       `p \<and> q \<and> r \<and> s \<and> t \<longleftrightarrow> (q \<and> s) \<and> p \<and> r \<and> t`] THEN
      CONJ_TAC THENL
       [CONJ_TAC THENL [EXISTS_TAC `x::A`; EXISTS_TAC `y::A`] THEN
        REWRITE_TAC[interior_of; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        MP_TAC(ISPECL [`X::A topology`; `c::A=>bool`] INTERIOR_OF_SUBSET) THEN
        ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`l:(A=>bool)->A=>bool`; `r:(A=>bool)->A=>bool`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `\<forall>b. \<exists>d::num=>A->bool.
          d 0 = k \<and>
          (\<forall>n. d(Suc n) = (if b n then r else l) (d n))`
    MP_TAC THENL
     [GEN_TAC THEN
      W(ACCEPT_TAC \<circ> prove_recursive_functions_exist num_RECURSION \<circ>
          snd \<circ> dest_exists \<circ> snd);
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM]] THEN
    X_GEN_TAC `d:(num=>bool)->num=>A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `\<forall>b n. closedin X (d b n) \<and> d b n \<subseteq> k \<and>
            \<not> (X interior_of ((d:(num=>bool)->num=>A->bool) b n) = {})`
    MP_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THENL
       [ASM_SIMP_TAC[SUBSET_REFL; COMPACT_IN_IMP_CLOSED_IN] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (SET_RULE
         `(u \<noteq> {}) \<Longrightarrow> u \<subseteq> i \<Longrightarrow> (i \<noteq> {})`)) THEN
        ASM_SIMP_TAC[INTERIOR_OF_MAXIMAL_EQ];
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
      REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     `\<forall>b. \<not> (\<Inter>{(d:(num=>bool)->num=>A->bool) b n | n \<in> UNIV} = {})`
    MP_TAC THENL
     [X_GEN_TAC `b::num=>bool` THEN MATCH_MP_TAC COMPACT_SPACE_IMP_NEST THEN
      EXISTS_TAC `subtopology X (k::A=>bool)` THEN
      ASM_SIMP_TAC[CLOSED_IN_SUBSET_TOPSPACE; COMPACT_SPACE_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[INTERIOR_OF_EMPTY]; ALL_TAC] THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
      REPEAT(CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
      ASM_SIMP_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `x:(num=>bool)->A` THEN
    REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN DISCH_TAC THEN
    REWRITE_TAC[le_c; IN_UNIV] THEN EXISTS_TAC `x:(num=>bool)->A` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CLOSED_IN_SUBSET; \<subseteq>]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`b::num=>bool`; `c::num=>bool`] THEN
    GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; NOT_FORALL_THM] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; TAUT `\<not> (p \<longleftrightarrow> q) \<longleftrightarrow> p \<longleftrightarrow> \<not> q`] THEN
    X_GEN_TAC `n::num` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `disjnt ((d:(num=>bool)->num=>A->bool) b (Suc n)) (d c (Suc n))`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_SIMP_TAC[COND_SWAP] THEN
    SUBGOAL_THEN `(d:(num=>bool)->num=>A->bool) b n = d c n` SUBST1_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[DISJOINT_SYM]] THEN
    UNDISCH_TAC `\<forall>m::num. m < n \<Longrightarrow> (b m \<longleftrightarrow> c m)` THEN
    SPEC_TAC(`n::num`,`p::num`) THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[LT_SUC_LE; LE_REFL; LT_IMP_LE]]);;


