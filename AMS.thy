section \<open>Abstract Metric Spaces\<close>

theory AMS
  imports
    "HOL-Analysis.Analysis" "HOL-Library.Equipollence"
    "HOL-ex.Sketch_and_Explore"
begin

(**must rename submetric in metric_spaces*)

(*REPLACE*****)
lemma real_le_lsqrt: "0 \<le> y \<Longrightarrow> x \<le> y\<^sup>2 \<Longrightarrow> sqrt x \<le> y"
  using real_sqrt_le_iff[of x "y\<^sup>2"] by simp

thm closed_compactin
lemma closed_compactin_Inter: "\<lbrakk>compactin X K; K \<in> \<K>; \<And>K. K \<in> \<K> \<Longrightarrow> closedin X K\<rbrakk> \<Longrightarrow> compactin X (\<Inter>\<K>)"
      by (metis Inf_lower closed_compactin closedin_Inter empty_iff)


lemma closedin_subtopology_Int_subset:
   "\<lbrakk>closedin (subtopology X U) (U \<inter> S); V \<subseteq> U\<rbrakk>
        \<Longrightarrow> closedin (subtopology X V) (V \<inter> S)"
  by (smt (verit, ccfv_SIG) closedin_subtopology inf.left_commute inf.orderE inf_commute)

lemma closedin_subtopology_Int_closedin:
   "\<lbrakk>closedin (subtopology X U) S; closedin X T\<rbrakk>
        \<Longrightarrow> closedin (subtopology X U) (S \<inter> T)"
  by (smt (verit, best) closedin_Int closedin_subtopology inf_assoc inf_commute)


thm deformation_retraction_imp_homotopy_equivalent_space
thm nullhomotopic_from_contractible_space

lemma homotopic_through_contractible_space:
   "continuous_map X Y f \<and>
        continuous_map X Y f' \<and>
        continuous_map Y Z g \<and>
        continuous_map Y Z g' \<and>
        contractible_space Y \<and> path_connected_space Z
        \<Longrightarrow> homotopic_with (\<lambda>h. True) X Z (g \<circ> f) (g' \<circ> f')"
  using nullhomotopic_through_contractible_space [of X Y f Z g]
  using nullhomotopic_through_contractible_space [of X Y f' Z g']
  by (metis continuous_map_const homotopic_constant_maps homotopic_with_imp_continuous_maps 
      homotopic_with_trans path_connected_space_iff_path_component homotopic_with_sym)

lemma homotopic_from_contractible_space:
   "continuous_map X Y f \<and> continuous_map X Y g \<and>
        contractible_space X \<and> path_connected_space Y
        \<Longrightarrow> homotopic_with (\<lambda>x. True) X Y f g"
  by (metis comp_id continuous_map_id homotopic_through_contractible_space)

lemma homotopic_into_contractible_space:
   "continuous_map X Y f \<and> continuous_map X Y g \<and>
        contractible_space Y
        \<Longrightarrow> homotopic_with (\<lambda>x. True) X Y f g"
  by (metis continuous_map_id contractible_imp_path_connected_space homotopic_through_contractible_space id_comp)


lemma empty_metrizable_space: "topspace X = {} \<Longrightarrow> metrizable_space X"
  by (metis metrizable_space_discrete_topology subtopology_eq_discrete_topology_empty)


typedef 'a metric = "{(M::'a set,d). Metric_space M d}"
  morphisms "dest_metric" "metric"
proof -
  have "Metric_space {} (\<lambda>x y. 0)"
    by (auto simp: Metric_space_def)
  then show ?thesis
    by blast
qed

definition mspace where "mspace m \<equiv> fst (dest_metric m)"

definition mdist where "mdist m \<equiv> snd (dest_metric m)"

lemma Metric_space_mspace_mdist: "Metric_space (mspace m) (mdist m)"
  by (metis Product_Type.Collect_case_prodD dest_metric mdist_def mspace_def)

lemma mdist_nonneg [simp]: "\<And>x y. 0 \<le> mdist m x y"
  by (metis Metric_space_def Metric_space_mspace_mdist)

lemma mdist_commute: "\<And>x y. mdist m x y = mdist m y x"
  by (metis Metric_space_def Metric_space_mspace_mdist)

lemma mdist_zero [simp]: "\<And>x y. \<lbrakk>x \<in> mspace m; y \<in> mspace m\<rbrakk> \<Longrightarrow> mdist m x y = 0 \<longleftrightarrow> x=y"
  by (meson Metric_space.zero Metric_space_mspace_mdist)

lemma mdist_triangle: "\<And>x y z. \<lbrakk>x \<in> mspace m; y \<in> mspace m; z \<in> mspace m\<rbrakk> \<Longrightarrow> mdist m x z \<le> mdist m x y + mdist m y z"
  by (meson Metric_space.triangle Metric_space_mspace_mdist)

lemma (in Metric_space) mspace_metric[simp]: 
  "mspace (metric (M,d)) = M"
  by (simp add: mspace_def Metric_space_axioms metric_inverse)

lemma (in Metric_space) mdist_metric[simp]: 
  "mdist (metric (M,d)) = d"
  by (simp add: mdist_def Metric_space_axioms metric_inverse)

lemma metric_collapse [simp]: "metric (mspace m, mdist m) = m"
  by (simp add: dest_metric_inverse mdist_def mspace_def)

definition mtopology_of :: "'a metric \<Rightarrow> 'a topology"
  where "mtopology_of \<equiv> \<lambda>m. Metric_space.mtopology (mspace m) (mdist m)"

lemma topspace_mtopology_of [simp]: "topspace (mtopology_of m) = mspace m"
  by (simp add: Metric_space.topspace_mtopology Metric_space_mspace_mdist mtopology_of_def)

lemma (in Metric_space) mtopology_of [simp]:
  "mtopology_of (metric (M,d)) = mtopology"
  by (simp add: mtopology_of_def)

definition "mball_of \<equiv> \<lambda>m. Metric_space.mball (mspace m) (mdist m)"

lemma (in Metric_space) mball_of [simp]:
  "mball_of (metric (M,d)) = mball"
  by (simp add: mball_of_def)

definition "mcball_of \<equiv> \<lambda>m. Metric_space.mcball (mspace m) (mdist m)"

lemma (in Metric_space) mcball_of [simp]:
  "mcball_of (metric (M,d)) = mcball"
  by (simp add: mcball_of_def)

definition "euclidean_metric \<equiv> metric (UNIV,dist)"

lemma mspace_euclidean_metric [simp]: "mspace euclidean_metric = UNIV"
  by (simp add: euclidean_metric_def)

lemma mdist_euclidean_metric [simp]: "mdist euclidean_metric = dist"
  by (simp add: euclidean_metric_def)

text\<open> Subspace of a metric space\<close>

definition submetric where
  "submetric \<equiv> \<lambda>m S. metric (S \<inter> mspace m, mdist m)"

lemma mspace_submetric [simp]: "mspace (submetric m S) = S \<inter> mspace m" 
  unfolding submetric_def
  by (meson Metric_space.subspace inf_le2 Metric_space_mspace_mdist Metric_space.mspace_metric)

lemma mdist_submetric [simp]: "mdist (submetric m S) = mdist m"
  unfolding submetric_def
  by (meson Metric_space.subspace inf_le2 Metric_space.mdist_metric Metric_space_mspace_mdist)

lemma submetric_UNIV [simp]: "submetric m UNIV = m"
  by (simp add: AMS.submetric_def dest_metric_inverse mdist_def mspace_def)

lemma submetric_submetric [simp]:
   "submetric (submetric m S) T = submetric m (S \<inter> T)"
  by (metis AMS.submetric_def Int_assoc inf_commute mdist_submetric mspace_submetric)

lemma submetric_mspace [simp]:
   "submetric m (mspace m) = m"
  by (simp add: AMS.submetric_def dest_metric_inverse mdist_def mspace_def)

lemma submetric_restrict:
   "submetric m S = submetric m (mspace m \<inter> S)"
  by (metis submetric_mspace submetric_submetric)


(*NEEDS LEPOLL*)
lemma card_lepoll_quasi_components_of_topspace:
  "quasi_components_of X \<lesssim> topspace X"
  unfolding lepoll_def
  by (metis bot.extremum image_empty inj_on_empty inj_on_iff_surj quasi_components_of_def)


subsection \<open>ATIN-WITHIN\<close>

(*REPLACE ORIGINAL DEFINITION TO USE ABBREVIATION, LIKE AT / AT_WITHIN
    ("atin (_) (_)/ within (_)" [1000, 60] 60)*)
thm atin_def at_within_def
definition atin_within :: "['a topology, 'a, 'a set] \<Rightarrow> 'a filter"
  where "atin_within X a S = inf (nhdsin X a) (principal (topspace X \<inter> S - {a}))"

lemma atin_within_UNIV [simp]:
  shows "atin_within X a UNIV = atin X a"
  by (simp add: atin_def atin_within_def)

lemma eventually_atin_subtopology:
  assumes "a \<in> topspace X"
  shows "eventually P (atin (subtopology X S) a) \<longleftrightarrow> 
    (a \<in> S \<longrightarrow> (\<exists>U. openin (subtopology X S) U \<and> a \<in> U \<and> (\<forall>x\<in>U - {a}. P x)))"
  using assms by (simp add: eventually_atin)

lemma eventually_atin_within:
  "eventually P (atin_within X a S) \<longleftrightarrow> a \<notin> topspace X \<or> (\<exists>T. openin X T \<and> a \<in> T \<and> (\<forall>x\<in>T. x \<in> S \<and> x \<noteq> a \<longrightarrow> P x))"
proof (cases "a \<in> topspace X")
  case True
  hence "eventually P (atin_within X a S) \<longleftrightarrow> 
         (\<exists>T. openin X T \<and> a \<in> T \<and>
          (\<forall>x\<in>T. x \<in> topspace X \<and> x \<in> S \<and> x \<noteq> a \<longrightarrow> P x))"
    by (simp add: atin_within_def eventually_inf_principal eventually_nhdsin)
  also have "\<dots> \<longleftrightarrow> (\<exists>T. openin X T \<and> a \<in> T \<and> (\<forall>x\<in>T. x \<in> S \<and> x \<noteq> a \<longrightarrow> P x))"
    using openin_subset by (intro ex_cong) auto
  finally show ?thesis by (simp add: True)
qed (simp add: atin_within_def)

lemma atin_subtopology_within:
  assumes "a \<in> S"
  shows "atin (subtopology X S) a = atin_within X a S"
proof -
  have "eventually P (atin (subtopology X S) a) \<longleftrightarrow> eventually P (atin_within X a S)" for P
    unfolding eventually_atin eventually_atin_within openin_subtopology
    using assms by auto
  then show ?thesis
    by (meson le_filter_def order.eq_iff)
qed

lemma limit_continuous_map_within:
   "\<lbrakk>continuous_map (subtopology X S) Y f; a \<in> S; a \<in> topspace X\<rbrakk>
    \<Longrightarrow> limitin Y f (f a) (atin_within X a S)"
  by (metis Int_iff atin_subtopology_within continuous_map_atin topspace_subtopology)

lemma atin_subtopology_within_if:
  shows "atin (subtopology X S) a = (if a \<in> S then atin_within X a S else bot)"
  by (simp add: atin_subtopology_within)

lemma trivial_limit_atpointof_within:
   "trivial_limit(atin_within X a S) \<longleftrightarrow>
        (a \<notin> X derived_set_of S)"
  by (auto simp: trivial_limit_def eventually_atin_within in_derived_set_of)

lemma derived_set_of_trivial_limit:
   "a \<in> X derived_set_of S \<longleftrightarrow> \<not> trivial_limit(atin_within X a S)"
  by (simp add: trivial_limit_atpointof_within)


subsection \<open>Misc other\<close>
    
subsection\<open>More sequential characterizations in a metric space\<close>

context Metric_space
begin
  
definition decreasing_dist :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool"
    where "decreasing_dist \<sigma> x \<equiv> (\<forall>m n. m < n \<longrightarrow> d (\<sigma> n) x < d (\<sigma> m) x)"

lemma decreasing_dist_imp_inj: "decreasing_dist \<sigma> a \<Longrightarrow> inj \<sigma>"
  by (metis decreasing_dist_def dual_order.irrefl linorder_inj_onI')

lemma eventually_atin_within_metric:
   "eventually P (atin_within mtopology a S) \<longleftrightarrow>
    (a \<in> M \<longrightarrow> (\<exists>\<delta>>0. \<forall>x. x \<in> M \<and> x \<in> S \<and> 0 < d x a \<and> d x a < \<delta> \<longrightarrow> P x))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
unfolding eventually_atin_within openin_mtopology subset_iff
  by (metis commute in_mball mdist_zero order_less_irrefl topspace_mtopology)
next
  assume R: ?rhs 
  show ?lhs
  proof (cases "a \<in> M")
    case True
    then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>x. \<lbrakk>x \<in> M; x \<in> S; 0 < d x a; d x a < \<delta>\<rbrakk> \<Longrightarrow> P x"
      using R by blast
    then have "openin mtopology (mball a \<delta>) \<and> (\<forall>x \<in> mball a \<delta>. x \<in> S \<and> x \<noteq> a \<longrightarrow> P x)"
      by (simp add: commute openin_mball)
    then show ?thesis
      by (metis True \<open>0 < \<delta>\<close> centre_in_mball_iff eventually_atin_within) 
  next
    case False
    with R show ?thesis
      by (simp add: eventually_atin_within)
  qed
qed


lemma eventually_atin_within_A:
  assumes 
    "(\<And>\<sigma>. \<lbrakk>range \<sigma> \<subseteq> (S \<inter> M) - {a}; decreasing_dist \<sigma> a;
          inj \<sigma>; limitin mtopology \<sigma> a sequentially\<rbrakk>
      \<Longrightarrow> eventually (\<lambda>n. P (\<sigma> n)) sequentially)"
  shows "eventually P (atin_within mtopology a S)"
proof -
  have False if SP: "\<And>\<delta>. \<delta>>0 \<Longrightarrow> \<exists>x \<in> M-{a}. d x a < \<delta> \<and> x \<in> S \<and> \<not> P x" and "a \<in> M"
  proof -
    define \<Phi> where "\<Phi> \<equiv> \<lambda>n x. x \<in> M-{a} \<and> d x a < inverse (Suc n) \<and> x \<in> S \<and> \<not> P x"
    obtain \<sigma> where \<sigma>: "\<And>n. \<Phi> n (\<sigma> n)" and dless: "\<And>n. d (\<sigma>(Suc n)) a < d (\<sigma> n) a"
    proof -
      obtain x0 where x0: "\<Phi> 0 x0"
        using SP [OF zero_less_one] by (force simp: \<Phi>_def)
      have "\<exists>y. \<Phi> (Suc n) y \<and> d y a < d x a" if "\<Phi> n x" for n x
        using SP [of "min (inverse (Suc (Suc n))) (d x a)"] \<open>a \<in> M\<close> that
        by (auto simp: \<Phi>_def)
      then obtain f where f: "\<And>n x. \<Phi> n x \<Longrightarrow> \<Phi> (Suc n) (f n x) \<and> d (f n x) a < d x a" 
        by metis
      show thesis
        proof
          show "\<Phi> n (rec_nat x0 f n)" for n
            by (induction n) (auto simp: x0 dest: f)
          with f show "d (rec_nat x0 f (Suc n)) a < d (rec_nat x0 f n) a" for n
            by auto 
        qed
    qed
    have 1: "range \<sigma> \<subseteq> (S \<inter> M) - {a}"
      using \<sigma> by (auto simp: \<Phi>_def)
    have "d (\<sigma>(Suc (m+n))) a < d (\<sigma> n) a" for m n
      by (induction m) (auto intro: order_less_trans dless)
    then have 2: "decreasing_dist \<sigma> a"
      unfolding decreasing_dist_def by (metis add.commute less_imp_Suc_add)
    have "\<forall>\<^sub>F xa in sequentially. d (\<sigma> xa) a < \<epsilon>" if "\<epsilon> > 0" for \<epsilon>
    proof -
      obtain N where "inverse (Suc N) < \<epsilon>"
        using \<open>\<epsilon> > 0\<close> reals_Archimedean by blast
      with \<sigma> 2 show ?thesis
        unfolding decreasing_dist_def by (smt (verit, best) \<Phi>_def eventually_at_top_dense)
    qed
    then have 4: "limitin mtopology \<sigma> a sequentially"
      using \<sigma> \<open>a \<in> M\<close> by (simp add: \<Phi>_def limitin_metric)
    show False
      using 2 assms [OF 1 _ decreasing_dist_imp_inj 4] \<sigma> by (force simp: \<Phi>_def)
  qed
  then show ?thesis
    by (fastforce simp: eventually_atin_within_metric)
qed


lemma eventually_atin_within_B:
  assumes ev: "eventually P (atin_within mtopology a S)" 
    and ran: "range \<sigma> \<subseteq> (S \<inter> M) - {a}"
    and lim: "limitin mtopology \<sigma> a sequentially"
  shows "eventually (\<lambda>n. P (\<sigma> n)) sequentially"
proof -
  have "a \<in> M"
    using lim limitin_mspace by auto
  with ev obtain \<delta> where "0 < \<delta>" 
    and \<delta>: "\<And>\<sigma>. \<lbrakk>\<sigma> \<in> M; \<sigma> \<in> S; 0 < d \<sigma> a; d \<sigma> a < \<delta>\<rbrakk> \<Longrightarrow> P \<sigma>"
    by (auto simp: eventually_atin_within_metric)
  then have *: "\<And>n. \<sigma> n \<in> M \<and> d (\<sigma> n) a < \<delta> \<Longrightarrow> P (\<sigma> n)"
    using \<open>a \<in> M\<close> ran by auto
  have "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M \<and> d (\<sigma> n) a < \<delta>"
    using lim \<open>0 < \<delta>\<close> by (auto simp: limitin_metric)
  then show ?thesis
    by (simp add: "*" eventually_mono)
qed

lemma eventually_atin_within_sequentially:
     "eventually P (atin_within mtopology a S) \<longleftrightarrow>
        (\<forall>\<sigma>. range \<sigma> \<subseteq> (S \<inter> M) - {a} \<and>
            limitin mtopology \<sigma> a sequentially
            \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
  by (metis eventually_atin_within_A eventually_atin_within_B)

lemma eventually_atin_within_sequentially_inj:
     "eventually P (atin_within mtopology a S) \<longleftrightarrow>
        (\<forall>\<sigma>. range \<sigma> \<subseteq> (S \<inter> M) - {a} \<and> inj \<sigma> \<and>
            limitin mtopology \<sigma> a sequentially
            \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
  by (metis eventually_atin_within_A eventually_atin_within_B)

lemma eventually_atin_within_sequentially_decreasing:
     "eventually P (atin_within mtopology a S) \<longleftrightarrow>
        (\<forall>\<sigma>. range \<sigma> \<subseteq> (S \<inter> M) - {a} \<and> decreasing_dist \<sigma> a \<and>
            limitin mtopology \<sigma> a sequentially
            \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
  by (metis eventually_atin_within_A eventually_atin_within_B)


lemma eventually_atin_sequentially:
   "eventually P (atin mtopology a) \<longleftrightarrow>
    (\<forall>\<sigma>. range \<sigma> \<subseteq> M - {a} \<and> limitin mtopology \<sigma> a sequentially
         \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
  using eventually_atin_within_sequentially [where S=UNIV] by simp

lemma eventually_atin_sequentially_inj:
   "eventually P (atin mtopology a) \<longleftrightarrow>
    (\<forall>\<sigma>. range \<sigma> \<subseteq> M - {a} \<and> inj \<sigma> \<and>
        limitin mtopology \<sigma> a sequentially
        \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
  using eventually_atin_within_sequentially_inj [where S=UNIV] by simp

lemma eventually_atin_sequentially_decreasing:
   "eventually P (atin mtopology a) \<longleftrightarrow>
    (\<forall>\<sigma>. range \<sigma> \<subseteq> M - {a} \<and> decreasing_dist \<sigma> a \<and>
         limitin mtopology \<sigma> a sequentially
        \<longrightarrow> eventually (\<lambda>n. P(\<sigma> n)) sequentially)"
  using eventually_atin_within_sequentially_decreasing [where S=UNIV] by simp

end

locale Metric_space12 = M1: Metric_space M1 d1 + M2: Metric_space M2 d2 for M1 d1 M2 d2
begin

lemma limit_atin_sequentially_within:
  "limitin M2.mtopology f l (atin_within M1.mtopology a S) \<longleftrightarrow>
     l \<in> M2 \<and>
     (\<forall>\<sigma>. range \<sigma> \<subseteq> S \<inter> M1 - {a} \<and>
          limitin M1.mtopology \<sigma> a sequentially
          \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
    by (auto simp: M1.eventually_atin_within_sequentially limitin_def)

lemma limit_atin_sequentially_within_inj:
  "limitin M2.mtopology f l (atin_within M1.mtopology a S) \<longleftrightarrow>
     l \<in> M2 \<and>
     (\<forall>\<sigma>. range \<sigma> \<subseteq> S \<inter> M1 - {a} \<and> inj \<sigma> \<and>
          limitin M1.mtopology \<sigma> a sequentially
          \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
    by (auto simp: M1.eventually_atin_within_sequentially_inj limitin_def)

lemma limit_atin_sequentially_within_decreasing:
  "limitin M2.mtopology f l (atin_within M1.mtopology a S) \<longleftrightarrow>
     l \<in> M2 \<and>
     (\<forall>\<sigma>. range \<sigma> \<subseteq> S \<inter> M1 - {a} \<and> M1.decreasing_dist \<sigma> a \<and> 
          limitin M1.mtopology \<sigma> a sequentially
          \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
    by (auto simp: M1.eventually_atin_within_sequentially_decreasing limitin_def)

lemma limit_atin_sequentially:
   "limitin M2.mtopology f l (atin M1.mtopology a) \<longleftrightarrow>
        l \<in> M2 \<and>
        (\<forall>\<sigma>. range \<sigma> \<subseteq> M1 - {a} \<and>
            limitin M1.mtopology \<sigma> a sequentially
            \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
  using limit_atin_sequentially_within [where S=UNIV] by simp

lemma limit_atin_sequentially_inj:
   "limitin M2.mtopology f l (atin M1.mtopology a) \<longleftrightarrow>
        l \<in> M2 \<and>
        (\<forall>\<sigma>. range \<sigma> \<subseteq> M1 - {a} \<and> inj \<sigma> \<and>
            limitin M1.mtopology \<sigma> a sequentially
            \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
  using limit_atin_sequentially_within_inj [where S=UNIV] by simp

lemma limit_atin_sequentially_decreasing:
  "limitin M2.mtopology f l (atin M1.mtopology a) \<longleftrightarrow>
     l \<in> M2 \<and>
     (\<forall>\<sigma>. range \<sigma> \<subseteq> M1 - {a} \<and> M1.decreasing_dist \<sigma> a \<and> 
          limitin M1.mtopology \<sigma> a sequentially
          \<longrightarrow> limitin M2.mtopology (f \<circ> \<sigma>) l sequentially)"
  using limit_atin_sequentially_within_decreasing [where S=UNIV] by simp

end

text \<open>For easy reference to theorems outside of the locale\<close>
lemma Metric_space12_mspace_mdist:
  "Metric_space12 (mspace m1) (mdist m1) (mspace m2) (mdist m2)"
  by (simp add: Metric_space12_def Metric_space_mspace_mdist)

text \<open>An experiment: same result as within the locale, but using metric space variables\<close>
lemma limit_atin_sequentially_within:
  "limitin (mtopology_of m2) f l (atin_within (mtopology_of m1) a S) \<longleftrightarrow>
     l \<in> mspace m2 \<and>
     (\<forall>\<sigma>. range \<sigma> \<subseteq> S \<inter> mspace m1 - {a} \<and>
          limitin (mtopology_of m1) \<sigma> a sequentially
          \<longrightarrow> limitin (mtopology_of m2) (f \<circ> \<sigma>) l sequentially)"
  using Metric_space12.limit_atin_sequentially_within [OF Metric_space12_mspace_mdist]
  by (metis mtopology_of_def)


context Metric_space
begin

lemma atin_within_imp_M:
   "atin_within mtopology x S \<noteq> bot \<Longrightarrow> x \<in> M"
  by (metis derived_set_of_trivial_limit in_derived_set_of topspace_mtopology)

lemma atin_within_sequentially_sequence:
  assumes "atin_within mtopology x S \<noteq> bot"
  obtains \<sigma> where "range \<sigma> \<subseteq> S \<inter> M - {x}" 
          "decreasing_dist \<sigma> x" "inj \<sigma>" "limitin mtopology \<sigma> x sequentially"
  by (metis eventually_atin_within_A eventually_False assms)

lemma derived_set_of_sequentially:
  "mtopology derived_set_of S =
   {x \<in> M. \<exists>\<sigma>. range \<sigma> \<subseteq> S \<inter> M - {x} \<and> limitin mtopology \<sigma> x sequentially}"
proof -
  have False
    if "range \<sigma> \<subseteq> S \<inter> M - {x}"
      and "limitin mtopology \<sigma> x sequentially"
      and "atin_within mtopology x S = bot"
    for x \<sigma>
  proof -
    have "\<forall>\<^sub>F n in sequentially. P (\<sigma> n)" for P
      using that by (metis eventually_atin_within_B eventually_bot)
    then show False
      by (meson eventually_False_sequentially eventually_mono)
  qed
  then show ?thesis
    using derived_set_of_trivial_limit 
    by (fastforce elim!: atin_within_sequentially_sequence intro: atin_within_imp_M)
qed

lemma derived_set_of_sequentially_alt:
  "mtopology derived_set_of S =
   {x. \<exists>\<sigma>. range \<sigma> \<subseteq> S - {x} \<and> limitin mtopology \<sigma> x sequentially}"
proof -
  have *: "\<exists>\<sigma>. range \<sigma> \<subseteq> S \<inter> M - {x} \<and> limitin mtopology \<sigma> x sequentially"
    if \<sigma>: "range \<sigma> \<subseteq> S - {x}" and lim: "limitin mtopology \<sigma> x sequentially" for x \<sigma>
  proof -
    obtain N where "\<forall>n\<ge>N. \<sigma> n \<in> M \<and> d (\<sigma> n) x < 1"
      using lim limit_metric_sequentially by fastforce
    with \<sigma> obtain a where a:"a \<in> S \<inter> M - {x}" by auto
    show ?thesis
    proof (intro conjI exI)
      show "range (\<lambda>n. if \<sigma> n \<in> M then \<sigma> n else a) \<subseteq> S \<inter> M - {x}"
        using a \<sigma> by fastforce
      show "limitin mtopology (\<lambda>n. if \<sigma> n \<in> M then \<sigma> n else a) x sequentially"
        using lim limit_metric_sequentially by fastforce
    qed
  qed
  show ?thesis
    by (auto simp: limitin_mspace derived_set_of_sequentially intro!: *)
qed

lemma derived_set_of_sequentially_inj:
   "mtopology derived_set_of S =
    {x \<in> M. \<exists>\<sigma>. range \<sigma> \<subseteq> S \<inter> M - {x} \<and> inj \<sigma> \<and> limitin mtopology \<sigma> x sequentially}"
proof -
  have False
    if "x \<in> M" and "range \<sigma> \<subseteq> S \<inter> M - {x}"
      and "limitin mtopology \<sigma> x sequentially"
      and "atin_within mtopology x S = bot"
    for x \<sigma>
  proof -
    have "\<forall>\<^sub>F n in sequentially. P (\<sigma> n)" for P
      using that derived_set_of_sequentially_alt derived_set_of_trivial_limit by fastforce
    then show False
      by (meson eventually_False_sequentially eventually_mono)
  qed
  then show ?thesis
    using derived_set_of_trivial_limit 
    by (fastforce elim!: atin_within_sequentially_sequence intro: atin_within_imp_M)
qed


lemma derived_set_of_sequentially_inj_alt:
   "mtopology derived_set_of S =
    {x. \<exists>\<sigma>. range \<sigma> \<subseteq> S - {x} \<and> inj \<sigma> \<and> limitin mtopology \<sigma> x sequentially}"
proof -
  have "\<exists>\<sigma>. range \<sigma> \<subseteq> S - {x} \<and> inj \<sigma> \<and> limitin mtopology \<sigma> x sequentially"
    if "atin_within mtopology x S \<noteq> bot" for x
    by (metis Diff_empty Int_subset_iff atin_within_sequentially_sequence subset_Diff_insert that)
  moreover have False
    if "range (\<lambda>x. \<sigma> (x::nat)) \<subseteq> S - {x}"
      and "limitin mtopology \<sigma> x sequentially"
      and "atin_within mtopology x S = bot"
    for x \<sigma>
  proof -
    have "\<forall>\<^sub>F n in sequentially. P (\<sigma> n)" for P
      using that derived_set_of_sequentially_alt derived_set_of_trivial_limit by fastforce
    then show False
      by (meson eventually_False_sequentially eventually_mono)
  qed
  ultimately show ?thesis
    using derived_set_of_trivial_limit by (fastforce intro: atin_within_imp_M)
qed

lemma derived_set_of_sequentially_decreasing:
   "mtopology derived_set_of S =
    {x \<in> M. \<exists>\<sigma>. range \<sigma> \<subseteq> S - {x} \<and> decreasing_dist \<sigma> x \<and> limitin mtopology \<sigma> x sequentially}"
proof -
  have "\<exists>\<sigma>. range \<sigma> \<subseteq> S - {x} \<and> decreasing_dist \<sigma> x \<and> limitin mtopology \<sigma> x sequentially"
    if "atin_within mtopology x S \<noteq> bot" for x
    by (metis Diff_empty atin_within_sequentially_sequence le_infE subset_Diff_insert that)
  moreover have False
    if "x \<in> M" and "range \<sigma> \<subseteq> S - {x}"
      and "limitin mtopology \<sigma> x sequentially"
      and "atin_within mtopology x S = bot"
    for x \<sigma>
  proof -
    have "\<forall>\<^sub>F n in sequentially. P (\<sigma> n)" for P
      using that derived_set_of_sequentially_alt derived_set_of_trivial_limit by fastforce
    then show False
      by (meson eventually_False_sequentially eventually_mono)
  qed
  ultimately show ?thesis
    using derived_set_of_trivial_limit by (fastforce intro: atin_within_imp_M)
qed

lemma derived_set_of_sequentially_decreasing_alt:
   "mtopology derived_set_of S =
    {x. \<exists>\<sigma>. range \<sigma> \<subseteq> S - {x} \<and> decreasing_dist \<sigma> x \<and> limitin mtopology \<sigma> x sequentially}"
  using derived_set_of_sequentially_alt derived_set_of_sequentially_decreasing by auto

lemma closure_of_sequentially:
   "mtopology closure_of S = 
    {x \<in> M. \<exists>\<sigma>. range \<sigma> \<subseteq> S \<inter> M \<and> limitin mtopology \<sigma> x sequentially}"
  by (auto simp: closure_of derived_set_of_sequentially)

end (*Metric_space*)


(*** REQUIRES Arcwise_Connected ***)

subsection \<open>Urysohn lemma and Tietze's theorem\<close>

lemma Urysohn_lemma:
  fixes a b :: real
  assumes "normal_space X" "closedin X S" "closedin X T" "disjnt S T" "a \<le> b" 
  obtains f where "continuous_map X (top_of_set {a..b}) f" "f ` S \<subseteq> {a}" "f ` T \<subseteq> {b}"
proof -
  obtain U where "openin X U" "S \<subseteq> U" "X closure_of U \<subseteq> topspace X - T"
    using assms unfolding normal_space_alt disjnt_def
    by (metis Diff_mono Un_Diff_Int closedin_def subset_eq sup_bot_right)
  have "\<exists>G :: real \<Rightarrow> 'a set. G 0 = U \<and> G 1 = topspace X - T \<and>
               (\<forall>x \<in> dyadics \<inter> {0..1}. \<forall>y \<in> dyadics \<inter> {0..1}. x < y \<longrightarrow> openin X (G x) \<and> openin X (G y) \<and> X closure_of (G x) \<subseteq> G y)"
  proof (rule recursion_on_dyadic_fractions)
    show "openin X U \<and> openin X (topspace X - T) \<and> X closure_of U \<subseteq> topspace X - T"
      using \<open>X closure_of U \<subseteq> topspace X - T\<close> \<open>openin X U\<close> \<open>closedin X T\<close> by blast
    show "\<exists>z. (openin X x \<and> openin X z \<and> X closure_of x \<subseteq> z) \<and> openin X z \<and> openin X y \<and> X closure_of z \<subseteq> y"
      if "openin X x \<and> openin X y \<and> X closure_of x \<subseteq> y" for x y
      by (meson that closedin_closure_of normal_space_alt \<open>normal_space X\<close>)
    show "openin X x \<and> openin X z \<and> X closure_of x \<subseteq> z"
      if "openin X x \<and> openin X y \<and> X closure_of x \<subseteq> y" and "openin X y \<and> openin X z \<and> X closure_of y \<subseteq> z" for x y z
      by (meson that closure_of_subset openin_subset subset_trans)
  qed
  then obtain G :: "real \<Rightarrow> 'a set"
      where G0: "G 0 = U" and G1: "G 1 = topspace X - T"
        and G: "\<And>x y. \<lbrakk>x \<in> dyadics; y \<in> dyadics; 0 \<le> x; x < y; y \<le> 1\<rbrakk>
                      \<Longrightarrow> openin X (G x) \<and> openin X (G y) \<and> X closure_of (G x) \<subseteq> G y"
    by (smt (verit, del_insts) Int_iff atLeastAtMost_iff)
  define f where "f \<equiv> \<lambda>x. Inf(insert 1 {r. r \<in> dyadics \<inter> {0..1} \<and> x \<in> G r})"
  have f_ge: "f x \<ge> 0" if "x \<in> topspace X" for x
    unfolding f_def by (force intro: cInf_greatest)
  moreover have f_le1: "f x \<le> 1" if "x \<in> topspace X" for x
  proof -
    have "bdd_below {r \<in> dyadics \<inter> {0..1}. x \<in> G r}"
      by (auto simp: bdd_below_def)
    then show ?thesis
       by (auto simp: f_def cInf_lower)
  qed
  ultimately have fim: "f ` topspace X \<subseteq> {0..1}"
    by (auto simp: f_def)
  have 0: "0 \<in> dyadics \<inter> {0..1::real}" and 1: "1 \<in> dyadics \<inter> {0..1::real}"
    by (force simp: dyadics_def)+
  then have opeG: "openin X (G r)" if "r \<in> dyadics \<inter> {0..1}" for r
    using G G0 \<open>openin X U\<close> less_eq_real_def that by auto
  have "x \<in> G 0" if "x \<in> S" for x
    using G0 \<open>S \<subseteq> U\<close> that by blast
  with 0 have fimS: "f ` S \<subseteq> {0}"
    unfolding f_def by (force intro!: cInf_eq_minimum)
  have False if "r \<in> dyadics" "0 \<le> r" "r < 1" "x \<in> G r" "x \<in> T" for r x
    using G [of r 1] 1
    by (smt (verit, best) DiffD2 G1 Int_iff closure_of_subset inf.orderE openin_subset that)
  then have "r\<ge>1" if "r \<in> dyadics" "0 \<le> r" "r \<le> 1" "x \<in> G r" "x \<in> T" for r x
    using linorder_not_le that by blast
  then have fimT: "f ` T \<subseteq> {1}"
    unfolding f_def by (force intro!: cInf_eq_minimum)
  have fle1: "f z \<le> 1" for z
    by (force simp: f_def intro: cInf_lower)
  have fle: "f z \<le> x" if "x \<in> dyadics \<inter> {0..1}" "z \<in> G x" for z x
    using that by (force simp: f_def intro: cInf_lower)
  have *: "b \<le> f z" if "b \<le> 1" "\<And>x. \<lbrakk>x \<in> dyadics \<inter> {0..1}; z \<in> G x\<rbrakk> \<Longrightarrow> b \<le> x" for z b
    using that by (force simp: f_def intro: cInf_greatest)
  have **: "r \<le> f x" if r: "r \<in> dyadics \<inter> {0..1}" "x \<notin> G r" for r x
  proof (rule *)
    show "r \<le> s" if "s \<in> dyadics \<inter> {0..1}" and "x \<in> G s" for s :: real
      using that r G [of s r] by (force simp add: dest: closure_of_subset openin_subset)
  qed (use that in force)

  have "\<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y \<in> U. \<bar>f y - f x\<bar> < \<epsilon>)"
    if "x \<in> topspace X" and "0 < \<epsilon>" for x \<epsilon>
  proof -
    have A: "\<exists>r. r \<in> dyadics \<inter> {0..1} \<and> r < y \<and> \<bar>r - y\<bar> < d" if "0 < y" "y \<le> 1" "0 < d" for y d::real
    proof -
      obtain n q r 
        where "of_nat q / 2^n < y" "y < of_nat r / 2^n" "\<bar>q / 2^n - r / 2^n \<bar> < d"
        by (smt (verit, del_insts) padic_rational_approximation_straddle_pos  \<open>0 < d\<close> \<open>0 < y\<close>) 
      then show ?thesis
        unfolding dyadics_def
        using divide_eq_0_iff that(2) by fastforce
    qed
    have B: "\<exists>r. r \<in> dyadics \<inter> {0..1} \<and> y < r \<and> \<bar>r - y\<bar> < d" if "0 \<le> y" "y < 1" "0 < d" for y d::real
    proof -
      obtain n q r 
        where "of_nat q / 2^n \<le> y" "y < of_nat r / 2^n" "\<bar>q / 2^n - r / 2^n \<bar> < d"
        using padic_rational_approximation_straddle_pos_le
        by (smt (verit, del_insts) \<open>0 < d\<close> \<open>0 \<le> y\<close>) 
      then show ?thesis
        apply (clarsimp simp: dyadics_def)
        using divide_eq_0_iff \<open>y < 1\<close>
        by (smt (verit) divide_nonneg_nonneg divide_self of_nat_0_le_iff of_nat_1 power_0 zero_le_power) 
    qed
    show ?thesis
    proof (cases "f x = 0")
      case True
      with B[of 0] obtain r where r: "r \<in> dyadics \<inter> {0..1}" "0 < r" "\<bar>r\<bar> < \<epsilon>/2"
        by (smt (verit) \<open>0 < \<epsilon>\<close> half_gt_zero)
      show ?thesis
      proof (intro exI conjI)
        show "openin X (G r)"
          using opeG r(1) by blast
        show "x \<in> G r"
          using True ** r by force
        show "\<forall>y \<in> G r. \<bar>f y - f x\<bar> < \<epsilon>"
          using f_ge \<open>openin X (G r)\<close> fle openin_subset r by (fastforce simp: True)
      qed
    next
      case False
      show ?thesis 
      proof (cases "f x = 1")
        case True
        with A[of 1] obtain r where r: "r \<in> dyadics \<inter> {0..1}" "r < 1" "\<bar>r-1\<bar> < \<epsilon>/2"
          by (smt (verit) \<open>0 < \<epsilon>\<close> half_gt_zero)
        define G' where "G' \<equiv> topspace X - X closure_of G r"
        show ?thesis
        proof (intro exI conjI)
          show "openin X G'"
            unfolding G'_def by fastforce
          obtain r' where "r' \<in> dyadics \<and> 0 \<le> r' \<and> r' \<le> 1 \<and> r < r' \<and> \<bar>r' - r\<bar> < 1 - r"
            using B r by force 
          moreover
          have "1 - r \<in> dyadics" "0 \<le> r"
            using 1 r dyadics_diff by force+
          ultimately have "x \<notin> X closure_of G r"
            using G True r fle by force
          then show "x \<in> G'"
            by (simp add: G'_def that)
          show "\<forall>y \<in> G'. \<bar>f y - f x\<bar> < \<epsilon>"
            using ** f_le1 in_closure_of r by (fastforce simp add: True G'_def)
        qed
      next
        case False
        have "0 < f x" "f x < 1"
          using fle1 f_ge that(1) \<open>f x \<noteq> 0\<close> \<open>f x \<noteq> 1\<close> by (metis order_le_less) +
        obtain r where r: "r \<in> dyadics \<inter> {0..1}" "r < f x" "\<bar>r - f x\<bar> < \<epsilon> / 2"
          using A \<open>0 < \<epsilon>\<close> \<open>0 < f x\<close> \<open>f x < 1\<close> by (smt (verit, best) half_gt_zero)
        obtain r' where r': "r' \<in> dyadics \<inter> {0..1}" "f x < r'" "\<bar>r' - f x\<bar> < \<epsilon> / 2"
          using B \<open>0 < \<epsilon>\<close> \<open>0 < f x\<close> \<open>f x < 1\<close> by (smt (verit, best) half_gt_zero)
        have "r < 1"
          using \<open>f x < 1\<close> r(2) by force
        show ?thesis
        proof (intro conjI exI)
          show "openin X (G r' - X closure_of G r)"
            using closedin_closure_of opeG r' by blast
          have "x \<in> X closure_of G r \<Longrightarrow> False"
            using B [of r "f x - r"] r \<open>r < 1\<close> G [of r] fle by force
          then show "x \<in> G r' - X closure_of G r"
            using ** r' by fastforce
          show "\<forall>y\<in>G r' - X closure_of G r. \<bar>f y - f x\<bar> < \<epsilon>"
            using r r' ** G closure_of_subset field_sum_of_halves fle openin_subset subset_eq
            by (smt (verit) DiffE opeG)
        qed
      qed
    qed
  qed
  then have contf: "continuous_map X (top_of_set {0..1}) f"
    by (force simp add: Met_TC.continuous_map_to_metric dist_real_def continuous_map_in_subtopology fim simp flip: Met_TC.mtopology_is_euclideanreal)
  define g where "g \<equiv> \<lambda>x. a + (b - a) * f x"
  show thesis
  proof
    have "continuous_map X euclideanreal g"
      using contf \<open>a \<le> b\<close> unfolding g_def by (auto simp: continuous_intros continuous_map_in_subtopology)
    moreover have "g ` (topspace X) \<subseteq> {a..b}"
      using mult_left_le [of "f _" "b-a"] contf \<open>a \<le> b\<close>   
      by (simp add: g_def add.commute continuous_map_in_subtopology image_subset_iff le_diff_eq)
    ultimately show "continuous_map X (top_of_set {a..b}) g"
      by (meson continuous_map_in_subtopology)
    show "g ` S \<subseteq> {a}" "g ` T \<subseteq> {b}"
      using fimS fimT by (auto simp: g_def)
  qed
qed

lemma Urysohn_lemma_alt:
  fixes a b :: real
  assumes "normal_space X" "closedin X S" "closedin X T" "disjnt S T"
  obtains f where "continuous_map X euclideanreal f" "f ` S \<subseteq> {a}" "f ` T \<subseteq> {b}"
  by (metis Urysohn_lemma assms continuous_map_in_subtopology disjnt_sym linear)

lemma normal_space_iff_Urysohn_gen_alt:
  assumes "a \<noteq> b"
  shows "normal_space X \<longleftrightarrow>
         (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
                \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and> f ` S \<subseteq> {a} \<and> f ` T \<subseteq> {b}))"
 (is "?lhs=?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs" 
    by (metis Urysohn_lemma_alt)
next
  assume R: ?rhs 
  show ?lhs
    unfolding normal_space_def
  proof clarify
    fix S T
    assume "closedin X S" and "closedin X T" and "disjnt S T"
    with R obtain f where contf: "continuous_map X euclideanreal f" and "f ` S \<subseteq> {a}" "f ` T \<subseteq> {b}"
      by meson
    show "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
    proof (intro conjI exI)
      show "openin X {x \<in> topspace X. f x \<in> ball a (\<bar>a - b\<bar> / 2)}"
        by (force intro!: openin_continuous_map_preimage [OF contf])
      show "openin X {x \<in> topspace X. f x \<in> ball b (\<bar>a - b\<bar> / 2)}"
        by (force intro!: openin_continuous_map_preimage [OF contf])
      show "S \<subseteq> {x \<in> topspace X. f x \<in> ball a (\<bar>a - b\<bar> / 2)}"
        using \<open>closedin X S\<close> closedin_subset \<open>f ` S \<subseteq> {a}\<close> assms by force
      show "T \<subseteq> {x \<in> topspace X. f x \<in> ball b (\<bar>a - b\<bar> / 2)}"
        using \<open>closedin X T\<close> closedin_subset \<open>f ` T \<subseteq> {b}\<close> assms by force
      have "\<And>x. \<lbrakk>x \<in> topspace X; dist a (f x) < \<bar>a-b\<bar>/2; dist b (f x) < \<bar>a-b\<bar>/2\<rbrakk> \<Longrightarrow> False"
        by (smt (verit, best) dist_real_def dist_triangle_half_l)
      then show "disjnt {x \<in> topspace X. f x \<in> ball a (\<bar>a-b\<bar> / 2)} {x \<in> topspace X. f x \<in> ball b (\<bar>a-b\<bar> / 2)}"
        using disjnt_iff by fastforce
    qed
  qed
qed 

lemma normal_space_iff_Urysohn_gen:
  fixes a b::real
  shows
   "a < b \<Longrightarrow> 
      normal_space X \<longleftrightarrow>
        (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
               \<longrightarrow> (\<exists>f. continuous_map X (top_of_set {a..b}) f \<and>
                        f ` S \<subseteq> {a} \<and> f ` T \<subseteq> {b}))"
  by (metis linear not_le Urysohn_lemma normal_space_iff_Urysohn_gen_alt continuous_map_in_subtopology)

lemma normal_space_iff_Urysohn_alt:
   "normal_space X \<longleftrightarrow>
     (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
           \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and>
                   f ` S \<subseteq> {0} \<and> f ` T \<subseteq> {1}))"
  by (rule normal_space_iff_Urysohn_gen_alt) auto

lemma normal_space_iff_Urysohn:
   "normal_space X \<longleftrightarrow>
     (\<forall>S T. closedin X S \<and> closedin X T \<and> disjnt S T
            \<longrightarrow> (\<exists>f::'a\<Rightarrow>real. continuous_map X (top_of_set {0..1}) f \<and> 
                               f ` S \<subseteq> {0} \<and> f ` T \<subseteq> {1}))"
  by (rule normal_space_iff_Urysohn_gen) auto

lemma normal_space_perfect_map_image:
   "\<lbrakk>normal_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> normal_space Y"
  unfolding perfect_map_def proper_map_def
  using normal_space_continuous_closed_map_image by fastforce

lemma Hausdorff_normal_space_closed_continuous_map_image:
   "\<lbrakk>normal_space X; closed_map X Y f; continuous_map X Y f;
     f ` topspace X = topspace Y; t1_space Y\<rbrakk>
    \<Longrightarrow> Hausdorff_space Y"
  by (metis normal_space_continuous_closed_map_image normal_t1_imp_Hausdorff_space)

lemma normal_Hausdorff_space_closed_continuous_map_image:
   "\<lbrakk>normal_space X; Hausdorff_space X; closed_map X Y f;
     continuous_map X Y f; f ` topspace X = topspace Y\<rbrakk>
    \<Longrightarrow> normal_space Y \<and> Hausdorff_space Y"
  by (meson normal_space_continuous_closed_map_image normal_t1_eq_Hausdorff_space t1_space_closed_map_image)

lemma Lindelof_cover:
  assumes "regular_space X" and "Lindelof_space X" and "S \<noteq> {}" 
    and clo: "closedin X S" "closedin X T" "disjnt S T"
  obtains h :: "nat \<Rightarrow> 'a set" where 
    "\<And>n. openin X (h n)" "\<And>n. disjnt T (X closure_of (h n))" and  "S \<subseteq> \<Union>(range h)"
proof -
  have "\<exists>U. openin X U \<and> x \<in> U \<and> disjnt T (X closure_of U)"
    if "x \<in> S" for x
    using \<open>regular_space X\<close> unfolding regular_space 
    by (metis (full_types) Diff_iff \<open>disjnt S T\<close> clo closure_of_eq disjnt_iff in_closure_of that)
  then obtain h where oh: "\<And>x. x \<in> S \<Longrightarrow> openin X (h x)"
    and xh: "\<And>x. x \<in> S \<Longrightarrow> x \<in> h x"
    and dh: "\<And>x. x \<in> S \<Longrightarrow> disjnt T (X closure_of h x)"
    by metis
  have "Lindelof_space(subtopology X S)"
    by (simp add: Lindelof_space_closedin_subtopology \<open>Lindelof_space X\<close> \<open>closedin X S\<close>)
  then obtain \<U> where \<U>: "countable \<U> \<and> \<U> \<subseteq> h ` S \<and> S \<subseteq> \<Union>\<U>"
    unfolding Lindelof_space_subtopology_subset [OF closedin_subset [OF \<open>closedin X S\<close>]]
    by (smt (verit, del_insts) oh xh UN_I image_iff subsetI)
  with \<open>S \<noteq> {}\<close> have "\<U> \<noteq> {}"
    by blast
  show ?thesis
  proof
    show "openin X (from_nat_into \<U> n)" for n
      by (metis \<U> from_nat_into image_iff \<open>\<U> \<noteq> {}\<close> oh subsetD)
    show "disjnt T (X closure_of (from_nat_into \<U>) n)" for n
      using dh from_nat_into [OF \<open>\<U> \<noteq> {}\<close>]
      by (metis \<U> f_inv_into_f inv_into_into subset_eq)
    show "S \<subseteq> \<Union>(range (from_nat_into \<U>))"
      by (simp add: \<U> \<open>\<U> \<noteq> {}\<close>)
  qed
qed

lemma regular_Lindelof_imp_normal_space:
  assumes "regular_space X" and "Lindelof_space X"
  shows "normal_space X"
  unfolding normal_space_def
proof clarify
  fix S T
  assume clo: "closedin X S" "closedin X T" and "disjnt S T"
  show "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
  proof (cases "S={} \<or> T={}")
    case True
    with clo show ?thesis
      by (meson closedin_def disjnt_empty1 disjnt_empty2 openin_empty openin_topspace subset_empty)
  next
    case False
    obtain h :: "nat \<Rightarrow> 'a set" where 
      opeh: "\<And>n. openin X (h n)" and dish: "\<And>n. disjnt T (X closure_of (h n))"
      and Sh: "S \<subseteq> \<Union>(range h)"
      by (metis Lindelof_cover False \<open>disjnt S T\<close> assms clo)
    obtain k :: "nat \<Rightarrow> 'a set" where 
      opek: "\<And>n. openin X (k n)" and disk: "\<And>n. disjnt S (X closure_of (k n))"
      and Tk: "T \<subseteq> \<Union>(range k)"
      by (metis Lindelof_cover False \<open>disjnt S T\<close> assms clo disjnt_sym)
    define U where "U \<equiv> \<Union>i. h i - (\<Union>j<i. X closure_of k j)"
    define V where "V \<equiv> \<Union>i. k i - (\<Union>j\<le>i. X closure_of h j)"
    show ?thesis
    proof (intro exI conjI)
      show "openin X U" "openin X V"
        unfolding U_def V_def
        by (force intro!: opek opeh closedin_Union closedin_closure_of)+
      show "S \<subseteq> U" "T \<subseteq> V"
        using Sh Tk dish disk by (fastforce simp: U_def V_def disjnt_iff)+
      have "\<And>x i j. \<lbrakk>x \<in> k i; x \<in> h j; \<forall>j\<le>i. x \<notin> X closure_of h j\<rbrakk>
                 \<Longrightarrow> \<exists>i<j. x \<in> X closure_of k i"
        by (metis in_closure_of linorder_not_less opek openin_subset subsetD)
      then show "disjnt U V"
        by (force simp add: U_def V_def disjnt_iff)
    qed
  qed
qed

lemma Tietze_extension_closed_real_interval:
  assumes "normal_space X" and "closedin X S"
    and contf: "continuous_map (subtopology X S) euclideanreal f"
    and fim: "f ` S \<subseteq> {a..b}" and "a \<le> b"
  obtains g 
  where "continuous_map X euclideanreal g" 
        "\<And>x. x \<in> S \<Longrightarrow> g x = f x" "g ` topspace X \<subseteq> {a..b}"
proof -
  define c where "c \<equiv> max \<bar>a\<bar> \<bar>b\<bar> + 1"
  have "0 < c" and c: "\<And>x. x \<in> S \<Longrightarrow> \<bar>f x\<bar> \<le> c"
    using fim by (auto simp: c_def image_subset_iff)
  define good where 
    "good \<equiv> \<lambda>g n. continuous_map X euclideanreal g \<and> (\<forall>x \<in> S. \<bar>f x - g x\<bar> \<le> c * (2/3)^n)"
  have step: "\<exists>g. good g (Suc n) \<and>
              (\<forall>x \<in> topspace X. \<bar>g x - h x\<bar> \<le> c * (2/3)^n / 3)"
    if h: "good h n" for n h
  proof -
    have pos: "0 < c * (2/3) ^ n"
      by (simp add: \<open>0 < c\<close>)
    have S_eq: "S = topspace(subtopology X S)" and "S \<subseteq> topspace X"
      using \<open>closedin X S\<close> closedin_subset by auto
    define d where "d \<equiv> c/3 * (2/3) ^ n"
    define SA where "SA \<equiv> {x \<in> S. f x - h x \<in> {..-d}}"
    define SB where "SB \<equiv> {x \<in> S. f x - h x \<in> {d..}}"
    have contfh: "continuous_map (subtopology X S) euclideanreal (\<lambda>x. f x - h x)"
      using that
      by (simp add: contf good_def continuous_map_diff continuous_map_from_subtopology)
    then have "closedin (subtopology X S) SA"
      unfolding SA_def
      by (smt (verit, del_insts) closed_closedin continuous_map_closedin Collect_cong S_eq closed_real_atMost)
    then have "closedin X SA"
      using \<open>closedin X S\<close> closedin_trans_full by blast
    moreover have  "closedin (subtopology X S) SB"      
      unfolding SB_def
      using closedin_continuous_map_preimage_gen [OF contfh]
      by (metis (full_types) S_eq closed_atLeast closed_closedin closedin_topspace)
    then have "closedin X SB"
      using \<open>closedin X S\<close> closedin_trans_full by blast
    moreover have "disjnt SA SB"
      using pos by (auto simp: d_def disjnt_def SA_def SB_def)
    moreover have "-d \<le> d"
      using pos by (auto simp: d_def)
    ultimately
    obtain g where contg: "continuous_map X (top_of_set {- d..d}) g"
      and ga: "g ` SA \<subseteq> {- d}" and gb: "g ` SB \<subseteq> {d}"
      using Urysohn_lemma \<open>normal_space X\<close> by metis
    then have g_le_d: "\<And>x. x \<in> topspace X \<Longrightarrow> \<bar>g x\<bar> \<le> d"
      by (simp add: abs_le_iff continuous_map_def minus_le_iff)
    have g_eq_d: "\<And>x. \<lbrakk>x \<in> S; f x - h x \<le> -d\<rbrakk> \<Longrightarrow> g x = -d"
      using ga by (auto simp: SA_def)
    have g_eq_negd: "\<And>x. \<lbrakk>x \<in> S; f x - h x \<ge> d\<rbrakk> \<Longrightarrow> g x = d"
      using gb by (auto simp: SB_def)
    show ?thesis
      unfolding good_def
    proof (intro conjI strip exI)
      show "continuous_map X euclideanreal (\<lambda>x. h x + g x)"
        using contg continuous_map_add continuous_map_in_subtopology that
        unfolding good_def by blast
      show "\<bar>f x - (h x + g x)\<bar> \<le> c * (2 / 3) ^ Suc n" if "x \<in> S" for x
      proof -
        have x: "x \<in> topspace X"
          using \<open>S \<subseteq> topspace X\<close> that by auto
        have "\<bar>f x - h x\<bar> \<le> c * (2/3) ^ n"
          using good_def h that by blast
        with g_eq_d [OF that] g_eq_negd [OF that] g_le_d [OF x] 
        have "\<bar>f x - (h x + g x)\<bar> \<le> d + d"
          unfolding d_def by linarith
        then show ?thesis 
          by (simp add: d_def)
      qed
      show "\<bar>h x + g x - h x\<bar> \<le> c * (2 / 3) ^ n / 3" if "x \<in> topspace X" for x
        using that d_def g_le_d by auto
    qed
  qed
  then obtain nxtg where nxtg: "\<And>h n. good h n \<Longrightarrow> 
          good (nxtg h n) (Suc n) \<and> (\<forall>x \<in> topspace X. \<bar>nxtg h n x - h x\<bar> \<le> c * (2/3)^n / 3)"
    by metis
  define g where "g \<equiv> rec_nat (\<lambda>x. 0) (\<lambda>n r. nxtg r n)"
  have [simp]: "g 0 x = 0" for x
    by (auto simp: g_def)
  have g_Suc: "g(Suc n) = nxtg (g n) n" for n
    by (auto simp: g_def)
  have good: "good (g n) n" for n
  proof (induction n)
    case 0
    with c show ?case
      by (auto simp: good_def)
  qed (simp add: g_Suc nxtg)
  have *: "\<And>n x. x \<in> topspace X \<Longrightarrow> \<bar>g(Suc n) x - g n x\<bar> \<le> c * (2/3) ^ n / 3"
    using nxtg g_Suc good by presburger
  obtain h where conth:  "continuous_map X euclideanreal h"
    and h: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>topspace X. dist (g n x) (h x) < \<epsilon>"
  proof (rule Met_TC.continuous_map_uniformly_Cauchy_limit)
    show "\<forall>\<^sub>F n in sequentially. continuous_map X (Met_TC.mtopology) (g n)"
      using good good_def by fastforce
    show "\<exists>N. \<forall>m n x. N \<le> m \<longrightarrow> N \<le> n \<longrightarrow> x \<in> topspace X \<longrightarrow> dist (g m x) (g n x) < \<epsilon>"
      if "\<epsilon> > 0" for \<epsilon> 
    proof -
      have "\<forall>\<^sub>F n in sequentially. \<bar>(2/3) ^ n\<bar> < \<epsilon>/c"
      proof (rule Archimedean_eventually_pow_inverse)
        show "0 < \<epsilon> / c"
          by (simp add: \<open>0 < c\<close> that)
      qed auto
      then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> \<bar>(2/3) ^ n\<bar> < \<epsilon>/c"
        by (meson eventually_sequentially order_le_less_trans)
      have "\<bar>g m x - g n x\<bar> < \<epsilon>"
        if "N \<le> m" "N \<le> n" and x: "x \<in> topspace X" "m \<le> n" for m n x
      proof (cases "m < n")
        case True
        have 23: "(\<Sum>k = m..<n. (2/3)^k) = 3 * ((2/3) ^ m - (2/3::real) ^ n)"
          using \<open>m \<le> n\<close>
          by (induction n) (auto simp: le_Suc_eq)
        have "\<bar>g m x - g n x\<bar> \<le> \<bar>\<Sum>k = m..<n. g (Suc k) x - g k x\<bar>"
          by (subst sum_Suc_diff' [OF \<open>m \<le> n\<close>]) linarith
        also have "\<dots> \<le> (\<Sum>k = m..<n. \<bar>g (Suc k) x - g k x\<bar>)"
          by (rule sum_abs)
        also have "\<dots> \<le> (\<Sum>k = m..<n. c * (2/3)^k / 3)"
          apply (rule sum_mono)
          using * x by blast
        also have "\<dots> = (c/3) * (\<Sum>k = m..<n. (2/3)^k)"
          by (simp add: sum_distrib_left)
        also have "\<dots> = (c/3) * 3 * ((2/3) ^ m - (2/3) ^ n)"
          by (simp add: sum_distrib_left 23)
        also have "... < (c/3) * 3 * ((2/3) ^ m)"
          using \<open>0 < c\<close> by auto
        also have "\<dots> < \<epsilon>"
          using N [OF \<open>N \<le> m\<close>] \<open>0 < c\<close> by (simp add: field_simps)
        finally show ?thesis .
      qed (use \<open>0 < \<epsilon>\<close> \<open>m \<le> n\<close> in auto)
      then show ?thesis
        by (metis dist_commute_lessI dist_real_def nle_le)
    qed
  qed auto
  define \<phi> where "\<phi> \<equiv> \<lambda>x. max a (min (h x) b)"
  show thesis
  proof
    show "continuous_map X euclidean \<phi>"
      unfolding \<phi>_def using conth by (intro continuous_intros) auto
    show "\<phi> x = f x" if "x \<in> S" for x 
    proof -
      have x: "x \<in> topspace X"
        using \<open>closedin X S\<close> closedin_subset that by blast
      have "h x = f x"
      proof (rule Met_TC.limitin_metric_unique)
        show "limitin Met_TC.mtopology (\<lambda>n. g n x) (h x) sequentially"
          using h x by (force simp: tendsto_iff eventually_sequentially)
        show "limitin Met_TC.mtopology (\<lambda>n. g n x) (f x) sequentially"
        proof (clarsimp simp: tendsto_iff)
          fix \<epsilon>::real
          assume "\<epsilon> > 0"
          then have "\<forall>\<^sub>F n in sequentially. \<bar>(2/3) ^ n\<bar> < \<epsilon>/c"
            by (intro Archimedean_eventually_pow_inverse) (auto simp: \<open>c > 0\<close>)
          then show "\<forall>\<^sub>F n in sequentially. dist (g n x) (f x) < \<epsilon>"
            apply eventually_elim
            by (smt (verit) good x good_def \<open>c > 0\<close> dist_real_def mult.commute pos_less_divide_eq that)
        qed
      qed auto
      then show ?thesis
        using that fim by (auto simp: \<phi>_def)
    qed
    then show "\<phi> ` topspace X \<subseteq> {a..b}"
      using fim \<open>a \<le> b\<close> by (auto simp: \<phi>_def)
  qed
qed


lemma Tietze_extension_realinterval:
  assumes XS: "normal_space X" "closedin X S" and T: "is_interval T" "T \<noteq> {}" 
    and contf: "continuous_map (subtopology X S) euclideanreal f" 
    and "f ` S \<subseteq> T"
  obtains g where "continuous_map X euclideanreal g"  "g ` topspace X \<subseteq> T"  "\<And>x. x \<in> S \<Longrightarrow> g x = f x"
proof -
  define \<Phi> where 
        "\<Phi> \<equiv> \<lambda>T::real set. \<forall>f. continuous_map (subtopology X S) euclidean f \<longrightarrow> f`S \<subseteq> T
               \<longrightarrow> (\<exists>g. continuous_map X euclidean g \<and> g ` topspace X \<subseteq> T \<and> (\<forall>x \<in> S. g x = f x))"
  have "\<Phi> T"
    if *: "\<And>T. \<lbrakk>bounded T; is_interval T; T \<noteq> {}\<rbrakk> \<Longrightarrow> \<Phi> T"
      and "is_interval T" "T \<noteq> {}" for T
    unfolding \<Phi>_def
  proof (intro strip)
    fix f
    assume contf: "continuous_map (subtopology X S) euclideanreal f"
      and "f ` S \<subseteq> T"
    have \<Phi>T: "\<Phi> ((\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T)"
    proof (rule *)
      show "bounded ((\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T)"
        using shrink_range [of T] by (force intro: boundedI [where B=1])
      show "is_interval ((\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T)"
        using connected_shrink that(2) is_interval_connected_1 by blast
      show "(\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T \<noteq> {}"
        using \<open>T \<noteq> {}\<close> by auto
    qed
    moreover have "continuous_map (subtopology X S) euclidean ((\<lambda>x. x / (1 + \<bar>x\<bar>)) \<circ> f)"
      by (metis contf continuous_map_compose continuous_map_into_fulltopology continuous_map_real_shrink)
    moreover have "((\<lambda>x. x / (1 + \<bar>x\<bar>)) \<circ> f) ` S \<subseteq> (\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T"
      using \<open>f ` S \<subseteq> T\<close> by auto
    ultimately obtain g 
       where contg: "continuous_map X euclidean g" 
         and gim: "g ` topspace X \<subseteq> (\<lambda>x. x / (1 + \<bar>x\<bar>)) ` T"
         and geq: "\<And>x. x \<in> S \<Longrightarrow> g x = ((\<lambda>x. x / (1 + \<bar>x\<bar>)) \<circ> f) x"
      using \<Phi>T unfolding \<Phi>_def by force
    show "\<exists>g. continuous_map X euclideanreal g \<and> g ` topspace X \<subseteq> T \<and> (\<forall>x\<in>S. g x = f x)"
    proof (intro conjI exI)
      have "continuous_map X (top_of_set {-1<..<1}) g"
        using contg continuous_map_in_subtopology gim shrink_range by blast
      then show "continuous_map X euclideanreal ((\<lambda>x. x / (1 - \<bar>x\<bar>)) \<circ> g)"
        by (rule continuous_map_compose) (auto simp: continuous_on_real_grow)
      show "((\<lambda>x. x / (1 - \<bar>x\<bar>)) \<circ> g) ` topspace X \<subseteq> T"
        using gim real_grow_shrink by fastforce
      show "\<forall>x\<in>S. ((\<lambda>x. x / (1 - \<bar>x\<bar>)) \<circ> g) x = f x"
        using geq real_grow_shrink by force
    qed
  qed
  moreover have "\<Phi> T"
    if "bounded T" "is_interval T" "T \<noteq> {}" for T
    unfolding \<Phi>_def
  proof (intro strip)
    fix f
    assume contf: "continuous_map (subtopology X S) euclideanreal f"
      and "f ` S \<subseteq> T"
    obtain a b where ab: "closure T = {a..b}"
      by (meson \<open>bounded T\<close> \<open>is_interval T\<close> compact_closure connected_compact_interval_1 
            connected_imp_connected_closure is_interval_connected)
    with \<open>T \<noteq> {}\<close> have "a \<le> b" by auto
    have "f ` S \<subseteq> {a..b}"
      using \<open>f ` S \<subseteq> T\<close> ab closure_subset by auto
    then obtain g where contg: "continuous_map X euclideanreal g"
      and gf: "\<And>x. x \<in> S \<Longrightarrow> g x = f x" and gim: "g ` topspace X \<subseteq> {a..b}"
      using Tietze_extension_closed_real_interval [OF XS contf _ \<open>a \<le> b\<close>] by metis
    define W where "W \<equiv> {x \<in> topspace X. g x \<in> closure T - T}"
    have "{a..b} - {a, b} \<subseteq> T"
      using that
      by (metis ab atLeastAtMost_diff_ends convex_interior_closure interior_atLeastAtMost_real 
          interior_subset is_interval_convex)
    with finite_imp_compact have "compact (closure T - T)"
      by (metis Diff_eq_empty_iff Diff_insert2 ab finite.emptyI finite_Diff_insert)
    then have "closedin X W"
      unfolding W_def using closedin_continuous_map_preimage [OF contg] compact_imp_closed by force
    moreover have "disjnt W S"
      unfolding W_def disjnt_iff using \<open>f ` S \<subseteq> T\<close> gf by blast
    ultimately obtain h :: "'a \<Rightarrow> real" 
      where conth: "continuous_map X (top_of_set {0..1}) h" 
            and him: "h ` W \<subseteq> {0}" "h ` S \<subseteq> {1}"
      by (metis XS normal_space_iff_Urysohn) 
    then have him01: "h ` topspace X \<subseteq> {0..1}"
      by (meson continuous_map_in_subtopology)
    obtain z where "z \<in> T"
      using \<open>T \<noteq> {}\<close> by blast
    define g' where "g' \<equiv> \<lambda>x. z + h x * (g x - z)"
    show "\<exists>g. continuous_map X euclidean g \<and> g ` topspace X \<subseteq> T \<and> (\<forall>x\<in>S. g x = f x)"
    proof (intro exI conjI)
      show "continuous_map X euclideanreal g'"
        unfolding g'_def using contg conth continuous_map_in_subtopology
        by (intro continuous_intros) auto
      show "g' ` topspace X \<subseteq> T"
        unfolding g'_def 
      proof clarify
        fix x
        assume "x \<in> topspace X"
        show "z + h x * (g x - z) \<in> T"
        proof (cases "g x \<in> T")
          case True
          define w where "w \<equiv> z + h x * (g x - z)"
          have "\<bar>h x\<bar> * \<bar>g x - z\<bar> \<le> \<bar>g x - z\<bar>" "\<bar>1 - h x\<bar> * \<bar>g x - z\<bar> \<le> \<bar>g x - z\<bar>"
            using him01 \<open>x \<in> topspace X\<close> by (force simp: intro: mult_left_le_one_le)+
          then consider "z \<le> w \<and> w \<le> g x" | "g x \<le> w \<and> w \<le> z"
            unfolding w_def by (smt (verit) left_diff_distrib mult_cancel_right2 mult_minus_right zero_less_mult_iff)
          then show ?thesis
            using \<open>is_interval T\<close> unfolding w_def is_interval_1 by (metis True \<open>z \<in> T\<close>)
        next
          case False
          then have "g x \<in> closure T"
            using \<open>x \<in> topspace X\<close> ab gim by blast
          then have "h x = 0"
            using him False \<open>x \<in> topspace X\<close> by (auto simp: W_def image_subset_iff)
          then show ?thesis
            by (simp add: \<open>z \<in> T\<close>)
        qed
      qed
      show "\<forall>x\<in>S. g' x = f x"
        using gf him by (auto simp: W_def g'_def)
    qed 
  qed
  ultimately show thesis
    using assms that unfolding \<Phi>_def by best
qed

lemma normal_space_iff_Tietze:
   "normal_space X \<longleftrightarrow>
    (\<forall>f S. closedin X S \<and>
           continuous_map (subtopology X S) euclidean f
           \<longrightarrow> (\<exists>g:: 'a \<Rightarrow> real. continuous_map X euclidean g \<and> (\<forall>x \<in> S. g x = f x)))" 
   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs 
  then show ?rhs
    by (metis Tietze_extension_realinterval empty_not_UNIV is_interval_univ subset_UNIV)
next
  assume R: ?rhs 
  show ?lhs
    unfolding normal_space_iff_Urysohn_alt
  proof clarify
    fix S T
    assume "closedin X S"
      and "closedin X T"
      and "disjnt S T"
    then have cloST: "closedin X (S \<union> T)"
      by (simp add: closedin_Un)
    moreover 
    have "continuous_map (subtopology X (S \<union> T)) euclideanreal (\<lambda>x. if x \<in> S then 0 else 1)"
      unfolding continuous_map_closedin
    proof (intro conjI strip)
      fix C :: "real set"
      define D where "D \<equiv> {x \<in> topspace X. if x \<in> S then 0 \<in> C else x \<in> T \<and> 1 \<in> C}"
      have "D \<in> {{}, S, T, S \<union> T}"
        unfolding D_def
        using closedin_subset [OF \<open>closedin X S\<close>] closedin_subset [OF \<open>closedin X T\<close>] \<open>disjnt S T\<close>
        by (auto simp: disjnt_iff)
      then have "closedin X D"
        using \<open>closedin X S\<close> \<open>closedin X T\<close> closedin_empty by blast
      with closedin_subset_topspace
      show "closedin (subtopology X (S \<union> T)) {x \<in> topspace (subtopology X (S \<union> T)). (if x \<in> S then 0::real else 1) \<in> C}"
        apply (simp add: D_def)
        by (smt (verit, best) Collect_cong Collect_mono_iff Un_def closedin_subset_topspace)
    qed auto
    ultimately obtain g :: "'a \<Rightarrow> real"  where 
      contg: "continuous_map X euclidean g" and gf: "\<forall>x \<in> S \<union> T. g x = (if x \<in> S then 0 else 1)"
      using R by blast
    then show "\<exists>f. continuous_map X euclideanreal f \<and> f ` S \<subseteq> {0} \<and> f ` T \<subseteq> {1}"
      by (smt (verit) Un_iff \<open>disjnt S T\<close> disjnt_iff image_subset_iff insert_iff)
  qed
qed

subsection \<open>random metric space stuff\<close>


lemma metrizable_imp_k_space:
  assumes "metrizable_space X"
  shows "k_space X"
proof -
  obtain M d where "Metric_space M d" and Xeq: "X = Metric_space.mtopology M d"
    using assms unfolding metrizable_space_def by metis
  then interpret Metric_space M d 
    by blast
  show ?thesis
    unfolding k_space Xeq
  proof clarsimp
    fix S
    assume "S \<subseteq> M" and S: "\<forall>K. compactin mtopology K \<longrightarrow> closedin (subtopology mtopology K) (K \<inter> S)"
    have "l \<in> S"
      if \<sigma>: "range \<sigma> \<subseteq> S" and l: "limitin mtopology \<sigma> l sequentially" for \<sigma> l
    proof -
      define K where "K \<equiv> insert l (range \<sigma>)"
      interpret submetric M d K
      proof
        show "K \<subseteq> M"
          unfolding K_def using l limitin_mspace \<open>S \<subseteq> M\<close> \<sigma> by blast
      qed
      have "compactin mtopology K"
        unfolding K_def using \<open>S \<subseteq> M\<close> \<sigma>
        by (force intro: compactin_sequence_with_limit [OF l])
      then have *: "closedin sub.mtopology (K \<inter> S)"
        by (simp add: S mtopology_submetric)
      have "\<sigma> n \<in> K \<inter> S" for n
        by (simp add: K_def range_subsetD \<sigma>)
      moreover have "limitin sub.mtopology \<sigma> l sequentially"
        using l 
        unfolding sub.limit_metric_sequentially limit_metric_sequentially
        by (force simp: K_def)
      ultimately have "l \<in> K \<inter> S"
        by (meson * \<sigma> image_subsetI sub.metric_closedin_iff_sequentially_closed) 
      then show ?thesis
        by simp
    qed
    then show "closedin mtopology S"
      unfolding metric_closedin_iff_sequentially_closed
      using \<open>S \<subseteq> M\<close> by blast
  qed
qed

lemma (in Metric_space) k_space_mtopology: "k_space mtopology"
  by (simp add: metrizable_imp_k_space metrizable_space_mtopology)

lemma k_space_euclideanreal: "k_space (euclidean :: 'a::metric_space topology)"
  using metrizable_imp_k_space metrizable_space_euclidean by auto


subsection\<open>Hereditarily normal spaces\<close>

lemma hereditarily_B:
  assumes "\<And>S T. separatedin X S T
      \<Longrightarrow> \<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
  shows "hereditarily normal_space X"
  unfolding hereditarily_def
proof (intro strip)
  fix W
  assume "W \<subseteq> topspace X"
  show "normal_space (subtopology X W)"
    unfolding normal_space_def
  proof clarify
    fix S T
    assume clo: "closedin (subtopology X W) S" "closedin (subtopology X W) T"
      and "disjnt S T"
    then have "separatedin (subtopology X W) S T"
      by (simp add: separatedin_closed_sets)
    then obtain U V where "openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
      using assms [of S T] by (meson separatedin_subtopology)
    then show "\<exists>U V. openin (subtopology X W) U \<and> openin (subtopology X W) V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
      apply (simp add: openin_subtopology_alt)
      by (meson clo closedin_imp_subset disjnt_subset1 disjnt_subset2 inf_le2)
  qed
qed

lemma hereditarily_C: 
  assumes "separatedin X S T" and norm: "\<And>U. openin X U \<Longrightarrow> normal_space (subtopology X U)"
  shows "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
proof -
  define ST where "ST \<equiv> X closure_of S \<inter> X closure_of T"
  have subX: "S \<subseteq> topspace X" "T \<subseteq> topspace X"
    by (meson \<open>separatedin X S T\<close> separation_closedin_Un_gen)+
  have sub: "S \<subseteq> topspace X - ST" "T \<subseteq> topspace X - ST"
    unfolding ST_def
    by (metis Diff_mono Diff_triv \<open>separatedin X S T\<close> Int_lower1 Int_lower2 separatedin_def)+
  have "normal_space (subtopology X (topspace X - ST))"
    by (simp add: ST_def norm closedin_Int openin_diff)
  moreover have " disjnt (subtopology X (topspace X - ST) closure_of S)
                         (subtopology X (topspace X - ST) closure_of T)"
    using Int_absorb1 ST_def sub by (fastforce simp: disjnt_iff closure_of_subtopology)
  ultimately show ?thesis
    using sub subX
    apply (simp add: normal_space_closures)
    by (metis ST_def closedin_Int closedin_closure_of closedin_def openin_trans_full)
qed

lemma hereditarily_normal_space: 
  "hereditarily normal_space X \<longleftrightarrow> (\<forall>U. openin X U \<longrightarrow> normal_space(subtopology X U))"
  by (metis hereditarily_B hereditarily_C hereditarily)

lemma hereditarily_normal_separation:
  "hereditarily normal_space X \<longleftrightarrow>
        (\<forall>S T. separatedin X S T
             \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V))"
  by (metis hereditarily_B hereditarily_C hereditarily)


lemma metrizable_imp_hereditarily_normal_space:
   "metrizable_space X \<Longrightarrow> hereditarily normal_space X"
  by (simp add: hereditarily metrizable_imp_normal_space metrizable_space_subtopology)

lemma metrizable_space_separation:
   "\<lbrakk>metrizable_space X; separatedin X S T\<rbrakk>
    \<Longrightarrow> \<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
  by (metis hereditarily hereditarily_C metrizable_imp_hereditarily_normal_space)

lemma hereditarily_normal_separation_pairwise:
   "hereditarily normal_space X \<longleftrightarrow>
    (\<forall>\<U>. finite \<U> \<and> (\<forall>S \<in> \<U>. S \<subseteq> topspace X) \<and> pairwise (separatedin X) \<U>
        \<longrightarrow> (\<exists>\<F>. (\<forall>S \<in> \<U>. openin X (\<F> S) \<and> S \<subseteq> \<F> S) \<and>
                pairwise (\<lambda>S T. disjnt (\<F> S) (\<F> T)) \<U>))"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof clarify
    fix \<U>
    assume "finite \<U>" and \<U>: "\<forall>S\<in>\<U>. S \<subseteq> topspace X" 
      and pw\<U>: "pairwise (separatedin X) \<U>"
    have "\<exists>V W. openin X V \<and> openin X W \<and> S \<subseteq> V \<and>
                    (\<forall>T. T \<in> \<U> \<and> T \<noteq> S \<longrightarrow> T \<subseteq> W) \<and> disjnt V W" 
      if "S \<in> \<U>" for S
    proof -
      have "separatedin X S (\<Union>(\<U> - {S}))"
        by (metis \<U> \<open>finite \<U>\<close> pw\<U> finite_Diff pairwise_alt separatedin_Union(1) that)
      with L show ?thesis
        unfolding hereditarily_normal_separation
        by (smt (verit) Diff_iff UnionI empty_iff insert_iff subset_iff)
    qed
    then obtain \<F> \<G> 
        where *: "\<And>S. S \<in> \<U> \<Longrightarrow> S \<subseteq> \<F> S \<and> (\<forall>T. T \<in> \<U> \<and> T \<noteq> S \<longrightarrow> T \<subseteq> \<G> S)" 
        and ope: "\<And>S. S \<in> \<U> \<Longrightarrow> openin X (\<F> S) \<and> openin X (\<G> S)" 
        and dis: "\<And>S. S \<in> \<U> \<Longrightarrow> disjnt (\<F> S) (\<G> S)" 
      by metis
    define \<H> where "\<H> \<equiv> \<lambda>S. \<F> S \<inter> (\<Inter>T \<in> \<U> - {S}. \<G> T)"
    show "\<exists>\<F>. (\<forall>S\<in>\<U>. openin X (\<F> S) \<and> S \<subseteq> \<F> S) \<and> pairwise (\<lambda>S T. disjnt (\<F> S) (\<F> T)) \<U>"
    proof (intro exI conjI strip)
      show "openin X (\<H> S)" if "S \<in> \<U>" for S
        unfolding \<H>_def 
        by (smt (verit) ope that DiffD1 \<open>finite \<U>\<close> finite_Diff finite_imageI imageE openin_Int_Inter)
      show "S \<subseteq> \<H> S" if "S \<in> \<U>" for S
        unfolding \<H>_def using "*" that by auto 
    show "pairwise (\<lambda>S T. disjnt (\<H> S) (\<H> T)) \<U>"
      using dis by (fastforce simp: disjnt_iff pairwise_alt \<H>_def)
    qed
  qed
next
  assume R: ?rhs 
  show ?lhs
    unfolding hereditarily_normal_separation
  proof (intro strip)
    fix S T
    assume "separatedin X S T"
    show "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
    proof (cases "T=S")
      case True
      then show ?thesis
        using \<open>separatedin X S T\<close> by force
    next
      case False
      have "pairwise (separatedin X) {S, T}"
        by (simp add: \<open>separatedin X S T\<close> pairwise_insert separatedin_sym)
      moreover have "\<forall>S\<in>{S, T}. S \<subseteq> topspace X"
        by (metis \<open>separatedin X S T\<close> insertE separatedin_def singletonD)
        ultimately show ?thesis
        using R by (smt (verit) False finite.emptyI finite.insertI insertCI pairwiseD)
    qed
  qed
qed

lemma hereditarily_normal_space_perfect_map_image:
   "\<lbrakk>hereditarily normal_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> hereditarily normal_space Y"
  unfolding perfect_map_def proper_map_def
  by (meson hereditarily_normal_space_continuous_closed_map_image)

lemma regular_second_countable_imp_hereditarily_normal_space:
  assumes "regular_space X \<and> second_countable X"
  shows  "hereditarily normal_space X"
  unfolding hereditarily
  proof (intro regular_Lindelof_imp_normal_space strip)
  show "regular_space (subtopology X S)" for S
    by (simp add: assms regular_space_subtopology)
  show "Lindelof_space (subtopology X S)" for S
    using assms by (simp add: second_countable_imp_Lindelof_space second_countable_subtopology)
qed


subsection\<open>Completely regular spaces\<close>

definition completely_regular_space where
 "completely_regular_space X \<equiv>
    \<forall>S x. closedin X S \<and> x \<in> topspace X - S
          \<longrightarrow> (\<exists>f::'a\<Rightarrow>real. continuous_map X (top_of_set {0..1}) f \<and>
                  f x = 0 \<and> (f ` S \<subseteq> {1}))"

lemma homeomorphic_completely_regular_space_aux:
  assumes X: "completely_regular_space X" and hom: "X homeomorphic_space Y"
  shows "completely_regular_space Y"
proof -
  obtain f g where hmf: "homeomorphic_map X Y f" and hmg: "homeomorphic_map Y X g"
    and fg: "(\<forall>x \<in> topspace X. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"
    using assms X homeomorphic_maps_map homeomorphic_space_def by fastforce
  show ?thesis
    unfolding completely_regular_space_def
  proof clarify
    fix S x
    assume A: "closedin Y S" and x: "x \<in> topspace Y" and "x \<notin> S"
    then have "closedin X (g`S)"
      using hmg homeomorphic_map_closedness_eq by blast
    moreover have "g x \<notin> g`S"
      by (meson A x \<open>x \<notin> S\<close> closedin_subset hmg homeomorphic_imp_injective_map inj_on_image_mem_iff)
    ultimately obtain \<phi> where \<phi>: "continuous_map X (top_of_set {0..1::real}) \<phi> \<and> \<phi> (g x) = 0 \<and> \<phi> ` g`S \<subseteq> {1}"
      by (metis DiffI X completely_regular_space_def hmg homeomorphic_imp_surjective_map image_eqI x)
    then have "continuous_map Y (top_of_set {0..1::real}) (\<phi> \<circ> g)"
      by (meson continuous_map_compose hmg homeomorphic_imp_continuous_map)
    then show "\<exists>\<psi>. continuous_map Y (top_of_set {0..1::real}) \<psi> \<and> \<psi> x = 0 \<and> \<psi> ` S \<subseteq> {1}"
      by (metis \<phi> comp_apply image_comp)
  qed
qed

lemma homeomorphic_completely_regular_space:
  assumes "X homeomorphic_space Y"
  shows "completely_regular_space X \<longleftrightarrow> completely_regular_space Y"
  by (meson assms homeomorphic_completely_regular_space_aux homeomorphic_space_sym)

lemma completely_regular_space_alt:
   "completely_regular_space X \<longleftrightarrow>
     (\<forall>S x. closedin X S \<longrightarrow> x \<in> topspace X - S
           \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}))"
proof -
  have "\<exists>f. continuous_map X (top_of_set {0..1::real}) f \<and> f x = 0 \<and> f ` S \<subseteq> {1}" 
    if "closedin X S" "x \<in> topspace X - S" and f: "continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
    for S x f
  proof (intro exI conjI)
    show "continuous_map X (top_of_set {0..1}) (\<lambda>x. max 0 (min (f x) 1))"
      using that
      by (auto simp: continuous_map_in_subtopology intro!: continuous_map_real_max continuous_map_real_min)
  qed (use that in auto)
  with continuous_map_in_subtopology show ?thesis
    unfolding completely_regular_space_def by metis 
qed

text \<open>As above, but with @{term openin}\<close>
lemma completely_regular_space_alt':
   "completely_regular_space X \<longleftrightarrow>
     (\<forall>S x. openin X S \<longrightarrow> x \<in> S
           \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` (topspace X - S) \<subseteq> {1}))"
  apply (simp add: completely_regular_space_alt all_closedin)
  by (meson openin_subset subsetD)

lemma completely_regular_space_gen_alt:
  fixes a b::real
  assumes "a \<noteq> b"
  shows "completely_regular_space X \<longleftrightarrow>
         (\<forall>S x. closedin X S \<longrightarrow> x \<in> topspace X - S
               \<longrightarrow> (\<exists>f. continuous_map X euclidean f \<and> f x = a \<and> (f ` S \<subseteq> {b})))"
proof -
  have "\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}" 
    if "closedin X S" "x \<in> topspace X - S" 
        and f: "continuous_map X euclidean f \<and> f x = a \<and> f ` S \<subseteq> {b}"
    for S x f
  proof (intro exI conjI)
    show "continuous_map X euclideanreal ((\<lambda>x. inverse(b - a) * (x - a)) \<circ> f)"
      using that by (intro continuous_intros) auto
  qed (use that assms in auto)
  moreover
  have "\<exists>f. continuous_map X euclidean f \<and> f x = a \<and> f ` S \<subseteq> {b}" 
    if "closedin X S" "x \<in> topspace X - S" 
        and f: "continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
    for S x f
  proof (intro exI conjI)
    show "continuous_map X euclideanreal ((\<lambda>x. a + (b - a) * x) \<circ> f)"
      using that by (intro continuous_intros) auto
  qed (use that in auto)
  ultimately show ?thesis
    unfolding completely_regular_space_alt by meson
qed

text \<open>As above, but with @{term openin}\<close>
lemma completely_regular_space_gen_alt':
  fixes a b::real
  assumes "a \<noteq> b"
  shows "completely_regular_space X \<longleftrightarrow>
         (\<forall>S x. openin X S \<longrightarrow> x \<in> S
               \<longrightarrow> (\<exists>f. continuous_map X euclidean f \<and> f x = a \<and> (f ` (topspace X - S) \<subseteq> {b})))"
  apply (simp add: completely_regular_space_gen_alt[OF assms] all_closedin)
  by (meson openin_subset subsetD)

lemma completely_regular_space_gen:
  fixes a b::real
  assumes "a < b"
  shows "completely_regular_space X \<longleftrightarrow>
         (\<forall>S x. closedin X S \<and> x \<in> topspace X - S
               \<longrightarrow> (\<exists>f. continuous_map X (top_of_set {a..b}) f \<and> f x = a \<and> f ` S \<subseteq> {b}))"
proof -
  have "\<exists>f. continuous_map X (top_of_set {a..b}) f \<and> f x = a \<and> f ` S \<subseteq> {b}" 
    if "closedin X S" "x \<in> topspace X - S" 
      and f: "continuous_map X euclidean f \<and> f x = a \<and> f ` S \<subseteq> {b}"
    for S x f
  proof (intro exI conjI)
    show "continuous_map X (top_of_set {a..b}) (\<lambda>x. max a (min (f x) b))"
      using that assms
      by (auto simp: continuous_map_in_subtopology intro!: continuous_map_real_max continuous_map_real_min)
  qed (use that assms in auto)
  with continuous_map_in_subtopology assms show ?thesis
    using completely_regular_space_gen_alt [of a b]
    by (smt (verit) atLeastAtMost_singleton atLeastatMost_empty singletonI)
qed

lemma normal_imp_completely_regular_space_A:
  assumes "normal_space X" "t1_space X"
  shows "completely_regular_space X"
  unfolding completely_regular_space_alt
proof clarify
  fix x S
  assume A: "closedin X S" "x \<notin> S"
  assume "x \<in> topspace X" 
  then have "closedin X {x}"
    by (simp add: \<open>t1_space X\<close> closedin_t1_singleton)
  with A \<open>normal_space X\<close> have "\<exists>f. continuous_map X euclideanreal f \<and> f ` {x} \<subseteq> {0} \<and> f ` S \<subseteq> {1}"
    using assms unfolding normal_space_iff_Urysohn_alt disjnt_iff by blast
  then show "\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
    by auto
qed

lemma normal_imp_completely_regular_space_B:
  assumes "normal_space X" "regular_space X"
  shows "completely_regular_space X"
  unfolding completely_regular_space_alt
proof clarify
  fix x S
  assume "closedin X S" "x \<notin> S" "x \<in> topspace X" 
  then obtain U C where "openin X U" "closedin X C" "x \<in> U" "U \<subseteq> C" "C \<subseteq> topspace X - S"
    using assms
    unfolding neighbourhood_base_of_closedin [symmetric] neighbourhood_base_of closedin_def by (metis Diff_iff)
  then obtain f where "continuous_map X euclideanreal f \<and> f ` C \<subseteq> {0} \<and> f ` S \<subseteq> {1}"
    using assms unfolding normal_space_iff_Urysohn_alt
    by (metis Diff_iff \<open>closedin X S\<close> disjnt_iff subsetD)
  then show "\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
    by (meson \<open>U \<subseteq> C\<close> \<open>x \<in> U\<close> image_subset_iff singletonD subsetD)
qed

lemma normal_imp_completely_regular_space_gen:
   "\<lbrakk>normal_space X; t1_space X \<or> Hausdorff_space X \<or> regular_space X\<rbrakk> \<Longrightarrow> completely_regular_space X"
  using normal_imp_completely_regular_space_A normal_imp_completely_regular_space_B t1_or_Hausdorff_space by blast

lemma normal_imp_completely_regular_space:
   "\<lbrakk>normal_space X; Hausdorff_space X \<or> regular_space X\<rbrakk> \<Longrightarrow> completely_regular_space X"
  by (simp add: normal_imp_completely_regular_space_gen)

lemma (in Metric_space) completely_regular_space_mtopology:
   "completely_regular_space mtopology"
  by (simp add: normal_imp_completely_regular_space normal_space_mtopology regular_space_mtopology)

lemma metrizable_imp_completely_regular_space:
   "metrizable_space X \<Longrightarrow> completely_regular_space X"
  by (simp add: metrizable_imp_normal_space metrizable_imp_regular_space normal_imp_completely_regular_space)

lemma completely_regular_space_discrete_topology:
   "completely_regular_space(discrete_topology U)"
  by (simp add: normal_imp_completely_regular_space normal_space_discrete_topology)

lemma completely_regular_space_subtopology:
  assumes "completely_regular_space X"
  shows "completely_regular_space (subtopology X S)"
  unfolding completely_regular_space_def
proof clarify
  fix A x
  assume "closedin (subtopology X S) A" and x: "x \<in> topspace (subtopology X S)" and "x \<notin> A"
  then obtain T where "closedin X T" "A = S \<inter> T" "x \<in> topspace X" "x \<in> S"
    by (force simp: closedin_subtopology_alt image_iff)
  then show "\<exists>f. continuous_map (subtopology X S) (top_of_set {0::real..1}) f \<and> f x = 0 \<and> f ` A \<subseteq> {1}"
    using assms \<open>x \<notin> A\<close>  
    apply (simp add: completely_regular_space_def continuous_map_from_subtopology)
    using continuous_map_from_subtopology by fastforce
qed

lemma completely_regular_space_retraction_map_image:
   " \<lbrakk>retraction_map X Y r; completely_regular_space X\<rbrakk> \<Longrightarrow> completely_regular_space Y"
  using completely_regular_space_subtopology hereditary_imp_retractive_property homeomorphic_completely_regular_space by blast

lemma completely_regular_imp_regular_space:
  assumes "completely_regular_space X" 
  shows "regular_space X"
proof -
  have *: "\<exists>U V. openin X U \<and> openin X V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V"
    if contf: "continuous_map X euclideanreal f" and a: "a \<in> topspace X - C" and "closedin X C"
      and fim: "f ` topspace X \<subseteq> {0..1}" and f0: "f a = 0" and f1: "f ` C \<subseteq> {1}"
    for C a f
  proof (intro exI conjI)
    show "openin X {x \<in> topspace X. f x \<in> {..<1 / 2}}" "openin X {x \<in> topspace X. f x \<in> {1 / 2<..}}"
      using openin_continuous_map_preimage [OF contf]
      by (meson open_lessThan open_greaterThan open_openin)+
    show "a \<in> {x \<in> topspace X. f x \<in> {..<1 / 2}}"
      using a f0 by auto
    show "C \<subseteq> {x \<in> topspace X. f x \<in> {1 / 2<..}}"
      using \<open>closedin X C\<close> f1 closedin_subset by auto
  qed (auto simp: disjnt_iff)
  show ?thesis
    using assms
    unfolding completely_regular_space_def regular_space_def continuous_map_in_subtopology
    by (meson "*")
qed


lemma locally_compact_regular_imp_completely_regular_space:
  assumes "locally_compact_space X" "Hausdorff_space X \<or> regular_space X"
  shows "completely_regular_space X"
  unfolding completely_regular_space_def
proof clarify
  fix S x
  assume "closedin X S" and "x \<in> topspace X" and "x \<notin> S"
  have "regular_space X"
    using assms locally_compact_Hausdorff_imp_regular_space by blast
  then have nbase: "neighbourhood_base_of (\<lambda>C. compactin X C \<and> closedin X C) X"
    using assms(1) locally_compact_regular_space_neighbourhood_base by blast
  then obtain U M where "openin X U" "compactin X M" "closedin X M" "x \<in> U" "U \<subseteq> M" "M \<subseteq> topspace X - S"
    unfolding neighbourhood_base_of by (metis (no_types, lifting) Diff_iff \<open>closedin X S\<close> \<open>x \<in> topspace X\<close> \<open>x \<notin> S\<close> closedin_def)
  then have "M \<subseteq> topspace X"
    by blast
  obtain V K where "openin X V" "closedin X K" "x \<in> V" "V \<subseteq> K" "K \<subseteq> U"
    by (metis (no_types, lifting) \<open>openin X U\<close> \<open>x \<in> U\<close> neighbourhood_base_of nbase)
  have "compact_space (subtopology X M)"
    by (simp add: \<open>compactin X M\<close> compact_space_subtopology)
  then have "normal_space (subtopology X M)"
    by (simp add: \<open>regular_space X\<close> compact_Hausdorff_or_regular_imp_normal_space regular_space_subtopology)
  moreover have "closedin (subtopology X M) K"
    using \<open>K \<subseteq> U\<close> \<open>U \<subseteq> M\<close> \<open>closedin X K\<close> closedin_subset_topspace by fastforce
  moreover have "closedin (subtopology X M) (M - U)"
    by (simp add: \<open>closedin X M\<close> \<open>openin X U\<close> closedin_diff closedin_subset_topspace)
  moreover have "disjnt K (M - U)"
    by (meson DiffD2 \<open>K \<subseteq> U\<close> disjnt_iff subsetD)
  ultimately obtain f::"'a\<Rightarrow>real" where contf: "continuous_map (subtopology X M) (top_of_set {0..1}) f" 
    and f0: "f ` K \<subseteq> {0}" and f1: "f ` (M - U) \<subseteq> {1}"
    using Urysohn_lemma [of "subtopology X M" K "M-U" 0 1] by auto
  then obtain g::"'a\<Rightarrow>real" where contg: "continuous_map (subtopology X M) euclidean g" and gim: "g ` M \<subseteq> {0..1}"
    and g0: "\<And>x. x \<in> K \<Longrightarrow> g x = 0" and g1: "\<And>x. \<lbrakk>x \<in> M; x \<notin> U\<rbrakk> \<Longrightarrow> g x = 1"
    using \<open>M \<subseteq> topspace X\<close> by (force simp add: continuous_map_in_subtopology image_subset_iff)
  show "\<exists>f::'a\<Rightarrow>real. continuous_map X (top_of_set {0..1}) f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
  proof (intro exI conjI)
    show "continuous_map X (top_of_set {0..1}) (\<lambda>x. if x \<in> M then g x else 1)"
      unfolding continuous_map_closedin
    proof (intro strip conjI)
      fix C
      assume C: "closedin (top_of_set {0::real..1}) C"
      have eq: "{x \<in> topspace X. (if x \<in> M then g x else 1) \<in> C} = {x \<in> M. g x \<in> C} \<union> (if 1 \<in> C then topspace X - U else {})"
        using \<open>U \<subseteq> M\<close> \<open>M \<subseteq> topspace X\<close> g1 by auto
      show "closedin X {x \<in> topspace X. (if x \<in> M then g x else 1) \<in> C}"
        unfolding eq
      proof (intro closedin_Un)
        have "closedin euclidean C"
          using C closed_closedin closedin_closed_trans by blast
        then have "closedin (subtopology X M) {x \<in> M. g x \<in> C}"
          using closedin_continuous_map_preimage_gen [OF contg] \<open>M \<subseteq> topspace X\<close> by auto
        then show "closedin X {x \<in> M. g x \<in> C}"
          using \<open>closedin X M\<close> closedin_trans_full by blast
      qed (use \<open>openin X U\<close> in force)
    qed (use gim in force)
    show "(if x \<in> M then g x else 1) = 0"
      using \<open>U \<subseteq> M\<close> \<open>V \<subseteq> K\<close> g0 \<open>x \<in> U\<close> \<open>x \<in> V\<close> by auto
    show "(\<lambda>x. if x \<in> M then g x else 1) ` S \<subseteq> {1}"
      using \<open>M \<subseteq> topspace X - S\<close> by auto
  qed
qed

lemma completely_regular_eq_regular_space:
   "locally_compact_space X
        \<Longrightarrow> (completely_regular_space X \<longleftrightarrow> regular_space X)"
  using completely_regular_imp_regular_space locally_compact_regular_imp_completely_regular_space 
  by blast

lemma completely_regular_space_prod_topology:
   "completely_regular_space (prod_topology X Y) \<longleftrightarrow>
      topspace (prod_topology X Y) = {} \<or>
      completely_regular_space X \<and> completely_regular_space Y" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (rule topological_property_of_prod_component) 
       (auto simp: completely_regular_space_subtopology homeomorphic_completely_regular_space)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "topspace(prod_topology X Y) = {}")
    case False
    then have X: "completely_regular_space X" and Y: "completely_regular_space Y"
      using R by blast+
    show ?thesis
      unfolding completely_regular_space_alt'
    proof clarify
      fix W x y
      assume "openin (prod_topology X Y) W" and "(x, y) \<in> W"
      then obtain U V where "openin X U" "openin Y V" "x \<in> U" "y \<in> V" "U\<times>V \<subseteq> W"
        by (force simp: openin_prod_topology_alt)
      then have "x \<in> topspace X" "y \<in> topspace Y"
        using openin_subset by fastforce+
      obtain f where contf: "continuous_map X euclideanreal f" and "f x = 0" 
        and f1: "\<And>x. x \<in> topspace X \<Longrightarrow> x \<notin> U \<Longrightarrow> f x = 1"
        using X \<open>openin X U\<close> \<open>x \<in> U\<close> unfolding completely_regular_space_alt'
        by (smt (verit, best) Diff_iff image_subset_iff singletonD)
      obtain g where contg: "continuous_map Y euclideanreal g" and "g y = 0" 
        and g1: "\<And>y. y \<in> topspace Y \<Longrightarrow> y \<notin> V \<Longrightarrow> g y = 1"
        using Y \<open>openin Y V\<close> \<open>y \<in> V\<close> unfolding completely_regular_space_alt'
        by (smt (verit, best) Diff_iff image_subset_iff singletonD)
      define h where "h \<equiv> \<lambda>(x,y). 1 - (1 - f x) * (1 - g y)"
      show "\<exists>h. continuous_map (prod_topology X Y) euclideanreal h \<and> h (x,y) = 0 \<and> h ` (topspace (prod_topology X Y) - W) \<subseteq> {1}"
      proof (intro exI conjI)
        have "continuous_map (prod_topology X Y) euclideanreal (f \<circ> fst)"
          using contf continuous_map_of_fst by blast
        moreover
        have "continuous_map (prod_topology X Y) euclideanreal (g \<circ> snd)"
          using contg continuous_map_of_snd by blast
        ultimately
        show "continuous_map (prod_topology X Y) euclideanreal h"
          unfolding o_def h_def case_prod_unfold
          by (intro continuous_intros) auto
        show "h (x, y) = 0"
          by (simp add: h_def \<open>f x = 0\<close> \<open>g y = 0\<close>)
        show "h ` (topspace (prod_topology X Y) - W) \<subseteq> {1}"
          using \<open>U \<times> V \<subseteq> W\<close> f1 g1 by (force simp: h_def)
      qed
    qed
  qed (force simp: completely_regular_space_def)
qed


lemma completely_regular_space_product_topology:
   "completely_regular_space (product_topology X I) \<longleftrightarrow>
    (\<Pi>\<^sub>E i\<in>I. topspace(X i)) = {} \<or> (\<forall>i \<in> I. completely_regular_space (X i))" 
   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (rule topological_property_of_product_component) 
       (auto simp: completely_regular_space_subtopology homeomorphic_completely_regular_space)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "(\<Pi>\<^sub>E i\<in>I. topspace(X i)) = {}")
    case False
    show ?thesis
      unfolding completely_regular_space_alt'
    proof clarify
      fix W x
      assume W: "openin (product_topology X I) W" and "x \<in> W"
      then obtain U where finU: "finite {i \<in> I. U i \<noteq> topspace (X i)}" 
             and ope: "\<And>i. i\<in>I \<Longrightarrow> openin (X i) (U i)" 
             and x: "x \<in> Pi\<^sub>E I U" and "Pi\<^sub>E I U \<subseteq> W"
        by (auto simp: openin_product_topology_alt)
      have "\<forall>i \<in> I. openin (X i) (U i) \<and> x i \<in> U i
              \<longrightarrow> (\<exists>f. continuous_map (X i) euclideanreal f \<and>
                       f (x i) = 0 \<and> (\<forall>x \<in> topspace(X i). x \<notin> U i \<longrightarrow> f x = 1))"
        using R unfolding completely_regular_space_alt'
        by (smt (verit) DiffI False image_subset_iff singletonD)
      with ope x have "\<And>i. \<exists>f. i \<in> I \<longrightarrow> continuous_map (X i) euclideanreal f \<and>
              f (x i) = 0 \<and> (\<forall>x \<in> topspace (X i). x \<notin> U i \<longrightarrow> f x = 1)"
        by auto
      then obtain f where f: "\<And>i. i \<in> I \<Longrightarrow> continuous_map (X i) euclideanreal (f i) \<and>
                                             f i (x i) = 0 \<and> (\<forall>x \<in> topspace (X i). x \<notin> U i \<longrightarrow> f i x = 1)"
        by metis
      define h where "h \<equiv> \<lambda>z. 1 - prod (\<lambda>i. 1 - f i (z i)) {i\<in>I. U i \<noteq> topspace(X i)}"
      show "\<exists>h. continuous_map (product_topology X I) euclideanreal h \<and> h x = 0 \<and>
                     h ` (topspace (product_topology X I) - W) \<subseteq> {1}"
      proof (intro conjI exI)
        have "continuous_map (product_topology X I) euclidean (f i \<circ> (\<lambda>x. x i))" if "i\<in>I" for i
          using f that
          by (blast intro: continuous_intros continuous_map_product_projection)
        then show "continuous_map (product_topology X I) euclideanreal h"
          unfolding h_def o_def by (intro continuous_intros) (auto simp: finU)
        show "h x = 0"
          by (simp add: h_def f)
        show "h ` (topspace (product_topology X I) - W) \<subseteq> {1}"
          proof -
          have "\<exists>i. i \<in> I \<and> U i \<noteq> topspace (X i) \<and> f i (x' i) = 1"
            if "x' \<in> (\<Pi>\<^sub>E i\<in>I. topspace (X i))" "x' \<notin> W" for x'
            using that \<open>Pi\<^sub>E I U \<subseteq> W\<close> by (smt (verit, best) PiE_iff f in_mono)
          then show ?thesis
            by (auto simp: f h_def finU)
        qed
      qed
    qed      
  qed (force simp: completely_regular_space_def)
qed


lemma (in Metric_space) t1_space_mtopology:
   "t1_space mtopology"
  using Hausdorff_space_mtopology t1_or_Hausdorff_space by blast


subsection\<open>More generally, the k-ification functor\<close>

definition kification_open 
  where "kification_open \<equiv> 
          \<lambda>X S. S \<subseteq> topspace X \<and> (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> S))"

definition kification 
  where "kification X \<equiv> topology (kification_open X)"

lemma istopology_kification_open: "istopology (kification_open X)"
  unfolding istopology_def
proof (intro conjI strip)
  show "kification_open X (S \<inter> T)"
    if "kification_open X S" and "kification_open X T" for S T
    using that unfolding kification_open_def
    by (smt (verit, best) inf.idem inf_commute inf_left_commute le_infI2 openin_Int)
  show "kification_open X (\<Union> \<K>)" if "\<forall>K\<in>\<K>. kification_open X K" for \<K>
    using that unfolding kification_open_def Int_Union by blast
qed

lemma openin_kification:
   "openin (kification X) U \<longleftrightarrow>
        U \<subseteq> topspace X \<and>
        (\<forall>K. compactin X K \<longrightarrow> openin (subtopology X K) (K \<inter> U))"
  by (metis topology_inverse' kification_def istopology_kification_open kification_open_def)

lemma openin_kification_finer:
   "openin X S \<Longrightarrow> openin (kification X) S"
  by (simp add: openin_kification openin_subset openin_subtopology_Int2)

lemma topspace_kification [simp]:
   "topspace(kification X) = topspace X"
  by (meson openin_kification openin_kification_finer openin_topspace subset_antisym)

lemma closedin_kification:
   "closedin (kification X) U \<longleftrightarrow>
      U \<subseteq> topspace X \<and>
      (\<forall>K. compactin X K \<longrightarrow> closedin (subtopology X K) (K \<inter> U))"
proof (cases "U \<subseteq> topspace X")
  case True
  then show ?thesis
    by (simp add: closedin_def Diff_Int_distrib inf_commute le_infI2 openin_kification)
qed (simp add: closedin_def)

lemma closedin_kification_finer: "closedin X S \<Longrightarrow> closedin (kification X) S"
  by (simp add: closedin_def openin_kification_finer)

lemma kification_eq_self: "kification X = X \<longleftrightarrow> k_space X"
  unfolding fun_eq_iff openin_kification k_space_alt openin_inject [symmetric]
  by (metis openin_closedin_eq)

lemma compactin_kification [simp]:
   "compactin (kification X) K \<longleftrightarrow> compactin X K" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: compactin_contractive openin_kification_finer)
next
  assume R: ?rhs
  show ?lhs
    unfolding compactin_def
  proof (intro conjI strip)
    show "K \<subseteq> topspace (kification X)"
      by (simp add: R compactin_subset_topspace)
    fix \<U>
    assume \<U>: "Ball \<U> (openin (kification X)) \<and> K \<subseteq> \<Union> \<U>"
    then have *: "\<And>U. U \<in> \<U> \<Longrightarrow> U \<subseteq> topspace X \<and> openin (subtopology X K) (K \<inter> U)"
      by (simp add: R openin_kification)
    have "K \<subseteq> topspace X" "compact_space (subtopology X K)"
      using R compactin_subspace by force+
    then have "\<exists>V. finite V \<and> V \<subseteq> (\<lambda>U. K \<inter> U) ` \<U> \<and> \<Union> V = topspace (subtopology X K)"
      unfolding compact_space
      by (smt (verit, del_insts) Int_Union \<U> * image_iff inf.order_iff inf_commute topspace_subtopology)
    then show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> K \<subseteq> \<Union> \<F>"
      by (metis Int_Union \<open>K \<subseteq> topspace X\<close> finite_subset_image inf.orderI topspace_subtopology_subset)
  qed
qed

lemma compact_space_kification [simp]:
   "compact_space(kification X) \<longleftrightarrow> compact_space X"
  by (simp add: compact_space_def)

lemma kification_kification [simp]:
   "kification(kification X) = kification X"
  unfolding openin_inject [symmetric]
proof
  fix U
  show "openin (kification (kification X)) U = openin (kification X) U"
  proof
    show "openin (kification (kification X)) U \<Longrightarrow> openin (kification X) U"
      by (metis compactin_kification inf_commute openin_kification openin_subtopology topspace_kification)
  qed (simp add: openin_kification_finer)
qed

lemma k_space_kification [iff]: "k_space(kification X)"
  using kification_eq_self by fastforce

lemma continuous_map_into_kification:
  assumes "k_space X"
  shows "continuous_map X (kification Y) f \<longleftrightarrow> continuous_map X Y f" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: continuous_map_def openin_kification_finer)
next
  assume R: ?rhs
  have "openin X {x \<in> topspace X. f x \<in> V}" if V: "openin (kification Y) V" for V
  proof -
    have "openin (subtopology X K) (K \<inter> {x \<in> topspace X. f x \<in> V})"
      if "compactin X K" for K
    proof -
      have "compactin Y (f ` K)"
        using R image_compactin that by blast
      then have "openin (subtopology Y (f ` K)) (f ` K \<inter> V)"
        by (meson V openin_kification)
      then obtain U where U: "openin Y U" "f`K \<inter> V = U \<inter> f`K"
        by (meson openin_subtopology)
      show ?thesis
        unfolding openin_subtopology
      proof (intro conjI exI)
        show "openin X {x \<in> topspace X. f x \<in> U}"
          using R U openin_continuous_map_preimage_gen by blast
      qed (use U in auto)
    qed
    then show ?thesis
      by (metis (full_types) Collect_subset assms k_space_open)
  qed
  with R show ?lhs
    by (simp add: continuous_map_def)
qed

lemma continuous_map_from_kification:
   "continuous_map X Y f \<Longrightarrow> continuous_map (kification X) Y f"
  by (simp add: continuous_map_openin_preimage_eq openin_kification_finer)

lemma continuous_map_kification:
   "continuous_map X Y f \<Longrightarrow> continuous_map (kification X) (kification Y) f"
  by (simp add: continuous_map_from_kification continuous_map_into_kification)

lemma subtopology_kification_compact:
  assumes "compactin X K"
  shows "subtopology (kification X) K = subtopology X K"
  unfolding openin_inject [symmetric]
proof
  fix U
  show "openin (subtopology (kification X) K) U = openin (subtopology X K) U"
    by (metis assms inf_commute openin_kification openin_subset openin_subtopology)
qed


lemma subtopology_kification_finer:
  assumes "openin (subtopology (kification X) S) U"
  shows "openin (kification (subtopology X S)) U"
  using assms 
  by (fastforce simp: openin_subtopology_alt image_iff openin_kification subtopology_subtopology compactin_subtopology)

lemma proper_map_from_kification:
  assumes "k_space Y"
  shows "proper_map (kification X) Y f \<longleftrightarrow> proper_map X Y f"   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: closed_map_def closedin_kification_finer proper_map_alt)
next
  assume R: ?rhs
  have "compactin Y K \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> K}" for K
    using R proper_map_alt by auto
  with R show ?lhs
    by (simp add: assms proper_map_into_k_space_eq subtopology_kification_compact)
qed

lemma perfect_map_from_kification:
   "\<lbrakk>k_space Y; perfect_map X Y f\<rbrakk> \<Longrightarrow> perfect_map(kification X) Y f"
  by (simp add: continuous_map_from_kification perfect_map_def proper_map_from_kification)

lemma k_space_perfect_map_image_eq:
  assumes "Hausdorff_space X" "perfect_map X Y f"
  shows "k_space X \<longleftrightarrow> k_space Y"
proof
  show "k_space X \<Longrightarrow> k_space Y"
    using k_space_perfect_map_image assms by blast
  assume "k_space Y"
  have "homeomorphic_map (kification X) X id"
    unfolding homeomorphic_eq_injective_perfect_map
    proof (intro conjI perfect_map_from_composition_right [where f = id])
  show "perfect_map (kification X) Y (f \<circ> id)"
    by (simp add: \<open>k_space Y\<close> assms(2) perfect_map_from_kification)
  show "continuous_map (kification X) X id"
    by (simp add: continuous_map_from_kification)
qed (use assms perfect_map_def in auto)
  then show "k_space X"
    using homeomorphic_k_space homeomorphic_space by blast 
qed

subsection\<open>One-point compactifications and the Alexandroff extension construction\<close>

lemma one_point_compactification_dense:
   "\<lbrakk>compact_space X; \<not> compactin X (topspace X - {a})\<rbrakk> \<Longrightarrow> X closure_of (topspace X - {a}) = topspace X"
  unfolding closure_of_complement
  by (metis Diff_empty closedin_compact_space interior_of_eq_empty openin_closedin_eq subset_singletonD)

lemma one_point_compactification_interior:
   "\<lbrakk>compact_space X; \<not> compactin X (topspace X - {a})\<rbrakk> \<Longrightarrow> X interior_of {a} = {}"
  by (simp add: interior_of_eq_empty_complement one_point_compactification_dense)

lemma kc_space_one_point_compactification_gen:
  assumes "compact_space X"
  shows "kc_space X \<longleftrightarrow>
         openin X (topspace X - {a}) \<and> (\<forall>K. compactin X K \<and> a\<notin>K \<longrightarrow> closedin X K) \<and>
         k_space (subtopology X (topspace X - {a})) \<and> kc_space (subtopology X (topspace X - {a}))"
 (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs show ?rhs
  proof (intro conjI strip)
    show "openin X (topspace X - {a})"
      using L kc_imp_t1_space t1_space_openin_delete_alt by auto
    then show "k_space (subtopology X (topspace X - {a}))"
      by (simp add: L assms k_space_open_subtopology_aux)
    show "closedin X k" if "compactin X k \<and> a \<notin> k" for k :: "'a set"
      using L kc_space_def that by blast
    show "kc_space (subtopology X (topspace X - {a}))"
      by (simp add: L kc_space_subtopology)
  qed
next
  assume R: ?rhs
  show ?lhs
    unfolding kc_space_def
  proof (intro strip)
    fix S
    assume "compactin X S"
    then have "S \<subseteq>topspace X"
      by (simp add: compactin_subset_topspace)
    show "closedin X S"
    proof (cases "a \<in> S")
      case True
      then have "topspace X - S = topspace X - {a} - (S - {a})"
        by auto
      moreover have "openin X (topspace X - {a} - (S - {a}))"
      proof (rule openin_trans_full)
        show "openin (subtopology X (topspace X - {a})) (topspace X - {a} - (S - {a}))"
        proof
          show "openin (subtopology X (topspace X - {a})) (topspace X - {a})"
            using R openin_open_subtopology by blast
          have "closedin (subtopology X ((topspace X - {a}) \<inter> K)) (K \<inter> (S - {a}))"
            if "compactin X K" "K \<subseteq> topspace X - {a}" for K
          proof (intro closedin_subset_topspace)
            show "closedin X (K \<inter> (S - {a}))"
              using that
              by (metis IntD1 Int_insert_right_if0 R True \<open>compactin X S\<close> closed_Int_compactin insert_Diff subset_Diff_insert)
          qed (use that in auto)
          moreover have "k_space (subtopology X (topspace X - {a}))"
            using R by blast
          moreover have "S-{a} \<subseteq> topspace X \<and> S-{a} \<subseteq> topspace X - {a}"
            using \<open>S \<subseteq> topspace X\<close> by auto
          ultimately show "closedin (subtopology X (topspace X - {a})) (S - {a})"
            using \<open>S \<subseteq> topspace X\<close> True
            by (simp add: k_space_def compactin_subtopology subtopology_subtopology)
        qed 
        show "openin X (topspace X - {a})"
          by (simp add: R)
      qed
      ultimately show ?thesis
        by (simp add: \<open>S \<subseteq> topspace X\<close> closedin_def)
    next
      case False
      then show ?thesis
        by (simp add: R \<open>compactin X S\<close>)
    qed
  qed
qed

  
inductive Alexandroff_open for X where
  base: "openin X U \<Longrightarrow> Alexandroff_open X (Some ` U)"
| ext: "\<lbrakk>compactin X C; closedin X C\<rbrakk> \<Longrightarrow> Alexandroff_open X (insert None (Some ` (topspace X - C)))"

lemma Alexandroff_open_iff: "Alexandroff_open X S \<longleftrightarrow>
   (\<exists>U. (S = Some ` U \<and> openin X U) \<or> (S = insert None (Some ` (topspace X - U)) \<and> compactin X U \<and> closedin X U))"
  by (meson Alexandroff_open.cases Alexandroff_open.ext base)

lemma Alexandroff_open_Un_aux:
  assumes U: "openin X U" and "Alexandroff_open X T"
  shows  "Alexandroff_open X (Some ` U \<union> T)"
  using \<open>Alexandroff_open X T\<close>
proof (induction rule: Alexandroff_open.induct)
  case (base V)
  then show ?case
    by (metis Alexandroff_open.base U image_Un openin_Un)
next
  case (ext C)
  have "U \<subseteq> topspace X"
    by (simp add: U openin_subset)
  then have eq: "Some ` U \<union> insert None (Some ` (topspace X - C)) = insert None (Some ` (topspace X - (C \<inter> (topspace X - U))))"
    by force
  have "closedin X (C \<inter> (topspace X - U))"
    using U ext.hyps(2) by blast
  moreover
  have "compactin X (C \<inter> (topspace X - U))"
    using U compact_Int_closedin ext.hyps(1) by blast
  ultimately show ?case
    unfolding eq using Alexandroff_open.ext by blast
qed

lemma Alexandroff_open_Un:
  assumes "Alexandroff_open X S" and "Alexandroff_open X T"
  shows "Alexandroff_open X (S \<union> T)"
  using assms
proof (induction rule: Alexandroff_open.induct)
  case (base U)
  then show ?case
    by (simp add: Alexandroff_open_Un_aux)
next
  case (ext C)
  then show ?case
    by (smt (verit, best) Alexandroff_open_Un_aux Alexandroff_open_iff Un_commute Un_insert_left closedin_def insert_absorb2)
qed

lemma Alexandroff_open_Int_aux:
  assumes U: "openin X U" and "Alexandroff_open X T"
  shows  "Alexandroff_open X (Some ` U \<inter> T)"
  using \<open>Alexandroff_open X T\<close>
proof (induction rule: Alexandroff_open.induct)
  case (base V)
  then show ?case
    by (metis Alexandroff_open.base U image_Int inj_Some openin_Int)
next
  case (ext C)
  have eq: "Some ` U \<inter> insert None (Some ` (topspace X - C)) = Some ` (topspace X - (C \<union> (topspace X - U)))"
    by force
  have "openin X (topspace X - (C \<union> (topspace X - U)))"
    using U ext.hyps(2) by blast
  then show ?case
    unfolding eq using Alexandroff_open.base by blast
qed

lemma istopology_Alexandroff_open: "istopology (Alexandroff_open X)"
  unfolding istopology_def
proof (intro conjI strip)
  fix S T
  assume "Alexandroff_open X S" and "Alexandroff_open X T"
  then show "Alexandroff_open X (S \<inter> T)"
  proof (induction rule: Alexandroff_open.induct)
    case (base U)
    then show ?case
      using Alexandroff_open_Int_aux by blast
  next
    case EC: (ext C)
    show ?case
      using \<open>Alexandroff_open X T\<close>
    proof (induction rule: Alexandroff_open.induct)
      case (base V)
      then show ?case
        by (metis Alexandroff_open.ext Alexandroff_open_Int_aux EC.hyps inf_commute)
    next
      case (ext D)
      have eq: "insert None (Some ` (topspace X - C)) \<inter> insert None (Some ` (topspace X - D))
              = insert None (Some ` (topspace X - (C \<union> D)))"
        by auto
      show ?case
        unfolding eq
        by (simp add: Alexandroff_open.ext EC.hyps closedin_Un compactin_Un ext.hyps)
    qed
  qed
next
  fix \<K>
  assume \<section>: "\<forall>K\<in>\<K>. Alexandroff_open X K"
  show "Alexandroff_open X (\<Union>\<K>)"
  proof (cases "None \<in> \<Union>\<K>")
    case True
    have "\<forall>K\<in>\<K>. \<exists>U. (openin X U \<and> K = Some ` U) \<or> (K = insert None (Some ` (topspace X - U)) \<and> compactin X U \<and> closedin X U)"
      by (metis \<section> Alexandroff_open_iff)
    then obtain U where U: 
      "\<And>K. K \<in> \<K> \<Longrightarrow> openin X (U K) \<and> K = Some ` (U K) 
                    \<or> (K = insert None (Some ` (topspace X - U K)) \<and> compactin X (U K) \<and> closedin X (U K))"
      by metis
    define \<K>N where "\<K>N \<equiv> {K \<in> \<K>. None \<in> K}"
    define A where "A \<equiv> \<Union>K\<in>\<K>-\<K>N. U K"
    define B where "B \<equiv> \<Inter>K\<in>\<K>N. U K"
    have U1: "\<And>K. K \<in> \<K>-\<K>N \<Longrightarrow> openin X (U K) \<and> K = Some ` (U K)"
      using U \<K>N_def by auto
    have U2: "\<And>K. K \<in> \<K>N \<Longrightarrow> K = insert None (Some ` (topspace X - U K)) \<and> compactin X (U K) \<and> closedin X (U K)"
      using U \<K>N_def by auto
    have eqA: "\<Union>(\<K>-\<K>N) = Some ` A"
    proof
      show "\<Union> (\<K> - \<K>N) \<subseteq> Some ` A"
        by (metis A_def Sup_le_iff U1 UN_upper subset_image_iff)
      show "Some ` A \<subseteq> \<Union> (\<K> - \<K>N)"
        using A_def U1 by blast
    qed
    have eqB: "\<Union>\<K>N = insert None (Some ` (topspace X - B))"
      using U2 True
      by (auto simp: B_def image_iff \<K>N_def)
    have "\<Union>\<K> = \<Union>\<K>N \<union> \<Union>(\<K>-\<K>N)"
      by (auto simp: \<K>N_def)
    then have eq: "\<Union>\<K> = (Some ` A) \<union> (insert None (Some ` (topspace X - B)))"
      by (simp add: eqA eqB Un_commute)
    show ?thesis
      unfolding eq
    proof (intro Alexandroff_open_Un Alexandroff_open.intros)
      show "openin X A"
        using A_def U1 by blast
      show "closedin X B"
        unfolding B_def using U2 True \<K>N_def by auto
      show "compactin X B"
        by (metis B_def U2 eqB Inf_lower Union_iff \<open>closedin X B\<close> closed_compactin imageI insertI1)
    qed
  next
    case False
    then have "\<forall>K\<in>\<K>. \<exists>U. openin X U \<and> K = Some ` U"
      by (metis Alexandroff_open.simps UnionI \<section> insertCI)
    then obtain U where U: "\<forall>K\<in>\<K>. openin X (U K) \<and> K = Some ` (U K)"
      by metis
    then have eq: "\<Union>\<K> = Some ` (\<Union> K\<in>\<K>. U K)"
      using image_iff by fastforce
    show ?thesis
      unfolding eq by (simp add: U base openin_clauses(3))
  qed
qed


definition Alexandroff_compactification where
  "Alexandroff_compactification X \<equiv> topology (Alexandroff_open X)"

lemma openin_Alexandroff_compactification:
   "openin(Alexandroff_compactification X) V \<longleftrightarrow>
        (\<exists>U. openin X U \<and> V = Some ` U) \<or>
        (\<exists>C. compactin X C \<and> closedin X C \<and> V = insert None (Some ` (topspace X - C)))"
  by (auto simp: Alexandroff_compactification_def istopology_Alexandroff_open Alexandroff_open.simps)


lemma topspace_Alexandroff_compactification [simp]:
   "topspace(Alexandroff_compactification X) = insert None (Some ` topspace X)"
   (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (force simp add: topspace_def openin_Alexandroff_compactification)
  have "None \<in> topspace (Alexandroff_compactification X)"
    by (meson closedin_empty compactin_empty insert_subset openin_Alexandroff_compactification openin_subset)
  moreover have "Some x \<in> topspace (Alexandroff_compactification X)"
    if "x \<in> topspace X" for x 
    by (meson that imageI openin_Alexandroff_compactification openin_subset openin_topspace subsetD)
  ultimately show "?rhs \<subseteq> ?lhs"
    by (auto simp: image_subset_iff)
qed

lemma closedin_Alexandroff_compactification:
   "closedin (Alexandroff_compactification X) C \<longleftrightarrow>
      (\<exists>K. compactin X K \<and> closedin X K \<and> C = Some ` K) \<or>
      (\<exists>U. openin X U \<and> C = topspace(Alexandroff_compactification X) - Some ` U)"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  show "?lhs \<Longrightarrow> ?rhs"
    apply (clarsimp simp: closedin_def openin_Alexandroff_compactification)
    by (smt (verit) Diff_Diff_Int None_notin_image_Some image_set_diff inf.absorb_iff2 inj_Some insert_Diff_if subset_insert)
  show "?rhs \<Longrightarrow> ?lhs"
    using openin_subset 
    by (fastforce simp: closedin_def openin_Alexandroff_compactification)
qed

lemma openin_Alexandroff_compactification_image_Some [simp]:
   "openin(Alexandroff_compactification X) (Some ` U) \<longleftrightarrow> openin X U"
  by (auto simp: openin_Alexandroff_compactification inj_image_eq_iff)

lemma closedin_Alexandroff_compactification_image_Some [simp]:
   "closedin (Alexandroff_compactification X) (Some ` K) \<longleftrightarrow> compactin X K \<and> closedin X K"
  by (auto simp: closedin_Alexandroff_compactification inj_image_eq_iff)

lemma open_map_Some: "open_map X (Alexandroff_compactification X) Some"
  using open_map_def openin_Alexandroff_compactification by blast

lemma continuous_map_Some: "continuous_map X (Alexandroff_compactification X) Some"
  unfolding continuous_map_def 
proof (intro conjI strip)
  fix U
  assume "openin (Alexandroff_compactification X) U"
  then consider V where "openin X V" "U = Some ` V" 
    | C where "compactin X C" "closedin X C" "U = insert None (Some ` (topspace X - C))" 
    by (auto simp: openin_Alexandroff_compactification)
  then show "openin X {x \<in> topspace X. Some x \<in> U}"
  proof cases
    case 1
    then show ?thesis
      using openin_subopen openin_subset by fastforce
  next
    case 2
    then show ?thesis
      by (simp add: closedin_def image_iff set_diff_eq)
  qed
qed auto


lemma embedding_map_Some: "embedding_map X (Alexandroff_compactification X) Some"
  by (simp add: continuous_map_Some injective_open_imp_embedding_map open_map_Some)

lemma compact_space_Alexandroff_compactification [simp]:
   "compact_space(Alexandroff_compactification X)"
proof (clarsimp simp: compact_space_alt image_subset_iff)
  fix \<U> U
  assume ope [rule_format]: "\<forall>U\<in>\<U>. openin (Alexandroff_compactification X) U"
      and cover: "\<forall>x\<in>topspace X. \<exists>X\<in>\<U>. Some x \<in> X"
      and "U \<in> \<U>" "None \<in> U"
  then have Usub: "U \<subseteq> insert None (Some ` topspace X)"
    by (metis openin_subset topspace_Alexandroff_compactification)
  with ope [OF \<open>U \<in> \<U>\<close>] \<open>None \<in> U\<close>
  obtain C where C: "compactin X C \<and> closedin X C \<and>
          insert None (Some ` topspace X) - U = Some ` C"
    by (auto simp: openin_closedin closedin_Alexandroff_compactification)
  then have D: "compactin (Alexandroff_compactification X) (insert None (Some ` topspace X) - U)"
    by (metis continuous_map_Some image_compactin)
  consider V where "openin X V" "U = Some ` V" 
    | C where "compactin X C" "closedin X C" "U = insert None (Some ` (topspace X - C))" 
    using ope [OF \<open>U \<in> \<U>\<close>] by (auto simp: openin_Alexandroff_compactification)
  then show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> (\<exists>X\<in>\<F>. None \<in> X) \<and> (\<forall>x\<in>topspace X. \<exists>X\<in>\<F>. Some x \<in> X)"
  proof cases
    case 1
    then show ?thesis
      using \<open>None \<in> U\<close> by blast      
  next
    case 2
    obtain \<F> where "finite \<F>" "\<F> \<subseteq> \<U>" "insert None (Some ` topspace X) - U \<subseteq> \<Union>\<F>"
      by (smt (verit, del_insts) C D Union_iff compactinD compactin_subset_topspace cover image_subset_iff ope subsetD)
    with \<open>U \<in> \<U>\<close> show ?thesis
      by (rule_tac x="insert U \<F>" in exI) auto
  qed
qed

lemma topspace_Alexandroff_compactification_delete:
   "topspace(Alexandroff_compactification X) - {None} = Some ` topspace X"
  by simp

lemma Alexandroff_compactification_dense:
  assumes "\<not> compact_space X"
  shows "(Alexandroff_compactification X) closure_of (Some ` topspace X) =
         topspace(Alexandroff_compactification X)"
  unfolding topspace_Alexandroff_compactification_delete [symmetric]
proof (intro one_point_compactification_dense)
  show "\<not> compactin (Alexandroff_compactification X) (topspace (Alexandroff_compactification X) - {None})"
    using assms compact_space_proper_map_preimage compact_space_subtopology embedding_map_Some embedding_map_def homeomorphic_imp_proper_map by fastforce
qed auto


lemma t0_space_one_point_compactification:
  assumes "compact_space X \<and> openin X (topspace X - {a})"
  shows "t0_space X \<longleftrightarrow> t0_space (subtopology X (topspace X - {a}))"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  show "?lhs \<Longrightarrow> ?rhs"
    using t0_space_subtopology by blast
  show "?rhs \<Longrightarrow> ?lhs"
    using assms
    unfolding t0_space_def by (bestsimp simp flip: Int_Diff dest: openin_trans_full)
qed

lemma t0_space_Alexandroff_compactification [simp]:
   "t0_space (Alexandroff_compactification X) \<longleftrightarrow> t0_space X"
  using t0_space_one_point_compactification [of "Alexandroff_compactification X" None]
  using embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_t0_space by fastforce

lemma t1_space_one_point_compactification:
  assumes Xa: "openin X (topspace X - {a})"
    and \<section>: "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk> \<Longrightarrow> closedin X K"
  shows "t1_space X \<longleftrightarrow> t1_space (subtopology X (topspace X - {a}))"  (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  show "?lhs \<Longrightarrow> ?rhs"
    using t1_space_subtopology by blast
  assume R: ?rhs
  show ?lhs
    unfolding t1_space_closedin_singleton
  proof (intro strip)
    fix x
    assume "x \<in> topspace X"
    show "closedin X {x}"
    proof (cases "x=a")
      case True
      then show ?thesis
        using \<open>x \<in> topspace X\<close> Xa closedin_def by blast
    next
      case False
      show ?thesis
        by (simp add: "\<section>" False R \<open>x \<in> topspace X\<close> closedin_t1_singleton)
    qed
  qed
qed

lemma closedin_Alexandroff_I: 
  assumes "compactin (Alexandroff_compactification X) K" "K \<subseteq> Some ` topspace X"
          "closedin (Alexandroff_compactification X) T" "K = T \<inter> Some ` topspace X"
  shows "closedin (Alexandroff_compactification X) K"
proof -
  obtain S where S: "S \<subseteq> topspace X" "K = Some ` S"
    by (meson \<open>K \<subseteq> Some ` topspace X\<close> subset_imageE)
  with assms have "compactin X S"
    by (metis compactin_subtopology embedding_map_Some embedding_map_def homeomorphic_map_compactness)
  moreover have "closedin X S"
    using assms S
    by (metis closedin_subtopology embedding_map_Some embedding_map_def homeomorphic_map_closedness)
  ultimately show ?thesis
    by (simp add: S)
qed


lemma t1_space_Alexandroff_compactification [simp]:
  "t1_space(Alexandroff_compactification X) \<longleftrightarrow> t1_space X"
proof -
  have "openin (Alexandroff_compactification X) (topspace (Alexandroff_compactification X) - {None})"
    by auto
  then show ?thesis
    using t1_space_one_point_compactification [of "Alexandroff_compactification X" None]
    using embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_t1_space 
    by (fastforce simp add: compactin_subtopology closedin_Alexandroff_I closedin_subtopology)
qed


lemma kc_space_one_point_compactification:
  assumes "compact_space X"
    and ope: "openin X (topspace X - {a})"
    and \<section>: "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk>
                \<Longrightarrow> closedin X K"
  shows "kc_space X \<longleftrightarrow>
         k_space (subtopology X (topspace X - {a})) \<and> kc_space (subtopology X (topspace X - {a}))"
proof -
  have "closedin X K"
    if "kc_space (subtopology X (topspace X - {a}))" and "compactin X K" "a \<notin> K" for K
    using that unfolding kc_space_def 
    by (metis "\<section>" Diff_empty compactin_subspace compactin_subtopology subset_Diff_insert)
  then show ?thesis
    by (metis \<open>compact_space X\<close> kc_space_one_point_compactification_gen ope)
qed

lemma kc_space_Alexandroff_compactification:
  "kc_space(Alexandroff_compactification X) \<longleftrightarrow> (k_space X \<and> kc_space X)" (is "kc_space ?Y = _")
proof -
  have "kc_space (Alexandroff_compactification X) \<longleftrightarrow>
      (k_space (subtopology ?Y (topspace ?Y - {None})) \<and> kc_space (subtopology ?Y (topspace ?Y - {None})))"
    by (rule kc_space_one_point_compactification) (auto simp: compactin_subtopology closedin_subtopology closedin_Alexandroff_I)
  also have "... \<longleftrightarrow> k_space X \<and> kc_space X"
    using embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_k_space homeomorphic_kc_space by simp blast
  finally show ?thesis .
qed


lemma regular_space_one_point_compactification:
  assumes "compact_space X" and ope: "openin X (topspace X - {a})"
    and \<section>: "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk> \<Longrightarrow> closedin X K"
  shows "regular_space X \<longleftrightarrow>
           regular_space (subtopology X (topspace X - {a})) \<and> locally_compact_space (subtopology X (topspace X - {a}))" 
    (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  show "?lhs \<Longrightarrow> ?rhs"
    using assms(1) compact_imp_locally_compact_space locally_compact_space_open_subset ope regular_space_subtopology by blast
  assume R: ?rhs
  let ?Xa = "subtopology X (topspace X - {a})"
  show ?lhs
    unfolding neighbourhood_base_of_closedin [symmetric] neighbourhood_base_of imp_conjL
  proof (intro strip)
    fix W x
    assume "openin X W" and "x \<in> W"
    show "\<exists>U V. openin X U \<and> closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
    proof (cases "x=a")
      case True
      have "compactin ?Xa (topspace X - W)"
        using \<open>openin X W\<close> assms(1) closedin_compact_space
        by (metis Diff_mono True \<open>x \<in> W\<close> compactin_subtopology empty_subsetI insert_subset openin_closedin_eq order_refl)
      then obtain V K where V: "openin ?Xa V" and K: "compactin ?Xa K" "closedin ?Xa K" and "topspace X - W \<subseteq> V" "V \<subseteq> K"
        by (metis locally_compact_space_compact_closed_compact R)
      show ?thesis
      proof (intro exI conjI)
        show "openin X (topspace X - K)"
          using "\<section>" K by blast
        show "closedin X (topspace X - V)"
          using V ope openin_trans_full by blast
        show "x \<in> topspace X - K"
        proof (rule)
          show "x \<in> topspace X"
            using \<open>openin X W\<close> \<open>x \<in> W\<close> openin_subset by blast
          show "x \<notin> K"
            using K True closedin_imp_subset by blast
        qed
        show "topspace X - K \<subseteq> topspace X - V"
          by (simp add: Diff_mono \<open>V \<subseteq> K\<close>)
        show "topspace X - V \<subseteq> W"
          using \<open>topspace X - W \<subseteq> V\<close> by auto
      qed
    next
      case False
      have "openin ?Xa ((topspace X - {a}) \<inter> W)"
        using \<open>openin X W\<close> openin_subtopology_Int2 by blast
      moreover have "x \<in> (topspace X - {a}) \<inter> W"
        using \<open>openin X W\<close> \<open>x \<in> W\<close> openin_subset False by blast
      ultimately obtain U V where "openin ?Xa U" "compactin ?Xa V" "closedin ?Xa V"
               "x \<in> U" "U \<subseteq> V" "V \<subseteq> (topspace X - {a}) \<inter> W"
        using R locally_compact_regular_space_neighbourhood_base neighbourhood_base_of
        by (metis (no_types, lifting))
      then show ?thesis
        by (meson "\<section>" le_infE ope openin_trans_full)
    qed
  qed
qed


lemma regular_space_Alexandroff_compactification:
  "regular_space(Alexandroff_compactification X) \<longleftrightarrow> regular_space X \<and> locally_compact_space X" 
  (is "regular_space ?Y = ?rhs")
proof -
  have "regular_space ?Y \<longleftrightarrow>
        regular_space (subtopology ?Y (topspace ?Y - {None})) \<and> locally_compact_space (subtopology ?Y (topspace ?Y - {None}))"
    by (rule regular_space_one_point_compactification) (auto simp: compactin_subtopology closedin_subtopology closedin_Alexandroff_I)
  also have "... \<longleftrightarrow> regular_space X \<and> locally_compact_space X"
    using embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_locally_compact_space homeomorphic_regular_space 
      by fastforce
  finally show ?thesis .
qed


lemma Hausdorff_space_one_point_compactification:
  assumes "compact_space X" and  "openin X (topspace X - {a})"
    and "\<And>K. \<lbrakk>compactin (subtopology X (topspace X - {a})) K; closedin (subtopology X (topspace X - {a})) K\<rbrakk> \<Longrightarrow> closedin X K"
  shows "Hausdorff_space X \<longleftrightarrow>
           Hausdorff_space (subtopology X (topspace X - {a})) \<and> locally_compact_space (subtopology X (topspace X - {a}))" 
    (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  show ?rhs if ?lhs
  proof -
    have "locally_compact_space (subtopology X (topspace X - {a}))"
      using assms that compact_imp_locally_compact_space locally_compact_space_open_subset 
      by blast
    with that show ?rhs
      by (simp add: Hausdorff_space_subtopology)
  qed
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (metis assms locally_compact_Hausdorff_or_regular regular_space_one_point_compactification
        regular_t1_eq_Hausdorff_space t1_space_one_point_compactification)
qed

lemma Hausdorff_space_Alexandroff_compactification:
   "Hausdorff_space(Alexandroff_compactification X) \<longleftrightarrow> Hausdorff_space X \<and> locally_compact_space X"
  by (meson compact_Hausdorff_imp_regular_space compact_space_Alexandroff_compactification 
      locally_compact_Hausdorff_or_regular regular_space_Alexandroff_compactification 
      regular_t1_eq_Hausdorff_space t1_space_Alexandroff_compactification)

lemma completely_regular_space_Alexandroff_compactification:
   "completely_regular_space(Alexandroff_compactification X) \<longleftrightarrow>
        completely_regular_space X \<and> locally_compact_space X"
  by (metis regular_space_Alexandroff_compactification completely_regular_eq_regular_space
      compact_imp_locally_compact_space compact_space_Alexandroff_compactification)

lemma Hausdorff_space_one_point_compactification_asymmetric_prod:
  assumes "compact_space X"
  shows "Hausdorff_space X \<longleftrightarrow>
         kc_space (prod_topology X (subtopology X (topspace X - {a}))) \<and>
         k_space (prod_topology X (subtopology X (topspace X - {a})))"  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "a \<in> topspace X")
  case True
  show ?thesis
  proof 
    show ?rhs if ?lhs
    proof
      show "kc_space (prod_topology X (subtopology X (topspace X - {a})))"
        using Hausdorff_imp_kc_space kc_space_prod_topology_right kc_space_subtopology that by blast
      show "k_space (prod_topology X (subtopology X (topspace X - {a})))"
        by (meson Hausdorff_imp_kc_space assms compact_imp_locally_compact_space k_space_prod_topology_left 
            kc_space_one_point_compactification_gen that)
    qed
  next
    assume R: ?rhs
    define D where "D \<equiv> (\<lambda>x. (x,x)) ` (topspace X - {a})"
    show ?lhs
    proof (cases "topspace X = {a}")
      case True
      then show ?thesis
        by (simp add: Hausdorff_space_def)
    next
      case False
      then have "kc_space X"
        using kc_space_retraction_map_image [of "prod_topology X (subtopology X (topspace X - {a}))" X fst]
        by (metis Diff_subset R True insert_Diff retraction_map_fst topspace_subtopology_subset)
      have "closedin (subtopology (prod_topology X (subtopology X (topspace X - {a}))) K) (K \<inter> D)" 
        if "compactin (prod_topology X (subtopology X (topspace X - {a}))) K" for K
      proof (intro closedin_subtopology_Int_subset[where V=K] closedin_subset_topspace)
        show "fst ` K \<times> snd ` K \<inter> D \<subseteq> fst ` K \<times> snd ` K" "K \<subseteq> fst ` K \<times> snd ` K"
          by force+
        have eq: "(fst ` K \<times> snd ` K \<inter> D) = ((\<lambda>x. (x,x)) ` (fst ` K \<inter> snd ` K))"
          using compactin_subset_topspace that by (force simp: D_def image_iff)
        have "compactin (prod_topology X (subtopology X (topspace X - {a}))) (fst ` K \<times> snd ` K \<inter> D)"
          unfolding eq
        proof (rule image_compactin [of "subtopology X (topspace X - {a})"])
          have "compactin X (fst ` K)" "compactin X (snd ` K)"
            by (meson compactin_subtopology continuous_map_fst continuous_map_snd image_compactin that)+
          moreover have "fst ` K \<inter> snd ` K \<subseteq> topspace X - {a}"
            using compactin_subset_topspace that by force
          ultimately
          show "compactin (subtopology X (topspace X - {a})) (fst ` K \<inter> snd ` K)"
            unfolding compactin_subtopology
            by (meson \<open>kc_space X\<close> closed_Int_compactin kc_space_def)
          show "continuous_map (subtopology X (topspace X - {a})) (prod_topology X (subtopology X (topspace X - {a}))) (\<lambda>x. (x,x))"
            by (simp add: continuous_map_paired)
        qed
        then show "closedin (prod_topology X (subtopology X (topspace X - {a}))) (fst ` K \<times> snd ` K \<inter> D)"
          using R compactin_imp_closedin_gen by blast
      qed
      moreover have "D \<subseteq> topspace X \<times> (topspace X \<inter> (topspace X - {a}))"
        by (auto simp: D_def)
      ultimately have *: "closedin (prod_topology X (subtopology X (topspace X - {a}))) D"
        using R by (auto simp: k_space)
      have "x=y"
        if "x \<in> topspace X" "y \<in> topspace X" 
          and \<section>: "\<And>T. \<lbrakk>(x,y) \<in> T; openin (prod_topology X X) T\<rbrakk> \<Longrightarrow> \<exists>z \<in> topspace X. (z,z) \<in> T" for x y
      proof (cases "x=a \<and> y=a")
        case False
        then consider "x\<noteq>a" | "y\<noteq>a"
          by blast
        then show ?thesis
        proof cases
          case 1
          have "\<exists>z \<in> topspace X - {a}. (z,z) \<in> T"
            if "(y,x) \<in> T" "openin (prod_topology X (subtopology X (topspace X - {a}))) T" for T
          proof -
            have "(x,y) \<in> {z \<in> topspace (prod_topology X X). (snd z,fst z) \<in> T \<inter> topspace X \<times> (topspace X - {a})}"
              by (simp add: "1" \<open>x \<in> topspace X\<close> \<open>y \<in> topspace X\<close> that)
            moreover have "openin (prod_topology X X) {z \<in> topspace (prod_topology X X). (snd z,fst z) \<in> T \<inter> topspace X \<times> (topspace X - {a})}"
            proof (rule openin_continuous_map_preimage)
              show "continuous_map (prod_topology X X) (prod_topology X X) (\<lambda>x. (snd x, fst x))"
                by (simp add: continuous_map_fst continuous_map_pairedI continuous_map_snd)
              have "openin (prod_topology X X) (topspace X \<times> (topspace X - {a}))"
                using \<open>kc_space X\<close> assms kc_space_one_point_compactification_gen openin_prod_Times_iff by fastforce
              moreover have "openin (prod_topology X X) T"
                using kc_space_one_point_compactification_gen [OF \<open>compact_space X\<close>] \<open>kc_space X\<close> that
                by (metis openin_prod_Times_iff openin_topspace openin_trans_full prod_topology_subtopology(2))
              ultimately show "openin (prod_topology X X) (T \<inter> topspace X \<times> (topspace X - {a}))"
                by blast
            qed
            ultimately show ?thesis
              by (smt (verit) \<section> Int_iff fst_conv mem_Collect_eq mem_Sigma_iff snd_conv)
          qed
          then have "(y,x) \<in> prod_topology X (subtopology X (topspace X - {a})) closure_of D"
            by (simp add: "1" D_def in_closure_of that)
          then show ?thesis
            using that "*" D_def closure_of_closedin by fastforce
        next
          case 2
          have "\<exists>z \<in> topspace X - {a}. (z,z) \<in> T"
            if "(x,y) \<in> T" "openin (prod_topology X (subtopology X (topspace X - {a}))) T" for T
          proof -
            have "openin (prod_topology X X) (topspace X \<times> (topspace X - {a}))"
              using \<open>kc_space X\<close> assms kc_space_one_point_compactification_gen openin_prod_Times_iff by fastforce
            moreover have XXT: "openin (prod_topology X X) T"
              using kc_space_one_point_compactification_gen [OF \<open>compact_space X\<close>] \<open>kc_space X\<close> that
              by (metis openin_prod_Times_iff openin_topspace openin_trans_full prod_topology_subtopology(2))
            ultimately have "openin (prod_topology X X) (T \<inter> topspace X \<times> (topspace X - {a}))"
              by blast
            then show ?thesis
              by (smt (verit) "\<section>" Diff_subset XXT mem_Sigma_iff openin_subset subsetD that topspace_prod_topology topspace_subtopology_subset)
          qed
          then have "(x,y) \<in> prod_topology X (subtopology X (topspace X - {a})) closure_of D"
            by (simp add: "2" D_def in_closure_of that)
          then show ?thesis
            using that "*" D_def closure_of_closedin by fastforce
        qed
      qed auto
      then show ?thesis
        unfolding Hausdorff_space_closedin_diagonal closure_of_subset_eq [symmetric] 
          by (force simp add: closure_of_def)
    qed
  qed
next
  case False
  then show ?thesis
    by (simp add: assms compact_imp_k_space compact_space_prod_topology kc_space_compact_prod_topology)
qed


lemma Hausdorff_space_Alexandroff_compactification_asymmetric_prod:
   "Hausdorff_space(Alexandroff_compactification X) \<longleftrightarrow>
        kc_space(prod_topology (Alexandroff_compactification X) X) \<and>
        k_space(prod_topology (Alexandroff_compactification X) X)"
    (is "Hausdorff_space ?Y = ?rhs")
proof -
  have *: "subtopology (Alexandroff_compactification X)
     (topspace (Alexandroff_compactification X) -
      {None}) homeomorphic_space X"
    using embedding_map_Some embedding_map_imp_homeomorphic_space homeomorphic_space_sym by fastforce
  have "Hausdorff_space (Alexandroff_compactification X) \<longleftrightarrow>
      (kc_space (prod_topology ?Y (subtopology ?Y (topspace ?Y - {None}))) \<and>
       k_space (prod_topology ?Y (subtopology ?Y (topspace ?Y - {None}))))"
    by (rule Hausdorff_space_one_point_compactification_asymmetric_prod) (auto simp: compactin_subtopology closedin_subtopology closedin_Alexandroff_I)
  also have "... \<longleftrightarrow> ?rhs"
    using homeomorphic_k_space homeomorphic_kc_space homeomorphic_space_prod_topology 
          homeomorphic_space_refl * by blast
  finally show ?thesis .
qed

lemma kc_space_as_compactification_unique:
  assumes "kc_space X" "compact_space X"
  shows "openin X U \<longleftrightarrow>
         (if a \<in> U then U \<subseteq> topspace X \<and> compactin X (topspace X - U)
                   else openin (subtopology X (topspace X - {a})) U)"
proof (cases "a \<in> U")
  case True
  then show ?thesis
    by (meson assms closedin_compact_space compactin_imp_closedin_gen openin_closedin_eq)
next
  case False
  then show ?thesis
  by (metis Diff_empty kc_space_one_point_compactification_gen openin_open_subtopology openin_subset subset_Diff_insert assms)
qed

lemma kc_space_as_compactification_unique_explicit:
  assumes "kc_space X" "compact_space X"
  shows "openin X U \<longleftrightarrow>
         (if a \<in> U then U \<subseteq> topspace X \<and>
                     compactin (subtopology X (topspace X - {a})) (topspace X - U) \<and>
                     closedin (subtopology X (topspace X - {a})) (topspace X - U)
                else openin (subtopology X (topspace X - {a})) U)"
  apply (simp add: kc_space_subtopology compactin_imp_closedin_gen assms compactin_subtopology cong: conj_cong)
  by (metis Diff_mono assms bot.extremum insert_subset kc_space_as_compactification_unique subset_refl)

lemma Alexandroff_compactification_unique:
  assumes "kc_space X" "compact_space X" and a: "a \<in> topspace X"
  shows "Alexandroff_compactification (subtopology X (topspace X - {a})) homeomorphic_space X"
        (is "?Y homeomorphic_space X")
proof -
  have [simp]: "topspace X \<inter> (topspace X - {a}) = topspace X - {a}"  
    by auto
  have [simp]: "insert None (Some ` A) = insert None (Some ` B) \<longleftrightarrow> A = B" 
               "insert None (Some ` A) \<noteq> Some ` B" for A B
    by auto
  have "quotient_map X ?Y (\<lambda>x. if x = a then None else Some x)"
    unfolding quotient_map_def
  proof (intro conjI strip)
    show "(\<lambda>x. if x = a then None else Some x) ` topspace X = topspace ?Y"
      using \<open>a \<in> topspace X\<close>  by force
    show "openin X {x \<in> topspace X. (if x = a then None else Some x) \<in> U} = openin ?Y U" (is "?L = ?R")
      if "U \<subseteq> topspace ?Y" for U
    proof (cases "None \<in> U")
      case True
      then obtain T where T[simp]: "U = insert None (Some ` T)"
        by (metis Int_insert_right UNIV_I UNIV_option_conv inf.orderE inf_le2 subsetI subset_imageE)
      have Tsub: "T \<subseteq> topspace X - {a}"
        using in_these_eq that by auto
      then have "{x \<in> topspace X. (if x = a then None else Some x) \<in> U} = insert a T"
        by (auto simp: a image_iff cong: conj_cong)
      then have "?L \<longleftrightarrow> openin X (insert a T)"
        by metis
      also have "\<dots> \<longleftrightarrow> ?R"
        using Tsub assms
        apply (simp add: openin_Alexandroff_compactification kc_space_as_compactification_unique_explicit [where a=a])
        by (smt (verit, best) Diff_insert2 Diff_subset closedin_imp_subset double_diff)
      finally show ?thesis .
    next
      case False
      then obtain T where [simp]: "U = Some ` T"
        by (metis Int_insert_right UNIV_I UNIV_option_conv inf.orderE inf_le2 subsetI subset_imageE)
      have **: "\<And>V. openin X V \<Longrightarrow> openin X (V - {a})"
        by (simp add: assms compactin_imp_closedin_gen openin_diff)
      have Tsub: "T \<subseteq> topspace X - {a}"
        using in_these_eq that by auto
      then have "{x \<in> topspace X. (if x = a then None else Some x) \<in> U} = T"
        by (auto simp: image_iff cong: conj_cong)
      then show ?thesis
        by (simp add: "**" Tsub openin_open_subtopology)
    qed
  qed
  moreover have "inj_on (\<lambda>x. if x = a then None else Some x) (topspace X)"
    by (auto simp: inj_on_def)
  ultimately show ?thesis
    using homeomorphic_space_sym homeomorphic_space homeomorphic_map_def by blast
qed

subsection \<open>Completely metrizable spaces\<close>

text \<open>These are topologically complete\<close>

definition completely_metrizable_space where
 "completely_metrizable_space X \<equiv> 
     \<exists>M d. Metric_space M d \<and> Metric_space.mcomplete M d \<and> X = Metric_space.mtopology M d"

lemma empty_completely_metrizable_space: 
  "topspace X = {} \<Longrightarrow> completely_metrizable_space X"
  unfolding completely_metrizable_space_def subtopology_eq_discrete_topology_empty [symmetric]
  by (metis Metric_space.mcomplete_empty_mspace discrete_metric.mtopology_discrete_metric metric_M_dd)

lemma completely_metrizable_imp_metrizable_space:
   "completely_metrizable_space X \<Longrightarrow> metrizable_space X"
  using completely_metrizable_space_def metrizable_space_def by auto

lemma (in Metric_space) completely_metrizable_space_mtopology:
   "mcomplete \<Longrightarrow> completely_metrizable_space mtopology"
  using Metric_space_axioms completely_metrizable_space_def by blast

lemma completely_metrizable_space_discrete_topology:
   "completely_metrizable_space (discrete_topology U)"
  unfolding completely_metrizable_space_def
  by (metis discrete_metric.mcomplete_discrete_metric discrete_metric.mtopology_discrete_metric metric_M_dd)

lemma completely_metrizable_space_euclideanreal:
    "completely_metrizable_space euclideanreal"
  by (metis Met_TC.mtopology_is_euclideanreal Met_TC.completely_metrizable_space_mtopology euclidean_metric)

lemma completely_metrizable_space_closedin:
  assumes X: "completely_metrizable_space X" and S: "closedin X S"
  shows "completely_metrizable_space(subtopology X S)"
proof -
  obtain M d where "Metric_space M d" and comp: "Metric_space.mcomplete M d" 
                and Xeq: "X = Metric_space.mtopology M d"
    using assms completely_metrizable_space_def by blast
  then interpret Metric_space M d
    by blast
  show ?thesis
    unfolding completely_metrizable_space_def
  proof (intro conjI exI)
    show "Metric_space S d"
      using S Xeq closedin_subset subspace by force
    have sub: "submetric_axioms M S"
      by (metis S Xeq closedin_metric submetric_axioms_def)
    then show "Metric_space.mcomplete S d"
      using Abstract_Metric_Spaces.submetric_def S Xeq comp submetric.closedin_eq_mcomplete by blast
    show "subtopology X S = Metric_space.mtopology S d"
      by (metis Metric_space_axioms Xeq sub submetric.intro submetric.mtopology_submetric)
  qed
qed

lemma homeomorphic_completely_metrizable_space_aux:
  assumes homXY: "X homeomorphic_space Y" and X: "completely_metrizable_space X"
  shows "completely_metrizable_space Y"
proof -
  obtain f g where hmf: "homeomorphic_map X Y f" and hmg: "homeomorphic_map Y X g"
    and fg: "(\<forall>x \<in> topspace X. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"
    and fim: "f ` (topspace X) = topspace Y" and gim: "g ` (topspace Y) = topspace X"
    by (smt (verit, best) homXY homeomorphic_imp_surjective_map homeomorphic_maps_map homeomorphic_space_def)
  obtain M d where Md: "Metric_space M d" "Metric_space.mcomplete M d" and Xeq: "X = Metric_space.mtopology M d"
    using X by (auto simp: completely_metrizable_space_def)
  then interpret MX: Metric_space M d by metis
  define D where "D \<equiv> \<lambda>x y. d (g x) (g y)"
  have "Metric_space (topspace Y) D"
  proof
    show "(D x y = 0) \<longleftrightarrow> (x = y)" if "x \<in> topspace Y" "y \<in> topspace Y" for x y
      unfolding D_def
      by (metis that MX.topspace_mtopology MX.zero Xeq fg gim imageI)
    show "D x z \<le> D x y +D y z"
      if "x \<in> topspace Y" "y \<in> topspace Y" "z \<in> topspace Y" for x y z
      using that MX.triangle Xeq gim by (auto simp: D_def)
  qed (auto simp: D_def MX.commute)
  then interpret MY: Metric_space "topspace Y" "\<lambda>x y. D x y" by metis
  show ?thesis
    unfolding completely_metrizable_space_def
  proof (intro exI conjI)
    show "Metric_space (topspace Y) D"
      using MY.Metric_space_axioms by blast
    have gball: "g ` MY.mball y r = MX.mball (g y) r" if "y \<in> topspace Y" for y r
      using that MX.topspace_mtopology Xeq gim
      unfolding MX.mball_def MY.mball_def by (auto simp: subset_iff image_iff D_def)
    have "\<exists>r>0. MY.mball y r \<subseteq> S" if "openin Y S" and "y \<in> S" for S y
    proof -
      have "openin X (g`S)"
        using hmg homeomorphic_map_openness_eq that by auto
      then obtain r where "r>0" "MX.mball (g y) r \<subseteq> g`S"
        using MX.openin_mtopology Xeq \<open>y \<in> S\<close> by auto
      then show ?thesis
        by (smt (verit, ccfv_SIG) MY.in_mball gball fg image_iff in_mono openin_subset subsetI that(1))
    qed
    moreover have "openin Y S"
      if "S \<subseteq> topspace Y" and "\<And>y. y \<in> S \<Longrightarrow> \<exists>r>0. MY.mball y r \<subseteq> S" for S
    proof -
      have "\<And>x. x \<in> g`S \<Longrightarrow> \<exists>r>0. MX.mball x r \<subseteq> g`S"
        by (smt (verit) gball imageE image_mono subset_iff that)
      then have "openin X (g`S)"
        using MX.openin_mtopology Xeq gim that(1) by auto
      then show ?thesis
        using hmg homeomorphic_map_openness_eq that(1) by blast
    qed
    ultimately show Yeq: "Y = MY.mtopology"
      unfolding topology_eq MY.openin_mtopology by (metis openin_subset)

    show "MY.mcomplete"
      unfolding MY.mcomplete_def
    proof (intro strip)
      fix \<sigma>
      assume \<sigma>: "MY.MCauchy \<sigma>"
      have "MX.MCauchy (g \<circ> \<sigma>)"
        unfolding MX.MCauchy_def 
      proof (intro conjI strip)
        show "range (g \<circ> \<sigma>) \<subseteq> M"
          using MY.MCauchy_def Xeq \<sigma> gim by auto
        fix \<epsilon> :: real
        assume "\<epsilon> > 0"
        then obtain N where "\<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> D (\<sigma> n) (\<sigma> n') < \<epsilon>"
          using MY.MCauchy_def \<sigma> by presburger
        then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d ((g \<circ> \<sigma>) n) ((g \<circ> \<sigma>) n') < \<epsilon>"
          by (auto simp: o_def D_def)
      qed
      then obtain x where x: "limitin MX.mtopology (g \<circ> \<sigma>) x sequentially" "x \<in> topspace X"
        using MX.limitin_mspace MX.topspace_mtopology Md Xeq unfolding MX.mcomplete_def
        by blast
      with x have "limitin MY.mtopology (f \<circ> (g \<circ> \<sigma>)) (f x) sequentially"
        by (metis Xeq Yeq continuous_map_limit hmf homeomorphic_imp_continuous_map)
      moreover have "f \<circ> (g \<circ> \<sigma>) = \<sigma>"
        using \<open>MY.MCauchy \<sigma>\<close>  by (force simp add: fg MY.MCauchy_def subset_iff)
      ultimately have "limitin MY.mtopology \<sigma> (f x) sequentially" by simp
      then show "\<exists>y. limitin MY.mtopology \<sigma> y sequentially"
        by blast 
    qed
  qed
qed

lemma homeomorphic_completely_metrizable_space:
   "X homeomorphic_space Y
        \<Longrightarrow> completely_metrizable_space X \<longleftrightarrow> completely_metrizable_space Y"
  by (meson homeomorphic_completely_metrizable_space_aux homeomorphic_space_sym)

lemma completely_metrizable_space_retraction_map_image:
  assumes r: "retraction_map X Y r" and X: "completely_metrizable_space X"
  shows "completely_metrizable_space Y"
proof -
  obtain s where s: "retraction_maps X Y r s"
    using r retraction_map_def by blast
  then have "subtopology X (s ` topspace Y) homeomorphic_space Y"
    using retraction_maps_section_image2 by blast
  then show ?thesis
    by (metis X retract_of_space_imp_closedin retraction_maps_section_image1 
        homeomorphic_completely_metrizable_space completely_metrizable_space_closedin 
        completely_metrizable_imp_metrizable_space metrizable_imp_Hausdorff_space s)
qed


subsection \<open>Product metric\<close>

text\<open>For the nicest fit with the main Euclidean theories, we choose the Euclidean product, 
though other definitions of the product work.\<close>


definition "prod_dist \<equiv> \<lambda>d1 d2 (x,y) (x',y'). sqrt(d1 x x' ^ 2 + d2 y y' ^ 2)"

lemma (in Metric_space12) prod_metric: "Metric_space (M1 \<times> M2) (prod_dist d1 d2)"
proof
  fix x y z
  assume xyz: "x \<in> M1 \<times> M2" "y \<in> M1 \<times> M2" "z \<in> M1 \<times> M2"
  have "sqrt ((d1 x1 z1)\<^sup>2 + (d2 x2 z2)\<^sup>2) \<le> sqrt ((d1 x1 y1)\<^sup>2 + (d2 x2 y2)\<^sup>2) + sqrt ((d1 y1 z1)\<^sup>2 + (d2 y2 z2)\<^sup>2)"
      (is "sqrt ?L \<le> ?R")
    if "x = (x1, x2)" "y = (y1, y2)" "z = (z1, z2)"
    for x1 x2 y1 y2 z1 z2
  proof -
    have tri: "d1 x1 z1 \<le> d1 x1 y1 + d1 y1 z1" "d2 x2 z2 \<le> d2 x2 y2 + d2 y2 z2"
      using that xyz M1.triangle [of x1 y1 z1] M2.triangle [of x2 y2 z2] by auto
    show ?thesis
    proof (rule real_le_lsqrt)
      have "?L \<le> (d1 x1 y1 + d1 y1 z1)\<^sup>2 + (d2 x2 y2 + d2 y2 z2)\<^sup>2"
        using tri by (smt (verit) M1.nonneg M2.nonneg power_mono)
      also have "... \<le> ?R\<^sup>2"
        by (metis real_sqrt_sum_squares_triangle_ineq sqrt_le_D)
      finally show "?L \<le> ?R\<^sup>2" .
    qed auto
  qed
  then show "prod_dist d1 d2 x z \<le> prod_dist d1 d2 x y + prod_dist d1 d2 y z"
    by (simp add: prod_dist_def case_prod_unfold)
qed (auto simp: M1.commute M2.commute case_prod_unfold prod_dist_def)

sublocale Metric_space12 \<subseteq> Prod_metric: Metric_space "M1\<times>M2" "prod_dist d1 d2" 
  by (simp add: prod_metric)

definition prod_metric where
 "prod_metric \<equiv> \<lambda>m1 m2. metric (mspace m1 \<times> mspace m2, prod_dist (mdist m1) (mdist m2))"

lemma submetric_prod_metric:
   "submetric (prod_metric m1 m2) (S \<times> T) = prod_metric (submetric m1 S) (submetric m2 T)"
  apply (simp add: prod_metric_def)
  by (simp add: submetric_def Metric_space.mspace_metric Metric_space.mdist_metric Metric_space12.prod_metric Metric_space12_def Metric_space_mspace_mdist Times_Int_Times)

context Metric_space12 begin

lemma component_le_prod_metric:
   "d1 x1 x2 \<le> prod_dist d1 d2 (x1,y1) (x2,y2)" "d2 y1 y2 \<le> prod_dist d1 d2 (x1,y1) (x2,y2)"
  by (auto simp: prod_dist_def)

lemma prod_metric_le_components:
  "\<lbrakk>x1 \<in> M1; y1 \<in> M1; x2 \<in> M2; y2 \<in> M2\<rbrakk>
    \<Longrightarrow> prod_dist d1 d2 (x1,x2) (y1,y2) \<le> d1 x1 y1 + d2 x2 y2"
  by (auto simp: prod_dist_def sqrt_sum_squares_le_sum)

lemma mball_prod_metric_subset:
   "Prod_metric.mball (x,y) r \<subseteq> M1.mball x r \<times> M2.mball y r"
  by clarsimp (smt (verit, best) component_le_prod_metric)

lemma mcball_prod_metric_subset:
   "Prod_metric.mcball (x,y) r \<subseteq> M1.mcball x r \<times> M2.mcball y r"
  by clarsimp (smt (verit, best) component_le_prod_metric)

lemma mball_subset_prod_metric:
   "M1.mball x1 r1 \<times> M2.mball x2 r2 \<subseteq> Prod_metric.mball (x1,x2) (r1 + r2)"
  using prod_metric_le_components by force

lemma mcball_subset_prod_metric:
   "M1.mcball x1 r1 \<times> M2.mcball x2 r2 \<subseteq> Prod_metric.mcball (x1,x2) (r1 + r2)"
  using prod_metric_le_components by force

lemma mtopology_prod_metric:
  "Prod_metric.mtopology = prod_topology M1.mtopology M2.mtopology"
  unfolding prod_topology_def
proof (rule topology_base_unique [symmetric])
  fix U
  assume "U \<in> {S \<times> T |S T. openin M1.mtopology S \<and> openin M2.mtopology T}"
  then obtain S T where Ueq: "U = S \<times> T"
    and S: "openin M1.mtopology S" and T: "openin M2.mtopology T"
    by auto
  have "S \<subseteq> M1"
    using M1.openin_mtopology S by auto
  have "T \<subseteq> M2"
    using M2.openin_mtopology T by auto
  show "openin Prod_metric.mtopology U"
    unfolding Prod_metric.openin_mtopology
  proof (intro conjI strip)
    show "U \<subseteq> M1 \<times> M2"
      using Ueq by (simp add: Sigma_mono \<open>S \<subseteq> M1\<close> \<open>T \<subseteq> M2\<close>)
    fix z
    assume "z \<in> U"
    then obtain x1 x2 where "x1 \<in> S" "x2 \<in> T" and zeq: "z = (x1,x2)"
      using Ueq by blast
    obtain r1 where "r1>0" and r1: "M1.mball x1 r1 \<subseteq> S"
      by (meson M1.openin_mtopology \<open>openin M1.mtopology S\<close> \<open>x1 \<in> S\<close>)
    obtain r2 where "r2>0" and r2: "M2.mball x2 r2 \<subseteq> T"
      by (meson M2.openin_mtopology \<open>openin M2.mtopology T\<close> \<open>x2 \<in> T\<close>)
    have "Prod_metric.mball (x1,x2) (min r1 r2) \<subseteq> U"
    proof (rule order_trans [OF mball_prod_metric_subset])
      show "M1.mball x1 (min r1 r2) \<times> M2.mball x2 (min r1 r2) \<subseteq> U"
        using Ueq r1 r2 by force
    qed
    then show "\<exists>r>0. Prod_metric.mball z r \<subseteq> U"
      by (smt (verit, del_insts) zeq \<open>0 < r1\<close> \<open>0 < r2\<close>)
  qed
next
  fix U z
  assume "openin Prod_metric.mtopology U" and "z \<in> U"
  then have "U \<subseteq> M1 \<times> M2"
    by (simp add: Prod_metric.openin_mtopology)
  then obtain x y where "x \<in> M1" "y \<in> M2" and zeq: "z = (x,y)"
    using \<open>z \<in> U\<close> by blast
  obtain r where "r>0" and r: "Prod_metric.mball (x,y) r \<subseteq> U"
    by (metis Prod_metric.openin_mtopology \<open>openin Prod_metric.mtopology U\<close> \<open>z \<in> U\<close> zeq)
  define B1 where "B1 \<equiv> M1.mball x (r/2)"
  define B2 where "B2 \<equiv> M2.mball y (r/2)"
  have "openin M1.mtopology B1" "openin M2.mtopology B2"
    by (simp_all add: B1_def B2_def)
  moreover have "(x,y) \<in> B1 \<times> B2"
    using \<open>r > 0\<close> by (simp add: \<open>x \<in> M1\<close> \<open>y \<in> M2\<close> B1_def B2_def)
  moreover have "B1 \<times> B2 \<subseteq> U"
    using r prod_metric_le_components by (force simp add: B1_def B2_def)
  ultimately show "\<exists>B. B \<in> {S \<times> T |S T. openin M1.mtopology S \<and> openin M2.mtopology T} \<and> z \<in> B \<and> B \<subseteq> U"
    by (auto simp: zeq)
qed

lemma MCauchy_prod_metric:
   "Prod_metric.MCauchy \<sigma> \<longleftrightarrow> M1.MCauchy (fst \<circ> \<sigma>) \<and> M2.MCauchy (snd \<circ> \<sigma>)"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof safe
  assume L: ?lhs
  then have "range \<sigma> \<subseteq> M1 \<times> M2"
    using Prod_metric.MCauchy_def by blast
  then have 1: "range (fst \<circ> \<sigma>) \<subseteq> M1" and 2: "range (snd \<circ> \<sigma>) \<subseteq> M2"
    by auto
  have N1: "\<exists>N. \<forall>n\<ge>N. \<forall>n'\<ge>N. d1 (fst (\<sigma> n)) (fst (\<sigma> n')) < \<epsilon>" 
    and N2: "\<exists>N. \<forall>n\<ge>N. \<forall>n'\<ge>N. d2 (snd (\<sigma> n)) (snd (\<sigma> n')) < \<epsilon>" if "\<epsilon>>0" for \<epsilon> :: real
    using that L unfolding Prod_metric.MCauchy_def
    by (smt (verit, del_insts) add.commute add_less_imp_less_left add_right_mono 
        component_le_prod_metric prod.collapse)+
  show "M1.MCauchy (fst \<circ> \<sigma>)"
    using 1 N1 M1.MCauchy_def by auto
  have "\<exists>N. \<forall>n\<ge>N. \<forall>n'\<ge>N. d2 (snd (\<sigma> n)) (snd (\<sigma> n')) < \<epsilon>" if "\<epsilon>>0" for \<epsilon> :: real
    using that L unfolding Prod_metric.MCauchy_def
    by (smt (verit, del_insts) add.commute add_less_imp_less_left add_right_mono 
        component_le_prod_metric prod.collapse)
  show "M2.MCauchy (snd \<circ> \<sigma>)"
    using 2 N2 M2.MCauchy_def by auto
next
  assume M1: "M1.MCauchy (fst \<circ> \<sigma>)" and M2: "M2.MCauchy (snd \<circ> \<sigma>)"
  then have subM12: "range (fst \<circ> \<sigma>) \<subseteq> M1" "range (snd \<circ> \<sigma>) \<subseteq> M2"
    using M1.MCauchy_def M2.MCauchy_def by blast+
  show ?lhs
    unfolding Prod_metric.MCauchy_def
  proof (intro conjI strip)
    show "range \<sigma> \<subseteq> M1 \<times> M2"
      using subM12 by (smt (verit, best) SigmaI image_subset_iff o_apply prod.collapse) 
    fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    obtain N1 where N1: "\<And>n n'. N1 \<le> n \<Longrightarrow> N1 \<le> n' \<Longrightarrow> d1 ((fst \<circ> \<sigma>) n) ((fst \<circ> \<sigma>) n') < \<epsilon>/2"
      by (meson M1.MCauchy_def \<open>0 < \<epsilon>\<close> M1 zero_less_divide_iff zero_less_numeral)
    obtain N2 where N2: "\<And>n n'. N2 \<le> n \<Longrightarrow> N2 \<le> n' \<Longrightarrow> d2 ((snd \<circ> \<sigma>) n) ((snd \<circ> \<sigma>) n') < \<epsilon>/2"
      by (meson M2.MCauchy_def \<open>0 < \<epsilon>\<close> M2 zero_less_divide_iff zero_less_numeral)
    have "prod_dist d1 d2 (\<sigma> n) (\<sigma> n') < \<epsilon>"
      if "N1 \<le> n" and "N2 \<le> n" and "N1 \<le> n'" and "N2 \<le> n'" for n n'
    proof -
      obtain a b a' b' where \<sigma>: "\<sigma> n = (a,b)" "\<sigma> n' = (a',b')"
        by fastforce+
      have "prod_dist d1 d2 (a,b) (a',b') \<le> d1 a a' + d2 b b'"
        by (metis \<open>range \<sigma> \<subseteq> M1 \<times> M2\<close> \<sigma> mem_Sigma_iff prod_metric_le_components range_subsetD)
      also have "\<dots> < \<epsilon>/2 + \<epsilon>/2"
        using N1 N2 \<sigma> that by fastforce
      finally show ?thesis
        by (simp add: \<sigma>)
    qed
    then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> prod_dist d1 d2 (\<sigma> n) (\<sigma> n') < \<epsilon>"
      by (metis order.trans linorder_le_cases)
  qed
qed


lemma mcomplete_prod_metric:
  "Prod_metric.mcomplete \<longleftrightarrow> M1 = {} \<or> M2 = {} \<or> M1.mcomplete \<and> M2.mcomplete"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "M1 = {} \<or> M2 = {}")
  case False
  then obtain x y where "x \<in> M1" "y \<in> M2"
    by blast
  have "M1.mcomplete \<and> M2.mcomplete \<Longrightarrow> Prod_metric.mcomplete"
    by (simp add: Prod_metric.mcomplete_def M1.mcomplete_def M2.mcomplete_def 
        mtopology_prod_metric MCauchy_prod_metric limitin_pairwise)
  moreover
  { assume L: "Prod_metric.mcomplete"
    have "M1.mcomplete"
      unfolding M1.mcomplete_def
    proof (intro strip)
      fix \<sigma>
      assume "M1.MCauchy \<sigma>"
      then have "Prod_metric.MCauchy (\<lambda>n. (\<sigma> n, y))"
        using \<open>y \<in> M2\<close> by (simp add: M1.MCauchy_def M2.MCauchy_def MCauchy_prod_metric)
      then obtain z where "limitin Prod_metric.mtopology (\<lambda>n. (\<sigma> n, y)) z sequentially"
        using L Prod_metric.mcomplete_def by blast
      then show "\<exists>x. limitin M1.mtopology \<sigma> x sequentially"
        by (auto simp: Prod_metric.mcomplete_def M1.mcomplete_def 
             mtopology_prod_metric limitin_pairwise o_def)
    qed
  }
  moreover
  { assume L: "Prod_metric.mcomplete"
    have "M2.mcomplete"
      unfolding M2.mcomplete_def
    proof (intro strip)
      fix \<sigma>
      assume "M2.MCauchy \<sigma>"
      then have "Prod_metric.MCauchy (\<lambda>n. (x, \<sigma> n))"
        using \<open>x \<in> M1\<close> by (simp add: M2.MCauchy_def M1.MCauchy_def MCauchy_prod_metric)
      then obtain z where "limitin Prod_metric.mtopology (\<lambda>n. (x, \<sigma> n)) z sequentially"
        using L Prod_metric.mcomplete_def by blast
      then show "\<exists>x. limitin M2.mtopology \<sigma> x sequentially"
        by (auto simp: Prod_metric.mcomplete_def M2.mcomplete_def 
             mtopology_prod_metric limitin_pairwise o_def)
    qed
  }
  ultimately show ?thesis
    using False by blast 
qed auto

lemma mbounded_prod_metric:
   "Prod_metric.mbounded U \<longleftrightarrow> M1.mbounded  (fst ` U) \<and> M2.mbounded (snd ` U)"
proof -
  have "(\<exists>B. U \<subseteq> Prod_metric.mcball (x,y) B) 
    \<longleftrightarrow> ((\<exists>B. (fst ` U) \<subseteq> M1.mcball x B) \<and> (\<exists>B. (snd ` U) \<subseteq> M2.mcball y B))" (is "?lhs \<longleftrightarrow> ?rhs")
    for x y
  proof safe
    fix B
    assume "U \<subseteq> Prod_metric.mcball (x, y) B"
    then have "(fst ` U) \<subseteq> M1.mcball x B" "(snd ` U) \<subseteq> M2.mcball y B"
      using mcball_prod_metric_subset by fastforce+
    then show "\<exists>B. (fst ` U) \<subseteq> M1.mcball x B" "\<exists>B. (snd ` U) \<subseteq> M2.mcball y B"
      by auto
  next
    fix B1 B2
    assume "(fst ` U) \<subseteq> M1.mcball x B1" "(snd ` U) \<subseteq> M2.mcball y B2"
    then have "fst ` U \<times> snd ` U \<subseteq>  M1.mcball x B1 \<times> M2.mcball y B2"
      by blast
    also have "\<dots> \<subseteq> Prod_metric.mcball (x, y) (B1+B2)"
      by (intro mcball_subset_prod_metric)
    finally show "\<exists>B. U \<subseteq> Prod_metric.mcball (x, y) B"
      by (metis subsetD subsetI subset_fst_snd)
  qed
  then show ?thesis
    by (simp add: M1.mbounded_def M2.mbounded_def Prod_metric.mbounded_def)
qed 

lemma mbounded_Times:
   "Prod_metric.mbounded (S \<times> T) \<longleftrightarrow> S = {} \<or> T = {} \<or> M1.mbounded S \<and> M2.mbounded T"
  by (auto simp: mbounded_prod_metric)


lemma mtotally_bounded_Times:
   "Prod_metric.mtotally_bounded (S \<times> T) \<longleftrightarrow>
    S = {} \<or> T = {} \<or> M1.mtotally_bounded S \<and> M2.mtotally_bounded T"
    (is "?lhs \<longleftrightarrow> _")
proof (cases "S = {} \<or> T = {}")
  case False
  then obtain x y where "x \<in> S" "y \<in> T"
    by auto
  have "M1.mtotally_bounded S" if L: ?lhs
    unfolding M1.mtotally_bounded_sequentially
  proof (intro conjI strip)
    show "S \<subseteq> M1"
      using Prod_metric.mtotally_bounded_imp_subset \<open>y \<in> T\<close> that by blast
    fix \<sigma> :: "nat \<Rightarrow> 'a"
    assume "range \<sigma> \<subseteq> S"
    with L obtain r where "strict_mono r" "Prod_metric.MCauchy ((\<lambda>n. (\<sigma> n,y)) o r)"
      unfolding Prod_metric.mtotally_bounded_sequentially
      by (smt (verit) SigmaI \<open>y \<in> T\<close> image_subset_iff)
    then have "M1.MCauchy (fst o (\<lambda>n. (\<sigma> n,y)) o r)"
      by (simp add: MCauchy_prod_metric o_def)
    with \<open>strict_mono r\<close> show "\<exists>r. strict_mono r \<and> M1.MCauchy (\<sigma> \<circ> r)"
      by (auto simp add: o_def)
  qed
  moreover
  have "M2.mtotally_bounded T" if L: ?lhs
    unfolding M2.mtotally_bounded_sequentially
  proof (intro conjI strip)
    show "T \<subseteq> M2"
      using Prod_metric.mtotally_bounded_imp_subset \<open>x \<in> S\<close> that by blast
    fix \<sigma> :: "nat \<Rightarrow> 'b"
    assume "range \<sigma> \<subseteq> T"
    with L obtain r where "strict_mono r" "Prod_metric.MCauchy ((\<lambda>n. (x,\<sigma> n)) o r)"
      unfolding Prod_metric.mtotally_bounded_sequentially
      by (smt (verit) SigmaI \<open>x \<in> S\<close> image_subset_iff)
    then have "M2.MCauchy (snd o (\<lambda>n. (x,\<sigma> n)) o r)"
      by (simp add: MCauchy_prod_metric o_def)
    with \<open>strict_mono r\<close> show "\<exists>r. strict_mono r \<and> M2.MCauchy (\<sigma> \<circ> r)"
      by (auto simp add: o_def)
  qed
  moreover have ?lhs if 1: "M1.mtotally_bounded S" and 2: "M2.mtotally_bounded T"
    unfolding Prod_metric.mtotally_bounded_sequentially
  proof (intro conjI strip)
    show "S \<times> T \<subseteq> M1 \<times> M2"
      using that 
      by (auto simp: M1.mtotally_bounded_sequentially M2.mtotally_bounded_sequentially)
    fix \<sigma> :: "nat \<Rightarrow> 'a \<times> 'b"
    assume \<sigma>: "range \<sigma> \<subseteq> S \<times> T"
    with 1 obtain r1 where r1: "strict_mono r1" "M1.MCauchy (fst o \<sigma> o r1)"
      apply (clarsimp simp: M1.mtotally_bounded_sequentially image_subset_iff)
      by (metis SigmaE comp_eq_dest_lhs fst_conv)
    from \<sigma> 2 obtain r2 where r2: "strict_mono r2" "M2.MCauchy (snd o \<sigma> o r1 o r2)"
      apply (clarsimp simp: M2.mtotally_bounded_sequentially image_subset_iff)
      by (smt (verit, best) comp_apply mem_Sigma_iff prod.collapse)
    then have "M1.MCauchy (fst \<circ> \<sigma> \<circ> r1 o r2)"
      by (simp add: M1.MCauchy_subsequence r1)
    with r2 have "Prod_metric.MCauchy (\<sigma> \<circ> (r1 \<circ> r2))"
      by (simp add: MCauchy_prod_metric o_def)
    then show "\<exists>r. strict_mono r \<and> Prod_metric.MCauchy (\<sigma> \<circ> r)"
      using r1 r2 strict_mono_o by blast
  qed
  ultimately show ?thesis
    using False by blast
qed auto

lemma mtotally_bounded_prod_metric:
   "Prod_metric.mtotally_bounded U \<longleftrightarrow>
    M1.mtotally_bounded (fst ` U) \<and> M2.mtotally_bounded (snd ` U)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume L: ?lhs
  then have "U \<subseteq> M1 \<times> M2" 
    and *: "\<And>\<sigma>. range \<sigma> \<subseteq> U \<Longrightarrow> \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> Prod_metric.MCauchy (\<sigma>\<circ>r)"
    by (simp_all add: Prod_metric.mtotally_bounded_sequentially)
  show ?rhs
    unfolding M1.mtotally_bounded_sequentially M2.mtotally_bounded_sequentially
  proof (intro conjI strip)
    show "fst ` U \<subseteq> M1" "snd ` U \<subseteq> M2"
      using \<open>U \<subseteq> M1 \<times> M2\<close> by auto
  next
    fix \<sigma> :: "nat \<Rightarrow> 'a"
    assume "range \<sigma> \<subseteq> fst ` U"
    then obtain \<zeta> where \<zeta>: "\<And>n. \<sigma> n = fst (\<zeta> n) \<and> \<zeta> n \<in> U"
      unfolding image_subset_iff image_iff by (meson UNIV_I)
    then obtain r where "strict_mono r \<and> Prod_metric.MCauchy (\<zeta>\<circ>r)"
      by (metis "*" image_subset_iff)
    with \<zeta> show "\<exists>r. strict_mono r \<and> M1.MCauchy (\<sigma> \<circ> r)"
      by (auto simp: MCauchy_prod_metric o_def)
  next
    fix \<sigma>:: "nat \<Rightarrow> 'b"
    assume "range \<sigma> \<subseteq> snd ` U"
    then obtain \<zeta> where \<zeta>: "\<And>n. \<sigma> n = snd (\<zeta> n) \<and> \<zeta> n \<in> U"
      unfolding image_subset_iff image_iff by (meson UNIV_I)
    then obtain r where "strict_mono r \<and> Prod_metric.MCauchy (\<zeta>\<circ>r)"
      by (metis "*" image_subset_iff)
    with \<zeta> show "\<exists>r. strict_mono r \<and> M2.MCauchy (\<sigma> \<circ> r)"
      by (auto simp: MCauchy_prod_metric o_def)
  qed
next
  assume ?rhs
  then have "Prod_metric.mtotally_bounded ((fst ` U) \<times> (snd ` U))"
    by (simp add: mtotally_bounded_Times)
  then show ?lhs
    by (metis Prod_metric.mtotally_bounded_subset subset_fst_snd)
qed

end


lemma metrizable_space_prod_topology:
   "metrizable_space (prod_topology X Y) \<longleftrightarrow>
    topspace(prod_topology X Y) = {} \<or> metrizable_space X \<and> metrizable_space Y"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "topspace(prod_topology X Y) = {}")
  case False
  then obtain x y where "x \<in> topspace X" "y \<in> topspace Y"
    by auto
  show ?thesis
  proof
    show "?rhs \<Longrightarrow> ?lhs"
      unfolding metrizable_space_def
      using Metric_space12.mtopology_prod_metric
      by (metis False Metric_space12.prod_metric Metric_space12_def) 
  next
    assume L: ?lhs 
    have "metrizable_space (subtopology (prod_topology X Y) (topspace X \<times> {y}))"
      "metrizable_space (subtopology (prod_topology X Y) ({x} \<times> topspace Y))"
      using L metrizable_space_subtopology by auto
    moreover
    have "(subtopology (prod_topology X Y) (topspace X \<times> {y})) homeomorphic_space X"
      by (metis \<open>y \<in> topspace Y\<close> homeomorphic_space_prod_topology_sing1 homeomorphic_space_sym prod_topology_subtopology(2))
    moreover
    have "(subtopology (prod_topology X Y) ({x} \<times> topspace Y)) homeomorphic_space Y"
      by (metis \<open>x \<in> topspace X\<close> homeomorphic_space_prod_topology_sing2 homeomorphic_space_sym prod_topology_subtopology(1))
    ultimately show ?rhs
      by (simp add: homeomorphic_metrizable_space)
  qed
qed (simp add: empty_metrizable_space)


lemma completely_metrizable_space_prod_topology:
   "completely_metrizable_space (prod_topology X Y) \<longleftrightarrow>
    topspace(prod_topology X Y) = {} \<or>
    completely_metrizable_space X \<and> completely_metrizable_space Y"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "topspace(prod_topology X Y) = {}")
  case False
  then obtain x y where "x \<in> topspace X" "y \<in> topspace Y"
    by auto
  show ?thesis
  proof
    show "?rhs \<Longrightarrow> ?lhs"
      unfolding completely_metrizable_space_def
      by (metis False Metric_space12.mtopology_prod_metric Metric_space12.mcomplete_prod_metric
          Metric_space12.prod_metric Metric_space12_def)
  next
    assume L: ?lhs 
    then have "Hausdorff_space (prod_topology X Y)"
      by (simp add: completely_metrizable_imp_metrizable_space metrizable_imp_Hausdorff_space)
    then have H: "Hausdorff_space X \<and> Hausdorff_space Y"
      using False Hausdorff_space_prod_topology by blast
    then have "closedin (prod_topology X Y) (topspace X \<times> {y}) \<and> closedin (prod_topology X Y) ({x} \<times> topspace Y)"
      using \<open>x \<in> topspace X\<close> \<open>y \<in> topspace Y\<close>
      by (auto simp: closedin_Hausdorff_sing_eq closedin_prod_Times_iff)
    with L have "completely_metrizable_space(subtopology (prod_topology X Y) (topspace X \<times> {y}))
               \<and> completely_metrizable_space(subtopology (prod_topology X Y) ({x} \<times> topspace Y))"
      by (simp add: completely_metrizable_space_closedin)
    moreover
    have "(subtopology (prod_topology X Y) (topspace X \<times> {y})) homeomorphic_space X"
      by (metis \<open>y \<in> topspace Y\<close> homeomorphic_space_prod_topology_sing1 homeomorphic_space_sym prod_topology_subtopology(2))
    moreover
    have "(subtopology (prod_topology X Y) ({x} \<times> topspace Y)) homeomorphic_space Y"
      by (metis \<open>x \<in> topspace X\<close> homeomorphic_space_prod_topology_sing2 homeomorphic_space_sym prod_topology_subtopology(1))
    ultimately show ?rhs
      by (simp add: homeomorphic_completely_metrizable_space)
  qed
qed (simp add: empty_completely_metrizable_space)


subsection \<open> Three more restrictive notions of continuity for metric spaces.           \<close>

subsubsection \<open>Lipschitz continuity\<close>

definition Lipschitz_continuous_map 
  where "Lipschitz_continuous_map \<equiv> 
      \<lambda>m1 m2 f. f ` mspace m1 \<subseteq> mspace m2 \<and>
        (\<exists>B. \<forall>x \<in> mspace m1. \<forall>y \<in> mspace m1. mdist m2 (f x) (f y) \<le> B * mdist m1 x y)"

lemma Lipschitz_continuous_map_image: 
  "Lipschitz_continuous_map m1 m2 f \<Longrightarrow> f ` mspace m1 \<subseteq> mspace m2"
  by (simp add: Lipschitz_continuous_map_def)

lemma Lipschitz_continuous_map_pos:
   "Lipschitz_continuous_map m1 m2 f \<longleftrightarrow>
    f ` mspace m1 \<subseteq> mspace m2 \<and>
        (\<exists>B>0. \<forall>x \<in> mspace m1. \<forall>y \<in> mspace m1. mdist m2 (f x) (f y) \<le> B * mdist m1 x y)"
proof -
  have "B * mdist m1 x y \<le> (\<bar>B\<bar> + 1) * mdist m1 x y" "\<bar>B\<bar> + 1 > 0" for x y B
    by (auto simp add: mult_right_mono)
  then show ?thesis
    unfolding Lipschitz_continuous_map_def by (meson dual_order.trans)
qed


lemma Lipschitz_continuous_map_eq:
  assumes "Lipschitz_continuous_map m1 m2 f" "\<And>x. x \<in> mspace m1 \<Longrightarrow> f x = g x"
  shows "Lipschitz_continuous_map m1 m2 g"
  using Lipschitz_continuous_map_def assms
  by (metis (no_types, opaque_lifting) image_subset_iff)

lemma Lipschitz_continuous_map_from_submetric:
  assumes "Lipschitz_continuous_map m1 m2 f"
  shows "Lipschitz_continuous_map (submetric m1 S) m2 f"
  unfolding Lipschitz_continuous_map_def 
proof
  show "f ` mspace (submetric m1 S) \<subseteq> mspace m2"
    using Lipschitz_continuous_map_pos assms by fastforce
qed (use assms in \<open>fastforce simp: Lipschitz_continuous_map_def\<close>)

lemma Lipschitz_continuous_map_from_submetric_mono:
   "\<lbrakk>Lipschitz_continuous_map (submetric m1 T) m2 f; S \<subseteq> T\<rbrakk>
           \<Longrightarrow> Lipschitz_continuous_map (submetric m1 S) m2 f"
  by (metis Lipschitz_continuous_map_from_submetric inf.absorb_iff2 submetric_submetric)

lemma Lipschitz_continuous_map_into_submetric:
   "Lipschitz_continuous_map m1 (submetric m2 S) f \<longleftrightarrow>
        f ` mspace m1 \<subseteq> S \<and> Lipschitz_continuous_map m1 m2 f"
  by (auto simp: Lipschitz_continuous_map_def)

lemma Lipschitz_continuous_map_const:
  "Lipschitz_continuous_map m1 m2 (\<lambda>x. c) \<longleftrightarrow>
        mspace m1 = {} \<or> c \<in> mspace m2"
  unfolding Lipschitz_continuous_map_def image_subset_iff
  by (metis all_not_in_conv mdist_nonneg mdist_zero mult_1)

lemma Lipschitz_continuous_map_id:
   "Lipschitz_continuous_map m1 m1 (\<lambda>x. x)"
  by (metis Lipschitz_continuous_map_def image_ident mult_1 order_refl)

lemma Lipschitz_continuous_map_compose:
  assumes f: "Lipschitz_continuous_map m1 m2 f" and g: "Lipschitz_continuous_map m2 m3 g"
  shows "Lipschitz_continuous_map m1 m3 (g o f)"
  unfolding Lipschitz_continuous_map_def image_subset_iff
proof
  show "\<forall>x\<in>mspace m1. (g \<circ> f) x \<in> mspace m3"
    by (metis Lipschitz_continuous_map_def assms comp_apply image_subset_iff)
  obtain B where B: "\<forall>x\<in>mspace m1. \<forall>y\<in>mspace m1. mdist m2 (f x) (f y) \<le> B * mdist m1 x y"
    using assms unfolding Lipschitz_continuous_map_def by presburger
  obtain C where "C>0" and C: "\<forall>x\<in>mspace m2. \<forall>y\<in>mspace m2. mdist m3 (g x) (g y) \<le> C * mdist m2 x y"
    using assms unfolding Lipschitz_continuous_map_pos by metis
  show "\<exists>B. \<forall>x\<in>mspace m1. \<forall>y\<in>mspace m1. mdist m3 ((g \<circ> f) x) ((g \<circ> f) y) \<le> B * mdist m1 x y"
    apply (rule_tac x="C*B" in exI)
  proof clarify
    fix x y
    assume \<section>: "x \<in> mspace m1" "y \<in> mspace m1"
    then have "mdist m3 ((g \<circ> f) x) ((g \<circ> f) y) \<le> C * mdist m2 (f x) (f y)"
      by (metis C Lipschitz_continuous_map_def f comp_apply image_subset_iff)
    also have "\<dots> \<le> C * B * mdist m1 x y"
      by (simp add: "\<section>" B \<open>0 < C\<close>)
    finally show "mdist m3 ((g \<circ> f) x) ((g \<circ> f) y) \<le> C * B * mdist m1 x y" .
  qed
qed

lemma Lipschitz_map_euclidean [simp]:
  "Lipschitz_continuous_map euclidean_metric euclidean_metric f
     = (\<exists>B. lipschitz_on B UNIV f)"
  apply (auto simp: Lipschitz_continuous_map_pos lipschitz_on_def)
   apply (meson less_le_not_le)
  by (metis dist_not_less_zero less_eq_real_def mult_zero_left not_one_le_zero zero_le_mult_iff)

subsubsection \<open>Uniform continuity\<close>

definition uniformly_continuous_map 
  where "uniformly_continuous_map \<equiv> 
      \<lambda>m1 m2 f. f ` mspace m1 \<subseteq> mspace m2 \<and>
        (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x \<in> mspace m1. \<forall>y \<in> mspace m1. 
                           mdist m1 y x < \<delta> \<longrightarrow> mdist m2 (f y) (f x) < \<epsilon>)"

lemma uniformly_continuous_map_image: 
  "uniformly_continuous_map m1 m2 f \<Longrightarrow> f ` mspace m1 \<subseteq> mspace m2"
  by (simp add: uniformly_continuous_map_def)

lemma ucmap_A:
  assumes "uniformly_continuous_map m1 m2 f"
  and "(\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0"
    and "range \<rho> \<subseteq> mspace m1" "range \<sigma> \<subseteq> mspace m1"
  shows "(\<lambda>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n))) \<longlonglongrightarrow> 0"
  using assms
  unfolding uniformly_continuous_map_def image_subset_iff tendsto_iff
  apply clarsimp
  by (metis (mono_tags, lifting) eventually_sequentially)

lemma ucmap_B:
  assumes \<section>: "\<And>\<rho> \<sigma>. \<lbrakk>range \<rho> \<subseteq> mspace m1; range \<sigma> \<subseteq> mspace m1;
              (\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0\<rbrakk>
              \<Longrightarrow> (\<lambda>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n))) \<longlonglongrightarrow> 0"
    and "0 < \<epsilon>"
    and \<rho>: "range \<rho> \<subseteq> mspace m1"
    and \<sigma>: "range \<sigma> \<subseteq> mspace m1"
    and "(\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0"
  shows "\<exists>n. mdist m2 (f (\<rho> (n::nat))) (f (\<sigma> n)) < \<epsilon>"
  using \<section> [OF \<rho> \<sigma>] assms by (meson LIMSEQ_le_const linorder_not_less)

lemma ucmap_C: 
  assumes \<section>: "\<And>\<rho> \<sigma> \<epsilon>. \<lbrakk>\<epsilon> > 0; range \<rho> \<subseteq> mspace m1; range \<sigma> \<subseteq> mspace m1;
                       ((\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0)\<rbrakk>
                      \<Longrightarrow> \<exists>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n)) < \<epsilon>"
    and fim: "f ` mspace m1 \<subseteq> mspace m2"
  shows "uniformly_continuous_map m1 m2 f"
proof -
  {assume "\<not> (\<forall>\<epsilon>>0. \<exists>\<delta>>0. \<forall>x\<in>mspace m1. \<forall>y\<in>mspace m1. mdist m1 y x < \<delta> \<longrightarrow> mdist m2 (f y) (f x) < \<epsilon>)" 
    then obtain \<epsilon> where "\<epsilon> > 0" 
      and "\<And>n. \<exists>x\<in>mspace m1. \<exists>y\<in>mspace m1. mdist m1 y x < inverse(Suc n) \<and> mdist m2 (f y) (f x) \<ge> \<epsilon>"
      by (meson inverse_Suc linorder_not_le)
    then obtain \<rho> \<sigma> where space: "range \<rho> \<subseteq> mspace m1" "range \<sigma> \<subseteq> mspace m1"
         and dist: "\<And>n. mdist m1 (\<sigma> n) (\<rho> n) < inverse(Suc n) \<and> mdist m2 (f(\<sigma> n)) (f(\<rho> n)) \<ge> \<epsilon>"
      by (metis image_subset_iff)
    have False 
      using \<section> [OF \<open>\<epsilon> > 0\<close> space] dist Lim_null_comparison
      by (smt (verit) LIMSEQ_norm_0 inverse_eq_divide mdist_commute mdist_nonneg real_norm_def)
  }
  moreover
  have "t \<in> mspace m2" if "t \<in> f ` mspace m1" for t
    using fim that by blast
  ultimately show ?thesis
    by (fastforce simp: uniformly_continuous_map_def)
qed

lemma uniformly_continuous_map_sequentially:
  "uniformly_continuous_map m1 m2 f \<longleftrightarrow>
    f ` mspace m1 \<subseteq> mspace m2 \<and>
    (\<forall>\<rho> \<sigma>. range \<rho> \<subseteq> mspace m1 \<and> range \<sigma> \<subseteq> mspace m1 \<and> (\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0
          \<longrightarrow> (\<lambda>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n))) \<longlonglongrightarrow> 0)"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (simp add: ucmap_A uniformly_continuous_map_image)
  show "?rhs \<Longrightarrow> ?lhs"
    by (intro ucmap_B ucmap_C) auto
qed


lemma uniformly_continuous_map_sequentially_alt:
    "uniformly_continuous_map m1 m2 f \<longleftrightarrow>
      f ` mspace m1 \<subseteq> mspace m2 \<and>
      (\<forall>\<epsilon>>0. \<forall>\<rho> \<sigma>. range \<rho> \<subseteq> mspace m1 \<and> range \<sigma> \<subseteq> mspace m1 \<and>
            ((\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0)
            \<longrightarrow> (\<exists>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n)) < \<epsilon>))"
   (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    using uniformly_continuous_map_image by (intro conjI strip ucmap_B | force simp: ucmap_A)+
  show "?rhs \<Longrightarrow> ?lhs"
    by (intro ucmap_C) auto
qed


lemma uniformly_continuous_map_eq:
   "\<lbrakk>\<And>x. x \<in> mspace m1 \<Longrightarrow> f x = g x; uniformly_continuous_map m1 m2 f\<rbrakk>
      \<Longrightarrow> uniformly_continuous_map m1 m2 g"
  by (simp add: uniformly_continuous_map_def)

lemma uniformly_continuous_map_from_submetric:
  assumes "uniformly_continuous_map m1 m2 f"
  shows "uniformly_continuous_map (submetric m1 S) m2 f"
  unfolding uniformly_continuous_map_def 
proof
  show "f ` mspace (submetric m1 S) \<subseteq> mspace m2"
    using assms by (auto simp: uniformly_continuous_map_def)
qed (use assms in \<open>force simp: uniformly_continuous_map_def\<close>)

lemma uniformly_continuous_map_from_submetric_mono:
   "\<lbrakk>uniformly_continuous_map (submetric m1 T) m2 f; S \<subseteq> T\<rbrakk>
           \<Longrightarrow> uniformly_continuous_map (submetric m1 S) m2 f"
  by (metis uniformly_continuous_map_from_submetric inf.absorb_iff2 submetric_submetric)

lemma uniformly_continuous_map_into_submetric:
   "uniformly_continuous_map m1 (submetric m2 S) f \<longleftrightarrow>
        f ` mspace m1 \<subseteq> S \<and> uniformly_continuous_map m1 m2 f"
  by (auto simp: uniformly_continuous_map_def)

lemma uniformly_continuous_map_const:
  "uniformly_continuous_map m1 m2 (\<lambda>x. c) \<longleftrightarrow>
        mspace m1 = {} \<or> c \<in> mspace m2"
  unfolding uniformly_continuous_map_def image_subset_iff
  by (metis empty_iff equals0I mdist_zero)

lemma uniformly_continuous_map_id:
   "uniformly_continuous_map m1 m1 (\<lambda>x. x)"
  by (metis image_ident order_refl uniformly_continuous_map_def)

lemma uniformly_continuous_map_compose:
  assumes f: "uniformly_continuous_map m1 m2 f" and g: "uniformly_continuous_map m2 m3 g"
  shows "uniformly_continuous_map m1 m3 (g o f)"
  by (smt (verit, ccfv_threshold) comp_apply f g image_subset_iff uniformly_continuous_map_def)

lemma uniformly_continuous_map_real_const:
   "uniformly_continuous_map m euclidean_metric (\<lambda>x. c)"
  by (simp add: euclidean_metric_def uniformly_continuous_map_const)

lemma uniformly_continuous_map_euclidean:
  "uniformly_continuous_map euclidean_metric euclidean_metric f
     = uniformly_continuous_on UNIV f"
  by (force simp add: uniformly_continuous_map_def isUCont_def)

subsubsection \<open>Cauchy continuity\<close>

definition Cauchy_continuous_map where
 "Cauchy_continuous_map \<equiv>
  \<lambda>m1 m2 f. \<forall>\<sigma>. Metric_space.MCauchy (mspace m1) (mdist m1) \<sigma> 
            \<longrightarrow> Metric_space.MCauchy (mspace m2) (mdist m2) (f \<circ> \<sigma>)"

lemma Cauchy_continuous_map_image:
  assumes "Cauchy_continuous_map m1 m2 f"
  shows "f ` mspace m1 \<subseteq> mspace m2"
proof clarsimp
  fix x
  assume "x \<in> mspace m1"
  then have "Metric_space.MCauchy (mspace m1) (mdist m1) (\<lambda>n. x)"
    by (simp add: Metric_space.MCauchy_const Metric_space_mspace_mdist)
  then have "Metric_space.MCauchy (mspace m2) (mdist m2) (f \<circ> (\<lambda>n. x))"
    by (meson Cauchy_continuous_map_def assms)
  then show "f x \<in> mspace m2"
    by (simp add: Metric_space.MCauchy_def [OF Metric_space_mspace_mdist])
qed


lemma Cauchy_continuous_map_eq:
   "\<lbrakk>\<And>x. x \<in> mspace m1 \<Longrightarrow> f x = g x; Cauchy_continuous_map m1 m2 f\<rbrakk>
      \<Longrightarrow> Cauchy_continuous_map m1 m2 g"
  by (simp add: image_subset_iff Cauchy_continuous_map_def Metric_space.MCauchy_def [OF Metric_space_mspace_mdist])

lemma Cauchy_continuous_map_from_submetric:
  assumes "Cauchy_continuous_map m1 m2 f"
  shows "Cauchy_continuous_map (submetric m1 S) m2 f"
  using assms
  by (simp add: image_subset_iff Cauchy_continuous_map_def Metric_space.MCauchy_def [OF Metric_space_mspace_mdist])

lemma Cauchy_continuous_map_from_submetric_mono:
   "\<lbrakk>Cauchy_continuous_map (submetric m1 T) m2 f; S \<subseteq> T\<rbrakk>
           \<Longrightarrow> Cauchy_continuous_map (submetric m1 S) m2 f"
  by (metis Cauchy_continuous_map_from_submetric inf.absorb_iff2 submetric_submetric)

lemma Cauchy_continuous_map_into_submetric:
   "Cauchy_continuous_map m1 (submetric m2 S) f \<longleftrightarrow>
   f ` mspace m1 \<subseteq> S \<and> Cauchy_continuous_map m1 m2 f"  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "?lhs \<Longrightarrow> Cauchy_continuous_map m1 m2 f"
    by (simp add: Cauchy_continuous_map_def Metric_space.MCauchy_def [OF Metric_space_mspace_mdist])
  moreover have "?rhs \<Longrightarrow> ?lhs"
    by (bestsimp simp add: Cauchy_continuous_map_def  Metric_space.MCauchy_def [OF Metric_space_mspace_mdist])
  ultimately show ?thesis
    by (metis Cauchy_continuous_map_image le_inf_iff mspace_submetric)
qed

lemma Cauchy_continuous_map_const [simp]:
  "Cauchy_continuous_map m1 m2 (\<lambda>x. c) \<longleftrightarrow> mspace m1 = {} \<or> c \<in> mspace m2"
proof -
   have "mspace m1 = {} \<Longrightarrow> Cauchy_continuous_map m1 m2 (\<lambda>x. c)"
    by (simp add: Cauchy_continuous_map_def Metric_space.MCauchy_def Metric_space_mspace_mdist)
  moreover have "c \<in> mspace m2 \<Longrightarrow> Cauchy_continuous_map m1 m2 (\<lambda>x. c)"
    by (simp add: Cauchy_continuous_map_def o_def Metric_space.MCauchy_const [OF Metric_space_mspace_mdist])
  ultimately show ?thesis
    using Cauchy_continuous_map_image by blast
qed

lemma Cauchy_continuous_map_id [simp]:
   "Cauchy_continuous_map m1 m1 (\<lambda>x. x)"
  by (simp add: Cauchy_continuous_map_def o_def)

lemma Cauchy_continuous_map_compose:
  assumes f: "Cauchy_continuous_map m1 m2 f" and g: "Cauchy_continuous_map m2 m3 g"
  shows "Cauchy_continuous_map m1 m3 (g o f)"
  by (metis (no_types, lifting) Cauchy_continuous_map_def f fun.map_comp g)

lemma Lipschitz_imp_uniformly_continuous_map:
  assumes "Lipschitz_continuous_map m1 m2 f"
  shows "uniformly_continuous_map m1 m2 f"
  proof -
  have "f ` mspace m1 \<subseteq> mspace m2"
    by (simp add: Lipschitz_continuous_map_image assms)
  moreover have "\<exists>\<delta>>0. \<forall>x\<in>mspace m1. \<forall>y\<in>mspace m1. mdist m1 y x < \<delta> \<longrightarrow> mdist m2 (f y) (f x) < \<epsilon>"
    if "\<epsilon> > 0" for \<epsilon>
  proof -
    obtain B where "\<forall>x\<in>mspace m1. \<forall>y\<in>mspace m1. mdist m2 (f x) (f y) \<le> B * mdist m1 x y"
             and "B>0"
      using that assms by (force simp add: Lipschitz_continuous_map_pos)
    then have "\<forall>x\<in>mspace m1. \<forall>y\<in>mspace m1. mdist m1 y x < \<epsilon>/B \<longrightarrow> mdist m2 (f y) (f x) < \<epsilon>"
      by (smt (verit, ccfv_SIG) less_divide_eq mdist_nonneg mult.commute that zero_less_divide_iff)
    with \<open>B>0\<close> show ?thesis
      by (metis divide_pos_pos that)
  qed
  ultimately show ?thesis
    by (auto simp: uniformly_continuous_map_def)
qed

lemma uniformly_imp_Cauchy_continuous_map:
   "uniformly_continuous_map m1 m2 f \<Longrightarrow> Cauchy_continuous_map m1 m2 f"
  unfolding uniformly_continuous_map_def Cauchy_continuous_map_def
  apply (simp add: image_subset_iff o_def Metric_space.MCauchy_def [OF Metric_space_mspace_mdist])
  by meson

lemma locally_Cauchy_continuous_map:
  assumes "\<epsilon> > 0"
    and \<section>: "\<And>x. x \<in> mspace m1 \<Longrightarrow> Cauchy_continuous_map (submetric m1 (mball_of m1 x \<epsilon>)) m2 f"
  shows "Cauchy_continuous_map m1 m2 f"
  unfolding Cauchy_continuous_map_def
proof (intro strip)
  interpret M1: Metric_space "mspace m1" "mdist m1"
    by (simp add: Metric_space_mspace_mdist)
  interpret M2: Metric_space "mspace m2" "mdist m2"
    by (simp add: Metric_space_mspace_mdist)
  fix \<sigma>
  assume \<sigma>: "M1.MCauchy \<sigma>"
  with \<open>\<epsilon> > 0\<close> obtain N where N: "\<And>n n'. \<lbrakk>n\<ge>N; n'\<ge>N\<rbrakk> \<Longrightarrow> mdist m1 (\<sigma> n) (\<sigma> n') < \<epsilon>"
    using M1.MCauchy_def by fastforce
  then have "M1.mball (\<sigma> N) \<epsilon> \<subseteq> mspace m1"
    by (auto simp: image_subset_iff M1.mball_def)
  then interpret MS1: Metric_space "mball_of m1 (\<sigma> N) \<epsilon> \<inter> mspace m1" "mdist m1"
    by (simp add: M1.subspace)
  show "M2.MCauchy (f \<circ> \<sigma>)"
  proof (rule M2.MCauchy_offset)
    have "M1.MCauchy (\<sigma> \<circ> (+) N)"
      by (simp add: M1.MCauchy_imp_MCauchy_suffix \<sigma>)
    moreover have "range (\<sigma> \<circ> (+) N) \<subseteq> M1.mball (\<sigma> N) \<epsilon>"
      using N [OF order_refl] M1.MCauchy_def \<sigma> by fastforce
    ultimately have "MS1.MCauchy (\<sigma> \<circ> (+) N)"
      unfolding M1.MCauchy_def MS1.MCauchy_def by (simp add: mball_of_def)
    moreover have "\<sigma> N \<in> mspace m1"
      using M1.MCauchy_def \<sigma> by auto
    ultimately show "M2.MCauchy (f \<circ> \<sigma> \<circ> (+) N)"
      unfolding comp_assoc
      by (metis "\<section>" Cauchy_continuous_map_def mdist_submetric mspace_submetric)
  next
    fix n
    have "\<sigma> n \<in> mspace m1"
      by (meson Metric_space.MCauchy_def Metric_space_mspace_mdist \<sigma> range_subsetD)
    then have "\<sigma> n \<in> mball_of m1 (\<sigma> n) \<epsilon>"
      by (simp add: Metric_space.centre_in_mball_iff Metric_space_mspace_mdist assms(1) mball_of_def)
    then show "(f \<circ> \<sigma>) n \<in> mspace m2"
      using Cauchy_continuous_map_image [OF \<section> [of "\<sigma> n"]] \<open>\<sigma> n \<in> mspace m1\<close> by auto
  qed
qed


lemma (in Metric_space12) Cauchy_continuous_imp_continuous_map:
  assumes "Cauchy_continuous_map (metric (M1,d1)) (metric (M2,d2)) f"
  shows "continuous_map M1.mtopology M2.mtopology f"
proof (clarsimp simp: continuous_map_atin)
  fix x
  assume "x \<in> M1"
  show "limitin M2.mtopology f (f x) (atin M1.mtopology x)"
    unfolding limit_atin_sequentially
  proof (intro conjI strip)
    show "f x \<in> M2"
      using Cauchy_continuous_map_image \<open>x \<in> M1\<close> assms by fastforce
    fix \<sigma>
    assume "range \<sigma> \<subseteq> M1 - {x} \<and> limitin M1.mtopology \<sigma> x sequentially"
    then have "M1.MCauchy (\<lambda>n. if even n then \<sigma> (n div 2) else x)"
      by (force simp add: M1.MCauchy_interleaving)
    then have "M2.MCauchy (f o (\<lambda>n. if even n then \<sigma> (n div 2) else x))"
      using assms by (simp add: Cauchy_continuous_map_def)
    then show "limitin M2.mtopology (f \<circ> \<sigma>) (f x) sequentially"
      using M2.MCauchy_interleaving [of "f \<circ> \<sigma>" "f x"]
      by (simp add: o_def if_distrib cong: if_cong)
  qed
qed

text \<open>The same outside the locale\<close>
lemma Cauchy_continuous_imp_continuous_map:
  assumes "Cauchy_continuous_map m1 m2 f"
  shows "continuous_map (mtopology_of m1) (mtopology_of m2) f"
  using assms Metric_space12.Cauchy_continuous_imp_continuous_map [OF Metric_space12_mspace_mdist]
  by (auto simp add: mtopology_of_def)

lemma uniformly_continuous_imp_continuous_map:
   "uniformly_continuous_map m1 m2 f
        \<Longrightarrow> continuous_map (mtopology_of m1) (mtopology_of m2) f"
  by (simp add: Cauchy_continuous_imp_continuous_map uniformly_imp_Cauchy_continuous_map)

lemma Lipschitz_continuous_imp_continuous_map:
   "Lipschitz_continuous_map m1 m2 f
     \<Longrightarrow> continuous_map (mtopology_of m1) (mtopology_of m2) f"
  by (simp add: Lipschitz_imp_uniformly_continuous_map uniformly_continuous_imp_continuous_map)

lemma Lipschitz_imp_Cauchy_continuous_map:
   "Lipschitz_continuous_map m1 m2 f
        \<Longrightarrow> Cauchy_continuous_map m1 m2 f"
  by (simp add: Lipschitz_imp_uniformly_continuous_map uniformly_imp_Cauchy_continuous_map)

lemma continuous_imp_Cauchy_continuous_map:
   "\<And>m1 m2 f::A=>B.
        mcomplete m1 \<and>
        continuous_map (mtopology m1,mtopology m2) f
        \<Longrightarrow> Cauchy_continuous_map m1 m2 f"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[Cauchy_continuous_map] THEN
  X_GEN_TAC `x::num=>A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> SPEC `x::num=>A` \<circ> REWRITE_RULE[mcomplete]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `y::A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP
   (REWRITE_RULE[IMP_CONJ] (ISPEC `sequentially` CONTINUOUS_MAP_LIMIT))) THEN
  DISCH_THEN(MP_TAC \<circ> SPECL [`x::num=>A`; `y::A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        CONVERGENT_IMP_CAUCHY_IN)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [continuous_map; TOPSPACE_MTOPOLOGY; MCauchy]) THEN
  REWRITE_TAC[o_DEF] THEN ASM SET_TAC[]);;

lemma Cauchy_imp_uniformly_continuous_map:
   "\<And>m1 m2 f::A=>B.
        mtotally_bounded1 (M1) \<and>
        Cauchy_continuous_map m1 m2 f
        \<Longrightarrow> uniformly_continuous_map m1 m2 f"
oops
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_SEQUENTIALLY_ALT] THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CAUCHY_CONTINUOUS_MAP_IMAGE) THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`e::real`; `x::num=>A`; `y::num=>A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> SPEC `x::num=>A` \<circ> CONJUNCT2 \<circ>
   REWRITE_RULE[TOTALLY_BOUNDED_IN_SEQUENTIALLY]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r1::num=>num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> SPEC `(y::num=>A) \<circ> (r1::num=>num)` \<circ> CONJUNCT2 \<circ>
   REWRITE_RULE[TOTALLY_BOUNDED_IN_SEQUENTIALLY]) THEN
  ASM_REWRITE_TAC[o_THM; GSYM o_ASSOC; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r2::num=>num` THEN STRIP_TAC THEN
  ABBREV_TAC `r = (r1::num=>num) \<circ> (r2::num=>num)` THEN
  SUBGOAL_THEN `\<forall>m n. m < n \<Longrightarrow> (r::num=>num) m < r n` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[o_DEF] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC \<circ>
   SPEC `\<lambda>n. if even n then (x \<circ> r) (n div 2):A
             else (y \<circ> (r::num=>num)) (n div 2)` \<circ>
   REWRITE_RULE[Cauchy_continuous_map]) THEN
  ASM_REWRITE_TAC[CAUCHY_IN_INTERLEAVING_GEN; ETA_AX] THEN ANTS_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[o_ASSOC] THEN
    ASM_SIMP_TAC[CAUCHY_IN_SUBSEQUENCE] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `r::num=>num` \<circ>
      MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] LIMIT_SUBSEQUENCE)) THEN
    ASM_REWRITE_TAC[GSYM o_ASSOC] THEN REWRITE_TAC[o_DEF];
    ONCE_REWRITE_TAC[o_DEF] THEN
    REWRITE_TAC[COND_RAND; CAUCHY_IN_INTERLEAVING_GEN] THEN
    DISCH_THEN(MP_TAC \<circ> CONJUNCT2 \<circ> CONJUNCT2) THEN
    REWRITE_TAC[LIMIT_NULL_REAL] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `e::real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP EVENTUALLY_HAPPENS) THEN
    REWRITE_TAC[o_DEF; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    ASM_SIMP_TAC[real_abs; MDIST_POS_LE] THEN MESON_TAC[]]);;

lemma continuous_imp_uniformly_continuous_map:
   "\<And>m1 m2 f::A=>B.
        compact_space (mtopology m1) \<and>
        continuous_map (mtopology m1,mtopology m2) f
        \<Longrightarrow> uniformly_continuous_map m1 m2 f"
oops
  REWRITE_TAC[COMPACT_SPACE_EQ_MCOMPLETE_TOTALLY_BOUNDED_IN] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CAUCHY_IMP_UNIFORMLY_CONTINUOUS_MAP THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_CAUCHY_CONTINUOUS_MAP THEN
  ASM_REWRITE_TAC[]);;

lemma continuous_eq_Cauchy_continuous_map:
   "\<And>m1 m2 f::A=>B.
        mcomplete m1
        \<Longrightarrow> (continuous_map (mtopology m1,mtopology m2) f \<longleftrightarrow>
             Cauchy_continuous_map m1 m2 f)"
oops
  MESON_TAC[CONTINUOUS_IMP_CAUCHY_CONTINUOUS_MAP;
            CAUCHY_CONTINUOUS_IMP_CONTINUOUS_MAP]);;

lemma continuous_eq_uniformly_continuous_map:
   "\<And>m1 m2 f::A=>B.
        compact_space (mtopology m1)
        \<Longrightarrow> (continuous_map (mtopology m1,mtopology m2) f \<longleftrightarrow>
             uniformly_continuous_map m1 m2 f)"
oops
  MESON_TAC[CONTINUOUS_IMP_UNIFORMLY_CONTINUOUS_MAP;
            UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS_MAP]);;

lemma Cauchy_eq_uniformly_continuous_map:
   "\<And>m1 m2 f::A=>B.
        mtotally_bounded1 (M1)
        \<Longrightarrow> (Cauchy_continuous_map m1 m2 f \<longleftrightarrow>
             uniformly_continuous_map m1 m2 f)"
oops
  MESON_TAC[CAUCHY_IMP_UNIFORMLY_CONTINUOUS_MAP;
            UNIFORMLY_IMP_CAUCHY_CONTINUOUS_MAP]);;

lemma Lipschitz_continuous_map_projections:
 (`(\<forall>m1::A metric m2::B metric.
        Lipschitz_continuous_map (prod_metric m1 m2,m1) fst) \<and>
   (\<forall>m1::A metric m2::B metric.
        Lipschitz_continuous_map (prod_metric m1 m2,m2) snd)"
oops
  CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[Lipschitz_continuous_map] THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; CONJUNCT1 PROD_METRIC] THEN
  SIMP_TAC[FORALL_PAIR_THM; IN_CROSS] THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[REAL_MUL_LID; COMPONENT_LE_PROD_METRIC]);;

lemma Lipschitz_continuous_map_pairwise:
   "\<And>m m1 m2 (f::A=>B#C).
        Lipschitz_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow>
        Lipschitz_continuous_map m m1 (fst \<circ> f) \<and>
        Lipschitz_continuous_map m m2 (snd \<circ> f)"
oops
  REWRITE_TAC[FORALL_AND_THM; TAUT `(p \<longleftrightarrow> q) \<longleftrightarrow> (p \<Longrightarrow> q) \<and> (q \<Longrightarrow> p)`] THEN
  CONJ_TAC THENL
   [MESON_TAC[LIPSCHITZ_CONTINUOUS_MAP_COMPOSE;
              LIPSCHITZ_CONTINUOUS_MAP_PROJECTIONS];
    REPLICATE_TAC 3 GEN_TAC THEN
    REWRITE_TAC[FORALL_PAIR_FUN_THM; o_DEF; ETA_AX] THEN
    MAP_EVERY X_GEN_TAC [`x::A=>B`; `y::A=>C`] THEN
    REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_POS] THEN
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; CONJUNCT1 PROD_METRIC] THEN
    DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[IN_CROSS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `B::real` THEN STRIP_TAC THEN
    X_GEN_TAC `C::real` THEN STRIP_TAC THEN EXISTS_TAC `B + C::real` THEN
    ASM_SIMP_TAC[REAL_LT_ADD] THEN REPEAT STRIP_TAC THEN
    W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand) PROD_METRIC_LE_COMPONENTS \<circ>
      lhand \<circ> snd) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `y \<le> c * m \<and> z \<le> b * m \<Longrightarrow> x \<le> y + z \<Longrightarrow> x \<le> (b + c) * m`) THEN
    ASM_SIMP_TAC[]]);;

lemma uniformly_continuous_map_pairwise:
   "\<And>m m1 m2 (f::A=>B#C).
        uniformly_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow>
        uniformly_continuous_map m m1 (fst \<circ> f) \<and>
        uniformly_continuous_map m m2 (snd \<circ> f)"
oops
  REWRITE_TAC[FORALL_AND_THM; TAUT `(p \<longleftrightarrow> q) \<longleftrightarrow> (p \<Longrightarrow> q) \<and> (q \<Longrightarrow> p)`] THEN
  CONJ_TAC THENL
   [MESON_TAC[UNIFORMLY_CONTINUOUS_MAP_COMPOSE;
              LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP;
              LIPSCHITZ_CONTINUOUS_MAP_PROJECTIONS];
    REPLICATE_TAC 3 GEN_TAC THEN
    REWRITE_TAC[FORALL_PAIR_FUN_THM; o_DEF; ETA_AX] THEN
    MAP_EVERY X_GEN_TAC [`x::A=>B`; `y::A=>C`] THEN
    REWRITE_TAC[uniformly_continuous_map] THEN
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; CONJUNCT1 PROD_METRIC] THEN
    DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_SIMP_TAC[IN_CROSS; IMP_IMP] THEN DISCH_TAC THEN
    X_GEN_TAC `e::real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN(MP_TAC \<circ> SPEC `e / 2`)) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d1::real` THEN STRIP_TAC THEN
    X_GEN_TAC `d2::real` THEN STRIP_TAC THEN
    EXISTS_TAC `min d1 d2::real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    REPEAT STRIP_TAC THEN
    W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand) PROD_METRIC_LE_COMPONENTS \<circ>
      lhand \<circ> snd) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `x < e / 2 \<and> y < e / 2 \<Longrightarrow> z \<le> x + y \<Longrightarrow> z < e`) THEN
    ASM_SIMP_TAC[]]);;

lemma Cauchy_continuous_map_pairwise:
   "\<And>m m1 m2 (f::A=>B#C).
        Cauchy_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow>
        Cauchy_continuous_map m m1 (fst \<circ> f) \<and>
        Cauchy_continuous_map m m2 (snd \<circ> f)"
oops
  REWRITE_TAC[Cauchy_continuous_map; CAUCHY_IN_PROD_METRIC; o_ASSOC] THEN
  MESON_TAC[]);;

lemma Lipschitz_continuous_map_paired:
   "\<And>m m1 m2 f (g::A=>C).
        Lipschitz_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
        Lipschitz_continuous_map m m1 f \<and> Lipschitz_continuous_map m m2 g"
oops
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma uniformly_continuous_map_paired:
   "\<And>m m1 m2 f (g::A=>C).
        uniformly_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
        uniformly_continuous_map m m1 f \<and> uniformly_continuous_map m m2 g"
oops
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma Cauchy_continuous_map_paired:
   "\<And>m m1 m2 f (g::A=>C).
        Cauchy_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
        Cauchy_continuous_map m m1 f \<and> Cauchy_continuous_map m m2 g"
oops
  REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma mbounded_Lipschitz_continuous_image:
   "\<And>m1 m2 f s.
        Lipschitz_continuous_map f \<and> mbounded m1 s
        \<Longrightarrow> mbounded m2 (f ` s)"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MBOUNDED_ALT_POS; LIPSCHITZ_CONTINUOUS_MAP_POS] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `B::real` THEN DISCH_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  STRIP_TAC THEN X_GEN_TAC `C::real` THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[FORALL_IN_IMAGE_2]] THEN
  EXISTS_TAC `B * C::real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `B * d m1 (x::A,y)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN ASM SET_TAC[]);;

lemma mtotally_bounded_Cauchy_continuous_image:
   "\<And>m1 m2 f s.
        Cauchy_continuous_map m1 m2 f \<and> mtotally_bounded1 s
        \<Longrightarrow> mtotally_bounded2 (f ` s)"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TOTALLY_BOUNDED_IN_SEQUENTIALLY] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP CAUCHY_CONTINUOUS_MAP_IMAGE) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_IMAGE]] THEN
  X_GEN_TAC `y::num=>B` THEN REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM]THEN
  DISCH_THEN(X_CHOOSE_THEN `x::num=>A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `x::num=>A`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r::num=>num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [Cauchy_continuous_map]) THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `(x::num=>A) \<circ> (r::num=>num)`) THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[o_DEF]);;

lemma Lipschitz_coefficient_pos:
   "\<And>m m' f::A=>B k.
     (\<forall>x. x \<in> M \<Longrightarrow> f x \<in> mspace m') \<and>
     (\<forall>x y. x \<in> M \<and> y \<in> M
            \<Longrightarrow> d m' (f x,f y) \<le> k * d x y) \<and>
     (\<exists>x y. x \<in> M \<and> y \<in> M \<and> \<not> (f x = f y))
     \<Longrightarrow> 0 < k"
oops
  REPEAT GEN_TAC THEN INTRO_TAC "f k (@x y. x y fneq)" THEN
  CLAIM_TAC "neq" `\<not> (x::A = y)` THENL [HYP MESON_TAC "fneq" []; ALL_TAC] THEN
  TRANS_TAC REAL_LTE_TRANS `d m' (f x::B,f y) / d x::A y` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; MDIST_POS_LT; REAL_LE_LDIV_EQ]);;

lemma Lipschitz_continuous_map_metric:
   "Lipschitz_continuous_map
          (prod_metric m m,real_euclidean_metric)
          (d m)"
oops
  SIMP_TAC[Lipschitz_continuous_map; CONJUNCT1 PROD_METRIC;
           REAL_EUCLIDEAN_METRIC] THEN
  GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; SUBSET_UNIV] THEN
  EXISTS_TAC `2` THEN
  MAP_EVERY X_GEN_TAC [`x1::A`; `y1::A`; `x2::A`; `y2::A`] THEN STRIP_TAC THEN
  W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand) COMPONENT_LE_PROD_METRIC \<circ>
    rand \<circ> rand \<circ> snd) THEN
  MATCH_MP_TAC(REAL_ARITH
   `x \<le> y + z \<Longrightarrow> y \<le> p \<and> z \<le> p \<Longrightarrow> x \<le> 2 * p`) THEN
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN CONJ_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC METRIC_ARITH);;

lemma Lipschitz_continuous_map_mdist:
   "\<And>m m' f g.
      Lipschitz_continuous_map m m' f \<and>
      Lipschitz_continuous_map m m' g
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric
             (\<lambda>x. d m' (f x,g x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric (m':B metric) m'` THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_METRIC] THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRED]);;

lemma uniformly_continuous_map_mdist:
   "\<And>m m' f g.
      uniformly_continuous_map m m' f \<and>
      uniformly_continuous_map m m' g
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric
             (\<lambda>x. d m' (f x,g x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric (m':B metric) m'` THEN
  SIMP_TAC[LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP;
           LIPSCHITZ_CONTINUOUS_MAP_METRIC] THEN
  ASM_REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_PAIRED]);;

lemma Cauchy_continuous_map_mdist:
   "\<And>m m' f g.
      Cauchy_continuous_map m m' f \<and>
      Cauchy_continuous_map m m' g
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric
             (\<lambda>x. d m' (f x,g x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric (m':B metric) m'` THEN
  SIMP_TAC[LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP;
           LIPSCHITZ_CONTINUOUS_MAP_METRIC] THEN
  ASM_REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_PAIRED]);;

lemma continuous_map_metric:
   "continuous_map (prod_topology mtopology mtopology,
                        euclideanreal)
                       (d m)"
oops
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC;
              GSYM MTOPOLOGY_PROD_METRIC] THEN
  GEN_TAC THEN MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_IMP_CONTINUOUS_MAP THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_METRIC]);;

lemma continuous_map_mdist_alt:
   "\<And>m f::A=>B#B.
        continuous_map X (prod_topology mtopology mtopology) f
        \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. d m (f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  ASM_MESON_TAC[CONTINUOUS_MAP_METRIC; CONTINUOUS_MAP_COMPOSE]);;

lemma continuous_map_mdist:
   "\<And>X m f g::A=>B.
        continuous_map X mtopology f \<and>
        continuous_map X mtopology g
        \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. d (f x) g x)"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (mtopology::B topology) mtopology` THEN
  REWRITE_TAC[CONTINUOUS_MAP_METRIC; CONTINUOUS_MAP_PAIRWISE] THEN
  ASM_REWRITE_TAC[o_DEF; ETA_AX]);;

lemma continuous_on_mdist:
   "a::A \<in> M
         \<Longrightarrow> continuous_map mtopology euclideanreal (\<lambda>x. d a x)"
oops
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_MDIST THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST] THEN
  ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY]);;

lemma Lipschitz_continuous_map_real_left_multiplication:
   "Lipschitz_continuous_map real_euclidean_metric real_euclidean_metric
         (\<lambda>x. c * x)"
oops
  GEN_TAC THEN REWRITE_TAC[Lipschitz_continuous_map] THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC; IN_UNIV; SUBSET_UNIV] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  MESON_TAC[REAL_LE_REFL]);;

lemma Lipschitz_continuous_map_real_right_multiplication:
   "Lipschitz_continuous_map real_euclidean_metric real_euclidean_metric
         (\<lambda>x. x * c)"
oops
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LEFT_MULTIPLICATION]);;

lemma Lipschitz_continuous_map_real_negation:
 (`Lipschitz_continuous_map real_euclidean_metric real_euclidean_metric (--)"
oops
  GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LEFT_MULTIPLICATION]);;

lemma Lipschitz_continuous_map_real_absolute_value:
 (`Lipschitz_continuous_map real_euclidean_metric real_euclidean_metric abs"
oops
  SIMP_TAC[Lipschitz_continuous_map; REAL_EUCLIDEAN_METRIC; SUBSET_UNIV] THEN
  EXISTS_TAC `1` THEN REAL_ARITH_TAC);;

lemma Lipschitz_continuous_map_real_addition:
 (`Lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\<lambda>(x,y). x + y)"
oops
  REWRITE_TAC[Lipschitz_continuous_map; CONJUNCT1 PROD_METRIC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV; IN_CROSS] THEN
  EXISTS_TAC `2` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `x \<le> 2 * y \<longleftrightarrow> x / 2 \<le> y`] THEN
  W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand)
        COMPONENT_LE_PROD_METRIC \<circ> rand \<circ> snd) THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN REAL_ARITH_TAC);;

lemma Lipschitz_continuous_map_real_subtraction:
 (`Lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\<lambda>(x,y). x - y)"
oops
  REWRITE_TAC[Lipschitz_continuous_map; CONJUNCT1 PROD_METRIC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV; IN_CROSS] THEN
  EXISTS_TAC `2` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `x \<le> 2 * y \<longleftrightarrow> x / 2 \<le> y`] THEN
  W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand)
        COMPONENT_LE_PROD_METRIC \<circ> rand \<circ> snd) THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN REAL_ARITH_TAC);;

lemma Lipschitz_continuous_map_real_maximum:
 (`Lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\<lambda>(x,y). max x y)"
oops
  REWRITE_TAC[Lipschitz_continuous_map; CONJUNCT1 PROD_METRIC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV; IN_CROSS] THEN
  EXISTS_TAC `1` THEN REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand)
        COMPONENT_LE_PROD_METRIC \<circ> rand \<circ> snd) THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN REAL_ARITH_TAC);;

lemma Lipschitz_continuous_map_real_minimum:
 (`Lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\<lambda>(x,y). min x y)"
oops
  REWRITE_TAC[Lipschitz_continuous_map; CONJUNCT1 PROD_METRIC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV; IN_CROSS] THEN
  EXISTS_TAC `1` THEN REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand)
        COMPONENT_LE_PROD_METRIC \<circ> rand \<circ> snd) THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN REAL_ARITH_TAC);;

lemma locally_Lipschitz_continuous_map_real_multiplication:
   "mbounded (prod_metric real_euclidean_metric real_euclidean_metric) s
       \<Longrightarrow> Lipschitz_continuous_map
            (submetric
              (prod_metric real_euclidean_metric real_euclidean_metric) s,
             real_euclidean_metric)
            (\<lambda>(x,y). x * y)"
oops
  GEN_TAC THEN REWRITE_TAC[MBOUNDED_PROD_METRIC] THEN
  REWRITE_TAC[MBOUNDED_REAL_EUCLIDEAN_METRIC; REAL_BOUNDED_POS] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B::real` THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `C::real` THEN REPEAT DISCH_TAC THEN
  SIMP_TAC[Lipschitz_continuous_map; REAL_EUCLIDEAN_METRIC; SUBSET_UNIV] THEN
  EXISTS_TAC `B + C::real` THEN
  REWRITE_TAC[FORALL_PAIR_THM; SUBMETRIC; IN_INTER; CONJUNCT1 PROD_METRIC] THEN
  MAP_EVERY X_GEN_TAC [`x1::real`; `y1::real`; `x2::real`; `y2::real`] THEN
  REWRITE_TAC[IN_CROSS; REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `B * d y1 y2 +
    C * d x1 x2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_EUCLIDEAN_METRIC];
    MATCH_MP_TAC(REAL_ARITH
     `x \<le> b * d \<and> y \<le> c * d \<Longrightarrow> x + y \<le> (b + c) * d`) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; COMPONENT_LE_PROD_METRIC]] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `x2 * y2 - x1 * y1::real = x2 * (y2 - y1) + y1 * (x2 - x1)`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs x \<le> a \<and> abs y \<le> b \<Longrightarrow> abs(x + y) \<le> a + b`) THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_MESON_TAC[]);;

lemma Cauchy_continuous_map_real_multiplication:
 (`Cauchy_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\<lambda>(x,y). x * y)"
oops
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LOCALLY_CAUCHY_CONTINUOUS_MAP THEN
  EXISTS_TAC `1` THEN REWRITE_TAC[REAL_LT_01] THEN
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP THEN
  MATCH_MP_TAC LOCALLY_LIPSCHITZ_CONTINUOUS_MAP_REAL_MULTIPLICATION THEN
  REWRITE_TAC[MBOUNDED_MBALL]);;

lemma locally_Lipschitz_continuous_map_real_inversion:
   "\<not> (0 \<in> euclideanreal closure_of s)
       \<Longrightarrow> Lipschitz_continuous_map
             (submetric real_euclidean_metric s,real_euclidean_metric)
             inverse"
oops
  X_GEN_TAC `s::real=>bool` THEN
  REWRITE_TAC[CLOSURE_OF_INTERIOR_OF; IN_DIFF; TOPSPACE_EUCLIDEANREAL] THEN
  REWRITE_TAC[IN_UNIV; GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_INTERIOR_OF_MBALL] THEN
  REWRITE_TAC[\<subseteq>; IN_MBALL; REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_NOT_LT; SET_RULE
   `(\<forall>x. P x \<Longrightarrow> x \<in> - s) \<longleftrightarrow> (\<forall>x. x \<in> s \<Longrightarrow> \<not> P x)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `b::real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[Lipschitz_continuous_map; REAL_EUCLIDEAN_METRIC; SUBSET_UNIV;
              SUBMETRIC; INTER_UNIV] THEN
  EXISTS_TAC `inverse(b ^ 2):real` THEN
  MAP_EVERY X_GEN_TAC [`x::real`; `y::real`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `x = 0` THENL
   [FIRST_X_ASSUM(MP_TAC \<circ> SPEC `x::real`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `y = 0` THENL
   [FIRST_X_ASSUM(MP_TAC \<circ> SPEC `y::real`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `(x \<noteq> 0) \<and> (y \<noteq> 0) \<Longrightarrow> inverse y - inverse x =-inverse(x * y) * (y - x)`] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_INV] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
  REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

lemma Lipschitz_continuous_map_fst:
   "\<And>m m1 m2 f::A=>B#C.
        Lipschitz_continuous_map m (prod_metric m1 m2) f
        \<Longrightarrow> Lipschitz_continuous_map m m1 (\<lambda>x. fst(f x))"
oops
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF]);;

lemma Lipschitz_continuous_map_snd:
   "\<And>m m1 m2 f::A=>B#C.
        Lipschitz_continuous_map m (prod_metric m1 m2) f
        \<Longrightarrow> Lipschitz_continuous_map m m2 (\<lambda>x. snd(f x))"
oops
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF]);;

lemma Lipschitz_continuous_map_real_lmul:
   "\<And>m c f::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. c * f x)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\<lambda>x. c * f x) = (\<lambda>y. c * y) \<circ> f`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `real_euclidean_metric` THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LEFT_MULTIPLICATION]);;

lemma Lipschitz_continuous_map_real_rmul:
   "\<And>m c f::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x * c)"
oops
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LMUL]);;

lemma Lipschitz_continuous_map_real_neg:
   "\<And>m f::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. --(f x))"
oops
  ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LMUL]);;

lemma Lipschitz_continuous_map_real_abs:
   "\<And>m f::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. abs(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `real_euclidean_metric` THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ABSOLUTE_VALUE]);;

lemma Lipschitz_continuous_map_real_inv:
   "\<And>m f::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f \<and>
      \<not> (0 \<in> euclideanreal closure_of (image f (M)))
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. inverse(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
   `submetric real_euclidean_metric (image f (M::A=>bool))` THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_INTO_SUBMETRIC; SUBSET_REFL] THEN
  MATCH_MP_TAC LOCALLY_LIPSCHITZ_CONTINUOUS_MAP_REAL_INVERSION THEN
  ASM_REWRITE_TAC[]);;

lemma Lipschitz_continuous_map_real_add:
   "\<And>m f g::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f \<and>
      Lipschitz_continuous_map m real_euclidean_metric g
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x + g x)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\<lambda>x. f x + g x) = (\<lambda>(x,y). x + y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ADDITION] THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma Lipschitz_continuous_map_real_sub:
   "\<And>m f g::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f \<and>
      Lipschitz_continuous_map m real_euclidean_metric g
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x - g x)"
oops
  REWRITE_TAC[real_sub] THEN
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ADD;
           LIPSCHITZ_CONTINUOUS_MAP_REAL_NEG]);;

lemma Lipschitz_continuous_map_real_max:
   "\<And>m f g::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f \<and>
      Lipschitz_continuous_map m real_euclidean_metric g
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric
            (\<lambda>x. max (f x) (g x))"
oops
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(\<lambda>x. max (f x) (g x)) = (\<lambda>(x,y). max x y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_MAXIMUM] THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma Lipschitz_continuous_map_real_min:
   "\<And>m f g::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f \<and>
      Lipschitz_continuous_map m real_euclidean_metric g
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric
            (\<lambda>x. min (f x) (g x))"
oops
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(\<lambda>x. min (f x) (g x)) = (\<lambda>(x,y). min x y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_MINIMUM] THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma Lipschitz_continuous_map_real_mul:
   "\<And>m f g::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f \<and>
      Lipschitz_continuous_map m real_euclidean_metric g \<and>
      real_bounded (image f (M)) \<and> real_bounded (image g (M))
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x * g x)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\<lambda>x. f x * g x) = (\<lambda>(x,y). x * y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC
   `submetric (prod_metric real_euclidean_metric real_euclidean_metric)
              (image f (M) \<times> image g (M))` THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX;
                  LIPSCHITZ_CONTINUOUS_MAP_INTO_SUBMETRIC] THEN
  SIMP_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_CROSS; FUN_IN_IMAGE] THEN
  MATCH_MP_TAC LOCALLY_LIPSCHITZ_CONTINUOUS_MAP_REAL_MULTIPLICATION THEN
  ASM_REWRITE_TAC[MBOUNDED_CROSS; MBOUNDED_REAL_EUCLIDEAN_METRIC]);;

lemma Lipschitz_continuous_map_real_div:
   "\<And>m f g::A=>real.
      Lipschitz_continuous_map m real_euclidean_metric f \<and>
      Lipschitz_continuous_map m real_euclidean_metric g \<and>
      real_bounded (image f (M)) \<and>
      \<not> (0 \<in> euclideanreal closure_of (image g (M)))
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x / g x)"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_REAL_MUL THEN
  ASM_SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_INV] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> check (is_neg \<circ> concl)) THEN
  REWRITE_TAC[CLOSURE_OF_INTERIOR_OF; IN_DIFF; TOPSPACE_EUCLIDEANREAL] THEN
  REWRITE_TAC[IN_UNIV; GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_INTERIOR_OF_MBALL] THEN
  REWRITE_TAC[\<subseteq>; IN_MBALL; REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_NOT_LT; SET_RULE
   `(\<forall>x. P x \<Longrightarrow> x \<in> - s) \<longleftrightarrow> (\<forall>x. x \<in> s \<Longrightarrow> \<not> P x)`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `b::real` THEN STRIP_TAC THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; REAL_ABS_INV] THEN
  EXISTS_TAC `inverse b::real` THEN X_GEN_TAC `x::A` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[]);;

lemma Lipschitz_continuous_map_sum:
   "\<And>m f::K=>A->real k.
      finite k \<and>
      (\<forall>i. i \<in> k
          \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x i))
      \<Longrightarrow> Lipschitz_continuous_map m real_euclidean_metric
                (\<lambda>x. sum k (f x))"
oops
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; LIPSCHITZ_CONTINUOUS_MAP_CONST; REAL_EUCLIDEAN_METRIC;
    FORALL_IN_INSERT; LIPSCHITZ_CONTINUOUS_MAP_REAL_ADD; ETA_AX; IN_UNIV]);;

lemma uniformly_continuous_map_fst:
   "\<And>m m1 m2 f::A=>B#C.
        uniformly_continuous_map m (prod_metric m1 m2) f
        \<Longrightarrow> uniformly_continuous_map m m1 (\<lambda>x. fst(f x))"
oops
  SIMP_TAC[UNIFORMLY_CONTINUOUS_MAP_PAIRWISE; o_DEF]);;

lemma uniformly_continuous_map_snd:
   "\<And>m m1 m2 f::A=>B#C.
        uniformly_continuous_map m (prod_metric m1 m2) f
        \<Longrightarrow> uniformly_continuous_map m m2 (\<lambda>x. snd(f x))"
oops
  SIMP_TAC[UNIFORMLY_CONTINUOUS_MAP_PAIRWISE; o_DEF]);;

lemma uniformly_continuous_map_real_lmul:
   "\<And>m c f::A=>real.
      uniformly_continuous_map m real_euclidean_metric f
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. c * f x)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\<lambda>x. c * f x) = (\<lambda>y. c * y) \<circ> f`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `real_euclidean_metric` THEN
  ASM_SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LEFT_MULTIPLICATION;
               LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP]);;

lemma uniformly_continuous_map_real_rmul:
   "\<And>m c f::A=>real.
      uniformly_continuous_map m real_euclidean_metric f
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. f x * c)"
oops
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_REAL_LMUL]);;

lemma uniformly_continuous_map_real_neg:
   "\<And>m f::A=>real.
      uniformly_continuous_map m real_euclidean_metric f
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. --(f x))"
oops
  ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_REAL_LMUL]);;

lemma uniformly_continuous_map_real_abs:
   "\<And>m f::A=>real.
      uniformly_continuous_map m real_euclidean_metric f
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. abs(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `real_euclidean_metric` THEN
  ASM_SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ABSOLUTE_VALUE;
               LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP]);;

lemma uniformly_continuous_map_real_inv:
   "\<And>m f::A=>real.
      uniformly_continuous_map m real_euclidean_metric f \<and>
      \<not> (0 \<in> euclideanreal closure_of (image f (M)))
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. inverse(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
   `submetric real_euclidean_metric (image f (M::A=>bool))` THEN
  ASM_REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_INTO_SUBMETRIC; SUBSET_REFL] THEN
  MATCH_MP_TAC LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP THEN
  MATCH_MP_TAC LOCALLY_LIPSCHITZ_CONTINUOUS_MAP_REAL_INVERSION THEN
  ASM_REWRITE_TAC[]);;

lemma uniformly_continuous_map_real_add:
   "\<And>m f g::A=>real.
      uniformly_continuous_map m real_euclidean_metric f \<and>
      uniformly_continuous_map m real_euclidean_metric g
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. f x + g x)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\<lambda>x. f x + g x) = (\<lambda>(x,y). x + y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ADDITION;
           LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP] THEN
  ASM_REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma uniformly_continuous_map_real_sub:
   "\<And>m f g::A=>real.
      uniformly_continuous_map m real_euclidean_metric f \<and>
      uniformly_continuous_map m real_euclidean_metric g
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. f x - g x)"
oops
  REWRITE_TAC[real_sub] THEN
  SIMP_TAC[UNIFORMLY_CONTINUOUS_MAP_REAL_ADD;
           UNIFORMLY_CONTINUOUS_MAP_REAL_NEG]);;

lemma uniformly_continuous_map_real_max:
   "\<And>m f g::A=>real.
      uniformly_continuous_map m real_euclidean_metric f \<and>
      uniformly_continuous_map m real_euclidean_metric g
     \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric
            (\<lambda>x. max (f x) (g x))"
oops
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(\<lambda>x. max (f x) (g x)) = (\<lambda>(x,y). max x y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_MAXIMUM;
           LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP] THEN
  ASM_REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma uniformly_continuous_map_real_min:
   "\<And>m f g::A=>real.
      uniformly_continuous_map m real_euclidean_metric f \<and>
      uniformly_continuous_map m real_euclidean_metric g
     \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric
            (\<lambda>x. min (f x) (g x))"
oops
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(\<lambda>x. min (f x) (g x)) = (\<lambda>(x,y). min x y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_MINIMUM;
           LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP] THEN
  ASM_REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma uniformly_continuous_map_real_mul:
   "\<And>m f g::A=>real.
      uniformly_continuous_map m real_euclidean_metric f \<and>
      uniformly_continuous_map m real_euclidean_metric g \<and>
      real_bounded (image f (M)) \<and> real_bounded (image g (M))
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. f x * g x)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\<lambda>x. f x * g x) = (\<lambda>(x,y). x * y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC
   `submetric (prod_metric real_euclidean_metric real_euclidean_metric)
              (image f (M) \<times> image g (M))` THEN
  ASM_REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX;
                  UNIFORMLY_CONTINUOUS_MAP_INTO_SUBMETRIC] THEN
  SIMP_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_CROSS; FUN_IN_IMAGE] THEN
  MATCH_MP_TAC LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP THEN
  MATCH_MP_TAC LOCALLY_LIPSCHITZ_CONTINUOUS_MAP_REAL_MULTIPLICATION THEN
  ASM_REWRITE_TAC[MBOUNDED_CROSS; MBOUNDED_REAL_EUCLIDEAN_METRIC]);;

lemma uniformly_continuous_map_real_div:
   "\<And>m f g::A=>real.
      uniformly_continuous_map m real_euclidean_metric f \<and>
      uniformly_continuous_map m real_euclidean_metric g \<and>
      real_bounded (image f (M)) \<and>
      \<not> (0 \<in> euclideanreal closure_of (image g (M)))
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. f x / g x)"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_REAL_MUL THEN
  ASM_SIMP_TAC[UNIFORMLY_CONTINUOUS_MAP_REAL_INV] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> check (is_neg \<circ> concl)) THEN
  REWRITE_TAC[CLOSURE_OF_INTERIOR_OF; IN_DIFF; TOPSPACE_EUCLIDEANREAL] THEN
  REWRITE_TAC[IN_UNIV; GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_INTERIOR_OF_MBALL] THEN
  REWRITE_TAC[\<subseteq>; IN_MBALL; REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_NOT_LT; SET_RULE
   `(\<forall>x. P x \<Longrightarrow> x \<in> - s) \<longleftrightarrow> (\<forall>x. x \<in> s \<Longrightarrow> \<not> P x)`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `b::real` THEN STRIP_TAC THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; REAL_ABS_INV] THEN
  EXISTS_TAC `inverse b::real` THEN X_GEN_TAC `x::A` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[]);;

lemma uniformly_continuous_map_sum:
   "\<And>m f::K=>A->real k.
      finite k \<and>
      (\<forall>i. i \<in> k
          \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. f x i))
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric
                (\<lambda>x. sum k (f x))"
oops
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; UNIFORMLY_CONTINUOUS_MAP_CONST; REAL_EUCLIDEAN_METRIC;
    FORALL_IN_INSERT; UNIFORMLY_CONTINUOUS_MAP_REAL_ADD; ETA_AX; IN_UNIV]);;

lemma Cauchy_continuous_map_fst:
   "\<And>m m1 m2 f::A=>B#C.
        Cauchy_continuous_map m (prod_metric m1 m2) f
        \<Longrightarrow> Cauchy_continuous_map m m1 (\<lambda>x. fst(f x))"
oops
  SIMP_TAC[CAUCHY_CONTINUOUS_MAP_PAIRWISE; o_DEF]);;

lemma Cauchy_continuous_map_snd:
   "\<And>m m1 m2 f::A=>B#C.
        Cauchy_continuous_map m (prod_metric m1 m2) f
        \<Longrightarrow> Cauchy_continuous_map m m2 (\<lambda>x. snd(f x))"
oops
  SIMP_TAC[CAUCHY_CONTINUOUS_MAP_PAIRWISE; o_DEF]);;

lemma Cauchy_continuous_map_real_inv:
   "\<And>m f::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f \<and>
      \<not> (0 \<in> euclideanreal closure_of (image f (M)))
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. inverse(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
   `submetric real_euclidean_metric (image f (M::A=>bool))` THEN
  ASM_REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_INTO_SUBMETRIC; SUBSET_REFL] THEN
  MATCH_MP_TAC LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP THEN
  MATCH_MP_TAC LOCALLY_LIPSCHITZ_CONTINUOUS_MAP_REAL_INVERSION THEN
  ASM_REWRITE_TAC[]);;

lemma Cauchy_continuous_map_real_add:
   "\<And>m f g::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f \<and>
      Cauchy_continuous_map m real_euclidean_metric g
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x + g x)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\<lambda>x. f x + g x) = (\<lambda>(x,y). x + y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ADDITION;
           LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP] THEN
  ASM_REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma Cauchy_continuous_map_real_mul:
   "\<And>m f g::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f \<and>
      Cauchy_continuous_map m real_euclidean_metric g
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x * g x)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\<lambda>x. f x * g x) = (\<lambda>(x,y). x * y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC
   `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_REAL_MULTIPLICATION] THEN
  ASM_REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma Cauchy_continuous_map_real_lmul:
   "\<And>m c f::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. c * f x)"
oops
  SIMP_TAC[CAUCHY_CONTINUOUS_MAP_REAL_MUL; CAUCHY_CONTINUOUS_MAP_REAL_CONST]);;

lemma Cauchy_continuous_map_real_rmul:
   "\<And>m c f::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x * c)"
oops
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_REAL_LMUL]);;

lemma Cauchy_continuous_map_real_pow:
   "\<And>m f n.
        Cauchy_continuous_map m real_euclidean_metric f
        \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x ^ n)"
oops
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; CAUCHY_CONTINUOUS_MAP_REAL_CONST;
               CAUCHY_CONTINUOUS_MAP_REAL_MUL]);;

lemma Cauchy_continuous_map_real_neg:
   "\<And>m f::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. --(f x))"
oops
  ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_REAL_LMUL]);;

lemma Cauchy_continuous_map_real_abs:
   "\<And>m f::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. abs(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `real_euclidean_metric` THEN
  ASM_SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ABSOLUTE_VALUE;
               LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP]);;

lemma Cauchy_continuous_map_real_sub:
   "\<And>m f g::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f \<and>
      Cauchy_continuous_map m real_euclidean_metric g
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x - g x)"
oops
  REWRITE_TAC[real_sub] THEN
  SIMP_TAC[CAUCHY_CONTINUOUS_MAP_REAL_ADD;
           CAUCHY_CONTINUOUS_MAP_REAL_NEG]);;

lemma Cauchy_continuous_map_real_max:
   "\<And>m f g::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f \<and>
      Cauchy_continuous_map m real_euclidean_metric g
    \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric
            (\<lambda>x. max (f x) (g x))"
oops
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(\<lambda>x. max (f x) (g x)) = (\<lambda>(x,y). max x y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_MAXIMUM;
           LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP] THEN
  ASM_REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma Cauchy_continuous_map_real_min:
   "\<And>m f g::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f \<and>
      Cauchy_continuous_map m real_euclidean_metric g
    \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric
            (\<lambda>x. min (f x) (g x))"
oops
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(\<lambda>x. min (f x) (g x)) = (\<lambda>(x,y). min x y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_MINIMUM;
           LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP] THEN
  ASM_REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma Cauchy_continuous_map_real_div:
   "\<And>m f g::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f \<and>
      Cauchy_continuous_map m real_euclidean_metric g \<and>
      \<not> (0 \<in> euclideanreal closure_of (image g (M)))
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x / g x)"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_REAL_MUL THEN
  ASM_SIMP_TAC[CAUCHY_CONTINUOUS_MAP_REAL_INV] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> check (is_neg \<circ> concl)) THEN
  REWRITE_TAC[CLOSURE_OF_INTERIOR_OF; IN_DIFF; TOPSPACE_EUCLIDEANREAL] THEN
  REWRITE_TAC[IN_UNIV; GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_INTERIOR_OF_MBALL] THEN
  REWRITE_TAC[\<subseteq>; IN_MBALL; REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
  REWRITE_TAC[REAL_SUB_RZERO; REAL_NOT_LT; SET_RULE
   `(\<forall>x. P x \<Longrightarrow> x \<in> - s) \<longleftrightarrow> (\<forall>x. x \<in> s \<Longrightarrow> \<not> P x)`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `b::real` THEN STRIP_TAC THEN
  REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; REAL_ABS_INV] THEN
  EXISTS_TAC `inverse b::real` THEN X_GEN_TAC `x::A` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[]);;

lemma Cauchy_continuous_map_sum:
   "\<And>m f::K=>A->real k.
      finite k \<and>
      (\<forall>i. i \<in> k
          \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x i))
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric
                (\<lambda>x. sum k (f x))"
oops
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; CAUCHY_CONTINUOUS_MAP_REAL_CONST;
    FORALL_IN_INSERT; CAUCHY_CONTINUOUS_MAP_REAL_ADD; ETA_AX]);;

lemma uniformly_continuous_map_square_root:
 (`uniformly_continuous_map real_euclidean_metric real_euclidean_metric sqrt"
oops
  REWRITE_TAC[uniformly_continuous_map; REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN X_GEN_TAC `e::real` THEN DISCH_TAC THEN
  EXISTS_TAC `e ^ 2 / 2` THEN ASM_SIMP_TAC[REAL_HALF; REAL_POW_LT] THEN
  MAP_EVERY X_GEN_TAC [`x::real`; `y::real`] THEN DISCH_TAC THEN
  TRANS_TAC REAL_LET_TRANS `sqrt(2 * abs(x - y))` THEN
  REWRITE_TAC[REAL_ABS_LE_SQRT] THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
  ASM_REAL_ARITH_TAC);;

lemma continuous_map_square_root:
 (`continuous_map euclideanreal euclideanreal sqrt"
oops
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS_MAP THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_SQUARE_ROOT]);;

lemma uniformly_continuous_map_sqrt:
   "\<And>m f::A=>real.
      uniformly_continuous_map m real_euclidean_metric f
      \<Longrightarrow> uniformly_continuous_map m real_euclidean_metric (\<lambda>x. sqrt(f x))"
oops
   REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `real_euclidean_metric` THEN
  ASM_REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_SQUARE_ROOT]);;

lemma Cauchy_continuous_map_sqrt:
   "\<And>m f::A=>real.
      Cauchy_continuous_map m real_euclidean_metric f
      \<Longrightarrow> Cauchy_continuous_map m real_euclidean_metric (\<lambda>x. sqrt(f x))"
oops
   REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `real_euclidean_metric` THEN
  ASM_SIMP_TAC[UNIFORMLY_CONTINUOUS_MAP_SQUARE_ROOT;
               UNIFORMLY_IMP_CAUCHY_CONTINUOUS_MAP]);;

lemma continuous_map_sqrt:
   "\<And>X f::A=>real.
        continuous_map X euclideanreal f
        \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. sqrt(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `euclideanreal` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[UNIFORMLY_CONTINUOUS_MAP_SQUARE_ROOT; GSYM
           MTOPOLOGY_REAL_EUCLIDEAN_METRIC;
           UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS_MAP]);;

lemma isometry_imp_embedding_map:
   "\<And>m m' f.
        image f (M) \<subseteq> mspace m' \<and>
        (\<forall>x y. x \<in> M \<and> y \<in> M
               \<Longrightarrow> d m' (f x,f y) = d x y)
        \<Longrightarrow> embedding_map mtopology (mtopology m') f"
oops
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `\<forall>x y. x \<in> M \<and> y \<in> M \<and> f x = f y \<Longrightarrow> x = y`
  MP_TAC THENL [ASM_MESON_TAC[MDIST_0]; ALL_TAC] THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g::B=>A` THEN DISCH_TAC THEN
  REWRITE_TAC[embedding_map; HOMEOMORPHIC_MAP_MAPS] THEN
  EXISTS_TAC `g::B=>A` THEN
  ASM_REWRITE_TAC[homeomorphic_maps; TOPSPACE_MTOPOLOGY;
                  TOPSPACE_SUBTOPOLOGY; IN_INTER; IMP_CONJ_ALT] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  ASM_REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; TOPSPACE_MTOPOLOGY] THEN
  SIMP_TAC[FUN_IN_IMAGE; GSYM MTOPOLOGY_SUBMETRIC] THEN
  CONJ_TAC THEN MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_IMP_CONTINUOUS_MAP THEN
  ASM_SIMP_TAC[Lipschitz_continuous_map; \<subseteq>; FORALL_IN_IMAGE;
               SUBMETRIC; IMP_CONJ; IN_INTER] THEN
  EXISTS_TAC `1` THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_LE_REFL]);;

lemma isometry_imp_homeomorphic_map:
   "\<And>m m' f.
        image f (M) = mspace m' \<and>
        (\<forall>x y. x \<in> M \<and> y \<in> M
               \<Longrightarrow> d m' (f x,f y) = d x y)
        \<Longrightarrow> homeomorphic_map mtopology (mtopology m') f"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m::A metric`; `m':B metric`; `f::A=>B`]
        ISOMETRY_IMP_EMBEDDING_MAP) THEN
  ASM_REWRITE_TAC[SUBSET_REFL; embedding_map; TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[GSYM TOPSPACE_MTOPOLOGY; SUBTOPOLOGY_TOPSPACE]);;


subsection\<open>Extending continuous maps "pointwise" in a regular space\<close>


lemma continuous_map_on_intermediate_closure_of:
   "\<And>X Y f::A=>B s t.
       regular_space Y \<and>
       t \<subseteq> X closure_of s \<and>
       (\<forall>x. x \<in> t \<Longrightarrow> limitin Y f (f x) (atin X x within s))
       \<Longrightarrow> continuous_map (subtopology X t,Y) f"
oops
  REWRITE_TAC[GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `image f t \<subseteq> topspace Y` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[limitin]) THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_ATPOINTOF; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  X_GEN_TAC `a::A` THEN STRIP_TAC THEN ASM_SIMP_TAC[ATPOINTOF_SUBTOPOLOGY] THEN
  REWRITE_TAC[limitin] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `w::B=>bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [NEIGHBOURHOOD_BASE_OF]) THEN
  DISCH_THEN(MP_TAC \<circ> SPECL [`w::B=>bool`; `f a`]) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v::B=>bool`; `c::B=>bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[EVENTUALLY_ATPOINTOF; EVENTUALLY_WITHIN_IMP] THEN DISJ2_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> SPEC `a::A`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[limitin]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC \<circ> SPEC `v::B=>bool`)) THEN
  ASM_REWRITE_TAC[EVENTUALLY_ATPOINTOF; EVENTUALLY_WITHIN_IMP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u::A=>bool` THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z::A` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `z \<in> topspace X \<and> f z \<in> topspace Y`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `\<not> (f z \<in> topspace Y - c)` MP_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN STRIP_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE RAND_CONV [limitin] \<circ> SPEC `z::A`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `topspace Y - c::B=>bool`) THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; IN_DIFF] THEN
  ASM_REWRITE_TAC[EVENTUALLY_ATPOINTOF; EVENTUALLY_WITHIN_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':A=>bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(t::A=>bool) \<subseteq> X closure_of s` THEN
  REWRITE_TAC[closure_of; IN_ELIM_THM; \<subseteq>] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `z::A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `u \<inter> u':A=>bool`) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[]);;

lemma continuous_map_on_intermediate_closure_of_eq:
   "\<And>X Y f::A=>B s t.
        regular_space Y \<and> s \<subseteq> t \<and> t \<subseteq> X closure_of s
        \<Longrightarrow> (continuous_map (subtopology X t,Y) f \<longleftrightarrow>
             \<forall>x. x \<in> t \<Longrightarrow> limitin Y f (f x) (atin X x within s))"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_ATPOINTOF; TOPSPACE_SUBTOPOLOGY] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x::A` THEN
    ASM_CASES_TAC `(x::A) \<in> t` THEN ASM_SIMP_TAC[ATPOINTOF_SUBTOPOLOGY] THEN
    ASSUME_TAC(ISPECL [`X::A topology`; `s::A=>bool`]
      CLOSURE_OF_SUBSET_TOPSPACE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[LIMIT_WITHIN_SUBSET]];
    ASM_MESON_TAC[CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE_OF]]);;

lemma continuous_map_extension_pointwise_alt:
   "\<And>top1 top2 f::A=>B s t.
        regular_space top2 \<and> s \<subseteq> t \<and> t \<subseteq> top1 closure_of s \<and>
        continuous_map (subtopology top1 s,top2) f \<and>
        (\<forall>x. x \<in> t - s \<Longrightarrow> \<exists>l. limitin top2 f l (atin top1 x within s))
        \<Longrightarrow> \<exists>g. continuous_map (subtopology top1 t,top2) g \<and>
                (\<forall>x. x \<in> s \<Longrightarrow> g x = f x)"
oops
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC \<circ> GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; IN_DIFF] THEN
  X_GEN_TAC `g::A=>B` THEN DISCH_TAC THEN
  EXISTS_TAC `\<lambda>x. if x \<in> s then f x else g x` THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE_OF_EQ] THEN
  X_GEN_TAC `x::A` THEN DISCH_TAC THEN
  MATCH_MP_TAC LIMIT_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `f::A=>B` THEN SIMP_TAC[ALWAYS_WITHIN_EVENTUALLY] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[GSYM ATPOINTOF_SUBTOPOLOGY] THEN
  FIRST_ASSUM(MATCH_MP_TAC \<circ>
   GEN_REWRITE_RULE id [CONTINUOUS_MAP_ATPOINTOF]) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[closure_of]) THEN ASM SET_TAC[]);;

lemma continuous_map_extension_pointwise:
   "\<And>top1 top2 f::A=>B s t.
        regular_space top2 \<and> s \<subseteq> t \<and> t \<subseteq> top1 closure_of s \<and>
        (\<forall>x. x \<in> t
             \<Longrightarrow> \<exists>g. continuous_map (subtopology top1 (insert x s),top2) g \<and>
                     \<forall>x. x \<in> s \<Longrightarrow> g x = f x)
        \<Longrightarrow> \<exists>g. continuous_map (subtopology top1 t,top2) g \<and>
                (\<forall>x. x \<in> s \<Longrightarrow> g x = f x)"
oops
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EXTENSION_POINTWISE_ALT THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_ATPOINTOF] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_DIFF; IN_INTER] THEN
  CONJ_TAC THEN X_GEN_TAC `x::A` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(x::A) \<in> topspace top1` ASSUME_TAC THENL
    [RULE_ASSUM_TAC(SIMP_RULE[closure_of]) THEN ASM SET_TAC[]; ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `x::A`) THEN
  (ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]]) THEN
  X_GEN_TAC `g::A=>B` THEN REWRITE_TAC[CONTINUOUS_MAP_ATPOINTOF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC \<circ> SPEC `x::A`) ASSUME_TAC) THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_INSERT] THEN
  ASM_SIMP_TAC[ATPOINTOF_SUBTOPOLOGY; IN_INSERT] THEN
  STRIP_TAC THENL [ALL_TAC; EXISTS_TAC `(g::A=>B) x`] THEN
  MATCH_MP_TAC LIMIT_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `(g::A=>B)` THEN ASM_SIMP_TAC[ALWAYS_WITHIN_EVENTUALLY] THEN
  MATCH_MP_TAC LIMIT_WITHIN_SUBSET THEN
  EXISTS_TAC `(x::A) insert s` THEN
  ASM_REWRITE_TAC[SET_RULE `s \<subseteq> insert x s`]);;


subsection\<open>Extending Cauchy continuous functions to the closure\<close>


lemma Cauchy_continuous_map_extends_to_continuous_closure_of:
   "\<And>m1 m2 f s.
        mcomplete m2 \<and> Cauchy_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> \<exists>g. continuous_map
                 (subtopology (mtopology m1) (mtopology m1 closure_of s),
                  mtopology m2) g \<and>
                \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC(MESON[]
   `\<forall>m. ((\<forall>s. s \<subseteq> M \<Longrightarrow> P s) \<Longrightarrow> (\<forall>s. P s)) \<and>
        (\<forall>s. s \<subseteq> M \<Longrightarrow> P s)
        \<Longrightarrow> \<forall>s. P s`) THEN
  EXISTS_TAC `m1::A metric` THEN CONJ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `s::A=>bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `M1 \<inter> s::A=>bool`) THEN
    ASM_REWRITE_TAC[GSYM SUBMETRIC_SUBMETRIC; SUBMETRIC_MSPACE] THEN
    REWRITE_TAC[INTER_SUBSET; GSYM TOPSPACE_MTOPOLOGY] THEN
    REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `g::A=>B` STRIP_ASSUME_TAC) THEN EXISTS_TAC
     `\<lambda>x. if x \<in> topspace(mtopology m1) then (g::A=>B) x else f x` THEN
    ASM_SIMP_TAC[COND_ID] THEN MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `g::A=>B` THEN ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EXTENSION_POINTWISE_ALT THEN
  REWRITE_TAC[REGULAR_SPACE_MTOPOLOGY; SUBSET_REFL] THEN
  ASM_SIMP_TAC[CLOSURE_OF_SUBSET; TOPSPACE_MTOPOLOGY] THEN
  ASM_SIMP_TAC[CAUCHY_CONTINUOUS_IMP_CONTINUOUS_MAP;
               GSYM MTOPOLOGY_SUBMETRIC; IN_DIFF] THEN
  X_GEN_TAC `a::A` THEN STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC \<circ> GEN_REWRITE_RULE RAND_CONV [CLOSURE_OF_SEQUENTIALLY]) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTER; FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `x::num=>A` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      CONVERGENT_IMP_CAUCHY_IN)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC \<circ>
    SPEC `x::num=>A` \<circ> REWRITE_RULE[Cauchy_continuous_map]) THEN
  ASM_REWRITE_TAC[CAUCHY_IN_SUBMETRIC] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> SPEC `f \<circ> (x::num=>A)` \<circ>
    REWRITE_RULE[mcomplete]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `l::B` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> CONJUNCT1 \<circ> REWRITE_RULE[limitin]) THEN
  REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[LIMIT_ATPOINTOF_SEQUENTIALLY_WITHIN] THEN
  X_GEN_TAC `y::num=>A` THEN
  REWRITE_TAC[IN_INTER; IN_DELETE; FORALL_AND_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ>
   SPEC `\<lambda>n. if even n then x(n div 2):A else y(n div 2)` \<circ>
   REWRITE_RULE[Cauchy_continuous_map]) THEN
  REWRITE_TAC[CAUCHY_IN_INTERLEAVING_GEN; o_DEF; COND_RAND] THEN
  ASM_REWRITE_TAC[SUBMETRIC; CAUCHY_IN_SUBMETRIC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[CONVERGENT_IMP_CAUCHY_IN]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`limitin (mtopology m1) y (a::A) sequentially`;
      `limitin (mtopology m1) x (a::A) sequentially`] THEN
    REWRITE_TAC[IMP_IMP] THEN
    GEN_REWRITE_TAC (LAND_CONV \<circ> BINOP_CONV) [LIMIT_METRIC_DIST_NULL] THEN
    ASM_REWRITE_TAC[EVENTUALLY_TRUE] THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP LIMIT_REAL_ADD) THEN
    REWRITE_TAC[REAL_ADD_LID] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
      LIMIT_NULL_REAL_COMPARISON) THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN REWRITE_TAC[] THEN GEN_TAC THEN
    MATCH_MP_TAC(METRIC_ARITH
      `a \<in> M \<and> x \<in> M \<and> y \<in> M
       \<Longrightarrow> abs(d x y) \<le> abs(d x a + d y a)`) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC \<circ> CONJUNCT2 \<circ> CONJUNCT2) THEN
    GEN_REWRITE_TAC RAND_CONV [LIMIT_METRIC_DIST_NULL] THEN
    UNDISCH_TAC `limitin (mtopology m2) (f \<circ> x) l sequentially` THEN
    GEN_REWRITE_TAC LAND_CONV [LIMIT_METRIC_DIST_NULL] THEN
    SIMP_TAC[o_DEF] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP LIMIT_REAL_ADD) THEN
    REWRITE_TAC[REAL_ADD_RID] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
     [DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
      FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CAUCHY_CONTINUOUS_MAP_IMAGE) THEN
      REWRITE_TAC[SUBMETRIC] THEN ASM SET_TAC[];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
        LIMIT_NULL_REAL_COMPARISON) THEN
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN REWRITE_TAC[] THEN GEN_TAC THEN
      MATCH_MP_TAC(METRIC_ARITH
       `a \<in> M \<and> x \<in> M \<and> y \<in> M
        \<Longrightarrow> abs(d y a) \<le> abs(d x a + d x y)`) THEN
      FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CAUCHY_CONTINUOUS_MAP_IMAGE) THEN
      REWRITE_TAC[SUBMETRIC] THEN ASM SET_TAC[]]]);;

lemma Cauchy_continuous_map_extends_to_continuous_intermediate_closure_of:
   "\<And>m1 m2 f s t.
        mcomplete m2 \<and> Cauchy_continuous_map (submetric1 s,m2) f \<and>
        t \<subseteq> mtopology m1 closure_of s
        \<Longrightarrow> \<exists>g. continuous_map(subtopology (mtopology m1) t,mtopology m2) g \<and>
                \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `s::A=>bool`]
        CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO]);;

lemma Lipschitz_continuous_map_on_intermediate_closure:
   "\<And>m1 m2 f::A=>B s t.
        s \<subseteq> t \<and> t \<subseteq> (mtopology m1) closure_of s \<and>
        continuous_map (subtopology (mtopology m1) t,mtopology m2) f \<and>
        Lipschitz_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> Lipschitz_continuous_map (submetric1 t,m2) f"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
  SUBGOAL_THEN `submetric1 (s::A=>bool) = submetric1 (M1 \<inter> s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBMETRIC_SUBMETRIC; SUBMETRIC_MSPACE];
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC \<circ> SPEC `M1::A=>bool` \<circ> MATCH_MP (SET_RULE
       `s \<subseteq> t \<Longrightarrow> \<forall>u. u \<inter> s \<subseteq> u \<and> u \<inter> s \<subseteq> t`))
     MP_TAC) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    SPEC_TAC(`M1 \<inter> (s::A=>bool)`,`s::A=>bool`)] THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(t::A=>bool) \<subseteq> M1` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[closure_of; TOPSPACE_MTOPOLOGY]) THEN
    ASM SET_TAC[];
    FIRST_ASSUM(MP_TAC \<circ> CONJUNCT1 \<circ> REWRITE_RULE[CONTINUOUS_MAP])] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_POS] THEN
  ASM_SIMP_TAC[SUBMETRIC; SET_RULE `s \<subseteq> u \<Longrightarrow> s \<inter> u = s`;
               SET_RULE `s \<subseteq> u \<Longrightarrow> u \<inter> s = s`] THEN
  DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B::real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology (mtopology m1) (t::A=>bool))
                   (subtopology (mtopology m1) (t::A=>bool))`;
    `\<lambda>z. d m2 (f (fst z),f(snd z)) \<le> B * d m1 (fst z,snd z)`;
    `s \<times> (s::A=>bool)`] FORALL_IN_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[CLOSURE_OF_CROSS; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN ASM_SIMP_TAC[SET_RULE
   `s \<subseteq> t \<Longrightarrow> t \<inter> s = s \<and> s \<inter> t = s`] THEN
  ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN REWRITE_TAC[SET_RULE
   `{x \<in> s. 0 \<le> f x} = {x \<in> s. f x \<in> {y. 0 \<le> y}}`] THEN
  MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
  EXISTS_TAC `euclideanreal` THEN REWRITE_TAC[GSYM REAL_CLOSED_IN] THEN
  REWRITE_TAC[REWRITE_RULE[real_ge] REAL_CLOSED_HALFSPACE_GE] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
    GEN_REWRITE_TAC (RAND_CONV \<circ> ABS_CONV \<circ> RAND_CONV) [GSYM PAIR];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_MDIST THENL
   [ALL_TAC;
    CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology (mtopology m1) (t::A=>bool)`] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC CONTINUOUS_MAP_INTO_SUBTOPOLOGY THEN
      REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IMAGE_FST_CROSS; IMAGE_SND_CROSS;
                  INTER_CROSS] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]]) THEN
  ASM_REWRITE_TAC[GSYM SUBTOPOLOGY_CROSS] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND]);;

lemma Lipschitz_continuous_map_extends_to_closure_of:
   "\<And>m1 m2 f s.
        mcomplete m2 \<and> Lipschitz_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> \<exists>g. Lipschitz_continuous_map
                   (submetric1 (mtopology m1 closure_of s),m2) g \<and>
                \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `s::A=>bool`]
         CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
  ASM_SIMP_TAC[LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g::A=>B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `M1 \<inter> s::A=>bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_INTER; GSYM TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT; SUBSET_REFL] THEN
  REWRITE_TAC[TOPSPACE_MTOPOLOGY; GSYM SUBMETRIC_RESTRICT] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_EQ THEN EXISTS_TAC `f::A=>B` THEN
  ASM_SIMP_TAC[SUBMETRIC; IN_INTER]);;

lemma Lipschitz_continuous_map_extends_to_intermediate_closure_of:
   "\<And>m1 m2 f s t.
        mcomplete m2 \<and>
        Lipschitz_continuous_map (submetric1 s,m2) f \<and>
        t \<subseteq> mtopology m1 closure_of s
        \<Longrightarrow> \<exists>g. Lipschitz_continuous_map (submetric1 t,m2) g \<and>
                \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `s::A=>bool`]
        LIPSCHITZ_CONTINUOUS_MAP_EXTENDS_TO_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LIPSCHITZ_CONTINUOUS_MAP_FROM_SUBMETRIC_MONO]);;

lemma uniformly_continuous_map_on_intermediate_closure:
   "\<And>m1 m2 f::A=>B s t.
        s \<subseteq> t \<and> t \<subseteq> (mtopology m1) closure_of s \<and>
        continuous_map (subtopology (mtopology m1) t,mtopology m2) f \<and>
        uniformly_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> uniformly_continuous_map (submetric1 t,m2) f"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
  SUBGOAL_THEN `submetric1 (s::A=>bool) = submetric1 (M1 \<inter> s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBMETRIC_SUBMETRIC; SUBMETRIC_MSPACE];
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC \<circ> SPEC `M1::A=>bool` \<circ> MATCH_MP (SET_RULE
       `s \<subseteq> t \<Longrightarrow> \<forall>u. u \<inter> s \<subseteq> u \<and> u \<inter> s \<subseteq> t`))
     MP_TAC) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    SPEC_TAC(`M1 \<inter> (s::A=>bool)`,`s::A=>bool`)] THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(t::A=>bool) \<subseteq> M1` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[closure_of; TOPSPACE_MTOPOLOGY]) THEN
    ASM SET_TAC[];
    FIRST_ASSUM(MP_TAC \<circ> CONJUNCT1 \<circ> REWRITE_RULE[CONTINUOUS_MAP])] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[uniformly_continuous_map] THEN
  ASM_SIMP_TAC[SUBMETRIC; SET_RULE `s \<subseteq> u \<Longrightarrow> s \<inter> u = s`;
               SET_RULE `s \<subseteq> u \<Longrightarrow> u \<inter> s = s`] THEN
  DISCH_TAC THEN STRIP_TAC THEN X_GEN_TAC `e::real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `e / 2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d::real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology (mtopology m1) (t::A=>bool))
                   (subtopology (mtopology m1) (t::A=>bool))`;
    `\<lambda>z. d m1 (fst z,snd z) < d
         \<Longrightarrow> d m2 (f (fst z),f(snd z)) \<le> e / 2`;
    `s \<times> (s::A=>bool)`] FORALL_IN_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[CLOSURE_OF_CROSS; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN ASM_SIMP_TAC[SET_RULE
   `s \<subseteq> t \<Longrightarrow> t \<inter> s = s \<and> s \<inter> t = s`] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_MESON_TAC[REAL_ARITH `0 < e \<and> x \<le> e / 2 \<Longrightarrow> x < e`]] THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  REWRITE_TAC[SET_RULE
   `{x \<in> s. (\<not> (0 \<le> f x) \<Longrightarrow> 0 \<le> g x)} =
    {x \<in> s. g x \<in> {y. 0 \<le> y}} \<union>
    {x \<in> s. f x \<in> {y. 0 \<le> y}}`] THEN
  MATCH_MP_TAC CLOSED_IN_UNION THEN CONJ_TAC THEN
  MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
  EXISTS_TAC `euclideanreal` THEN REWRITE_TAC[GSYM REAL_CLOSED_IN] THEN
  REWRITE_TAC[REWRITE_RULE[real_ge] REAL_CLOSED_HALFSPACE_GE] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
  REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_MDIST_ALT THEN
  REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; GSYM SUBTOPOLOGY_CROSS] THEN
  SIMP_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND; ETA_AX;
           CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
  CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology (mtopology m1) (t::A=>bool)` THEN
  ASM_SIMP_TAC[SUBTOPOLOGY_CROSS; CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND]);;

lemma uniformly_continuous_map_extends_to_closure_of:
   "\<And>m1 m2 f s.
        mcomplete m2 \<and> uniformly_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> \<exists>g. uniformly_continuous_map
                   (submetric1 (mtopology m1 closure_of s),m2) g \<and>
                \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `s::A=>bool`]
         CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
  ASM_SIMP_TAC[UNIFORMLY_IMP_CAUCHY_CONTINUOUS_MAP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g::A=>B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `M1 \<inter> s::A=>bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_INTER; GSYM TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT; SUBSET_REFL] THEN
  REWRITE_TAC[TOPSPACE_MTOPOLOGY; GSYM SUBMETRIC_RESTRICT] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_EQ THEN EXISTS_TAC `f::A=>B` THEN
  ASM_SIMP_TAC[SUBMETRIC; IN_INTER]);;

lemma uniformly_continuous_map_extends_to_intermediate_closure_of:
   "\<And>m1 m2 f s t.
        mcomplete m2 \<and>
        uniformly_continuous_map (submetric1 s,m2) f \<and>
        t \<subseteq> mtopology m1 closure_of s
        \<Longrightarrow> \<exists>g. uniformly_continuous_map (submetric1 t,m2) g \<and>
                \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `s::A=>bool`]
        UNIFORMLY_CONTINUOUS_MAP_EXTENDS_TO_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[UNIFORMLY_CONTINUOUS_MAP_FROM_SUBMETRIC_MONO]);;

lemma Cauchy_continuous_map_on_intermediate_closure:
   "\<And>m1 m2 f::A=>B s t.
        s \<subseteq> t \<and> t \<subseteq> (mtopology m1) closure_of s \<and>
        continuous_map (subtopology (mtopology m1) t,mtopology m2) f \<and>
        Cauchy_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> Cauchy_continuous_map (submetric1 t,m2) f"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
  SUBGOAL_THEN `submetric1 (s::A=>bool) = submetric1 (M1 \<inter> s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBMETRIC_SUBMETRIC; SUBMETRIC_MSPACE];
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC \<circ> SPEC `M1::A=>bool` \<circ> MATCH_MP (SET_RULE
       `s \<subseteq> t \<Longrightarrow> \<forall>u. u \<inter> s \<subseteq> u \<and> u \<inter> s \<subseteq> t`))
     MP_TAC) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    SPEC_TAC(`M1 \<inter> (s::A=>bool)`,`s::A=>bool`)] THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(t::A=>bool) \<subseteq> M1` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[closure_of; TOPSPACE_MTOPOLOGY]) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[Cauchy_continuous_map; CAUCHY_IN_SUBMETRIC] THEN
  X_GEN_TAC `x::num=>A` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `\<forall>n. \<exists>y. y \<in> s \<and>
            d m1 (x n,y) < inverse(Suc n) \<and>
            d m2 (f(x n),f y) < inverse(Suc n)`
  MP_TAC THENL
   [X_GEN_TAC `n::num` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM MTOPOLOGY_SUBMETRIC]) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [METRIC_CONTINUOUS_MAP]) THEN
    ASM_SIMP_TAC[SUBMETRIC; SET_RULE `s \<subseteq> u \<Longrightarrow> s \<inter> u = s`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC \<circ> SPECL [`(x::num=>A) n`; `inverse(Suc n)`]) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `0 < n + 1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `d::real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE RAND_CONV [METRIC_CLOSURE_OF]) THEN
    REWRITE_TAC[\<subseteq>; IN_ELIM_THM; IN_MBALL] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `(x::num=>A) n`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC \<circ> SPEC `min d (inverse(Suc n))`)) THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_INV_EQ; REAL_ARITH `0 < n + 1`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `y::num=>A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [Cauchy_continuous_map]) THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `y::num=>A`) THEN
  ASM_SIMP_TAC[CAUCHY_IN_SUBMETRIC; SUBMETRIC; SET_RULE
   `s \<subseteq> u \<Longrightarrow> s \<inter> u = s`] THEN
  ANTS_TAC THENL [UNDISCH_TAC `MCauchy m1 (x::num=>A)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[MCauchy; o_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> CONJUNCT1 \<circ> GEN_REWRITE_RULE id [continuous_map]) THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_MTOPOLOGY;
               SET_RULE `s \<subseteq> t \<Longrightarrow> t \<inter> s = s`] THEN
  DISCH_TAC THEN TRY(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  X_GEN_TAC `e::real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `e / 2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `M::num`) THEN
  MP_TAC(SPEC `e / 4` ARCH_EVENTUALLY_INV1) THEN
  ASM_REWRITE_TAC[REAL_ARITH `0 < e / 4 \<longleftrightarrow> 0 < e`] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  DISCH_THEN(X_CHOOSE_TAC `N::num`) THEN EXISTS_TAC `MAX M N` THEN
  ASM_REWRITE_TAC[ARITH_RULE `MAX M N \<le> n \<longleftrightarrow> M \<le> n \<and> N \<le> n`] THEN
  MAP_EVERY X_GEN_TAC [`m::num`; `n::num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`m::num`; `n::num`]) THEN
  ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC(METRIC_ARITH
     `(x \<in> M \<and> x' \<in> M \<and> y \<in> M \<and> y' \<in> M) \<and>
      (d x y < e / 4 \<and> d x' y' < e / 4)
      \<Longrightarrow> d x x' < e / 2 \<Longrightarrow> d y y' < e`);
    MATCH_MP_TAC(METRIC_ARITH
     `(x \<in> M \<and> x' \<in> M \<and> y \<in> M \<and> y' \<in> M) \<and>
      (d x y < e / 4 \<and> d x' y' < e / 4)
      \<Longrightarrow> d y y' < e / 2 \<Longrightarrow> d x x' < e`)] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[REAL_LT_TRANS]]));;

lemma Cauchy_continuous_map_extends_to_closure_of:
   "\<And>m1 m2 f s.
        mcomplete m2 \<and> Cauchy_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> \<exists>g. Cauchy_continuous_map
                   (submetric1 (mtopology m1 closure_of s),m2) g \<and>
                \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC \<circ> MATCH_MP
    CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g::A=>B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `M1 \<inter> s::A=>bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_INTER; GSYM TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT; SUBSET_REFL] THEN
  REWRITE_TAC[TOPSPACE_MTOPOLOGY; GSYM SUBMETRIC_RESTRICT] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_EQ THEN EXISTS_TAC `f::A=>B` THEN
  ASM_SIMP_TAC[SUBMETRIC; IN_INTER]);;

lemma Cauchy_continuous_map_extends_to_intermediate_closure_of:
   "\<And>m1 m2 f s t.
        mcomplete m2 \<and>
        Cauchy_continuous_map (submetric1 s,m2) f \<and>
        t \<subseteq> mtopology m1 closure_of s
        \<Longrightarrow> \<exists>g. Cauchy_continuous_map (submetric1 t,m2) g \<and>
                \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `s::A=>bool`]
        CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CAUCHY_CONTINUOUS_MAP_FROM_SUBMETRIC_MONO]);;


subsection\<open>Lavrentiev extension etc\<close>


lemma convergent_eq_zero_oscillation_gen:
   "\<And>X m f s a.
        mcomplete \<and> image f (topspace X \<inter> s) \<subseteq> M
        \<Longrightarrow> ((\<exists>l. limitin mtopology f l (atin X a within s)) \<longleftrightarrow>
             \<not> (M = {}) \<and>
             (a \<in> topspace X
              \<Longrightarrow> \<forall>e. 0 < e
                      \<Longrightarrow> \<exists>u. openin X u \<and> a \<in> u \<and>
                              \<forall>x y. x \<in> (s \<inter> u) - {a} \<and>
                                    y \<in> (s \<inter> u) - {a}
                                    \<Longrightarrow> d (f x) f y < e))"
oops
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `M::B=>bool = {}` THENL
   [ASM_REWRITE_TAC[LIMIT_METRIC; NOT_IN_EMPTY]; STRIP_TAC] THEN
  ASM_CASES_TAC `(a::A) \<in> topspace X` THENL
   [ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[LIMIT_METRIC; EVENTUALLY_WITHIN_IMP;
                 EVENTUALLY_ATPOINTOF; NOT_IN_EMPTY] THEN
    ASM SET_TAC[]] THEN
  ASM_CASES_TAC `(a::A) \<in> X derived_set_of s` THENL
   [ALL_TAC;
    MATCH_MP_TAC(TAUT `p \<and> q \<Longrightarrow> (p \<longleftrightarrow> q)`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MEMBER_NOT_EMPTY; TOPSPACE_MTOPOLOGY;
                    TRIVIAL_LIMIT_ATPOINTOF_WITHIN; LIMIT_TRIVIAL];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE (RAND_CONV \<circ> RAND_CONV)
       [derived_set_of]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; NOT_FORALL_THM; NOT_IMP] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]]] THEN
  EQ_TAC THENL
   [REWRITE_TAC[LIMIT_METRIC; EVENTUALLY_WITHIN_IMP; EVENTUALLY_ATPOINTOF] THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_IMP] THEN
    X_GEN_TAC `l::B` THEN STRIP_TAC THEN
    X_GEN_TAC `e::real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `e / 2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `u::A=>bool` THEN REWRITE_TAC[IN_DELETE; IN_INTER] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `y::A` th) THEN MP_TAC(SPEC `x::A` th)) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(l::B) \<in> M` THEN
    CONV_TAC METRIC_ARITH;
    DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [MCOMPLETE_FIP_SING]) THEN
  DISCH_THEN(MP_TAC \<circ> SPEC
   `{ mtopology closure_of (image f ((s \<inter> u) - {a})) |u|
      openin X u \<and> a \<in> u}`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC; CLOSED_IN_CLOSURE_OF] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE; RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_IN_GSPEC] THEN CONJ_TAC THENL
     [X_GEN_TAC `e::real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> SPEC `e::real`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `u::A=>bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [IN_DERIVED_SET_OF]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC \<circ> SPEC `u::A=>bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `b::A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `f b` THEN MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
      REWRITE_TAC[CLOSED_IN_MCBALL; \<subseteq>; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[IN_INTER; IN_DELETE; IN_MCBALL; CONJ_ASSOC] THEN
      GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[\<subseteq>; IN_INTER; FORALL_IN_IMAGE]) THEN
        ASM_MESON_TAC[\<subseteq>; OPEN_IN_SUBSET];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_INTER; IN_DELETE]];
      X_GEN_TAC `t:(A=>bool)->bool` THEN
      REWRITE_TAC[\<subseteq>; IN_ELIM_THM] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[IMAGE_o] THEN
      MATCH_MP_TAC(SET_RULE
       `\<forall>g. (\<forall>s. s \<in> t \<Longrightarrow> s \<subseteq> g s) \<and> (\<exists>x. x \<in> \<Inter> t)
             \<Longrightarrow> \<not> (\<Inter> (g ` t) = {})`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
        REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[OPEN_IN_CLOSED_IN_EQ]) THEN
        ASM SET_TAC[];
        FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [IN_DERIVED_SET_OF]) THEN
        DISCH_THEN(MP_TAC \<circ> SPEC
          `\<Inter> (topspace insert X t):A=>bool` \<circ> CONJUNCT2) THEN
        ASM_SIMP_TAC[OPEN_IN_INTERS; GSYM INTERS_INSERT; NOT_INSERT_EMPTY;
                     FINITE_INSERT; FORALL_IN_INSERT; OPEN_IN_TOPSPACE] THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `y::A` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `f y` THEN REWRITE_TAC[INTERS_IMAGE] THEN
        ASM SET_TAC[]]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b::B` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[LIMIT_METRIC] THEN X_GEN_TAC `e::real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `e / 2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `u::A=>bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP (SET_RULE `s = {a} \<Longrightarrow> a \<in> s`)) THEN
    REWRITE_TAC[INTERS_GSPEC; closure_of; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `u::A=>bool`) THEN
    ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `mball m (b::B,e / 2)`) THEN
    ASM_SIMP_TAC[CENTRE_IN_MBALL; REAL_HALF; OPEN_IN_MBALL; IN_INTER] THEN
    REWRITE_TAC[IN_MBALL; LEFT_IMP_EXISTS_THM; IN_DELETE; IN_INTER] THEN
    X_GEN_TAC `x::A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[EVENTUALLY_WITHIN_IMP; EVENTUALLY_ATPOINTOF] THEN
    EXISTS_TAC `u::A=>bool` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    X_GEN_TAC `y::A` THEN STRIP_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p \<and> (p \<Longrightarrow> q) \<Longrightarrow> p \<and> q`) THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[\<subseteq>; IN_INTER; FORALL_IN_IMAGE]) THEN
      ASM_MESON_TAC[\<subseteq>; OPEN_IN_SUBSET];
      FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`x::A`; `y::A`]) THEN
      ASM_REWRITE_TAC[IN_INTER; IN_DELETE] THEN
      MAP_EVERY UNDISCH_TAC
       [`d b f x < e / 2`; `(b::B) \<in> M`;
        `f x \<in> M`] THEN
      CONV_TAC METRIC_ARITH]]);;

lemma gdelta_in_points_of_convergence_within:
   "\<And>X Y f s.
        completely_metrizable_space Y \<and>
        (continuous_map (subtopology X s,Y) f \<or>
         t1_space X \<and> f ` s \<subseteq> topspace Y)
        \<Longrightarrow> gdelta_in X
             {x \<in> topspace X.
                  \<exists>l. limitin Y f l (atin X x within s)}"
oops
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_COMPLETELY_METRIZABLE_SPACE] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `image f (topspace X \<inter> s) \<subseteq> M`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; TOPSPACE_SUBTOPOLOGY;
                  TOPSPACE_MTOPOLOGY];
    ONCE_REWRITE_TAC[TAUT `p \<and> q \<longleftrightarrow> (p \<noteq>=> \<not> q)`] THEN
    ASM_SIMP_TAC[CONVERGENT_EQ_ZERO_OSCILLATION_GEN] THEN
    REWRITE_TAC[NOT_IMP]] THEN
  ASM_CASES_TAC `M::B=>bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; GDELTA_IN_EMPTY] THEN
  MATCH_MP_TAC(MESON[]
   `\<forall>s. gdelta_in X s \<and> t = s \<Longrightarrow> gdelta_in X t`) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC
     `topspace X \<inter>
      \<Inter> {\<Union>{u. openin X u \<and>
                          \<forall>x y. x \<in> (s \<inter> u) \<and>
                                y \<in> (s \<inter> u)
                                \<Longrightarrow> d (f x) f y < inverse(Suc n)}
              | n \<in> UNIV}`;
    EXISTS_TAC
     `topspace X \<inter>
      \<Inter> {\<Union>{u. openin X u \<and>
                          \<exists>b. b \<in> topspace X \<and>
                              \<forall>x y. x \<in> (s \<inter> u) - {b} \<and>
                                    y \<in> (s \<inter> u) - {b}
                                    \<Longrightarrow> d (f x) f y < inverse(Suc n)}
              | n \<in> UNIV}`] THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[gdelta_in] THEN MATCH_MP_TAC RELATIVE_TO_INC THEN
     MATCH_MP_TAC COUNTABLE_INTERSECTION_OF_INTERS THEN
     ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
     REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN GEN_TAC THEN
     MATCH_MP_TAC COUNTABLE_INTERSECTION_OF_INC THEN
     MATCH_MP_TAC OPEN_IN_UNIONS THEN SIMP_TAC[IN_ELIM_THM];
     ALL_TAC]) THEN
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
    DISCH_THEN(X_CHOOSE_THEN `u::A=>bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(a::A) \<in> s` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [CONTINUOUS_MAP_TO_METRIC]) THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `a::A`) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `e::real`) THEN
    ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_ALT; EXISTS_IN_GSPEC; IN_INTER] THEN
    REWRITE_TAC[IN_MBALL; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `v::A=>bool` THEN STRIP_TAC THEN
    EXISTS_TAC `u \<inter> v::A=>bool` THEN
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
    MAP_EVERY X_GEN_TAC [`u::A=>bool`; `b::A`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `b::A = a` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [t1_space]) THEN
    DISCH_THEN(MP_TAC \<circ> SPECL [`a::A`; `b::A`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v::A=>bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u \<inter> v::A=>bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN ASM SET_TAC[]]);;

lemma lavrentiev_extension_gen:
   "\<And>X s Y f.
        s \<subseteq> topspace X \<and>
        completely_metrizable_space Y \<and>
        continuous_map(subtopology X s,Y) f
        \<Longrightarrow> \<exists>u g. gdelta_in X u \<and>
                  s \<subseteq> u \<and>
                  continuous_map
                     (subtopology X (X closure_of s \<inter> u),Y) g \<and>
                  \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `{x \<in> topspace X.
         \<exists>l. limitin Y f l (atin X x within s)}` THEN
  REWRITE_TAC[INTER_SUBSET; RIGHT_EXISTS_AND_THM] THEN
  ASM_SIMP_TAC[GDELTA_IN_POINTS_OF_CONVERGENCE_WITHIN] THEN
  MATCH_MP_TAC(TAUT `p \<and> (p \<Longrightarrow> q) \<Longrightarrow> p \<and> q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[\<subseteq>; IN_ELIM_THM] THEN X_GEN_TAC `x::A` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [CONTINUOUS_MAP_ATPOINTOF]) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ASM_MESON_TAC[ATPOINTOF_SUBTOPOLOGY; \<subseteq>];
    DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_EXTENSION_POINTWISE_ALT THEN
    ASM_SIMP_TAC[INTER_SUBSET; METRIZABLE_IMP_REGULAR_SPACE;
                 COMPLETELY_METRIZABLE_IMP_METRIZABLE_SPACE] THEN
    SIMP_TAC[IN_INTER; IN_ELIM_THM; IN_DIFF] THEN
    ASM_SIMP_TAC[SUBSET_INTER; CLOSURE_OF_SUBSET]]);;

lemma lavrentiev_extension:
   "\<And>X s Y f.
        s \<subseteq> topspace X \<and>
        (metrizable_space X \<or> topspace X \<subseteq> X closure_of s) \<and>
        completely_metrizable_space Y \<and>
        continuous_map(subtopology X s,Y) f
        \<Longrightarrow> \<exists>u g. gdelta_in X u \<and>
                  s \<subseteq> u \<and>
                  u \<subseteq> X closure_of s \<and>
                  continuous_map(subtopology X u,Y) g \<and>
                  \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X::A topology`; `s::A=>bool`; `Y:B topology`; `f::A=>B`]
    LAVRENTIEV_EXTENSION_GEN) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g::A=>B` THEN
  DISCH_THEN(X_CHOOSE_THEN `u::A=>bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `X closure_of s \<inter> u::A=>bool` THEN
  ASM_SIMP_TAC[INTER_SUBSET; SUBSET_INTER; CLOSURE_OF_SUBSET] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [MATCH_MP_TAC GDELTA_IN_INTER THEN
    ASM_SIMP_TAC[CLOSED_IMP_GDELTA_IN; CLOSED_IN_CLOSURE_OF];
    FIRST_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (MESON[]
     `gdelta_in X s \<Longrightarrow> t = s \<Longrightarrow> gdelta_in X t`)) THEN
    REWRITE_TAC[SET_RULE `c \<inter> u = u \<longleftrightarrow> u \<subseteq> c`] THEN
    ASM_MESON_TAC[SUBSET_TRANS; GDELTA_IN_SUBSET]]);;


subsection\<open>"Capped" equivalent bounded metrics and general product metrics\<close>


definition capped_metric where
 `capped_metric d (m::A metric) =
        if d \<le> 0 then m
        else metric(M,(\<lambda>(x,y). min d (d x y)))"

lemma capped_metric:
   "mspace (capped_metric d m) = M \<and>
        d (capped_metric d m) =
           \<lambda>(x,y). if d \<le> 0 then d x y else min d (d x y)"
oops
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d::real \<le> 0` THEN
  ASM_REWRITE_TAC[capped_metric; PAIRED_ETA_THM; ETA_AX] THEN
  REWRITE_TAC[capped_metric; mspace; d; GSYM PAIR_EQ] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 metric_tybij)] THEN
  REWRITE_TAC[is_metric_space; GSYM mspace; GSYM d] THEN
  ASM_SIMP_TAC[REAL_ARITH `\<not> (d \<le> 0) \<Longrightarrow> (0 \<le> min d x \<longleftrightarrow> 0 \<le> x)`] THEN
  ASM_SIMP_TAC[MDIST_POS_LE; MDIST_0; REAL_ARITH
    `\<not> (d \<le> 0) \<and> 0 \<le> x  \<Longrightarrow> (min d x = 0 \<longleftrightarrow> x = 0)`] THEN
  CONJ_TAC THENL [MESON_TAC[MDIST_SYM]; REPEAT STRIP_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `\<not> (d \<le> 0) \<and> 0 \<le> y \<and> 0 \<le> z \<and> x \<le> y + z
    \<Longrightarrow> min d x \<le> min d y + min d z`) THEN
  ASM_MESON_TAC[MDIST_POS_LE; MDIST_TRIANGLE]);;

lemma mdist_capped:
   "0 < d \<Longrightarrow> d(capped_metric d m) (x,y) \<le> d"
oops
  SIMP_TAC[CAPPED_METRIC; GSYM REAL_NOT_LT] THEN REAL_ARITH_TAC);;

lemma mtopology_capped_metric:
   "mtopology(capped_metric d m) = mtopology"
oops
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d \<le> 0` THENL
   [ASM_MESON_TAC[capped_metric];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE])] THEN
  REWRITE_TAC[TOPOLOGY_EQ] THEN
  X_GEN_TAC `s::A=>bool` THEN ASM_REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN
  ASM_CASES_TAC `(s::A=>bool) \<subseteq> M` THEN
  ASM_REWRITE_TAC[CAPPED_METRIC] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
  X_GEN_TAC `a::A` THEN ASM_CASES_TAC `(a::A) \<in> s` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[\<subseteq>; IN_MBALL] THEN
  ASM_CASES_TAC `(a::A) \<in> M` THENL
   [ASM_REWRITE_TAC[CAPPED_METRIC]; ASM SET_TAC[]] THEN
  EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `r::real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d / 2) r` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

lemma MCauchy_capped_metric:
   "\<And>d (m::A metric) x.
        MCauchy (capped_metric d m) x \<longleftrightarrow> MCauchy x"
oops
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d \<le> 0` THENL
   [ASM_MESON_TAC[capped_metric]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MCauchy; CAPPED_METRIC; REAL_MIN_LT] THEN
  ASM_MESON_TAC[REAL_ARITH `\<not> (d < min d e)`; REAL_LT_MIN; REAL_NOT_LE]);;

lemma mcomplete_capped_metric:
   "\<And>d (m::A metric). mcomplete(capped_metric d m) \<longleftrightarrow> mcomplete"
oops
  REWRITE_TAC[mcomplete; CAUCHY_IN_CAPPED_METRIC; MTOPOLOGY_CAPPED_METRIC]);;

lemma bounded_equivalent_metric:
   "0 < d
        \<Longrightarrow> ?m'. mspace m' = M \<and>
                 mtopology m' = mtopology \<and>
                 \<forall>x y. d m' (x,y) < d"
oops
  REPEAT STRIP_TAC THEN EXISTS_TAC `capped_metric (d / 2) m::A metric` THEN
  ASM_REWRITE_TAC[MTOPOLOGY_CAPPED_METRIC; CAPPED_METRIC] THEN
  ASM_REAL_ARITH_TAC);;

lemma sup_metric_cartesian_product:
   "\<And>k (m::K-> Ametric) m'.
        metric(PiE k (mspace \<circ> m),
               \<lambda>(x,y). sup {d(m i) (x i,y i) | i \<in> k}) = m' \<and>
        (k \<noteq> {}) \<and>
        (\<exists>c. \<forall>i x y. i \<in> k \<and> x \<in> mspace(m i) \<and> y \<in> mspace(m i)
                      \<Longrightarrow> d(m i) (x,y) \<le> c)
        \<Longrightarrow> mspace m' = PiE k (mspace \<circ> m) \<and>
            d m' = (\<lambda>(x,y). sup {d(m i) (x i,y i) | i \<in> k}) \<and>
            \<forall>x y b. x \<in> PiE k (mspace \<circ> m) \<and>
                    y \<in> PiE k (mspace \<circ> m)
                    \<Longrightarrow> (d m' (x,y) \<le> b \<longleftrightarrow>
                         \<forall>i. i \<in> k \<Longrightarrow> d (m i) (x i,y i) \<le> b)"
oops
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `M = \<lambda>(x,y). sup {d(m i) (x i::A,y i) | (i::K) \<in> k}` THEN
  SUBGOAL_THEN
   `!x (y::K=>A) b.
        x \<in> PiE k (mspace \<circ> m) \<and>
        y \<in> PiE k (mspace \<circ> m)
        \<Longrightarrow> (M(x,y) \<le> b \<longleftrightarrow> \<forall>i. i \<in> k \<Longrightarrow> d (m i) (x i,y i) \<le> b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[PiE; o_DEF; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN EXPAND_TAC "M" THEN REWRITE_TAC[] THEN
    W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand) REAL_SUP_LE_EQ \<circ> lhand \<circ> snd) THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP (MESON[]
   `m = m' \<Longrightarrow> M = mspace m' \<and> d m = d m'`)) THEN
  REWRITE_TAC[GSYM PAIR_EQ; mspace; d] THEN
  W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand) (CONJUNCT2 metric_tybij) \<circ>
    lhand \<circ> lhand \<circ> snd) THEN
  DISCH_THEN(MP_TAC \<circ> fst \<circ> EQ_IMP_RULE) THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN(SUBST1_TAC \<circ> SYM) THEN
    ASM_REWRITE_TAC[GSYM d]] THEN
  REWRITE_TAC[is_metric_space] THEN
  MATCH_MP_TAC(TAUT `p \<and> (p \<Longrightarrow> q) \<Longrightarrow> p \<and> q`) THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "M" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_SUP THEN
    ASM_SIMP_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PiE; IN_ELIM_THM; o_THM]) THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `c::real`) THEN EXISTS_TAC `c::real` THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[MDIST_POS_LE];
    DISCH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun th ->
      SUBST1_TAC(MATCH_MP CARTESIAN_PRODUCT_EQ_MEMBERS_EQ th) THEN
      MP_TAC th) THEN
    REWRITE_TAC[PiE; o_THM; IN_ELIM_THM] THEN
    SIMP_TAC[METRIC_ARITH
     `x \<in> M \<and> y \<in> M \<Longrightarrow> (d x y \<le> 0 \<longleftrightarrow> x = y)`];
    REPEAT STRIP_TAC THEN EXPAND_TAC "M" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `(\<forall>i. i \<in> w \<Longrightarrow> f i = g i) \<Longrightarrow> {f i | i \<in> w} = {g i | i \<in> w}`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PiE; IN_ELIM_THM; o_THM]) THEN
    ASM_MESON_TAC[MDIST_SYM];
    MAP_EVERY X_GEN_TAC [`x::K=>A`; `y::K=>A`; `z::K=>A`] THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN X_GEN_TAC `i::K` THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS
      `d (m i) ((x::K=>A) i,y i) + d (m i) (y i,z i)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MDIST_TRIANGLE THEN
      RULE_ASSUM_TAC(REWRITE_RULE[PiE; IN_ELIM_THM; o_THM]) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_ADD2 THEN EXPAND_TAC "M" THEN
      REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC ELEMENT_LE_SUP THEN
      RULE_ASSUM_TAC(REWRITE_RULE[PiE; IN_ELIM_THM; o_THM]) THEN
      ASM SET_TAC[]]]);;

let (METRIZABLE_SPACE_PRODUCT_TOPOLOGY,
     COMPLETELY_METRIZABLE_SPACE_PRODUCT_TOPOLOGY) = (CONJ_PAIR \<circ> prove)
 (`(!(tops::K=>A topology) k.
        metrizable_space (product_topology k tops) \<longleftrightarrow>
        topspace (product_topology k tops) = {} \<or>
        countable {i. i \<in> k \<and> \<not> (\<exists>a. topspace(tops i) \<subseteq> {a})} \<and>
        \<forall>i. i \<in> k \<Longrightarrow> metrizable_space (tops i)) \<and>
   (!(tops::K=>A topology) k.
        completely_metrizable_space (product_topology k tops) \<longleftrightarrow>
        topspace (product_topology k tops) = {} \<or>
        countable {i. i \<in> k \<and> \<not> (\<exists>a. topspace(tops i) \<subseteq> {a})} \<and>
        \<forall>i. i \<in> k \<Longrightarrow> completely_metrizable_space (tops i))"
oops
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(n \<Longrightarrow> m) \<and> (t \<Longrightarrow> n) \<and> (m \<Longrightarrow> t \<or> m') \<and> (n \<Longrightarrow> t \<or> n') \<and>
    (\<not> t \<Longrightarrow> m \<and> m' \<Longrightarrow> c) \<and> (\<not> t \<Longrightarrow> c \<Longrightarrow> (m' \<Longrightarrow> m) \<and> (n' \<Longrightarrow> n))
    \<Longrightarrow> (m \<longleftrightarrow> t \<or> c \<and> m') \<and> (n \<longleftrightarrow> t \<or> c \<and> n')`) THEN
  REWRITE_TAC[COMPLETELY_METRIZABLE_IMP_METRIZABLE_SPACE] THEN CONJ_TAC THENL
   [SIMP_TAC[GSYM SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY_EMPTY] THEN
    REWRITE_TAC[COMPLETELY_METRIZABLE_SPACE_DISCRETE_TOPOLOGY];
    GEN_REWRITE_TAC id [CONJ_ASSOC]] THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC TOPOLOGICAL_PROPERTY_OF_PRODUCT_COMPONENT THEN
    REWRITE_TAC[HOMEOMORPHIC_COMPLETELY_METRIZABLE_SPACE;
                HOMEOMORPHIC_METRIZABLE_SPACE] THEN
    ASM_SIMP_TAC[METRIZABLE_SPACE_SUBTOPOLOGY] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COMPLETELY_METRIZABLE_SPACE_CLOSED_IN THEN
    ASM_REWRITE_TAC[CLOSED_IN_CARTESIAN_PRODUCT] THEN
    DISJ2_TAC THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
    FIRST_ASSUM(MP_TAC \<circ>
      MATCH_MP COMPLETELY_METRIZABLE_IMP_METRIZABLE_SPACE) THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP METRIZABLE_IMP_T1_SPACE) THEN
    REWRITE_TAC[T1_SPACE_PRODUCT_TOPOLOGY] THEN
    REWRITE_TAC[T1_SPACE_CLOSED_IN_SING; RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
    STRIP_TAC THENL [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [TOPSPACE_PRODUCT_TOPOLOGY; PiE; o_DEF; IN_ELIM_THM]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ABBREV_TAC
     `l = {i::K | i \<in> k \<and> \<not> (\<exists>a::A. topspace(tops i) \<subseteq> {a})}` THEN
    SUBGOAL_THEN
     `\<forall>i::K. \<exists>p q::A.
        i \<in> l \<Longrightarrow> p \<in> topspace(tops i) \<and> q \<in> topspace(tops i) \<and> (p \<noteq> q)`
    MP_TAC THENL [EXPAND_TAC "l" THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a::K=>A`; `b::K=>A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; o_DEF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `z::K=>A` THEN DISCH_TAC THEN
    ABBREV_TAC `p::K=>A = \<lambda>i. if i \<in> l then a i else z i` THEN
    ABBREV_TAC `q::K=>K->A = \<lambda>i j. if j = i then b i else p j` THEN
    SUBGOAL_THEN
     `p \<in> topspace(product_topology k (tops::K=>A topology)) \<and>
      (\<forall>i::K. i \<in> l
             \<Longrightarrow> q i \<in> topspace(product_topology k (tops::K=>A topology)))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z::K=>A) \<in> PiE k (\<lambda>x. topspace(tops x))` THEN
      MAP_EVERY EXPAND_TAC ["q"; "p"] THEN
      REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; PiE; o_THM] THEN
      REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `\<forall>u:(K=>A)->bool.
        openin (product_topology k tops) u \<and> p \<in> u
        \<Longrightarrow> finite {i::K | i \<in> l \<and> \<not> (q i \<in> u)}`
    ASSUME_TAC THENL
     [X_GEN_TAC `u:(K=>A)->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      REWRITE_TAC[OPEN_IN_PRODUCT_TOPOLOGY_ALT] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `p::K=>A`) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `v::K=>A->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
      REWRITE_TAC[\<subseteq>; IN_ELIM_THM] THEN X_GEN_TAC `i::K` THEN
      MATCH_MP_TAC(TAUT
       `(l \<Longrightarrow> k) \<and> (k \<and> l \<Longrightarrow> p \<Longrightarrow> q) \<Longrightarrow> l \<and> \<not> q \<Longrightarrow> k \<and> \<not> p`) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; REPEAT STRIP_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC \<circ> GEN_REWRITE_RULE id [\<subseteq>]) THEN
      EXPAND_TAC "q" THEN UNDISCH_TAC `(p::K=>A) \<in> PiE k v` THEN
      REWRITE_TAC[PiE; IN_ELIM_THM; EXTENSIONAL] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [metrizable_space]) THEN
    DISCH_THEN(X_CHOOSE_TAC `m:(K=>A)metric`) THEN
    MATCH_MP_TAC COUNTABLE_SUBSET THEN
    EXISTS_TAC `\<Union>{{i. i \<in> l \<and>
                             \<not> ((q::K=>K->A) i \<in> mball m (p,inverse(Suc n)))} |
                        n \<in> UNIV}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_UNIONS THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `n::num` THEN DISCH_THEN(K ALL_TAC) THEN
      MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[OPEN_IN_MBALL] THEN MATCH_MP_TAC CENTRE_IN_MBALL THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `0 < n + 1`] THEN
      ASM_MESON_TAC[TOPSPACE_MTOPOLOGY];
      REWRITE_TAC[\<subseteq>; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `i::K` THEN DISCH_TAC THEN MP_TAC(snd(EQ_IMP_RULE(ISPEC
       `d (m:(K=>A)metric) (p,q(i::K))` ARCH_EVENTUALLY_INV1))) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MDIST_POS_LT THEN REPEAT
         (CONJ_TAC THENL [ASM_MESON_TAC[TOPSPACE_MTOPOLOGY]; ALL_TAC]) THEN
        DISCH_THEN(MP_TAC \<circ> C AP_THM `i::K`) THEN
        MAP_EVERY EXPAND_TAC ["q"; "p"] THEN REWRITE_TAC[] THEN
        ASM_SIMP_TAC[];
        DISCH_THEN(MP_TAC \<circ> MATCH_MP EVENTUALLY_HAPPENS_SEQUENTIALLY) THEN
        MATCH_MP_TAC MONO_EXISTS THEN
        ASM_REWRITE_TAC[IN_MBALL] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `k::K=>bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; COUNTABLE_EMPTY] THEN
    REWRITE_TAC[PRODUCT_TOPOLOGY_EMPTY_DISCRETE;
                METRIZABLE_SPACE_DISCRETE_TOPOLOGY;
                COMPLETELY_METRIZABLE_SPACE_DISCRETE_TOPOLOGY];
    ALL_TAC] THEN
  REWRITE_TAC[metrizable_space; completely_metrizable_space] THEN
  GEN_REWRITE_TAC (BINOP_CONV \<circ> LAND_CONV \<circ> BINDER_CONV)
      [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; AND_FORALL_THM] THEN
  X_GEN_TAC `m::K=>A metric` THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  ASM_CASES_TAC `\<forall>i. i \<in> k \<Longrightarrow> mtopology(m i) = (tops::K=>A topology) i` THEN
  ASM_SIMP_TAC[] THENL [ALL_TAC; ASM_MESON_TAC[]] THEN MATCH_MP_TAC(MESON[]
   `\<forall>m. P m \<and> (Q \<Longrightarrow> C m) \<Longrightarrow> (\<exists>m. P m) \<and> (Q \<Longrightarrow> \<exists>m. C m \<and> P m)`) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id
   [COUNTABLE_AS_INJECTIVE_IMAGE_SUBSET]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; INJECTIVE_ON_LEFT_INVERSE] THEN
  MAP_EVERY X_GEN_TAC [`nk::num=>K`; `c::num=>bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `kn::K=>num`)) THEN
  MP_TAC(ISPECL
   [`k::K=>bool`; `\<lambda>i. capped_metric (inverse((kn i) + 1)) ((m::K=>A metric) i)`]
   SUP_METRIC_CARTESIAN_PRODUCT) THEN
  REWRITE_TAC[o_DEF; CONJUNCT1(SPEC_ALL CAPPED_METRIC)] THEN
  MATCH_MP_TAC(MESON[]
   `Q \<and> (\<forall>m. P m \<Longrightarrow> R m)
    \<Longrightarrow> (\<forall>m. a = m \<and> Q \<Longrightarrow> P m) \<Longrightarrow> \<exists>m. R m`) THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `1::real` THEN
    REWRITE_TAC[CAPPED_METRIC; GSYM REAL_NOT_LT] THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `0 < n + 1`] THEN
    REWRITE_TAC[REAL_NOT_LT; REAL_MIN_LE] THEN REPEAT STRIP_TAC THEN
    DISJ1_TAC THEN MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
    X_GEN_TAC `M:(K=>A)metric`] THEN
  SUBGOAL_THEN
   `PiE k (\<lambda>i. mspace (m i)) =
    topspace(product_topology k (tops::K=>A topology))`
  SUBST1_TAC THENL
   [REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; CARTESIAN_PRODUCT_EQ] THEN
    ASM_SIMP_TAC[GSYM TOPSPACE_MTOPOLOGY; o_THM];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC \<circ> SYM) ASSUME_TAC)] THEN
  MATCH_MP_TAC(TAUT `p \<and> (p \<Longrightarrow> q) \<Longrightarrow> p \<and> q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[MTOPOLOGY_BASE; product_topology] THEN
    REWRITE_TAC[GSYM TOPSPACE_PRODUCT_TOPOLOGY_ALT] THEN
    REWRITE_TAC[PRODUCT_TOPOLOGY_BASE_ALT] THEN
    MATCH_MP_TAC TOPOLOGY_BASES_EQ THEN
    REWRITE_TAC[SET_RULE `GSPEC P x \<longleftrightarrow> x \<in> GSPEC P`] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; GSYM CONJ_ASSOC; IN_MBALL] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z::K=>A`; `r::real`] THEN STRIP_TAC THEN
      X_GEN_TAC `x::K=>A` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `(\<forall>i. i \<in> k \<Longrightarrow> (z::K=>A) i \<in> topspace(tops i)) \<and>
        (\<forall>i. i \<in> k \<Longrightarrow> (x::K=>A) i \<in> topspace(tops i))`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(z::K=>A) \<in> mspace M`; `(x::K=>A) \<in> mspace M`] THEN
        ASM_SIMP_TAC[TOPSPACE_PRODUCT_TOPOLOGY; PiE; o_DEF] THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `\<exists>R. 0 < R \<and> d M (z::K=>A,x) < R \<and> R < r`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[REAL_LT_BETWEEN; REAL_LET_TRANS; MDIST_POS_LE];
        ALL_TAC] THEN
      EXISTS_TAC
       `\<lambda>i. if R \<le> inverse((kn i) + 1) then mball (m i) (z i,R)
            else topspace((tops::K=>A topology) i)` THEN
      REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ASSUME `0 < R`) THEN DISCH_THEN(MP_TAC \<circ>
          SPEC `1::real` \<circ> MATCH_MP REAL_ARCH) THEN
        DISCH_THEN(X_CHOOSE_TAC `n::num`) THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `image (nk::num=>K) (c \<inter> {0..n})` THEN
        SIMP_TAC[FINITE_IMAGE; FINITE_INTER; FINITE_NUMSEG] THEN
        REWRITE_TAC[\<subseteq>; IN_ELIM_THM; MESON[]
         `\<not> ((if p then x else y) = y) \<longleftrightarrow> p \<and> (x \<noteq> y)`] THEN
        FIRST_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (SET_RULE
         `{i. i \<in> k \<and> P i} = nk ` c
          \<Longrightarrow> (\<forall>i. i \<in> k \<and> Q i \<Longrightarrow> P i) \<and>
              (\<forall>n. n \<in> c \<Longrightarrow> Q(nk n) \<Longrightarrow> n \<in> s)
              \<Longrightarrow> \<forall>i. i \<in> k \<and> Q i \<Longrightarrow> i \<in> image nk (c \<inter> s)`)) THEN
        CONJ_TAC THENL
         [X_GEN_TAC `i::K` THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          MATCH_MP_TAC(SET_RULE
           `\<forall>x. b \<subseteq> u \<and> x \<in> b
                \<Longrightarrow> P \<and> (b \<noteq> u) \<Longrightarrow> \<not> (\<exists>a. u \<subseteq> {a})`) THEN
          EXISTS_TAC `(z::K=>A) i` THEN CONJ_TAC THENL
           [REWRITE_TAC[\<subseteq>; IN_MBALL];
            MATCH_MP_TAC CENTRE_IN_MBALL] THEN
          ASM_MESON_TAC[TOPSPACE_MTOPOLOGY];
          X_GEN_TAC `m::num` THEN ASM_SIMP_TAC[IN_NUMSEG; LE_0] THEN
          DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
          GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN
          REWRITE_TAC[NOT_LE; REAL_NOT_LE] THEN DISCH_TAC THEN
          REWRITE_TAC[REAL_ARITH `inverse x < y \<longleftrightarrow> 1 / x < y`] THEN
          ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `0 < n + 1`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (REAL_ARITH
           `1 < n * r \<Longrightarrow> r * n < r * m \<Longrightarrow> 1 < r * m`)) THEN
          ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
          ASM_ARITH_TAC];
        ASM_MESON_TAC[OPEN_IN_MBALL; OPEN_IN_TOPSPACE];
        SUBGOAL_THEN `(x::K=>A) \<in> PiE k (topspace \<circ> tops)`
        MP_TAC THENL [ASM_MESON_TAC[TOPSPACE_PRODUCT_TOPOLOGY]; ALL_TAC] THEN
        REWRITE_TAC[PiE; o_DEF; IN_ELIM_THM] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i::K` THEN
        DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[IN_MBALL] THEN
        REPEAT(CONJ_TAC THENL
         [ASM_MESON_TAC[TOPSPACE_MTOPOLOGY]; ALL_TAC]) THEN
        FIRST_X_ASSUM(MP_TAC \<circ> SPECL
         [`z::K=>A`; `x::K=>A`; `d M (z::K=>A,x)`]) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[REAL_LE_REFL]] THEN
        DISCH_THEN(MP_TAC \<circ> SPEC `i::K`) THEN
        ASM_REWRITE_TAC[CAPPED_METRIC] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[\<subseteq>] THEN X_GEN_TAC `y::K=>A` THEN
        DISCH_THEN(LABEL_TAC "*") THEN
        SUBGOAL_THEN `(y::K=>A) \<in> mspace M` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY] THEN
          REMOVE_THEN "*" MP_TAC THEN REWRITE_TAC[PiE] THEN
          REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
          MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
          MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i::K` THEN
          ASM_CASES_TAC `(i::K) \<in> k` THEN ASM_REWRITE_TAC[] THEN
          COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_MBALL] THEN
          MATCH_MP_TAC(SET_RULE
           `s \<subseteq> t \<Longrightarrow> P \<and> x \<in> s \<and> Q \<Longrightarrow> x \<in> t`) THEN
          ASM_SIMP_TAC[GSYM TOPSPACE_MTOPOLOGY; SUBSET_REFL];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[IN_MBALL] THEN
        TRANS_TAC REAL_LET_TRANS `R::real` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC \<circ> SPECL
         [`z::K=>A`; `y::K=>A`; `R::real`]) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        REWRITE_TAC[CAPPED_METRIC; REAL_ARITH `x \<le> 0 \<longleftrightarrow> \<not> (0 < x)`] THEN
        REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `0 < n + 1`] THEN
        REWRITE_TAC[REAL_MIN_LE] THEN X_GEN_TAC `i::K` THEN DISCH_TAC THEN
        MATCH_MP_TAC(REAL_ARITH
         `(a \<le> b \<Longrightarrow> c \<le> d) \<Longrightarrow> b \<le> a \<or> c \<le> d`) THEN
        DISCH_TAC THEN REMOVE_THEN "*" MP_TAC THEN
        ASM_REWRITE_TAC[PiE; IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC \<circ> SPEC `i::K` \<circ> CONJUNCT2) THEN
        ASM_REWRITE_TAC[IN_MBALL] THEN REAL_ARITH_TAC];
      X_GEN_TAC `u::K=>A->bool` THEN STRIP_TAC THEN
      X_GEN_TAC `z::K=>A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z::K=>A) \<in> mspace M` ASSUME_TAC THENL
       [UNDISCH_TAC `(z::K=>A) \<in> PiE k u` THEN
        ASM_REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; PiE] THEN
        REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
        ASM_MESON_TAC[OPEN_IN_SUBSET; \<subseteq>];
        EXISTS_TAC `z::K=>A` THEN ASM_SIMP_TAC[MDIST_REFL; CONJ_ASSOC]] THEN
      SUBGOAL_THEN
       `\<forall>i. \<exists>r. i \<in> k \<Longrightarrow> 0 < r \<and> mball (m i) ((z::K=>A) i,r) \<subseteq> u i`
      MP_TAC THENL
       [X_GEN_TAC `i::K` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `openin(mtopology(m i)) ((u::K=>A->bool) i)` MP_TAC THENL
         [ASM_MESON_TAC[]; REWRITE_TAC[OPEN_IN_MTOPOLOGY]] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC) THEN
        UNDISCH_TAC `(z::K=>A) \<in> PiE k u` THEN
        ASM_SIMP_TAC[PiE; IN_ELIM_THM];
        REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
      X_GEN_TAC `r::K=>real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `\<exists>a::K. a \<in> k` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC
        `inf (image (\<lambda>i. min (r i) (inverse((kn i) + 1)))
                 (a insert {i. i \<in> k \<and>
                                \<not> (u i = topspace ((tops::K=>A topology) i))})) /
         2` THEN
      ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_INSERT; NOT_INSERT_EMPTY;
        REAL_HALF; FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[REAL_LT_MIN; REAL_LT_INV_EQ] THEN
      REWRITE_TAC[REAL_ARITH `0 < n + 1`] THEN
      ASM_SIMP_TAC[FORALL_IN_INSERT; IN_ELIM_THM] THEN
      REWRITE_TAC[\<subseteq>; IN_MBALL] THEN X_GEN_TAC `x::K=>A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC \<circ> CONJUNCT2) THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP REAL_LT_IMP_LE) THEN
      FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`z::K=>A`; `x::K=>A`]) THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN `(x::K=>A) \<in> topspace(product_topology k tops)` MP_TAC THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY]] THEN
      REWRITE_TAC[PiE; o_THM; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i::K` THEN
      ASM_CASES_TAC `(i::K) \<in> k` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC[REAL_ARITH `x \<le> y / 2 \<longleftrightarrow> 2 * x \<le> y`] THEN
      ASM_SIMP_TAC[REAL_LE_INF_FINITE; FINITE_INSERT; NOT_INSERT_EMPTY;
        REAL_HALF; FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_INSERT] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `i::K` \<circ> CONJUNCT2) THEN
      ASM_CASES_TAC `(u::K=>A->bool) i = topspace(tops i)` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[CAPPED_METRIC; REAL_ARITH `x \<le> 0 \<longleftrightarrow> \<not> (0 < x)`] THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `0 < n + 1`] THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP (REAL_ARITH
       `2 * min a b \<le> min c a \<Longrightarrow> 0 < a \<and> 0 < c \<Longrightarrow> b < c`)) THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `0 < n + 1`] THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> SPEC `i::K`)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC \<circ> GEN_REWRITE_RULE id [\<subseteq>]) THEN
      ASM_REWRITE_TAC[IN_MBALL] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[TOPSPACE_MTOPOLOGY]] THEN
      UNDISCH_TAC `(z::K=>A) \<in> mspace M` THEN
      ASM_REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; PiE] THEN
      REWRITE_TAC[IN_ELIM_THM; o_DEF] THEN
      ASM_MESON_TAC[TOPSPACE_MTOPOLOGY]];
    DISCH_TAC THEN REWRITE_TAC[mcomplete] THEN DISCH_THEN(LABEL_TAC "*") THEN
    X_GEN_TAC `x::num=>K->A` THEN ASM_REWRITE_TAC[MCauchy] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[LIMIT_COMPONENTWISE] THEN
    SUBGOAL_THEN
     `\<forall>i. \<exists>y. i \<in> k \<Longrightarrow> limitin (tops i) (\<lambda>n. (x::num=>K->A) n i) y sequentially`
    MP_TAC THENL
     [X_GEN_TAC `i::K` THEN ASM_CASES_TAC `(i::K) \<in> k` THEN
      ASM_REWRITE_TAC[] THEN REMOVE_THEN "*" (MP_TAC \<circ> SPEC `i::K`) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[MCauchy; GSYM TOPSPACE_MTOPOLOGY] THEN CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_PRODUCT_TOPOLOGY;
           PiE; IN_ELIM_THM; o_DEF]) THEN ASM_MESON_TAC[];
        X_GEN_TAC `e::real` THEN DISCH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC \<circ> SPEC `min e (inverse(&(kn(i::K)) + 1)) / 2`) THEN
      REWRITE_TAC[REAL_HALF; REAL_LT_MIN; REAL_LT_INV_EQ] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
      X_GEN_TAC `N::num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`m::num`; `n::num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`m::num`; `n::num`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC \<circ> MATCH_MP REAL_LT_IMP_LE) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC \<circ> SPEC `i::K`) THEN
      ASM_REWRITE_TAC[CAPPED_METRIC; REAL_ARITH `x \<le> 0 \<longleftrightarrow> \<not> (0 < x)`] THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `0 < n + 1`] THEN
      MATCH_MP_TAC(REAL_ARITH
        `0 < d \<and> 0 < e \<Longrightarrow> min d x \<le> min e d / 2 \<Longrightarrow> x < e`) THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `0 < n + 1`];
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `y::K=>A` THEN DISCH_TAC THEN
    EXISTS_TAC `RESTRICTION k (y::K=>A)` THEN
    ASM_REWRITE_TAC[REWRITE_RULE[\<in>] RESTRICTION_IN_EXTENSIONAL] THEN
    SIMP_TAC[RESTRICTION; EVENTUALLY_TRUE] THEN ASM_REWRITE_TAC[]]);;


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
            \<Longrightarrow> \<exists>y z d. y \<in> s \<and> z \<in> s \<and> 0 < d \<and> d < e / 2 \<and>
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
        (REAL_ARITH `x \<le> y / 3 \<Longrightarrow> \<forall>e. y < e / 2 \<Longrightarrow> x < e / 6`)) THEN
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
         `d < e / 2 \<Longrightarrow> e \<le> i \<Longrightarrow> d \<le> inverse 2 * i`) THEN
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
     `\<forall>b. \<not> (\<Inter> {(d:(num=>bool)->num=>A->bool) b n | n \<in> UNIV} = {})`
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


subsection\<open>Euclidean space and n-spheres, as subtopologies of infinite product R^N\<close>


definition euclidean_space where
 `euclidean_space n = subtopology (product_topology UNIV (\<lambda>i. euclideanreal))
                         {x. \<forall>i. (i \<notin> 1..n) \<Longrightarrow> x i = 0}"

lemma topspace_euclidean_space:
   "topspace(euclidean_space n) = {x. \<forall>i. (i \<notin> 1..n) \<Longrightarrow> x i = 0}"
oops
  REWRITE_TAC[euclidean_space; TOPSPACE_SUBTOPOLOGY;
              TOPSPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
  REWRITE_TAC[INTER_UNIV]);;

lemma nonempty_euclidean_space:
   "\<not> (topspace(euclidean_space n) = {})"
oops
  GEN_TAC THEN REWRITE_TAC[TOPSPACE_EUCLIDEAN_SPACE] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  EXISTS_TAC `(\<lambda>i. 0):num=>real` THEN REWRITE_TAC[]);;

lemma subset_euclidean_space:
   "topspace(euclidean_space m) \<subseteq> topspace(euclidean_space n) \<longleftrightarrow>
         m \<le> n"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SPACE; \<subseteq>; IN_ELIM_THM; IN_NUMSEG] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[LE_TRANS]] THEN
  GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_LE] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `(\<lambda>i. if i = m then 1 else 0):num=>real`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC \<circ> SPEC `m::num`) THEN
    REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_ARITH_TAC]);;

lemma closedin_euclidean_space:
   "closedin (product_topology UNIV (\<lambda>i. euclideanreal))
                 (topspace(euclidean_space n))"
oops
  GEN_TAC THEN
  SUBGOAL_THEN
   `topspace(euclidean_space n) =
    \<Inter> {{x. x \<in> topspace(product_topology UNIV (\<lambda>i. euclideanreal)) \<and>
                 x i \<in> {0}}
            | (i \<notin> 1..n)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SPACE; INTERS_GSPEC; IN_ELIM_THM] THEN
    REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; o_DEF] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
    SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_INTERS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REWRITE_TAC[SET_RULE `\<not> ({f x | P x} = {}) \<longleftrightarrow> \<exists>x. P x`; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THENL [EXISTS_TAC `0` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `euclideanreal` THEN
    SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV] THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_SING]]);;

lemma completely_metrizable_euclidean_space:
   "completely_metrizable_space(euclidean_space n)"
oops
  GEN_TAC THEN REWRITE_TAC[euclidean_space] THEN
  MATCH_MP_TAC COMPLETELY_METRIZABLE_SPACE_CLOSED_IN THEN
  REWRITE_TAC[GSYM TOPSPACE_EUCLIDEAN_SPACE; CLOSED_IN_EUCLIDEAN_SPACE] THEN
  REWRITE_TAC[COMPLETELY_METRIZABLE_SPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[COMPLETELY_METRIZABLE_SPACE_EUCLIDEANREAL] THEN
  REWRITE_TAC[COUNTABLE_SUBSET_NUM]);;

lemma metrizable_euclidean_space:
   "metrizable_space(euclidean_space n)"
oops
  SIMP_TAC[COMPLETELY_METRIZABLE_IMP_METRIZABLE_SPACE;
           COMPLETELY_METRIZABLE_EUCLIDEAN_SPACE]);;

lemma continuous_map_componentwise_euclidean_space:
   "\<And>X (f::A=>num->real) n.
        continuous_map X (euclidean_space n)
                       (\<lambda>x i. if 1 \<le> i \<and> i \<le> n then f x i else 0) \<longleftrightarrow>
   \<forall>i. 1 \<le> i \<and> i \<le> n \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. f x i)"
oops
  REWRITE_TAC[euclidean_space; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  SIMP_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i::num` THEN
  ASM_CASES_TAC `1 \<le> i \<and> i \<le> n` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST]);;

lemma continuous_map_euclidean_space_add:
   "\<And>f g::A=>num->real.
        continuous_map X (euclidean_space n) f \<and>
        continuous_map X (euclidean_space n) g
        \<Longrightarrow> continuous_map X (euclidean_space n) (\<lambda>x i. f x i + g x i)"
oops
  REWRITE_TAC[euclidean_space; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  SIMP_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_ELIM_THM; REAL_ADD_LID] THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
  SIMP_TAC[CONTINUOUS_MAP_REAL_ADD; EXTENSIONAL_UNIV]);;

lemma continuous_map_euclidean_space_sub:
   "\<And>f g::A=>num->real.
        continuous_map X (euclidean_space n) f \<and>
        continuous_map X (euclidean_space n) g
        \<Longrightarrow> continuous_map X (euclidean_space n) (\<lambda>x i. f x i - g x i)"
oops
  REWRITE_TAC[euclidean_space; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  SIMP_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_ELIM_THM; REAL_SUB_RZERO] THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
  SIMP_TAC[CONTINUOUS_MAP_REAL_SUB; EXTENSIONAL_UNIV]);;

lemma homeomorphic_euclidean_space_product_topology:
   "euclidean_space n homeomorphic_space
       product_topology {1..n} (\<lambda>i. euclideanreal)"
oops
  GEN_TAC THEN REWRITE_TAC[homeomorphic_space; homeomorphic_maps] THEN
  EXISTS_TAC `\<lambda>f::num=>real. RESTRICTION {1..n} f` THEN
  EXISTS_TAC `\<lambda>(f::num=>real) i. if i \<in> 1..n then f i else 0` THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SPACE; TOPSPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[PiE; o_THM; TOPSPACE_EUCLIDEANREAL] THEN
  REWRITE_TAC[IN_ELIM_THM; EXTENSION; euclidean_space] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE] THEN
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; RESTRICTION_IN_EXTENSIONAL] THEN
    SIMP_TAC[RESTRICTION; CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    SIMP_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE] THEN
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_UNIV] THEN
    CONJ_TAC THENL [MESON_TAC[\<in>; EXTENSIONAL_UNIV; IN_UNIV]; ALL_TAC] THEN
    X_GEN_TAC `i::num` THEN ASM_CASES_TAC `i \<in> 1..n` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION];
    REPEAT STRIP_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
    SIMP_TAC[RESTRICTION] THEN ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSIONAL; FUN_EQ_THM; IN_UNIV; IN_ELIM_THM] THEN
    REWRITE_TAC[RESTRICTION] THEN MESON_TAC[]]);;

lemma contractible_euclidean_space:
   "contractible_space(euclidean_space n)"
oops
  GEN_TAC THEN
  MP_TAC(SPEC `n::num` HOMEOMORPHIC_EUCLIDEAN_SPACE_PRODUCT_TOPOLOGY) THEN
  DISCH_THEN(SUBST1_TAC \<circ> MATCH_MP HOMEOMORPHIC_SPACE_CONTRACTIBILITY) THEN
  REWRITE_TAC[CONTRACTIBLE_SPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[CONTRACTIBLE_SPACE_EUCLIDEANREAL]);;

lemma path_connected_euclidean_space:
   "path_connected_space(euclidean_space n)"
oops
  SIMP_TAC[CONTRACTIBLE_IMP_PATH_CONNECTED_SPACE;
           CONTRACTIBLE_EUCLIDEAN_SPACE]);;

lemma connected_euclidean_space:
   "connected_space(euclidean_space n)"
oops
  SIMP_TAC[PATH_CONNECTED_EUCLIDEAN_SPACE;
           PATH_CONNECTED_IMP_CONNECTED_SPACE]);;

lemma locally_compact_euclidean_space:
   "locally_compact_space(euclidean_space n)"
oops
  X_GEN_TAC `n::num` THEN
  MP_TAC(SPEC `n::num` HOMEOMORPHIC_EUCLIDEAN_SPACE_PRODUCT_TOPOLOGY) THEN
  DISCH_THEN(SUBST1_TAC \<circ> MATCH_MP HOMEOMORPHIC_LOCALLY_COMPACT_SPACE) THEN
  REWRITE_TAC[LOCALLY_COMPACT_SPACE_PRODUCT_TOPOLOGY] THEN
  DISJ2_TAC THEN REWRITE_TAC[LOCALLY_COMPACT_SPACE_EUCLIDEANREAL] THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_RESTRICT]);;

lemma locally_path_connected_euclidean_space:
   "locally_path_connected_space(euclidean_space n)"
oops
  X_GEN_TAC `n::num` THEN
  MP_TAC(SPEC `n::num` HOMEOMORPHIC_EUCLIDEAN_SPACE_PRODUCT_TOPOLOGY) THEN
  DISCH_THEN(SUBST1_TAC \<circ>
    MATCH_MP HOMEOMORPHIC_LOCALLY_PATH_CONNECTED_SPACE) THEN
  REWRITE_TAC[LOCALLY_PATH_CONNECTED_SPACE_PRODUCT_TOPOLOGY] THEN
  DISJ2_TAC THEN REWRITE_TAC[LOCALLY_PATH_CONNECTED_SPACE_EUCLIDEANREAL] THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_RESTRICT]);;

lemma locally_connected_euclidean_space:
   "locally_connected_space(euclidean_space n)"
oops
  SIMP_TAC[LOCALLY_PATH_CONNECTED_EUCLIDEAN_SPACE;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE]);;

lemma Hausdorff_euclidean_space:
   "Hausdorff_space (euclidean_space n)"
oops
  GEN_TAC THEN REWRITE_TAC[euclidean_space] THEN
  MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
  REWRITE_TAC[HAUSDORFF_SPACE_PRODUCT_TOPOLOGY;
              HAUSDORFF_SPACE_EUCLIDEANREAL]);;

lemma compact_euclidean_space:
   "compact_space(euclidean_space n) \<longleftrightarrow> n = 0"
oops
  X_GEN_TAC `n::num` THEN
  MP_TAC(SPEC `n::num` HOMEOMORPHIC_EUCLIDEAN_SPACE_PRODUCT_TOPOLOGY) THEN
  DISCH_THEN(SUBST1_TAC \<circ> MATCH_MP HOMEOMORPHIC_COMPACT_SPACE) THEN
  REWRITE_TAC[COMPACT_SPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; CARTESIAN_PRODUCT_EQ_EMPTY] THEN
  REWRITE_TAC[NOT_COMPACT_SPACE_EUCLIDEANREAL] THEN
  REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; UNIV_NOT_EMPTY] THEN
  REWRITE_TAC[GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[NUMSEG_EMPTY] THEN ARITH_TAC);;

definition nsphere where
 `nsphere n = subtopology (euclidean_space (Suc n))
                          { x | sum(1..n+1) (\<lambda>i. x i ^ 2) = 1 }"

lemma nsphere:
   "nsphere n = subtopology (product_topology UNIV (\<lambda>i. euclideanreal))
                               {x. sum(1..n+1) (\<lambda>i. x i ^ 2) = 1 \<and>
                                    \<forall>i. (i \<notin> 1..n+1) \<Longrightarrow> x i = 0}"
oops
  REWRITE_TAC[nsphere; euclidean_space; SUBTOPOLOGY_SUBTOPOLOGY] THEN
  GEN_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

lemma nonempty_nsphere:
   "\<not> (topspace(nsphere n) = {})"
oops
  GEN_TAC THEN REWRITE_TAC[nsphere; GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `(\<lambda>n. if n = 1 then 1 else 0):num=>real` THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SPACE] THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SUM_DELTA] THEN
    REWRITE_TAC[IN_NUMSEG; ARITH_RULE `1 \<le> 1 \<and> 1 \<le> n + 1`]]);;

lemma subtopology_nsphere_equator:
   "subtopology (nsphere (Suc n)) {x. x(n+2) = 0} = nsphere n"
oops
  GEN_TAC THEN
  REWRITE_TAC[NSPHERE; SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC `x::num=>real` THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `(Suc n) + 1 = Suc(Suc n)`; SUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `1 \<le> Suc n`; NUMSEG_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `Suc(Suc n) = n + 2`; IN_INSERT; IN_NUMSEG] THEN
  ASM_CASES_TAC `(x::num=>real)(n + 2) = 0` THENL
   [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `\<not> (n + 2 \<le> n + 1)`]] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ADD_RID] THEN ASM_MESON_TAC[]);;

lemma continuous_map_nsphere_reflection:
   "continuous_map (nsphere n,nsphere n)
                        (\<lambda>x i. if i = k then-x i else x i)"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[NSPHERE; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `i::num` THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    ASM_CASES_TAC `i::num = k` THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_REAL_NEG; CONTINUOUS_MAP_PRODUCT_PROJECTION;
                 IN_UNIV];
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    REWRITE_TAC[REAL_NEG_EQ_0; REAL_ARITH `(-x::real) ^ 2 = x ^ 2`] THEN
    SIMP_TAC[COND_ID; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM]]);;

lemma contractible_space_upper_hemisphere:
   "k \<in> 1..n+1
         \<Longrightarrow> contractible_space(subtopology (nsphere n) {x. x k >= 0})"
oops
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `p::num=>real = \<lambda>i. if i = k then 1 else 0` THEN
  REWRITE_TAC[contractible_space] THEN EXISTS_TAC `p::num=>real` THEN
  SUBGOAL_THEN `p \<in> topspace(nsphere n)` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[NSPHERE; TOPSPACE_SUBTOPOLOGY] THEN
    REWRITE_TAC[IN_INTER; TOPSPACE_PRODUCT_TOPOLOGY; IN_ELIM_THM; o_DEF] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV; IN_UNIV] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[COND_RAND; COND_RATOR] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[SUM_DELTA];
    ALL_TAC] THEN
  SIMP_TAC[HOMOTOPIC_WITH] THEN
  EXISTS_TAC `(\<lambda>x i. x i / sqrt(sum(1..n+1) (\<lambda>j. x j ^ 2))) \<circ>
              (\<lambda>(t,q) i. (1 - t) * q i + t * p i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE;
    UNDISCH_TAC `p \<in> topspace(nsphere n)` THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; NSPHERE; o_THM] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LID; REAL_MUL_LZERO; REAL_SUB_RZERO;
                REAL_ADD_LID; REAL_ADD_RID; IN_INTER; IN_ELIM_THM] THEN
    SIMP_TAC[SQRT_1; REAL_DIV_1; ETA_AX]] THEN
  EXISTS_TAC `subtopology (euclidean_space (Suc n))
               {x. x k >= 0 \<and> \<not> (\<forall>i. i \<in> 1..n+1 \<Longrightarrow> x i = 0)}` THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; euclidean_space] THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i::num` THEN REWRITE_TAC[LAMBDA_PAIR] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN
    REWRITE_TAC[CONTINUOUS_MAP_OF_FST; CONTINUOUS_MAP_OF_SND] THEN
    SIMP_TAC[GSYM SUBTOPOLOGY_CROSS; CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
             CONTINUOUS_MAP_FST] THEN
    REPEAT CONJ_TAC THEN DISJ2_TAC THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    SIMP_TAC[CONTINUOUS_MAP_REAL_SUB; CONTINUOUS_MAP_REAL_CONST;
             CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[NSPHERE] THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV];
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; NSPHERE;
                FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                IN_INTER; IN_ELIM_THM] THEN
    EXPAND_TAC "p" THEN SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_ENTIRE] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; TOPSPACE_SUBTOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; IN_INTER; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`t::real`; `x::num=>real`] THEN
    REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[real_ge] THEN CONJ_TAC THENL
     [EXPAND_TAC "p" THEN REWRITE_TAC[REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_CASES_TAC `t = 0` THENL
       [ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID; REAL_MUL_LZERO] THEN
        REWRITE_TAC[REAL_ADD_RID] THEN DISCH_TAC THEN
        UNDISCH_TAC `x \<in> topspace(nsphere n)` THEN
        ASM_SIMP_TAC[NSPHERE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SUM_0] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        DISCH_THEN(MP_TAC \<circ> SPEC `k::num`) THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "p" THEN REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
          `0 \<le> x \<and> 0 \<le> t \<and> (t \<noteq> 0) \<Longrightarrow> \<not> (x + t * 1 = 0)`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC]];
      ALL_TAC;
      REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; real_ge] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LE THEN
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      REWRITE_TAC[REAL_LE_POW_2]] THEN
  REWRITE_TAC[NSPHERE; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN
    X_GEN_TAC `i::num` THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
             CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_SQRT THEN
      MATCH_MP_TAC CONTINUOUS_MAP_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THEN
      REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY) THEN
      SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV];
      REWRITE_TAC[SQRT_EQ_0; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM]];
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY] THEN
    SIMP_TAC[IN_INTER; IN_ELIM_THM; real_ge; IN_NUMSEG] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_POW_MUL; SUM_RMUL] THEN
    REWRITE_TAC[REAL_POW_INV; GSYM real_div] THEN
    SIMP_TAC[SQRT_POW_2; SUM_POS_LE_NUMSEG; REAL_LE_POW_2] THEN
    REWRITE_TAC[REAL_DIV_EQ_1]] THEN
  REWRITE_TAC[IMP_CONJ; CONTRAPOS_THM] THEN
  GEN_TAC THEN REPLICATE_TAC 3 DISCH_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
  DISCH_THEN(MP_TAC \<circ> MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
    SUM_POS_EQ_0_NUMSEG)) THEN
  SIMP_TAC[REAL_POW_EQ_0; REAL_LE_POW_2; ARITH]);;

lemma contractible_space_lower_hemisphere:
   "k \<in> 1..n+1
         \<Longrightarrow> contractible_space(subtopology (nsphere n) {x. x k \<le> 0})"
oops
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC \<circ> MATCH_MP CONTRACTIBLE_SPACE_UPPER_HEMISPHERE) THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOMEOMORPHIC_SPACE_CONTRACTIBILITY THEN
  REWRITE_TAC[homeomorphic_space] THEN
  REPEAT(EXISTS_TAC `\<lambda>(x::num=>real) i. if i = k then --(x i) else x i`) THEN
  REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
           CONTINUOUS_MAP_NSPHERE_REFLECTION] THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_ELIM_THM; REAL_NEG_NEG;
              TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
  TRY COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

lemma nullhomotopic_nonsurjective_sphere_map:
   "continuous_map(nsphere p,nsphere p) f \<and>
         \<not> (image f (topspace(nsphere p)) = topspace(nsphere p))
         \<Longrightarrow> \<exists>a. homotopic_with (\<lambda>x. True) (nsphere p,nsphere p) f (\<lambda>x. a)"
oops
  SIMP_TAC[IMP_CONJ; CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; SET_RULE
            `s \<subseteq> t \<Longrightarrow> ((s \<noteq> t) \<longleftrightarrow> \<exists>a. a \<in> t \<and> (a \<notin> s))`] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `a::num=>real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(\<lambda>i. --(a i)):num=>real` THEN SIMP_TAC[HOMOTOPIC_WITH] THEN
  EXISTS_TAC
   `(\<lambda>x i. x i / sqrt(sum(1..p+1) (\<lambda>j. x j ^ 2))) \<circ>
    (\<lambda>(t,x) i. (1 - t) * f(x::num=>real) i - t * a i)` THEN
  REWRITE_TAC[o_THM; REAL_ARITH
   `(1 - 1) * x - 1 * a =-a \<and> (1 - 0) * x - 0 * a = x`] THEN
  MP_TAC(ASSUME `a \<in> topspace(nsphere p)`) THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[NSPHERE; TOPSPACE_SUBTOPOLOGY; \<subseteq>] THEN
  REWRITE_TAC[GSYM NSPHERE; IN_ELIM_THM; IN_INTER; FORALL_IN_IMAGE] THEN
  SIMP_TAC[REAL_ARITH `(-x::real) ^ 2 = x ^ 2`] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC \<circ> CONJUNCT2) THEN
  REWRITE_TAC[SQRT_1; REAL_DIV_1; ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology (euclidean_space(Suc p)) (UNIV DELETE (\<lambda>i. 0))` THEN
  REWRITE_TAC[euclidean_space; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i::num` THEN REWRITE_TAC[LAMBDA_PAIR] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN
    REWRITE_TAC[CONTINUOUS_MAP_OF_FST; CONTINUOUS_MAP_OF_SND] THEN
    SIMP_TAC[GSYM SUBTOPOLOGY_CROSS; nsphere; CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
             CONTINUOUS_MAP_FST] THEN
    REPEAT CONJ_TAC THEN DISJ2_TAC THEN
    SIMP_TAC[CONTINUOUS_MAP_REAL_SUB; CONTINUOUS_MAP_REAL_CONST;
             CONTINUOUS_MAP_ID; CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
    REWRITE_TAC[GSYM nsphere] THEN
    SUBGOAL_THEN `(\<lambda>x::num=>real. f x i) = (\<lambda>y::num=>real. y i) \<circ> f`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `nsphere p` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[NSPHERE; CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
             CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV];
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    GEN_REWRITE_TAC (LAND_CONV \<circ> RAND_CONV \<circ> RAND_CONV) [NSPHERE] THEN
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY;
                FORALL_PAIR_THM; IN_CROSS; TOPSPACE_PROD_TOPOLOGY] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
    MAP_EVERY X_GEN_TAC [`t::real`; `b::num=>real`] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    REWRITE_TAC[IN_UNIV; IN_REAL_INTERVAL; IN_DELETE] THEN
    STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; REAL_SUB_0] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM FUN_EQ_THM] THEN
    MATCH_MP_TAC(MESON[]
     `(a = b \<Longrightarrow> t = 1/2) \<and> (t = 1/2 \<Longrightarrow> (a \<noteq> b))
      \<Longrightarrow> (a \<noteq> b)`) THEN
    CONJ_TAC THENL
     [DISCH_THEN(MP_TAC \<circ> AP_TERM `\<lambda>x. sum(1..p+1) (\<lambda>i. x i ^ 2)`) THEN
      FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      GEN_REWRITE_TAC (LAND_CONV \<circ> RAND_CONV \<circ> RAND_CONV) [NSPHERE] THEN
      REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY;
                  FORALL_PAIR_THM; IN_CROSS; TOPSPACE_PROD_TOPOLOGY] THEN
      ASM_SIMP_TAC[IN_ELIM_THM; IN_INTER; REAL_POW_MUL; SUM_LMUL] THEN
      DISCH_TAC THEN CONV_TAC REAL_RING;
      DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[FUN_EQ_THM; REAL_ARITH
       `1/2 * x = 1/2 * y \<longleftrightarrow> x = y`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM FUN_EQ_THM] THEN
      REWRITE_TAC[ETA_AX] THEN ASM SET_TAC[]];
    REWRITE_TAC[NSPHERE; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE; IN_UNIV] THEN
      REWRITE_TAC[EXTENSIONAL_UNIV; \<in>; \<subseteq>] THEN
      X_GEN_TAC `k::num` THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [CONJ_TAC THEN REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY) THEN
        SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_SQRT THEN
        MATCH_MP_TAC CONTINUOUS_MAP_SUM THEN
        SIMP_TAC[CONTINUOUS_MAP_REAL_POW; CONTINUOUS_MAP_PRODUCT_PROJECTION;
                 IN_UNIV; FINITE_NUMSEG];
        ALL_TAC];
      ALL_TAC] THEN
    SIMP_TAC[\<subseteq>; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER;
             IN_ELIM_THM; IN_DELETE; IN_UNIV; real_div; REAL_POW_MUL;
             REAL_MUL_LZERO; SUM_RMUL; REAL_POW_INV; SQRT_POW_2;
             SUM_POS_LE_NUMSEG; REAL_LE_POW_2; SQRT_EQ_0] THEN
    X_GEN_TAC `x::num=>real` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM real_div ] THEN TRY(MATCH_MP_TAC REAL_DIV_REFL) THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        SUM_POS_EQ_0_NUMSEG)) THEN
    REWRITE_TAC[REAL_LE_POW_2; GSYM IN_NUMSEG; REAL_POW_EQ_0] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE RAND_CONV [FUN_EQ_THM]) THEN
    ASM_MESON_TAC[\<in>]]);;


subsection\<open>Contractions\<close>


lemma contraction_imp_unique_fixpoint:
   "\<And>m (f::A=>A) k x y.
     k < 1 \<and>
     (\<forall>x. x \<in> M \<Longrightarrow> f x \<in> M) \<and>
     (\<forall>x y. x \<in> M \<and> y \<in> M
            \<Longrightarrow> d (f x) f y \<le> k * d x y) \<and>
     x \<in> M \<and> y \<in> M \<and> f x = x \<and> f y = y
     \<Longrightarrow> x = y"
oops
  INTRO_TAC "!m f k x y; k f le x y xeq yeq" THEN
  ASM_CASES_TAC `x::A = y` THENL [POP_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REMOVE_THEN "le" (MP_TAC \<circ> SPECL[`x::A`;`y::A`]) THEN ASM_REWRITE_TAC[] THEN
  CUT_TAC `0 < (1 - k) * d x::A y::A` THENL
  [REAL_ARITH_TAC;
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[MDIST_POS_LT] THEN
   ASM_REAL_ARITH_TAC]);;


(* Banach Fixed-Point Theorem (aka, Contraction Mapping Principle).          *)


lemma banach_fixpoint_thm:
   "\<And>m f::A=>A k.
     \<not> (M = {}) \<and>
     mcomplete \<and>
     (\<forall>x. x \<in> M \<Longrightarrow> f x \<in> M) \<and>
     k < 1 \<and>
     (\<forall>x y. x \<in> M \<and> y \<in> M
            \<Longrightarrow> d (f x) f y \<le> k * d x y)
     \<Longrightarrow> (?\<forall>x. x \<in> M \<and> f x = x)"
oops
  INTRO_TAC "!m f k; ne compl 4 k1 contr" THEN REMOVE_THEN "ne" MP_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN INTRO_TAC "@a. aINm" THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
  [ALL_TAC;
   REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTRACTION_IMP_UNIQUE_FIXPOINT THEN
   ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `\<forall>x::A. x \<in> M \<Longrightarrow> f x::A = f a` THENL
  [ASM_MESON_TAC[]; POP_ASSUM (LABEL_TAC "nonsing")] THEN
  CLAIM_TAC "kpos" `0 < k` THENL
  [MATCH_MP_TAC (ISPECL [`m::A metric`; `m::A metric`; `f::A=>A`]
     LIPSCHITZ_COEFFICIENT_POS) THEN
   ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "fINm" `\<forall>n::num. (ITER n f (a::A)) \<in> M` THENL
  [LABEL_INDUCT_TAC THEN ASM_SIMP_TAC[ITER]; ALL_TAC] THEN
  ASM_CASES_TAC `f a = a::A` THENL
  [ASM_MESON_TAC[]; POP_ASSUM (LABEL_TAC "aneq")] THEN
  CUT_TAC `MCauchy (m::A metric) (\<lambda>n. ITER n f (a::A))` THENL
  [DISCH_THEN (fun cauchy -> HYP_TAC "compl : @l. lim"
    (C MATCH_MP cauchy \<circ> REWRITE_RULE[mcomplete])) THEN
   EXISTS_TAC `l::A` THEN CONJ_TAC THENL
   [ASM_MESON_TAC [LIMIT_IN_MSPACE]; ALL_TAC] THEN
   MATCH_MP_TAC
     (ISPECL [`sequentially`; `m::A metric`; `(\<lambda>n. ITER n f a::A)`]
             LIMIT_METRIC_UNIQUE) THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   MATCH_MP_TAC LIMIT_SEQUENTIALLY_OFFSET_REV THEN
   EXISTS_TAC `1` THEN REWRITE_TAC[GSYM ADD1] THEN
   SUBGOAL_THEN `(\<lambda>i. ITER (Suc i) f (a::A)) = f \<circ> (\<lambda>i. ITER i f a)`
     SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; ITER]; ALL_TAC] THEN
   MATCH_MP_TAC CONTINUOUS_MAP_LIMIT THEN
   EXISTS_TAC `mtopology (m::A metric)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_IMP_CONTINUOUS_MAP THEN
   ASM_REWRITE_TAC[Lipschitz_continuous_map; \<subseteq>; FORALL_IN_IMAGE] THEN
   EXISTS_TAC `k::real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "k1'" `0 < 1 - k` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MCauchy] THEN INTRO_TAC "!e; e" THEN
  CLAIM_TAC "@N. N" `\<exists>N. k ^ N < ((1 - k) * e) / d a::A f a` THENL
  [MATCH_MP_TAC REAL_ARCH_POW_INV THEN
   ASM_SIMP_TAC[REAL_LT_DIV; MDIST_POS_LT; REAL_LT_MUL];
   EXISTS_TAC `N::num`] THEN
  MATCH_MP_TAC WLOG_LT THEN ASM_SIMP_TAC[MDIST_REFL] THEN CONJ_TAC THENL
  [HYP MESON_TAC "fINm" [MDIST_SYM]; ALL_TAC] THEN
  INTRO_TAC "!n n'; lt; le le'" THEN
  TRANS_TAC REAL_LET_TRANS
    `sum (n..n'-1) (\<lambda>i. d m (ITER i f a::A, ITER (Suc i) f a))` THEN
  CONJ_TAC THENL
  [REMOVE_THEN "lt" MP_TAC THEN SPEC_TAC (`n':num`,`n':num`) THEN
   LABEL_INDUCT_TAC THENL [REWRITE_TAC[LT]; REWRITE_TAC[LT_SUC_LE]] THEN
   INTRO_TAC "nle" THEN HYP_TAC "nle : nlt | neq" (REWRITE_RULE[LE_LT]) THENL
   [ALL_TAC;
    POP_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[ITER;
      ARITH_RULE `Suc n'' - 1 = n''`; SUM_SING_NUMSEG; REAL_LE_REFL]] THEN
   USE_THEN "nlt" (HYP_TAC "ind_n'" \<circ> C MATCH_MP) THEN REWRITE_TAC[ITER] THEN
   TRANS_TAC REAL_LE_TRANS
     `d ITER n f a::A ITER n'' f a +
      d m (ITER n'' f a,f (ITER n'' f a))` THEN
   ASM_SIMP_TAC[MDIST_TRIANGLE] THEN
   SUBGOAL_THEN `Suc n'' - 1 = Suc (n'' - 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG]] THEN
   SUBGOAL_THEN `Suc (n'' - 1) = n''` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[LT_IMP_LE; REAL_LE_RADD]] THEN
   REMOVE_THEN "ind_n'" (ACCEPT_TAC \<circ> REWRITE_RULE[ITER]);
   ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
     `sum (n..n'-1) (\<lambda>i. d a::A f a * k ^ i)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC SUM_LE_NUMSEG THEN
   CUT_TAC `\<forall>i. d m (ITER i f a,ITER (Suc i) f a) \<le>
                d a::A f a * k ^ i` THENL
   [SIMP_TAC[ITER]; ALL_TAC] THEN
   LABEL_INDUCT_TAC THENL
   [REWRITE_TAC[ITER; real_pow; REAL_MUL_RID; REAL_LE_REFL];
    HYP_TAC "ind_i" (REWRITE_RULE[ITER]) THEN
    TRANS_TAC REAL_LE_TRANS `k * d m (ITER i f a::A, f (ITER i f a))` THEN
    ASM_SIMP_TAC[real_pow; REAL_LE_LMUL_EQ; ITER;
      REAL_ARITH `\<forall>x. x * k * k ^ i = k * x * k ^ i`]];
   ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; SUM_GP] THEN
  HYP SIMP_TAC "lt" [ARITH_RULE `n < n' \<Longrightarrow> \<not> (n' - 1 < n)`] THEN
  HYP SIMP_TAC "k1" [REAL_ARITH `k < 1 \<Longrightarrow> (k \<noteq> 1)`] THEN
  USE_THEN "lt" (SUBST1_TAC \<circ>
    MATCH_MP (ARITH_RULE `n < n' \<Longrightarrow> Suc (n' - 1) = n'`)) THEN
  SUBGOAL_THEN `k ^ n - k ^ n' = k ^ n * (1 - k ^ (n' - n))`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID; GSYM REAL_POW_ADD] THEN
   HYP SIMP_TAC "lt" [ARITH_RULE `n < n' \<Longrightarrow> n + n' - n = n':num`];
   (SUBST1_TAC \<circ> REAL_ARITH)
     `d a::A f a * (k ^ n * (1 - k ^ (n' - n))) / (1 - k) =
      ((k ^ n * (1 - k ^ (n' - n))) / (1 - k)) * d a f a`] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; MDIST_POS_LT; REAL_LT_LDIV_EQ] THEN
  TRANS_TAC REAL_LET_TRANS `k ^ n` THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
   REWRITE_TAC[GSYM REAL_POW_ADD;
     REAL_ARITH `k ^ n - k ^ n * (1 - k ^ (n' - n)) =
                 k ^ n * k ^ (n' - n)`] THEN
   HYP SIMP_TAC "lt" [ARITH_RULE `n < n' \<Longrightarrow> n + n' - n = n':num`] THEN
   HYP SIMP_TAC "kpos" [REAL_POW_LE; REAL_LT_IMP_LE];
   TRANS_TAC REAL_LET_TRANS `k ^ N` THEN
   ASM_SIMP_TAC[REAL_POW_MONO_INV; REAL_LT_IMP_LE;
     REAL_ARITH `e / d a::A f a * (1 - k) =
                 ((1 - k) * e) / d a f a`]]);;


subsection\<open>Metric space of bounded functions\<close>


definition funspace where
  `funspace s m =
   metric ({f::A=>B | (\<forall>x. x \<in> s \<Longrightarrow> f x \<in> M) \<and>
                     f \<in> EXTENSIONAL s \<and>
                     mbounded (f ` s)},
           (\<lambda>(f,g). if s = {} then 0 else
                    sup {d (f x) g x | x | x \<in> s}))"

let FUNSPACE = (REWRITE_RULE[GSYM FORALL_AND_THM] \<circ> prove)
   "mspace (funspace s m) =
       {f::A=>B | (\<forall>x. x \<in> s \<Longrightarrow> f x \<in> M) \<and>
                 f \<in> EXTENSIONAL s \<and>
                 mbounded (f ` s)} \<and>
     (\<forall>f g. d (funspace s m) (f,g) =
              if s = {} then 0 else
              sup {d (f x) g x | x | x \<in> s})"
oops
  REPEAT GEN_TAC THEN MAP_EVERY LABEL_ABBREV_TAC
    [`fspace = {f::A=>B | (\<forall>x. x \<in> s \<Longrightarrow> f x \<in> M) \<and>
                         f \<in> EXTENSIONAL s \<and>
                         mbounded (f ` s)}`;
     `fdist =
        \<lambda>(f,g). if s = {} then 0 else
                sup {d (f x)::B g x | x | x::A \<in> s}`] THEN
  CUT_TAC `mspace (funspace s m) = fspace:(A=>B)->bool \<and>
           d (funspace s m:(A=>B)metric) = fdist` THENL
  [EXPAND_TAC "fdist" THEN DISCH_THEN (fun th -> REWRITE_TAC[th]);
   ASM_REWRITE_TAC[funspace] THEN MATCH_MP_TAC METRIC] THEN
  ASM_CASES_TAC `s::A=>bool = {}` THENL
  [POP_ASSUM SUBST_ALL_TAC THEN MAP_EVERY EXPAND_TAC ["fspace"; "fdist"] THEN
   SIMP_TAC[is_metric_space; NOT_IN_EMPTY; IN_EXTENSIONAL; IMAGE_CLAUSES;
     MBOUNDED_EMPTY; IN_ELIM_THM; REAL_LE_REFL; REAL_ADD_LID; FUN_EQ_THM];
   POP_ASSUM (LABEL_TAC "nempty")] THEN
  REMOVE_THEN "nempty" (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN LABEL_TAC "nempty" th) THEN
  CLAIM_TAC "wd ext bound"
    `(\<forall>f x::A. f \<in> fspace \<and> x \<in> s \<Longrightarrow> f x::B \<in> M) \<and>
     (\<forall>f. f \<in> fspace \<Longrightarrow> f \<in> EXTENSIONAL s) \<and>
     (\<forall>f. f \<in> fspace
          \<Longrightarrow> (\<exists>c b. c \<in> M \<and>
                     (\<forall>x. x \<in> s \<Longrightarrow> d c f x \<le> b)))` THENL
  [EXPAND_TAC "fspace" THEN
   ASM_SIMP_TAC[IN_ELIM_THM; MBOUNDED; IMAGE_EQ_EMPTY] THEN SET_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "bound2"
    `\<forall>f g::A=>B. f \<in> fspace \<and> g \<in> fspace
                \<Longrightarrow> (\<exists>b. \<forall>x. x \<in> s \<Longrightarrow> d (f x) g x \<le> b)` THENL
  [REMOVE_THEN "fspace" (SUBST_ALL_TAC \<circ> GSYM) THEN
   REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   CUT_TAC `mbounded (image f s \<union> g ` s)` THENL
   [REWRITE_TAC[MBOUNDED_ALT; \<subseteq>; IN_UNION] THEN
    STRIP_TAC THEN EXISTS_TAC `b::real` THEN ASM SET_TAC [];
    ASM_REWRITE_TAC[MBOUNDED_UNION]];
   ALL_TAC] THEN
  HYP_TAC "nempty -> @a. a" (REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[is_metric_space] THEN CONJ_TAC THENL
  [INTRO_TAC "![f] [g]; f  g" THEN EXPAND_TAC "fdist" THEN
   REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_SUP THEN
   CLAIM_TAC "@b. b" `\<exists>b. \<forall>x::A. x \<in> s \<Longrightarrow> d (f x)::B g x \<le> b` THENL
   [HYP SIMP_TAC "bound2 f g" [];
    ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`b::real`; `d m (f(a::A):B,g a)`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN HYP SIMP_TAC "wd f g a" [MDIST_POS_LE] THEN
    HYP MESON_TAC "a b" [];
    ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![f] [g]; f  g" THEN EXPAND_TAC "fdist" THEN
   REWRITE_TAC[] THEN EQ_TAC THENL
   [INTRO_TAC "sup0" THEN MATCH_MP_TAC (SPEC `s::A=>bool` EXTENSIONAL_EQ) THEN
    HYP SIMP_TAC "f g ext" [] THEN INTRO_TAC "!x; x" THEN
    REFUTE_THEN (LABEL_TAC "neq") THEN
    CUT_TAC
      `0 < d m (f (x::A):B, g x) \<and>
       d (f x) g x \<le> sup {d (f x) g x | x \<in> s}` THENL
    [HYP REWRITE_TAC "sup0" [] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    HYP SIMP_TAC "wd f g x neq" [MDIST_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_SUP THEN
    CLAIM_TAC "@B. B" `\<exists>b. \<forall>x::A. x \<in> s \<Longrightarrow> d (f x)::B g x \<le> b` THENL
    [HYP SIMP_TAC "bound2 f g" []; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`B::real`; `d m (f (x::A):B,g x)`] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; REAL_LE_REFL] THEN
    HYP MESON_TAC "B x" [];
    DISCH_THEN (SUBST1_TAC \<circ> GSYM) THEN
    SUBGOAL_THEN `{d (f x)::B f x | x::A \<in> s} = {0}`
      (fun th -> REWRITE_TAC[th; SUP_SING]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIV; IN_INSERT] THEN
    HYP MESON_TAC "wd f a" [MDIST_REFL]];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![f] [g]; f g" THEN EXPAND_TAC "fdist" THEN REWRITE_TAC[] THEN
   AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   HYP MESON_TAC "wd f g" [MDIST_SYM];
   ALL_TAC] THEN
  INTRO_TAC "![f] [g] [h]; f g h" THEN EXPAND_TAC "fdist" THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIV] THEN
   HYP MESON_TAC "a" [];
   ALL_TAC] THEN
  FIX_TAC "[d]" THEN REWRITE_TAC [IN_ELIM_THM; IN_UNIV] THEN
  INTRO_TAC "@x. x d" THEN POP_ASSUM SUBST1_TAC THEN
  CUT_TAC
    `d m (f (x::A):B,h x) \<le> d (f x) g x + d (g x) h x \<and>
     d (f x) g x \<le> fdist (f,g) \<and>
     d (g x) h x \<le> fdist (g,h)` THEN
  EXPAND_TAC "fdist" THEN REWRITE_TAC[] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  HYP SIMP_TAC "wd f g h x" [MDIST_TRIANGLE] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_SUP THENL
  [CLAIM_TAC "@B. B" `\<exists>b. \<forall>x::A. x \<in> s \<Longrightarrow> d (f x)::B g x \<le> b` THENL
   [HYP SIMP_TAC "bound2 f g" [];
    MAP_EVERY EXISTS_TAC [`B::real`; `d m (f(x::A):B,g x)`]] THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV; REAL_LE_REFL] THEN HYP MESON_TAC "B x" [];
   CLAIM_TAC "@B. B" `\<exists>b. \<forall>x::A. x \<in> s \<Longrightarrow> d (g x)::B h x \<le> b` THENL
   [HYP SIMP_TAC "bound2 g h" []; ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`B::real`; `d m (g(x::A):B,h x)`] THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV; REAL_LE_REFL] THEN
   HYP MESON_TAC "B x" []]);;

lemma funspace_imp_welldefined:
   "\<And>s m f::A=>B x. f \<in> mspace (funspace s m) \<and> x \<in> s \<Longrightarrow> f x \<in> M"
oops
  SIMP_TAC[FUNSPACE; IN_ELIM_THM]);;

lemma funspace_imp_extensional:
   "\<And>s m f::A=>B. f \<in> mspace (funspace s m) \<Longrightarrow> f \<in> EXTENSIONAL s"
oops
  SIMP_TAC[FUNSPACE; IN_ELIM_THM]);;

lemma funspace_imp_bounded_image:
   "\<And>s m f::A=>B. f \<in> mspace (funspace s m) \<Longrightarrow> mbounded (f ` s)"
oops
  SIMP_TAC[FUNSPACE; IN_ELIM_THM]);;

lemma funspace_imp_bounded:
   "\<And>s m f::A=>B. f \<in> mspace (funspace s m)
                \<Longrightarrow> s = {} \<or> (\<exists>c b. \<forall>x. x \<in> s \<Longrightarrow> d c f x \<le> b)"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FUNSPACE; MBOUNDED; IMAGE_EQ_EMPTY; IN_ELIM_THM] THEN
  ASM_CASES_TAC `s::A=>bool = {}` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

lemma funspace_imp_bounded2:
   "\<And>s m f g::A=>B. f \<in> mspace (funspace s m) \<and> g \<in> mspace (funspace s m)
                  \<Longrightarrow> (\<exists>b. \<forall>x. x \<in> s \<Longrightarrow> d (f x) g x \<le> b)"
oops
  REWRITE_TAC[FUNSPACE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  CUT_TAC `mbounded (image f s \<union> g ` s)` THENL
  [REWRITE_TAC[MBOUNDED_ALT; \<subseteq>; IN_UNION] THEN
   STRIP_TAC THEN EXISTS_TAC `b::real` THEN ASM SET_TAC [];
   ASM_REWRITE_TAC[MBOUNDED_UNION]]);;

lemma funspace_mdist_le:
   "\<And>s m f g::A=>B a.
     (s \<noteq> {}) \<and>
     f \<in> mspace (funspace s m) \<and>
     g \<in> mspace (funspace s m)
     \<Longrightarrow> (d (funspace s m) (f,g) \<le> a \<longleftrightarrow>
          \<forall>x. x \<in> s \<Longrightarrow> d (f x) g x \<le> a)"
oops
  INTRO_TAC "! *; ne f g" THEN
  HYP (DESTRUCT_TAC "@b. b" \<circ>
    MATCH_MP FUNSPACE_IMP_BOUNDED2 \<circ> CONJ_LIST) "f g" [] THEN
  ASM_REWRITE_TAC[FUNSPACE] THEN
  MP_TAC (ISPECL [`{d (f x)::B g x | x::A \<in> s}`; `a::real`]
    REAL_SUP_LE_EQ) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM]] THEN
  MESON_TAC[]);;

lemma mcomplete_funspace:
   "\<And>s::A=>bool m::B metric. mcomplete \<Longrightarrow> mcomplete (funspace s m)"
oops
  REWRITE_TAC[mcomplete] THEN INTRO_TAC "!s m; cpl; ![f]; cy" THEN
  ASM_CASES_TAC `s::A=>bool = {}` THENL
  [POP_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `\<lambda>x::A. undefined::B` THEN
   REMOVE_THEN "cy" MP_TAC THEN
   SIMP_TAC[MCauchy; LIMIT_METRIC_SEQUENTIALLY; FUNSPACE; NOT_IN_EMPTY;
     IN_ELIM_THM; IN_EXTENSIONAL; IMAGE_CLAUSES; MBOUNDED_EMPTY];
   POP_ASSUM (LABEL_TAC "nempty")] THEN
  LABEL_ABBREV_TAC
    `g (x::A) = if x \<in> s
               then @y. limitin mtopology (\<lambda>n::num. f n x) y sequentially
               else undefined::B` THEN
  EXISTS_TAC `g::A=>B` THEN USE_THEN "cy" MP_TAC THEN
  HYP REWRITE_TAC "nempty"
    [MCauchy; FUNSPACE; IN_ELIM_THM; FORALL_AND_THM] THEN
  INTRO_TAC "(fwd fext fbd) cy'" THEN
  ASM_REWRITE_TAC[LIMIT_METRIC_SEQUENTIALLY; FUNSPACE; IN_ELIM_THM] THEN
  CLAIM_TAC "gext" `g::A=>B \<in> EXTENSIONAL s` THENL
  [REMOVE_THEN "g" (fun th -> SIMP_TAC[IN_EXTENSIONAL; GSYM th]);
   HYP REWRITE_TAC "gext" []] THEN
  CLAIM_TAC "bd2"
     `!n n'. \<exists>b. \<forall>x::A. x \<in> s \<Longrightarrow> d m (f (n::num) x::B, f n' x) \<le> b` THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC FUNSPACE_IMP_BOUNDED2 THEN
   ASM_REWRITE_TAC[FUNSPACE; IN_ELIM_THM; ETA_AX];
   ALL_TAC] THEN
  CLAIM_TAC "sup"
    `!n n':num x0::A. x0 \<in> s
                     \<Longrightarrow> d f n x0::B f n' x0 \<le>
                         sup {d f n x f n' x | x \<in> s}` THENL
  [INTRO_TAC "!n n' x0; x0" THEN MATCH_MP_TAC REAL_LE_SUP THEN
   REMOVE_THEN "bd2" (DESTRUCT_TAC "@b. b" \<circ> SPECL[`n::num`;`n':num`]) THEN
   MAP_EVERY EXISTS_TAC
     [`b::real`; `d m (f (n::num) (x0::A):B, f n' x0)`] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [HYP MESON_TAC "x0" []; REWRITE_TAC[REAL_LE_REFL]] THEN
   INTRO_TAC "![d]; @y. y d" THEN REMOVE_THEN "d" SUBST1_TAC THEN
   HYP SIMP_TAC "b y" [];
   ALL_TAC] THEN
  CLAIM_TAC "pcy" `\<forall>x::A. x \<in> s \<Longrightarrow> MCauchy (\<lambda>n. f n x::B)` THENL
  [INTRO_TAC "!x; x" THEN REWRITE_TAC[MCauchy] THEN
   HYP SIMP_TAC "fwd x" [] THEN INTRO_TAC "!e; e" THEN
   USE_THEN "e" (HYP_TAC "cy': @N.N" \<circ> C MATCH_MP) THEN EXISTS_TAC `N::num` THEN
   REPEAT GEN_TAC THEN DISCH_THEN (HYP_TAC "N" \<circ> C MATCH_MP) THEN
   TRANS_TAC REAL_LET_TRANS
     `sup {d m (f (n::num) x::B,f n' x) | x::A \<in> s}` THEN
   HYP REWRITE_TAC "N" [] THEN HYP SIMP_TAC "sup x" [];
   ALL_TAC] THEN
  CLAIM_TAC "glim"
    `\<forall>x::A. x \<in> s
           \<Longrightarrow> limitin mtopology (\<lambda>n. f n x::B) (g x) sequentially` THENL
  [INTRO_TAC "!x; x" THEN
   REMOVE_THEN "g" (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
   SELECT_ELIM_TAC THEN HYP SIMP_TAC "cpl pcy x" [];
   ALL_TAC] THEN
  CLAIM_TAC "gwd" `\<forall>x::A. x \<in> s \<Longrightarrow> g x::B \<in> M` THENL
  [INTRO_TAC "!x; x" THEN
   MATCH_MP_TAC (ISPECL[`sequentially`] LIMIT_IN_MSPACE) THEN
   EXISTS_TAC `\<lambda>n::num. f n (x::A):B` THEN HYP SIMP_TAC "glim x" [];
   HYP REWRITE_TAC "gwd" []] THEN
  CLAIM_TAC "unif"
    `\<forall>e>0.  \<exists>N::num. \<forall>x::A n. x \<in> s \<and> N \<le> n
                    \<Longrightarrow> d f n x::B g x < e` THENL
  [INTRO_TAC "!e; e" THEN REMOVE_THEN "cy'" (MP_TAC \<circ> SPEC `e / 2`) THEN
   HYP REWRITE_TAC "e" [REAL_HALF] THEN INTRO_TAC "@N. N" THEN
   EXISTS_TAC `N::num` THEN INTRO_TAC "!x n; x n" THEN
   USE_THEN "x" (HYP_TAC "glim" \<circ> C MATCH_MP) THEN
   HYP_TAC "glim: gx glim" (REWRITE_RULE[LIMIT_METRIC_SEQUENTIALLY]) THEN
   REMOVE_THEN "glim" (MP_TAC \<circ> SPEC `e / 2`) THEN
   HYP REWRITE_TAC "e" [REAL_HALF] THEN
   HYP SIMP_TAC "fwd x" [] THEN INTRO_TAC "@N'. N'" THEN
   TRANS_TAC REAL_LET_TRANS
     `d m (f n (x::A):B, f (MAX N N') x) +
      d m (f (MAX N N') x, g x)` THEN
   HYP SIMP_TAC "fwd x gwd" [MDIST_TRIANGLE] THEN
   TRANS_TAC REAL_LTE_TRANS `e / 2 + e / 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD2; REWRITE_TAC[REAL_HALF; REAL_LE_REFL]] THEN
   CONJ_TAC THENL [ALL_TAC; REMOVE_THEN "N'" MATCH_MP_TAC THEN ARITH_TAC] THEN
   TRANS_TAC REAL_LET_TRANS
     `sup {d m (f n x::B,f (MAX N N') x) | x::A \<in> s}` THEN
   HYP SIMP_TAC "N n" [ARITH_RULE `N \<le> MAX N N'`] THEN
   HYP SIMP_TAC "sup x" [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [HYP_TAC "cy': @N. N" (C MATCH_MP REAL_LT_01) THEN
   USE_THEN "fbd" (MP_TAC \<circ> REWRITE_RULE[MBOUNDED] \<circ> SPEC `N::num`) THEN
   HYP REWRITE_TAC "nempty" [mbounded; IMAGE_EQ_EMPTY] THEN
   INTRO_TAC "Nwd (@c b. c Nbd)" THEN
   MAP_EVERY EXISTS_TAC [`c::B`; `b + 1`] THEN
   REWRITE_TAC[\<subseteq>; IN_IMAGE; IN_MCBALL] THEN
   INTRO_TAC "![y]; (@x. y x)" THEN REMOVE_THEN "y" SUBST1_TAC THEN
   HYP SIMP_TAC "x gwd c" [] THEN TRANS_TAC REAL_LE_TRANS
     `d m (c::B, f (N::num) (x::A)) + d f N x g x` THEN
   HYP SIMP_TAC "c fwd gwd x" [MDIST_TRIANGLE] THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [REMOVE_THEN "Nbd" MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    HYP MESON_TAC "x" [];
    REFUTE_THEN (LABEL_TAC "contra" \<circ> REWRITE_RULE[REAL_NOT_LE])] THEN
   CLAIM_TAC "@a. a1 a2"
     `\<exists>a. 1 < a \<and> a < d m (f (N::num) (x::A), g x::B)` THENL
   [EXISTS_TAC `(1 + d m (f (N::num) (x::A), g x::B)) / 2` THEN
    REMOVE_THEN "contra" MP_TAC THEN REAL_ARITH_TAC;
    USE_THEN "x" (HYP_TAC "glim" \<circ> C MATCH_MP)] THEN
   REMOVE_THEN "glim" (MP_TAC \<circ> REWRITE_RULE[LIMIT_METRIC_SEQUENTIALLY]) THEN
   HYP SIMP_TAC "gwd x" [] THEN DISCH_THEN (MP_TAC \<circ> SPEC `a - 1`) THEN
   ANTS_TAC THENL [REMOVE_THEN "a1" MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   HYP SIMP_TAC "fwd x" [] THEN INTRO_TAC "@N'. N'" THEN
   CUT_TAC `d m (f (N::num) (x::A), g x::B) < a` THENL
   [REMOVE_THEN "a2" MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   TRANS_TAC REAL_LET_TRANS
     `d m (f N (x::A),f (MAX N N') x::B) + d m (f (MAX N N') x,g x)` THEN
   HYP SIMP_TAC "fwd gwd x" [MDIST_TRIANGLE] THEN
   SUBST1_TAC (REAL_ARITH `a = 1 + (a - 1)`) THEN
   MATCH_MP_TAC REAL_LT_ADD2 THEN CONJ_TAC THENL
   [ALL_TAC; REMOVE_THEN "N'" MATCH_MP_TAC THEN ARITH_TAC] THEN
   TRANS_TAC REAL_LET_TRANS
     `sup {d m (f N x::B,f (MAX N N') x) | x::A \<in> s}` THEN
   CONJ_TAC THENL
   [HYP SIMP_TAC "sup x" []; REMOVE_THEN "N" MATCH_MP_TAC THEN ARITH_TAC];
   ALL_TAC] THEN
  INTRO_TAC "!e; e" THEN REMOVE_THEN "unif" (MP_TAC \<circ> SPEC `e / 2`) THEN
  HYP REWRITE_TAC "e" [REAL_HALF] THEN INTRO_TAC "@N. N" THEN
  EXISTS_TAC `N::num` THEN INTRO_TAC "!n; n" THEN
  TRANS_TAC REAL_LET_TRANS `e / 2` THEN CONJ_TAC THENL
  [ALL_TAC; REMOVE_THEN "e" MP_TAC THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
  [HYP SET_TAC "nempty" []; HYP MESON_TAC "N n" [REAL_LT_IMP_LE]]);;


subsection\<open>Metric space of continuous bounded functions\<close>


definition cfunspace where
  `cfunspace X m =
   submetric (funspace (topspace X) m)
     {f::A=>B | continuous_map X mtopology f}"

let CFUNSPACE = (REWRITE_RULE[GSYM FORALL_AND_THM] \<circ> prove)
 (`(\<forall>X m.
      mspace (cfunspace X m) =
      {f::A=>B | (\<forall>x. x \<in> topspace X \<Longrightarrow> f x \<in> M) \<and>
                f \<in> EXTENSIONAL (topspace X) \<and>
                mbounded (f ` (topspace X)) \<and>
                continuous_map X mtopology f}) \<and>
     (\<forall>f g::A=>B.
        d (cfunspace X m) (f,g) =
        if topspace X = {} then 0 else
        sup {d (f x) g x | x \<in> topspace X})"
oops
  REWRITE_TAC[cfunspace; SUBMETRIC; FUNSPACE] THEN SET_TAC[]);;

lemma cfunspace_subset_funspace:
   "mspace (cfunspace X m) \<subseteq> mspace (funspace (topspace X) m)"
oops
  SIMP_TAC[\<subseteq>; FUNSPACE; CFUNSPACE; IN_ELIM_THM]);;

lemma mdist_cfunspace_eq_mdist_funspace:
   "\<And>X m f g::A=>B.
     d (cfunspace X m) (f,g) = d (funspace (topspace X) m) (f,g)"
oops
  REWRITE_TAC[FUNSPACE; CFUNSPACE]);;

lemma cfunspace_mdist_le:
   "\<And>X m f g::A=>B a.
     \<not> (topspace X = {}) \<and>
     f \<in> mspace (cfunspace X m) \<and>
     g \<in> mspace (cfunspace X m)
     \<Longrightarrow> (d (cfunspace X m) (f,g) \<le> a \<longleftrightarrow>
          \<forall>x. x \<in> topspace X \<Longrightarrow> d (f x) g x \<le> a)"
oops
  INTRO_TAC "! *; ne f g" THEN
  REWRITE_TAC[MDIST_CFUNSPACE_EQ_MDIST_FUNSPACE] THEN
  MATCH_MP_TAC FUNSPACE_MDIST_LE THEN
  ASM_SIMP_TAC[REWRITE_RULE[\<subseteq>] CFUNSPACE_SUBSET_FUNSPACE]);;

lemma cfunspace_imp_bounded2:
   "\<And>X m f g::A=>B.
     f \<in> mspace (cfunspace X m) \<and> g \<in> mspace (cfunspace X m)
     \<Longrightarrow> (\<exists>b. \<forall>x. x \<in> topspace X \<Longrightarrow> d (f x) g x \<le> b)"
oops
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUNSPACE_IMP_BOUNDED2 THEN
  ASM SET_TAC [CFUNSPACE_SUBSET_FUNSPACE]);;

lemma cfunspace_mdist_lt:
   "\<And>X m f g::A=>B a x.
     compactin X (topspace X) \<and>
     f \<in> mspace (cfunspace X m) \<and> g \<in> mspace (cfunspace X m) \<and>
     d (cfunspace X m) (f, g) < a \<and>
     x \<in> topspace X
     \<Longrightarrow> d (f x) g x < a"
oops
  REPEAT GEN_TAC THEN ASM_CASES_TAC `topspace X = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN INTRO_TAC "cpt f g lt x" THEN
  REMOVE_THEN "lt" MP_TAC THEN ASM_REWRITE_TAC[CFUNSPACE] THEN
  INTRO_TAC "lt" THEN
  TRANS_TAC REAL_LET_TRANS
    `sup {d (f x)::B g x | x::A \<in> topspace X}` THEN
  HYP SIMP_TAC "lt" [] THEN  MATCH_MP_TAC REAL_LE_SUP THEN
  HYP (DESTRUCT_TAC "@b. b" \<circ>
    MATCH_MP CFUNSPACE_IMP_BOUNDED2 \<circ> CONJ_LIST) "f g" [] THEN
  MAP_EVERY EXISTS_TAC [`b::real`; `d m (f (x::A):B,g x)`] THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN HYP MESON_TAC "x b" []);;

lemma mdist_cfunspace_le:
   "0 \<le> B \<and>
     (\<forall>x::A. x \<in> topspace X \<Longrightarrow> d (f x)::B g x \<le> B)
     \<Longrightarrow> d (cfunspace X m) (f,g) \<le> B"
oops
  INTRO_TAC "!X m B f g; Bpos bound" THEN
  REWRITE_TAC[CFUNSPACE] THEN COND_CASES_TAC THEN
  HYP REWRITE_TAC "Bpos" [] THEN MATCH_MP_TAC REAL_SUP_LE THEN
  CONJ_TAC THENL
  [POP_ASSUM MP_TAC THEN SET_TAC[];
   REWRITE_TAC[IN_ELIM_THM] THEN HYP MESON_TAC "bound" []]);;

lemma mdist_cfunspace_imp_mdist_le:
   "\<And>X m f g::A=>B a x.
     f \<in> mspace (cfunspace X m) \<and>
     g \<in> mspace (cfunspace X m) \<and>
     d (cfunspace X m) (f,g) \<le> a \<and>
     x \<in> topspace X
     \<Longrightarrow> d (f x) g x \<le> a"
oops
  MESON_TAC[MEMBER_NOT_EMPTY; CFUNSPACE_MDIST_LE]);;

lemma compact_in_mspace_cfunspace:
   "compactin X (topspace X)
     \<Longrightarrow> mspace (cfunspace X m) =
          {f. (\<forall>x::A. x \<in> topspace X \<Longrightarrow> f x::B \<in> M) \<and>
               f \<in> EXTENSIONAL (topspace X) \<and>
               continuous_map X mtopology f}"
oops
  REWRITE_TAC[CFUNSPACE; EXTENSION; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN SIMP_TAC[] THEN INTRO_TAC "wd ext cont" THEN
  MATCH_MP_TAC COMPACT_IN_IMP_MBOUNDED THEN
  MATCH_MP_TAC (ISPEC `X::A topology` IMAGE_COMPACT_IN) THEN
  ASM_REWRITE_TAC[]);;

lemma mcomplete_cfunspace:
   "mcomplete \<Longrightarrow> mcomplete (cfunspace X m)"
oops
  INTRO_TAC "!X m; cpl" THEN REWRITE_TAC[cfunspace] THEN
  MATCH_MP_TAC SEQUENTIALLY_CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE THEN
  ASM_SIMP_TAC[MCOMPLETE_FUNSPACE] THEN
  REWRITE_TAC[IN_ELIM_THM; LIMIT_METRIC_SEQUENTIALLY] THEN
  INTRO_TAC "![f] [g]; fcont g lim" THEN
  ASM_CASES_TAC `topspace X = {}:A=>bool` THENL
  [ASM_REWRITE_TAC[continuous_map; NOT_IN_EMPTY; EMPTY_GSPEC; OPEN_IN_EMPTY];
   POP_ASSUM (LABEL_TAC "nempty")] THEN
  REWRITE_TAC[CONTINUOUS_MAP_TO_METRIC; IN_MBALL] THEN
  INTRO_TAC "!x; x; ![e]; e" THEN CLAIM_TAC "e3pos" `0 < e / 3` THENL
  [REMOVE_THEN "e" MP_TAC THEN REAL_ARITH_TAC;
   USE_THEN "e3pos" (HYP_TAC "lim: @N. N" \<circ> C MATCH_MP)] THEN
  HYP_TAC "N: f lt" (C MATCH_MP (SPEC `N::num` LE_REFL)) THEN
  HYP_TAC "fcont" (REWRITE_RULE[CONTINUOUS_MAP_TO_METRIC]) THEN
  USE_THEN "x" (HYP_TAC "fcont" \<circ> C MATCH_MP) THEN
  USE_THEN "e3pos" (HYP_TAC "fcont" \<circ> C MATCH_MP) THEN
  HYP_TAC "fcont: @u. u x' inc" (SPEC `N::num`) THEN EXISTS_TAC `u::A=>bool` THEN
  HYP REWRITE_TAC "u x'" [] THEN INTRO_TAC "!y; y'" THEN
  CLAIM_TAC "uinc" `\<forall>x::A. x \<in> u \<Longrightarrow> x \<in> topspace X` THENL
  [REMOVE_THEN "u" (MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
   ALL_TAC] THEN
  HYP_TAC "g -> gwd gext gbd" (REWRITE_RULE[FUNSPACE; IN_ELIM_THM]) THEN
  HYP_TAC "f -> fwd fext fbd" (REWRITE_RULE[FUNSPACE; IN_ELIM_THM]) THEN
  CLAIM_TAC "y" `y::A \<in> topspace X` THENL
  [HYP SIMP_TAC "uinc y'" [OPEN_IN_SUBSET]; HYP SIMP_TAC "gwd x y" []] THEN
  CLAIM_TAC "sup" `\<forall>x0::A. x0 \<in> topspace X
                          \<Longrightarrow> d m (f (N::num) x0::B,g x0) \<le> e / 3` THENL
  [INTRO_TAC "!x0; x0" THEN TRANS_TAC REAL_LE_TRANS
     `sup {d m (f (N::num) x,g x::B) | x::A \<in> topspace X}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_SUP THEN HYP (DESTRUCT_TAC "@b. b" \<circ>
      MATCH_MP FUNSPACE_IMP_BOUNDED2 \<circ> CONJ_LIST) "f g" [] THEN
    MAP_EVERY EXISTS_TAC [`b::real`; `d m (f (N::num) (x0::A), g x0::B)`] THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
    CONJ_TAC THENL [HYP SET_TAC "x0" []; HYP MESON_TAC "b" []];
    REMOVE_THEN "lt" MP_TAC THEN HYP REWRITE_TAC "nempty" [FUNSPACE] THEN
    MATCH_ACCEPT_TAC REAL_LT_IMP_LE];
   ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
    `d m (g (x::A):B, f (N::num) x) + d f N x g y` THEN
  HYP SIMP_TAC "gwd fwd x y" [MDIST_TRIANGLE] THEN
  SUBST1_TAC (ARITH_RULE `e = e / 3 + (e / 3 + e / 3)`) THEN
  MATCH_MP_TAC REAL_LET_ADD2 THEN HYP SIMP_TAC "gwd fwd x sup" [MDIST_SYM] THEN
  TRANS_TAC REAL_LET_TRANS
    `d m (f (N::num) (x::A):B, f N y) + d f N y g y` THEN
  HYP SIMP_TAC "fwd gwd x y" [MDIST_TRIANGLE] THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN HYP SIMP_TAC "gwd fwd y sup" [] THEN
  REMOVE_THEN "inc" MP_TAC THEN HYP SIMP_TAC "fwd x y' uinc" [IN_MBALL]);;


subsection\<open>Existence of completion for any metric space M as a subspace of M=>R\<close>


lemma metric_completion_explicit:
   "\<exists>s f::A=>A->real.
      s \<subseteq> mspace(funspace (M) real_euclidean_metric) \<and>
      mcomplete(submetric (funspace (M) real_euclidean_metric) s) \<and>
      image f (M) \<subseteq> s \<and>
      mtopology(funspace (M) real_euclidean_metric) closure_of
      image f (M) = s \<and>
      \<forall>x y. x \<in> M \<and> y \<in> M
            \<Longrightarrow> d (funspace (M) real_euclidean_metric) (f x,f y) =
                d x y"
oops
  GEN_TAC THEN
  ABBREV_TAC `m' = funspace (M::A=>bool) real_euclidean_metric` THEN
  ASM_CASES_TAC `M::A=>bool = {}` THENL
   [EXISTS_TAC `{}:(A=>real)->bool` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; IMAGE_CLAUSES; CLOSURE_OF_EMPTY;
                 EMPTY_SUBSET; INTER_EMPTY; mcomplete; CAUCHY_IN_SUBMETRIC];
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY])] THEN
  DISCH_THEN(X_CHOOSE_TAC `a::A`) THEN
  ABBREV_TAC
    `f::A=>A->real =
     \<lambda>x. RESTRICTION (M) (\<lambda>u. d x u - d a u)` THEN
  EXISTS_TAC `mtopology(funspace (M) real_euclidean_metric) closure_of
              image (f::A=>A->real) (M)` THEN
  EXISTS_TAC `f::A=>A->real` THEN
  EXPAND_TAC "m'" THEN
 SUBGOAL_THEN `image (f::A=>A->real) (M) \<subseteq> mspace m'`
  ASSUME_TAC THENL
   [EXPAND_TAC "m'" THEN REWRITE_TAC[\<subseteq>; FUNSPACE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; EXTENSIONAL] THEN
    REWRITE_TAC[REAL_EUCLIDEAN_METRIC; IN_UNIV; mbounded; mcball] THEN
    X_GEN_TAC `b::A` THEN DISCH_TAC THEN
    EXPAND_TAC "f" THEN SIMP_TAC[RESTRICTION; \<subseteq>; FORALL_IN_IMAGE] THEN
    MAP_EVERY EXISTS_TAC [`0::real`; `d a::A b`] THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_SUB_RZERO] THEN
    MAP_EVERY UNDISCH_TAC [`(a::A) \<in> M`; `(b::A) \<in> M`] THEN
    CONV_TAC METRIC_ARITH;
    ALL_TAC] THEN
  REWRITE_TAC[SUBMETRIC] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM TOPSPACE_MTOPOLOGY] THEN
    REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE];
    MATCH_MP_TAC CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE THEN
    REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN EXPAND_TAC "m'" THEN
    MATCH_MP_TAC MCOMPLETE_FUNSPACE THEN
    REWRITE_TAC[MCOMPLETE_REAL_EUCLIDEAN_METRIC];
    MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
    ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY];
    MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN STRIP_TAC THEN
    EXPAND_TAC "m'" THEN REWRITE_TAC[FUNSPACE] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
    MATCH_MP_TAC SUP_UNIQUE THEN SIMP_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `b::real` THEN REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[RESTRICTION] THEN EQ_TAC THENL
     [DISCH_THEN(fun th -> MP_TAC(SPEC `x::A` th)) THEN EXPAND_TAC "f" THEN
      ASM_SIMP_TAC[MDIST_REFL; MDIST_SYM] THEN REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`(x::A) \<in> M`; `(y::A) \<in> M`] THEN
      CONV_TAC METRIC_ARITH]]);;

lemma metric_completion:
   "?m' f::A=>A->real.
                mcomplete m' \<and>
                image f (M) \<subseteq> mspace m' \<and>
                (mtopology m') closure_of (image f (M)) = mspace m' \<and>
                \<forall>x y. x \<in> M \<and> y \<in> M
                      \<Longrightarrow> d m' (f x,f y) = d x y"
oops
  GEN_TAC THEN
  MATCH_MP_TAC(MESON[]
   `(\<exists>s f. P (submetric (funspace (M) real_euclidean_metric) s) f)
    \<Longrightarrow> \<exists>n f. P n f`) THEN
  MP_TAC(SPEC `m::A metric` METRIC_COMPLETION_EXPLICIT) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  REWRITE_TAC[SUBMETRIC; SUBSET_INTER] THEN
  REWRITE_TAC[MTOPOLOGY_SUBMETRIC; CLOSURE_OF_SUBTOPOLOGY] THEN
  SIMP_TAC[SET_RULE `t \<subseteq> s \<Longrightarrow> s \<inter> t = t`] THEN SET_TAC[]);;

lemma metrizable_space_completion:
   "metrizable_space X
        \<Longrightarrow> ?top' (f::A=>A->real).
                completely_metrizable_space Y \<and>
                embedding_map X Y f \<and>
                Y closure_of (f ` (topspace X)) = topspace Y"
oops
  REWRITE_TAC[FORALL_METRIZABLE_SPACE; RIGHT_EXISTS_AND_THM] THEN
  X_GEN_TAC `m::A metric` THEN
  REWRITE_TAC[EXISTS_COMPLETELY_METRIZABLE_SPACE; RIGHT_AND_EXISTS_THM] THEN
  MP_TAC(ISPEC `m::A metric` METRIC_COMPLETION) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  MESON_TAC[ISOMETRY_IMP_EMBEDDING_MAP]);;


text\<open> The Baire Category Theorem                                                \<close>


lemma metric_baire_category:
   "mcomplete \<and>
     countable g \<and>
     (\<forall>t. t \<in> g \<Longrightarrow> openin mtopology t \<and>
                     mtopology closure_of t = M)
     \<Longrightarrow> mtopology closure_of \<Inter> g = M"
oops
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN INTRO_TAC "!m; m" THEN
  REWRITE_TAC[FORALL_COUNTABLE_AS_IMAGE; NOT_IN_EMPTY; CLOSURE_OF_UNIV;
  INTERS_0; TOPSPACE_MTOPOLOGY; FORALL_IN_IMAGE; IN_UNIV; FORALL_AND_THM] THEN
  INTRO_TAC "![u]; u_open u_dense" THEN
  REWRITE_TAC[GSYM TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[DENSE_INTERSECTS_OPEN] THEN
  INTRO_TAC "![w]; w_open w_ne" THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  CLAIM_TAC "@x0. x0" `\<exists>x0::A. x0 \<in> u 0 \<inter> w` THENL
  [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
   ASM_MESON_TAC[DENSE_INTERSECTS_OPEN; TOPSPACE_MTOPOLOGY];
   ALL_TAC] THEN
  CLAIM_TAC "@r0. r0pos r0lt1 sub"
    `\<exists>r. 0 < r \<and> r < 1 \<and> mcball m (x0::A,r) \<subseteq> u 0 \<inter> w` THENL
  [SUBGOAL_THEN `openin mtopology (u 0 \<inter> w::A=>bool)` MP_TAC THENL
   [HYP SIMP_TAC "u_open w_open" [OPEN_IN_INTER]; ALL_TAC] THEN
   REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN INTRO_TAC "u0w hp" THEN
   REMOVE_THEN "hp" (MP_TAC \<circ> SPEC `x0::A`) THEN
   ANTS_TAC THENL [HYP REWRITE_TAC "x0" []; ALL_TAC] THEN
   INTRO_TAC "@r. rpos ball" THEN EXISTS_TAC `min r 1/2` THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   TRANS_TAC SUBSET_TRANS `mball m (x0::A,r)` THEN
   HYP REWRITE_TAC "ball" [] THEN
   MATCH_MP_TAC MCBALL_SUBSET_MBALL_CONCENTRIC THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (DESTRUCT_TAC "@b. b0 b1" \<circ> prove_general_recursive_function_exists)
    `\<exists>b::num->(A#real).
       b 0 = (x0::A,r0) \<and>
       (\<forall>n. b (Suc n) =
            @(x,r). 0 < r \<and> r < snd (b n) / 2 \<and> x \<in> M \<and>
                    mcball x r \<subseteq> mball m (b n) \<inter> u n)` THEN
  CLAIM_TAC "rmk"
    `\<forall>n. (\ (x::A,r). 0 < r \<and> r < snd (b n) / 2 \<and> x \<in> M \<and>
                   mcball x r \<subseteq> mball m (b n) \<inter> u n)
         (b (Suc n))` THENL
  [LABEL_INDUCT_TAC THENL
   [REMOVE_THEN "b1" (fun b1 -> REWRITE_TAC[b1]) THEN
    MATCH_MP_TAC CHOICE_PAIRED_THM THEN
    REMOVE_THEN "b0" (fun b0 -> REWRITE_TAC[b0]) THEN
    MAP_EVERY EXISTS_TAC [`x0::A`; `r0 / 4`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [CUT_TAC `u 0::A=>bool \<subseteq> M` THENL
     [HYP SET_TAC "x0" [];
      HYP SIMP_TAC "u_open" [GSYM TOPSPACE_MTOPOLOGY; OPEN_IN_SUBSET]];
     ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS `mball m (x0::A,r0)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC MCBALL_SUBSET_MBALL_CONCENTRIC THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[SUBSET_INTER; SUBSET_REFL] THEN
     TRANS_TAC SUBSET_TRANS `mcball m (x0::A,r0)` THEN
     REWRITE_TAC [MBALL_SUBSET_MCBALL] THEN HYP SET_TAC "sub" []];
    ALL_TAC] THEN
   USE_THEN "b1" (fun b1 -> GEN_REWRITE_TAC RAND_CONV [b1]) THEN
   MATCH_MP_TAC CHOICE_PAIRED_THM THEN REWRITE_TAC[] THEN
   HYP_TAC "ind_n: rpos rlt x subn" (REWRITE_RULE[LAMBDA_PAIR]) THEN
   USE_THEN "u_dense" (MP_TAC \<circ> SPEC `Suc n` \<circ>
     REWRITE_RULE[GSYM TOPSPACE_MTOPOLOGY]) THEN
   REWRITE_TAC[DENSE_INTERSECTS_OPEN] THEN
   DISCH_THEN (MP_TAC \<circ> SPEC `mball m (b (Suc n):A#real)`) THEN
   (DESTRUCT_TAC "@x1 r1. bsuc" \<circ> MESON[PAIR])
     `\<exists>x1::A r1::real. b (Suc n) = x1,r1` THEN
   HYP REWRITE_TAC "bsuc" [] THEN
   REMOVE_THEN "bsuc"
    (fun th -> RULE_ASSUM_TAC (REWRITE_RULE[th]) THEN LABEL_TAC "bsuc" th) THEN
   ANTS_TAC THENL
   [HYP REWRITE_TAC "x" [OPEN_IN_MBALL; MBALL_EQ_EMPTY; DE_MORGAN_THM] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN INTRO_TAC "@z. hp" THEN
   EXISTS_TAC `z::A` THEN
   SUBGOAL_THEN `openin mtopology (mball m (x1::A,r1) \<inter> u (Suc n))`
     (DESTRUCT_TAC "hp1 hp2" \<circ> REWRITE_RULE[OPEN_IN_MTOPOLOGY_MCBALL]) THENL
   [HYP SIMP_TAC "u_open" [OPEN_IN_INTER; OPEN_IN_MBALL]; ALL_TAC] THEN
   CLAIM_TAC "z" `z::A \<in> M` THENL
   [CUT_TAC `u (Suc n):A=>bool \<subseteq> M` THENL
    [HYP SET_TAC "hp" [];
     HYP SIMP_TAC "u_open" [GSYM TOPSPACE_MTOPOLOGY; OPEN_IN_SUBSET]];
    HYP REWRITE_TAC "z" []] THEN
   REMOVE_THEN "hp2" (MP_TAC \<circ> SPEC `z::A`) THEN
   ANTS_TAC THENL [HYP SET_TAC "hp" []; ALL_TAC] THEN
   INTRO_TAC "@r. rpos ball" THEN EXISTS_TAC `min r (r1 / 4)` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   TRANS_TAC SUBSET_TRANS `mcball m (z::A,r)` THEN
   HYP SIMP_TAC "ball" [MCBALL_SUBSET_CONCENTRIC; REAL_MIN_MIN];
   ALL_TAC] THEN
  CLAIM_TAC "@x r. b" `\<exists>x r. \<forall>n::num. b n = x n::A, r n::real` THENL
  [MAP_EVERY EXISTS_TAC
     [`fst \<circ> (b::num=>A#real)`; `snd \<circ> (b::num=>A#real)`] THEN
   REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  REMOVE_THEN "b"
    (fun b -> RULE_ASSUM_TAC (REWRITE_RULE[b]) THEN LABEL_TAC "b" b) THEN
  HYP_TAC "b0: x_0 r_0" (REWRITE_RULE[PAIR_EQ]) THEN
  REMOVE_THEN "x_0" (SUBST_ALL_TAC \<circ> GSYM) THEN
  REMOVE_THEN "r_0" (SUBST_ALL_TAC \<circ> GSYM) THEN
  HYP_TAC "rmk: r1pos r1lt x1 ball" (REWRITE_RULE[FORALL_AND_THM]) THEN
  CLAIM_TAC "x" `\<forall>n::num. x n::A \<in> M` THENL
  [LABEL_INDUCT_TAC THENL
   [CUT_TAC `u 0::A=>bool \<subseteq> M` THENL
    [HYP SET_TAC "x0" [];
     HYP SIMP_TAC "u_open" [GSYM TOPSPACE_MTOPOLOGY; OPEN_IN_SUBSET]];
    HYP REWRITE_TAC "x1" []];
   ALL_TAC] THEN
  CLAIM_TAC "rpos" `\<forall>n::num. 0 < r n` THENL
  [LABEL_INDUCT_TAC THENL
   [HYP REWRITE_TAC "r0pos" []; HYP REWRITE_TAC "r1pos" []];
   ALL_TAC] THEN
  CLAIM_TAC "rmono" `\<forall>p q::num. p \<le> q \<Longrightarrow> r q \<le> r p` THENL
  [MATCH_MP_TAC LE_INDUCT THEN REWRITE_TAC[REAL_LE_REFL] THEN
   INTRO_TAC "!p q; pq rpq" THEN
   REMOVE_THEN "r1lt" (MP_TAC \<circ> SPEC `q::num`) THEN
   REMOVE_THEN "rpos" (MP_TAC \<circ> SPEC `q::num`) THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  CLAIM_TAC "rlt" `\<forall>n::num. r n < inverse (2 ^ n)` THENL
  [LABEL_INDUCT_TAC THENL
   [CONV_TAC (RAND_CONV REAL_RAT_REDUCE_CONV) THEN HYP REWRITE_TAC "r0lt1" [];
    TRANS_TAC REAL_LTE_TRANS `r (n::num) / 2` THEN
    HYP REWRITE_TAC "r1lt" [real_pow] THEN REMOVE_THEN "ind_n" MP_TAC THEN
    REMOVE_THEN "rpos" (MP_TAC \<circ> SPEC `n::num`) THEN CONV_TAC REAL_FIELD];
   ALL_TAC] THEN
  CLAIM_TAC "nested"
    `\<forall>p q::num. p \<le> q \<Longrightarrow> mball m (x q::A, r q) \<subseteq> mball m (x p, r p)` THENL
  [MATCH_MP_TAC LE_INDUCT THEN REWRITE_TAC[SUBSET_REFL] THEN
   INTRO_TAC "!p q; pq sub" THEN
   TRANS_TAC SUBSET_TRANS `mball m (x (q::num):A,r q)` THEN
   HYP REWRITE_TAC "sub" [] THEN
   TRANS_TAC SUBSET_TRANS `mcball m (x (Suc q):A,r(Suc q))` THEN
   REWRITE_TAC[MBALL_SUBSET_MCBALL] THEN HYP SET_TAC "ball" [];
   ALL_TAC] THEN
  CLAIM_TAC "in_ball" `\<forall>p q::num. p \<le> q \<Longrightarrow> x q::A \<in> mball m (x p, r p)` THENL
  [INTRO_TAC "!p q; le" THEN CUT_TAC `x (q::num):A \<in> mball m (x q, r q)` THENL
   [HYP SET_TAC "nested le" []; HYP SIMP_TAC "x rpos" [CENTRE_IN_MBALL_EQ]];
   ALL_TAC] THEN
  CLAIM_TAC "@l. l" `\<exists>l::A. limitin mtopology x l sequentially` THENL
  [HYP_TAC "m" (REWRITE_RULE[mcomplete]) THEN REMOVE_THEN "m" MATCH_MP_TAC THEN
   HYP REWRITE_TAC "x" [MCauchy] THEN INTRO_TAC "!e; epos" THEN
   CLAIM_TAC "@N. N" `\<exists>N. inverse(2 ^ N) < e` THENL
   [REWRITE_TAC[REAL_INV_POW] THEN MATCH_MP_TAC REAL_ARCH_POW_INV THEN
    HYP REWRITE_TAC "epos" [] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   EXISTS_TAC `N::num` THEN MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [HYP SIMP_TAC "x" [MDIST_SYM] THEN MESON_TAC[]; ALL_TAC] THEN
   INTRO_TAC "!n n'; le; n n'" THEN
   TRANS_TAC REAL_LT_TRANS `inverse (2 ^ N)` THEN HYP REWRITE_TAC "N" [] THEN
   TRANS_TAC REAL_LT_TRANS `r (N::num):real` THEN HYP REWRITE_TAC "rlt" [] THEN
   CUT_TAC `x (n':num):A \<in> mball m (x n, r n)` THENL
   [HYP REWRITE_TAC "x" [IN_MBALL] THEN INTRO_TAC "hp" THEN
    TRANS_TAC REAL_LTE_TRANS `r (n::num):real` THEN
    HYP SIMP_TAC "n rmono hp" [];
    HYP SIMP_TAC "in_ball le" []];
   ALL_TAC] THEN
  EXISTS_TAC `l::A` THEN
  CLAIM_TAC "in_mcball" `\<forall>n::num. l::A \<in> mcball m (x n, r n)` THENL
  [GEN_TAC THEN
   (MATCH_MP_TAC \<circ> ISPECL [`sequentially`; `mtopology (m::A metric)`])
   LIMIT_IN_CLOSED_IN THEN EXISTS_TAC `x::num=>A` THEN
   HYP REWRITE_TAC "l" [TRIVIAL_LIMIT_SEQUENTIALLY; CLOSED_IN_MCBALL] THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `n::num` THEN
   INTRO_TAC "![p]; p" THEN CUT_TAC `x (p::num):A \<in> mball m (x n, r n)` THENL
   [SET_TAC[MBALL_SUBSET_MCBALL]; HYP SIMP_TAC "in_ball p" []];
   ALL_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
  [REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN
   LABEL_INDUCT_TAC THENL
   [HYP SET_TAC "in_mcball sub " []; HYP SET_TAC "in_mcball ball " []];
   HYP SET_TAC "sub in_mcball" []]);;

lemma metric_baire_category_alt:
   "\<And>m g:(A=>bool)->bool.
         mcomplete \<and>
         countable g \<and>
         (\<forall>t. t \<in> g
              \<Longrightarrow> closedin mtopology t \<and> mtopology interior_of t = {})
         \<Longrightarrow> mtopology interior_of (\<Union>g) = {}"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m::A metric`; `image (\<lambda>u::A=>bool. M - u) g`]
        METRIC_BAIRE_CATEGORY) THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_MSPACE] THEN
  REWRITE_TAC[CLOSURE_OF_COMPLEMENT; GSYM TOPSPACE_MTOPOLOGY] THEN
  ASM_SIMP_TAC[DIFF_EMPTY] THEN REWRITE_TAC[CLOSURE_OF_INTERIOR_OF] THEN
  MATCH_MP_TAC(SET_RULE
    `s \<subseteq> u \<and> s' = s \<Longrightarrow> u - s' = u \<Longrightarrow> s = {}`) THEN
  REWRITE_TAC[INTERIOR_OF_SUBSET_TOPSPACE] THEN AP_TERM_TAC THEN
  REWRITE_TAC[DIFF_INTERS; SET_RULE
   `{f y | y \<in> g ` s} = {f(g x) | x \<in> s}`] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
   `(\<forall>x. x \<in> s \<Longrightarrow> f x = x) \<Longrightarrow> {f x | x \<in> s} = s`) THEN
  X_GEN_TAC `s::A=>bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `s::A=>bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET) THEN SET_TAC[]);;

lemma baire_category_alt:
   " (completely_metrizable_space X \<or>
         locally_compact_space X \<and>
         (Hausdorff_space X \<or> regular_space X)) \<and>
        countable g \<and>
        (\<forall>t. t \<in> g \<Longrightarrow> closedin X t \<and> X interior_of t = {})
        \<Longrightarrow> X interior_of (\<Union>g) = {}"
oops
  REWRITE_TAC[TAUT `(p \<or> q) \<and> r \<Longrightarrow> s \<longleftrightarrow>
                    (p \<Longrightarrow> r \<Longrightarrow> s) \<and> (q \<and> r \<Longrightarrow> s)`] THEN
  REWRITE_TAC[FORALL_AND_THM; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[GSYM FORALL_MCOMPLETE_TOPOLOGY] THEN
  SIMP_TAC[METRIC_BAIRE_CATEGORY_ALT] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP (TAUT `(p \<or> q) \<Longrightarrow> (p \<Longrightarrow> q) \<Longrightarrow> q`)) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[LOCALLY_COMPACT_HAUSDORFF_IMP_REGULAR_SPACE]; DISCH_TAC] THEN
  ASM_CASES_TAC `g:(A=>bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; INTERIOR_OF_EMPTY] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ]
        COUNTABLE_AS_IMAGE)) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `t::num=>A->bool` THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [FORALL_IN_IMAGE]) THEN
  REWRITE_TAC[IN_UNIV; FORALL_AND_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[interior_of; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z::A` THEN
  DISCH_THEN(X_CHOOSE_THEN `u::A=>bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `X::A topology`
        LOCALLY_COMPACT_SPACE_NEIGHBOURHOOD_BASE_CLOSED_IN) THEN
  ASM_REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN
  FIRST_ASSUM(MP_TAC \<circ> SPEC `z::A` \<circ> REWRITE_RULE[\<subseteq>] \<circ> MATCH_MP
    OPEN_IN_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC \<circ> SPECL [`u::A=>bool`; `z::A`]) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v::A=>bool`; `k::A=>bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `\<exists>c::num=>A->bool.
        (\<forall>n. c n \<subseteq> k \<and> closedin X (c n) \<and>
             \<not> (X interior_of c n = {}) \<and> disjnt (c n) (t n)) \<and>
        (\<forall>n. c (Suc n) \<subseteq> c n)`
  MP_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id
       [GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN]) THEN
      REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `v - (t::num=>A->bool) 0`) THEN
      ASM_SIMP_TAC[OPEN_IN_DIFF] THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP MONO_EXISTS) THEN ANTS_TAC THENL
       [REWRITE_TAC[SET_RULE `(\<exists>x. x \<in> s - t) \<longleftrightarrow> \<not> (s \<subseteq> t)`] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `X interior_of (t::num=>A->bool) 0 = {}` MP_TAC THENL
         [ASM_REWRITE_TAC[]; REWRITE_TAC[interior_of]] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`x::A`; `n::A=>bool`; `c::A=>bool`] THEN
        STRIP_TAC THEN EXISTS_TAC `c::A=>bool` THEN
        ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC; ASM SET_TAC[]] THEN
        EXISTS_TAC `x::A` THEN REWRITE_TAC[interior_of; IN_ELIM_THM] THEN
        ASM_MESON_TAC[]];
      MAP_EVERY X_GEN_TAC [`n::num`; `c::A=>bool`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id
       [GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN]) THEN
      REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC
        `X interior_of c - (t::num=>A->bool) (Suc n)`) THEN
      ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_INTERIOR_OF] THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP MONO_EXISTS) THEN ANTS_TAC THENL
       [REWRITE_TAC[SET_RULE `(\<exists>x. x \<in> s - t) \<longleftrightarrow> \<not> (s \<subseteq> t)`] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `X interior_of t(Suc n):A=>bool = {}` MP_TAC THENL
         [ASM_REWRITE_TAC[]; REWRITE_TAC[interior_of]] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        ASM_MESON_TAC[OPEN_IN_INTERIOR_OF; MEMBER_NOT_EMPTY];
        REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`x::A`; `n::A=>bool`; `d::A=>bool`] THEN
        STRIP_TAC THEN EXISTS_TAC `d::A=>bool` THEN
        ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN REPEAT CONJ_TAC THENL
         [MP_TAC(ISPECL[`X::A topology`; `c::A=>bool`] INTERIOR_OF_SUBSET) THEN
          ASM SET_TAC[];
          EXISTS_TAC `x::A` THEN REWRITE_TAC[interior_of; IN_ELIM_THM] THEN
          ASM_MESON_TAC[];
          ASM SET_TAC[];
          MP_TAC(ISPECL[`X::A topology`; `c::A=>bool`] INTERIOR_OF_SUBSET) THEN
          ASM SET_TAC[]]]];
    REWRITE_TAC[NOT_EXISTS_THM; FORALL_AND_THM]] THEN
  X_GEN_TAC `c::num=>A->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology X (k::A=>bool)`; `c::num=>A->bool`]
        COMPACT_SPACE_IMP_NEST) THEN
  ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; CLOSED_IN_SUBSET_TOPSPACE] THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[INTERIOR_OF_SUBSET; CLOSED_IN_SUBSET; MEMBER_NOT_EMPTY;
                  \<subseteq>];
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM SET_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[UNIONS_IMAGE; IN_UNIV]) THEN
    REWRITE_TAC[INTERS_GSPEC] THEN ASM SET_TAC[]]);;

lemma baire_category:
   "\<And>X g:(A=>bool)->bool.
        (completely_metrizable_space X \<or>
         locally_compact_space X \<and>
         (Hausdorff_space X \<or> regular_space X)) \<and>
        countable g \<and>
        (\<forall>t. t \<in> g \<Longrightarrow> openin X t \<and> X closure_of t = topspace X)
        \<Longrightarrow> X closure_of \<Inter> g = topspace X"
oops
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `g:(A=>bool)->bool = {}` THENL
   [ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
    ASM_SIMP_TAC[INTERS_0; INTER_UNIV; CLOSURE_OF_TOPSPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X::A topology`;
                 `image (\<lambda>u::A=>bool. topspace X - u) g`]
        BAIRE_CATEGORY_ALT) THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE] THEN
  ASM_SIMP_TAC[INTERIOR_OF_COMPLEMENT; DIFF_EQ_EMPTY] THEN
  REWRITE_TAC[INTERIOR_OF_CLOSURE_OF] THEN
  MATCH_MP_TAC(SET_RULE
    `s \<subseteq> u \<and> s' = s \<Longrightarrow> u - s' = {} \<Longrightarrow> s = u`) THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE] THEN AP_TERM_TAC THEN
  REWRITE_TAC[DIFF_UNIONS; SET_RULE
   `{f y | y \<in> g ` s} = {f(g x) | x \<in> s}`] THEN
  MATCH_MP_TAC(SET_RULE `t \<subseteq> u \<and> s = t \<Longrightarrow> u \<inter> s = t`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INTERS_SUBSET; OPEN_IN_SUBSET]; ALL_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
   `(\<forall>x. x \<in> s \<Longrightarrow> f x = x) \<Longrightarrow> {f x | x \<in> s} = s`) THEN
  X_GEN_TAC `s::A=>bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `s::A=>bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]);;


subsection\<open>Sierpinski-Hausdorff type results about countable closed unions\<close>


lemma locally_connected_not_countable_closed_union:
   "\<And>X u:(A=>bool)->bool.
        \<not> (topspace X = {}) \<and>
        connected_space X \<and>
        locally_connected_space X \<and>
        (completely_metrizable_space X \<or>
         locally_compact_space X \<and> Hausdorff_space X) \<and>
        countable u \<and> pairwise disjnt u \<and>
        (\<forall>c. c \<in> u \<Longrightarrow> closedin X c \<and> (c \<noteq> {})) \<and>
        \<Union>u = topspace X
         \<Longrightarrow> u = {topspace X}"
oops
  lemma lemma:
   (`\<Union>(f ` s \<union> g ` s) =
     \<Union>(image (\<lambda>x. f x \<union> g x) s)"
oops
    REWRITE_TAC[UNIONS_UNION; UNIONS_IMAGE] THEN SET_TAC[])
in

  REWRITE_TAC[REAL_CLOSED_IN] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `v = image (\<lambda>c::A=>bool. X frontier_of c) u` THEN
  ABBREV_TAC `b::A=>bool = \<Union>v` THEN
  MATCH_MP_TAC(TAUT `(\<not> p \<Longrightarrow> False) \<Longrightarrow> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(b::A=>bool) \<subseteq> topspace X` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[UNIONS_SUBSET] THEN
    EXPAND_TAC "v" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    REWRITE_TAC[GSYM TOPSPACE_MTOPOLOGY; FRONTIER_OF_SUBSET_TOPSPACE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology X (b::A=>bool)`; `v:(A=>bool)->bool`]
        BAIRE_CATEGORY_ALT) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "v" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; NOT_IMP] THEN CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPEC `subtopology X (b::A=>bool)`
        INTERIOR_OF_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[TOPSPACE_MTOPOLOGY; SET_RULE
     `s \<subseteq> u \<Longrightarrow> u \<inter> s = s`] THEN
    DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "b" THEN
    EXPAND_TAC "v" THEN MATCH_MP_TAC(SET_RULE
     `(\<forall>s. s \<in> u \<and> s \<subseteq> \<Union>u \<and> f s = {} \<Longrightarrow> s = {}) \<and>
      \<not> (\<Union>u = {})
      \<Longrightarrow> \<not> (\<Union>(f ` u) = {})`) THEN
    ASM_SIMP_TAC[IMP_CONJ; FRONTIER_OF_EQ_EMPTY; GSYM TOPSPACE_MTOPOLOGY] THEN
    ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    X_GEN_TAC `s::A=>bool` THEN REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [CONNECTED_SPACE_CLOPEN_IN]) THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `s::A=>bool`) THEN
    ASM_CASES_TAC `s::A=>bool = {}` THEN ASM_SIMP_TAC[] THEN
    ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP (SET_RULE
     `(u \<noteq> {a}) \<Longrightarrow> a \<in> u \<Longrightarrow> \<exists>b. b \<in> u \<and> (b \<noteq> a)`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t::A=>bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [pairwise]) THEN
    DISCH_THEN(MP_TAC \<circ> SPECL [`topspace X::A=>bool`; `t::A=>bool`]) THEN
    ASM SET_TAC[]] THEN
  SUBGOAL_THEN `closedin X (b::A=>bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `b = topspace X -
          \<Union>(image (\<lambda>c::A=>bool. X interior_of c) u)`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["b"; "v"] THEN MATCH_MP_TAC(SET_RULE
       `s \<union> t = u \<and> disjnt s t \<Longrightarrow> s = u - t`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM UNIONS_UNION; lemma] THEN
        ONCE_REWRITE_TAC[UNION_COMM] THEN
        REWRITE_TAC[INTERIOR_OF_UNION_FRONTIER_OF] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
         `(\<forall>x. x \<in> s \<Longrightarrow> f x = x) \<Longrightarrow> f ` s = s`) THEN
        ASM_SIMP_TAC[CLOSURE_OF_EQ];
        REWRITE_TAC[SET_RULE
         `disjnt (\<Union>s) (\<Union>t) \<longleftrightarrow>
          \<forall>x. x \<in> s \<Longrightarrow> \<forall>y. y \<in> t \<Longrightarrow> disjnt x y`] THEN
        REWRITE_TAC[FORALL_IN_IMAGE] THEN
        X_GEN_TAC `s::A=>bool` THEN DISCH_TAC THEN
        X_GEN_TAC `t::A=>bool` THEN DISCH_TAC THEN
        ASM_CASES_TAC `s::A=>bool = t` THENL
         [ASM_REWRITE_TAC[frontier_of] THEN SET_TAC[];
          FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [pairwise])] THEN
        DISCH_THEN(MP_TAC \<circ> SPECL [`s::A=>bool`; `t::A=>bool`]) THEN
        ASM_SIMP_TAC[frontier_of; CLOSURE_OF_CLOSED_IN] THEN
        MP_TAC(ISPECL [`X::A topology`; `t::A=>bool`]
          INTERIOR_OF_SUBSET) THEN
        SET_TAC[]];
      MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
      MATCH_MP_TAC OPEN_IN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_IMAGE; OPEN_IN_INTERIOR_OF]];
      ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[COMPLETELY_METRIZABLE_SPACE_CLOSED_IN;
                  LOCALLY_COMPACT_SPACE_CLOSED_SUBSET;
                  HAUSDORFF_SPACE_SUBTOPOLOGY];
    ALL_TAC] THEN
  X_GEN_TAC `s::A=>bool` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_SUBSET_TOPSPACE THEN
    REWRITE_TAC[CLOSED_IN_FRONTIER_OF; FRONTIER_OF_SUBSET_TOPSPACE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; interior_of; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `a::A` THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_ALT; EXISTS_IN_GSPEC; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `u::A=>bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a::A) \<in> X frontier_of s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(a::A) \<in> s` ASSUME_TAC THENL
   [UNDISCH_TAC `(a::A) \<in> X frontier_of s` THEN
    REWRITE_TAC[frontier_of; IN_DIFF] THEN  ASM_SIMP_TAC[CLOSURE_OF_CLOSED_IN];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [locally_connected_space]) THEN
  DISCH_THEN(MP_TAC \<circ> GEN_REWRITE_RULE id [NEIGHBOURHOOD_BASE_OF]) THEN
  DISCH_THEN(MP_TAC \<circ> SPECL [`u::A=>bool`; `a::A`]) THEN
  REWRITE_TAC[GSYM TOPSPACE_MTOPOLOGY; SUBTOPOLOGY_TOPSPACE] THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`w::A=>bool`; `c::A=>bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X::A topology`; `s::A=>bool`; `w::A=>bool`]
        FRONTIER_OF_OPEN_IN_STRADDLE_INTER) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `\<exists>t::A=>bool. t \<in> u \<and> (t \<noteq> s) \<and> \<not> (w \<inter> t = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET)) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC \<circ> SPECL [`s::A=>bool`; `t::A=>bool`] \<circ>
    GEN_REWRITE_RULE id [pairwise]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`X::A topology`; `c::A=>bool`; `t::A=>bool`]
        CONNECTED_IN_INTER_FRONTIER_OF) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `X frontier_of (s::A=>bool) \<subseteq> s \<and>
    X frontier_of (t::A=>bool) \<subseteq> t`
  STRIP_ASSUME_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_SIMP_TAC[FRONTIER_OF_SUBSET_CLOSED_IN]);;

lemma real_sierpinski_lemma:
   "a \<le> b \<and>
        countable u \<and> pairwise disjnt u \<and>
        (\<forall>c. c \<in> u \<Longrightarrow> real_closed c \<and> (c \<noteq> {})) \<and>
        \<Union>u = {a..b}
         \<Longrightarrow> u = {{a..b}}"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `subtopology euclideanreal {a..b}`
    LOCALLY_CONNECTED_NOT_COUNTABLE_CLOSED_UNION) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[REAL_INTERVAL_NE_EMPTY; REAL_POS] THEN
  ASM_SIMP_TAC[CONNECTED_SPACE_SUBTOPOLOGY;
               CONNECTED_IN_EUCLIDEANREAL_INTERVAL;
               LOCALLY_CONNECTED_REAL_INTERVAL] THEN
  CONJ_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC COMPLETELY_METRIZABLE_SPACE_CLOSED_IN THEN
    REWRITE_TAC[COMPLETELY_METRIZABLE_SPACE_EUCLIDEANREAL] THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_IN_SUBSET_TOPSPACE THEN
    ASM_SIMP_TAC[GSYM REAL_CLOSED_IN] THEN ASM SET_TAC[]]);;


subsection\<open>Size bounds on connected or path-connected spaces\<close>


lemma connected_space_imp_card_ge_alt:
   "connected_space X \<and> completely_regular_space X \<and>
        closedin X s \<and> (s \<noteq> {}) \<and> (s \<noteq> topspace X)
        \<Longrightarrow> UNIV \<lesssim> topspace X"
oops
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET) THEN
  SUBGOAL_THEN `\<exists>a::A. a \<in> topspace X \<and> (a \<notin> s)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `{0..1}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
    MATCH_MP_TAC CARD_EQ_REAL_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`0::real`; `1::real`] THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LT_01; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [completely_regular_space]) THEN
  DISCH_THEN(MP_TAC \<circ> SPECL [`s::A=>bool`; `a::A`]) THEN
  ASM_REWRITE_TAC[LE_C; IN_DIFF; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f::A=>real` THEN STRIP_TAC THEN
  X_GEN_TAC `t::real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  FIRST_ASSUM
   (MP_TAC \<circ> SPEC `topspace X::A=>bool` \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONNECTED_IN_CONTINUOUS_MAP_IMAGE)) THEN
  ASM_REWRITE_TAC[CONNECTED_IN_TOPSPACE] THEN
  REWRITE_TAC[CONNECTED_IN_EUCLIDEANREAL; is_interval] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`0::real`; `1::real`] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET)) THEN
  ASM SET_TAC[]);;

lemma connected_space_imp_card_ge_gen:
   "\<And>X s t::A=>bool.
        connected_space X \<and> normal_space X \<and>
        closedin X s \<and> closedin X t \<and>
        (s \<noteq> {}) \<and> (t \<noteq> {}) \<and> disjnt s t
        \<Longrightarrow> UNIV \<lesssim> topspace X"
oops
  REPEAT STRIP_TAC THEN
  TRANS_TAC CARD_LE_TRANS `{0..1}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
    MATCH_MP_TAC CARD_EQ_REAL_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`0::real`; `1::real`] THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LT_01; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [NORMAL_SPACE_IFF_URYSOHN]) THEN
  DISCH_THEN(MP_TAC \<circ> SPECL [`s::A=>bool`; `t::A=>bool`]) THEN
  ASM_REWRITE_TAC[LE_C; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f::A=>real` THEN STRIP_TAC THEN
  X_GEN_TAC `t::real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  FIRST_ASSUM
   (MP_TAC \<circ> SPEC `topspace X::A=>bool` \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONNECTED_IN_CONTINUOUS_MAP_IMAGE)) THEN
  ASM_REWRITE_TAC[CONNECTED_IN_TOPSPACE] THEN
  REWRITE_TAC[CONNECTED_IN_EUCLIDEANREAL; is_interval] THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`0::real`; `1::real`] THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET)) THEN
  ASM SET_TAC[]);;

lemma connected_space_imp_card_ge:
   "connected_space X \<and> normal_space X \<and>
        (t1_space X \<or> Hausdorff_space X) \<and>
        \<not> (\<exists>a. topspace X \<subseteq> {a})
        \<Longrightarrow> UNIV \<lesssim> topspace X"
oops
  GEN_TAC THEN REWRITE_TAC[T1_OR_HAUSDORFF_SPACE] THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_SPACE_IMP_CARD_GE_ALT THEN
  FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP (SET_RULE
   `\<not> (\<exists>a. s \<subseteq> {a}) \<Longrightarrow> \<exists>a b. a \<in> s \<and> b \<in> s \<and> (a \<noteq> b)`)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a::A`; `b::A`] THEN STRIP_TAC THEN
  EXISTS_TAC `{a::A}` THEN
  ASM_SIMP_TAC[NORMAL_IMP_COMPLETELY_REGULAR_SPACE_GEN] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[T1_SPACE_CLOSED_IN_SING]; ASM SET_TAC[]]);;

lemma connected_space_imp_infinite_gen:
   "connected_space X \<and> t1_space X \<and>
        \<not> (\<exists>a. topspace X \<subseteq> {a})
        \<Longrightarrow> infinite(topspace X)"
oops
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INFINITE_PERFECT_SET_GEN THEN
  EXISTS_TAC `X::A topology` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONNECTED_IN_IMP_PERFECT_GEN THEN
  ASM_REWRITE_TAC[CONNECTED_IN_TOPSPACE] THEN ASM SET_TAC[]);;

lemma connected_space_imp_infinite:
   "connected_space X \<and> Hausdorff_space X \<and>
        \<not> (\<exists>a. topspace X \<subseteq> {a})
        \<Longrightarrow> infinite(topspace X)"
oops
    MESON_TAC[CONNECTED_SPACE_IMP_INFINITE_GEN; HAUSDORFF_IMP_T1_SPACE]);;

lemma connected_space_imp_infinite_alt:
   "connected_space X \<and> regular_space X \<and>
        closedin X s \<and> (s \<noteq> {}) \<and> (s \<noteq> topspace X)
        \<Longrightarrow> infinite(topspace X)"
oops
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET) THEN
  SUBGOAL_THEN `\<exists>a::A. a \<in> topspace X \<and> (a \<notin> s)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `\<exists>u. (\<forall>n. disjnt (u n) s \<and> (a::A) \<in> u n \<and> openin X (u n)) \<and>
        (\<forall>n. u(Suc n) \<subset> u n)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
     [EXISTS_TAC `topspace X - s::A=>bool` THEN
      ASM_SIMP_TAC[IN_DIFF; OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n::num`; `v::A=>bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ>
      GEN_REWRITE_RULE id [GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN]) THEN
    REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN
    DISCH_THEN(MP_TAC \<circ> SPECL [`v::A=>bool`; `a::A`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `u::A=>bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `c::A=>bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `c::A=>bool = u` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC; ASM SET_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `u::A=>bool` \<circ>
        GEN_REWRITE_RULE id [CONNECTED_SPACE_CLOPEN_IN]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    SUBGOAL_THEN `\<forall>n. \<exists>x::A. x \<in> u n \<and> (x \<notin> u(Suc n))` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[SKOLEM_THM]] THEN
    REWRITE_TAC[INFINITE_CARD_LE; le_c; IN_UNIV; FORALL_AND_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f::num=>A` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[\<subseteq>; OPEN_IN_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC WLOG_LT THEN
    SUBGOAL_THEN `\<forall>m n. m < n \<Longrightarrow> \<not> (f m \<in> u n)` MP_TAC THENL
     [X_GEN_TAC `m::num`; ASM SET_TAC[]] THEN
    REWRITE_TAC[GSYM LE_SUC_LT] THEN
    SUBGOAL_THEN `\<forall>m n. m \<le> n \<Longrightarrow> U n \<subseteq> u m`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM SET_TAC[]]);;

lemma path_connected_space_imp_card_ge:
   "path_connected_space X \<and> Hausdorff_space X \<and>
        \<not> (\<exists>a. topspace X \<subseteq> {a})
        \<Longrightarrow> UNIV \<lesssim> topspace X"
oops
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP (SET_RULE
   `\<not> (\<exists>a. s \<subseteq> {a}) \<Longrightarrow> \<exists>a b. a \<in> s \<and> b \<in> s \<and> (a \<noteq> b)`)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a::A`; `b::A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> SPECL [`a::A`; `b::A`] \<circ>
    REWRITE_RULE[path_connected_space]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g::real=>A` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CARD_LE_SUBSET \<circ>
    MATCH_MP PATH_IMAGE_SUBSET_TOPSPACE) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CARD_LE_TRANS) THEN
  MP_TAC(ISPEC
   `subtopology X
     (image g (topspace (subtopology euclideanreal (real_interval [0,1]))))`
   CONNECTED_SPACE_IMP_CARD_GE) THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP PATH_IMAGE_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
  SIMP_TAC[SET_RULE `s \<subseteq> u \<Longrightarrow> u \<inter> s = s`] THEN
  DISCH_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[CONNECTED_SPACE_SUBTOPOLOGY; CONNECTED_IN_PATH_IMAGE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_HAUSDORFF_OR_REGULAR_IMP_NORMAL_SPACE THEN
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[COMPACT_IN_PATH_IMAGE; COMPACT_SPACE_SUBTOPOLOGY];
    MP_TAC ENDS_IN_UNIT_REAL_INTERVAL THEN ASM SET_TAC[]]);;

lemma connected_space_imp_uncountable:
   "connected_space X \<and> regular_space X \<and> Hausdorff_space X \<and>
        \<not> (\<exists>a. topspace X \<subseteq> {a})
        \<Longrightarrow> \<not> countable(topspace X)"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `X::A topology` CONNECTED_SPACE_IMP_CARD_GE) THEN
  ASM_SIMP_TAC[NOT_IMP; CARD_NOT_LE; COUNTABLE_IMP_CARD_LT_REAL] THEN
  MATCH_MP_TAC REGULAR_LINDELOF_IMP_NORMAL_SPACE THEN
  ASM_SIMP_TAC[COUNTABLE_IMP_LINDELOF_SPACE]);;

lemma path_connected_space_imp_uncountable:
   "path_connected_space X \<and> t1_space X \<and>
        \<not> (\<exists>a. topspace X \<subseteq> {a})
        \<Longrightarrow> \<not> countable(topspace X)"
oops
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP (SET_RULE
   `\<not> (\<exists>a. s \<subseteq> {a}) \<Longrightarrow> \<exists>a b. a \<in> s \<and> b \<in> s \<and> (a \<noteq> b)`)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a::A`; `b::A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`a::A`; `b::A`] \<circ>
    REWRITE_RULE[path_connected_space]) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM; pathin] THEN
  X_GEN_TAC `g::real=>A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`0::real`; `1::real`;
   `{{x. x \<in> topspace(subtopology euclideanreal ({0..1})) \<and>
          (g::real=>A) x \<in> {a}} |
     a \<in> topspace X} DELETE {}`] REAL_SIERPINSKI_LEMMA) THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; COUNTABLE_DELETE] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; IN_DELETE] THEN
  REWRITE_TAC[REAL_POS; NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] PAIRWISE_MONO)
     (SET_RULE `s - {a} \<subseteq> s`)) THEN
    REWRITE_TAC[PAIRWISE_IMAGE] THEN REWRITE_TAC[pairwise] THEN SET_TAC[];
    X_GEN_TAC `x::A` THEN REWRITE_TAC[IMP_IMP] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_CLOSED_IN] THEN
    MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN
    EXISTS_TAC `{0..1}` THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN; REAL_CLOSED_REAL_INTERVAL] THEN
    FIRST_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CLOSED_IN_CONTINUOUS_MAP_PREIMAGE)) THEN
    ASM_MESON_TAC[T1_SPACE_CLOSED_IN_SING];
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[UNIONS_IMAGE; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    REWRITE_TAC[UNIONS_DELETE_EMPTY; UNIONS_IMAGE] THEN ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `\<forall>a b. a \<in> s \<and> b \<in> s \<and> \<not> (f a = z) \<and> \<not> (f b = z) \<and> \<not> (f a = f b)
            \<Longrightarrow> \<not> (f ` s - {z} = {c})`) THEN
    MAP_EVERY EXISTS_TAC [`a::A`; `b::A`] THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    MATCH_MP_TAC(SET_RULE `(p \<and> q \<Longrightarrow> r) \<and> p \<and> q \<Longrightarrow> p \<and> q \<and> r`) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[GSYM MEMBER_NOT_EMPTY]] THEN
    CONJ_TAC THENL [EXISTS_TAC `0::real`; EXISTS_TAC `1::real`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    REWRITE_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_NE_EMPTY; REAL_POS]]);;


subsection\<open>The Tychonoff embedding\<close>


lemma completely_regular_space_cube_embedding_explicit:
   "completely_regular_space X \<and> Hausdorff_space X
        \<Longrightarrow> embedding_map
             (X,
              product_topology
                (mspace (submetric (cfunspace X real_euclidean_metric)
                  {f. f ` (topspace X) \<subseteq> real_interval [0,1]}))
                (\<lambda>f. subtopology euclideanreal (real_interval [0,1])))
             (\<lambda>x. RESTRICTION
                  (mspace (submetric (cfunspace X real_euclidean_metric)
                    {f. f ` (topspace X) \<subseteq> real_interval [0,1]}))
                  (\<lambda>f. f x))"
oops
  REPEAT STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`k = mspace(submetric (cfunspace X real_euclidean_metric)
                          {f. image f (topspace X::A=>bool) \<subseteq>
                               {0..1}})`;
    `e = \<lambda>x. RESTRICTION k (\<lambda>f::A=>real. f x)`] THEN
  SUBGOAL_THEN
   `\<forall>x y. x \<in> topspace X \<and> y \<in> topspace X
          \<Longrightarrow> ((e::A->(A=>real)->real) x = e y \<longleftrightarrow> x = y)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN STRIP_TAC THEN
    EQ_TAC THEN SIMP_TAC[] THEN GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN
    DISCH_TAC THEN EXPAND_TAC "e" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [completely_regular_space]) THEN
    DISCH_THEN(MP_TAC \<circ> SPECL [`{x::A}`; `y::A`]) THEN
    ASM_SIMP_TAC[IN_DIFF; IN_SING; CLOSED_IN_HAUSDORFF_SING] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; FORALL_UNWIND_THM2] THEN
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f::A=>real`THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC \<circ> C AP_THM `RESTRICTION(topspace X) f`) THEN
    ASM_REWRITE_TAC[RESTRICTION] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_X_ASSUM(MP_TAC \<circ> check (is_neg \<circ> concl)) THEN
    EXPAND_TAC "k" THEN REWRITE_TAC[SUBMETRIC] THEN
    SIMP_TAC[CFUNSPACE; IN_ELIM_THM; IN_INTER; RESTRICTION_IN_EXTENSIONAL] THEN
    REWRITE_TAC[REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
    SIMP_TAC[IMAGE_RESTRICTION; RESTRICTION_CONTINUOUS_MAP; SUBSET_REFL] THEN
    ASM_REWRITE_TAC[MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
    ASM_SIMP_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
    REWRITE_TAC[MBOUNDED_REAL_EUCLIDEAN_METRIC; real_bounded] THEN
    EXISTS_TAC `1` THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[real_abs];
    FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM INJECTIVE_ON_ALT])] THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `e':((A=>real)->real)->A`) THEN
  REWRITE_TAC[embedding_map; HOMEOMORPHIC_MAP_MAPS] THEN
  EXISTS_TAC `e':((A=>real)->real)->A` THEN
  ASM_REWRITE_TAC[homeomorphic_maps; TOPSPACE_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[IN_INTER; IMP_CONJ_ALT; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE; \<subseteq>; FORALL_IN_IMAGE] THEN
    EXPAND_TAC "e" THEN REWRITE_TAC[RESTRICTION_IN_EXTENSIONAL] THEN
    X_GEN_TAC `f::A=>real` THEN SIMP_TAC[RESTRICTION] THEN EXPAND_TAC "k" THEN
    REWRITE_TAC[SUBMETRIC; CFUNSPACE; IN_ELIM_THM] THEN
    SIMP_TAC[IN_ELIM_THM; CONTINUOUS_MAP_IN_SUBTOPOLOGY; ETA_AX; IN_INTER;
             MTOPOLOGY_REAL_EUCLIDEAN_METRIC];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_ATPOINTOF; TOPSPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[IN_INTER; IMP_CONJ_ALT; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x::A` THEN ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_REWRITE_TAC[LIMIT_ATPOINTOF] THEN DISCH_THEN(K ALL_TAC) THEN
  X_GEN_TAC `u::A=>bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`topspace X - u::A=>bool`; `x::A`] \<circ>
        GEN_REWRITE_RULE id [completely_regular_space]) THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE; IN_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `g::A=>real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_ALT; EXISTS_IN_GSPEC] THEN
  EXISTS_TAC
   `PiE (k:(A=>real)->bool)
      (\<lambda>f. if f = RESTRICTION (topspace X) g
           then {0..1} DELETE 1
           else {0..1})` THEN
  REWRITE_TAC[OPEN_IN_CARTESIAN_PRODUCT_GEN] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REPEAT(CONJ_TAC ORELSE DISJ2_TAC) THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{RESTRICTION (topspace X) (g::A=>real)}` THEN
    REWRITE_TAC[FINITE_SING; \<subseteq>; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(MATCH_MP_TAC OPEN_IN_HAUSDORFF_DELETE) THEN
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY;
                 HAUSDORFF_SPACE_EUCLIDEANREAL] THEN
    MESON_TAC[OPEN_IN_TOPSPACE; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY];
    ASM_SIMP_TAC[IN_INTER; FUN_IN_IMAGE] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE RAND_CONV
     [TOPSPACE_PRODUCT_TOPOLOGY]) THEN
    REWRITE_TAC[PiE; IN_ELIM_THM; o_THM;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[IN_DELETE] THEN FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP
     (REAL_ARITH `y = 0 \<Longrightarrow> x = y \<Longrightarrow> (x \<noteq> 1)`)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[RESTRICTION] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_DELETE; IN_INTER; IMP_CONJ] THEN
    X_GEN_TAC `y::A` THEN ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[PiE; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC \<circ> SPEC `RESTRICTION (topspace X) (g::A=>real)`)) THEN
    REWRITE_TAC[] THEN EXPAND_TAC "e" THEN REWRITE_TAC[] THEN
    SIMP_TAC[RESTRICTION] THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    ANTS_TAC THENL [EXPAND_TAC "k"; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[SUBMETRIC; CFUNSPACE; IN_ELIM_THM; IN_INTER] THEN
    REWRITE_TAC[RESTRICTION_IN_EXTENSIONAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; SUBSET_REFL] THEN
    ASM_SIMP_TAC[IMAGE_RESTRICTION; SUBSET_REFL] THEN
    ASM_REWRITE_TAC[REAL_EUCLIDEAN_METRIC; MTOPOLOGY_REAL_EUCLIDEAN_METRIC;
                    IN_UNIV] THEN
    MATCH_MP_TAC MBOUNDED_SUBSET THEN EXISTS_TAC `{0..1}` THEN
    ASM_REWRITE_TAC[MBOUNDED_REAL_EUCLIDEAN_METRIC;
                    REAL_BOUNDED_REAL_INTERVAL]]);;

lemma completely_regular_space_cube_embedding:
   "completely_regular_space X \<and> Hausdorff_space X
        \<Longrightarrow> \<exists>k:((A=>real)->bool) e.
               embedding_map
                (X,
                 product_topology k
                  (\<lambda>f. subtopology euclideanreal ({0..1})))
                e"
oops
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC \<circ> MATCH_MP
    COMPLETELY_REGULAR_SPACE_CUBE_EMBEDDING_EXPLICIT) THEN
  MESON_TAC[]);;


(* Urysohn and Tietze analogs for completely regular spaces if (()) set is  *)
(* assumed compact instead of closed. Note that Hausdorffness is *not*       *)
text\<open> required: inside () proof we factor through the Kolmogorov quotient.     \<close>


lemma Urysohn_completely_regular_closed_compact:
   "\<And>X s (t::A=>bool) a b.
        a \<le> b \<and> completely_regular_space X \<and>
        closedin X s \<and> compactin X t \<and> disjnt s t
        \<Longrightarrow> \<exists>f. continuous_map
                  (X,subtopology euclideanreal {a..b}) f \<and>
                (\<forall>x. x \<in> t \<Longrightarrow> f x = a) \<and>
                (\<forall>x. x \<in> s \<Longrightarrow> f x = b)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `\<exists>f. continuous_map
          (X,subtopology euclideanreal ({0..1})) f \<and>
        (\<forall>x. x \<in> t \<Longrightarrow> f x = 0) \<and>
        (\<forall>x::A. x \<in> s \<Longrightarrow> f x = 1)`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; \<subseteq>] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_REAL_INTERVAL; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f::A=>real` THEN STRIP_TAC THEN
    EXISTS_TAC `\<lambda>x. a + (b - a) * f x` THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_REAL_ADD; CONTINUOUS_MAP_REAL_LMUL;
                 CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_ADDR] THEN
    REWRITE_TAC[REAL_ARITH
      `a + (b - a) * y \<le> b \<longleftrightarrow> 0 \<le> (b - a) * (1 - y)`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE]] THEN
  ASM_CASES_TAC `t::A=>bool = {}` THENL
   [EXISTS_TAC `(\<lambda>x. 1):A=>real` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST; NOT_IN_EMPTY] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `\<forall>a. a \<in> t
        \<Longrightarrow> \<exists>f. continuous_map
                  (X,subtopology euclideanreal ({0..1})) f \<and>
                f a = 0 \<and> \<forall>x. x \<in> s \<Longrightarrow> f x = 1`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC \<circ> REWRITE_RULE[completely_regular_space]) THEN
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[];
    GEN_REWRITE_TAC (LAND_CONV \<circ> BINDER_CONV) [RIGHT_IMP_EXISTS_THM]] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g::A=>A->real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [compactin]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC \<circ> SPEC
    `{{x \<in> topspace X. (g::A=>A->real) a x \<in> {t. t < 1/2}} |
      a \<in> t}`)) THEN
  REWRITE_TAC[SIMPLE_IMAGE; EXISTS_FINITE_SUBSET_IMAGE; FORALL_IN_IMAGE] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `a::A` THEN DISCH_TAC THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `euclideanreal` THEN REWRITE_TAC[GSYM REAL_OPEN_IN] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
      ASM_SIMP_TAC[REAL_OPEN_HALFSPACE_LT; ETA_AX];
      MATCH_MP_TAC(SET_RULE
       `(\<forall>a. a \<in> s \<Longrightarrow> a \<in> f a) \<Longrightarrow> s \<subseteq> \<Union>(f ` s)`) THEN
      ASM_SIMP_TAC[IN_ELIM_THM] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `k::A=>bool` MP_TAC)] THEN
  ASM_CASES_TAC `k::A=>bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; SUBSET_EMPTY] THEN STRIP_TAC THEN
  EXISTS_TAC
   `\<lambda>x. 2 * max 0 (inf {(g::A=>A->real) a x | a \<in> k} - 1/2)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; \<subseteq>; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[REAL_ARITH `2 * max 0 (x - 1/2) = 0 \<longleftrightarrow> x \<le> 1/2`;
              REAL_ARITH `2 * max 0 (x - 1/2) = 1 \<longleftrightarrow> x = 1`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REWRITE_TAC[REAL_ARITH `0 \<le> 2 * max 0 a`;
              REAL_ARITH  `2 * max 0 (x - 1/2) \<le> 1 \<longleftrightarrow> x \<le> 1`] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_INF THEN REWRITE_TAC[ETA_AX] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p \<and> (p \<Longrightarrow> q) \<Longrightarrow> p \<and> q`) THEN CONJ_TAC THENL
   [X_GEN_TAC `x::A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_INF_LE THEN REWRITE_TAC[EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `0` THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a::A` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY;
     \<subseteq>; FORALL_IN_IMAGE; IN_REAL_INTERVAL]) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `x::A` THEN DISCH_TAC THENL
   [MATCH_MP_TAC REAL_INF_LE THEN REWRITE_TAC[EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `0`;
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[\<subseteq>; CLOSED_IN_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INF THEN
    ASM_REWRITE_TAC[SIMPLE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY; \<subseteq>;
   FORALL_IN_IMAGE; IN_REAL_INTERVAL; UNIONS_IMAGE; IN_ELIM_THM]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_REFL]);;

lemma Urysohn_completely_regular_compact_closed:
   "\<And>X s (t::A=>bool) a b.
        a \<le> b \<and> completely_regular_space X \<and>
        compactin X s \<and> closedin X t \<and> disjnt s t
        \<Longrightarrow> \<exists>f. continuous_map
                  (X,subtopology euclideanreal {a..b}) f \<and>
                (\<forall>x. x \<in> t \<Longrightarrow> f x = a) \<and>
                (\<forall>x. x \<in> s \<Longrightarrow> f x = b)"
oops
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
     [`X::A topology`; `t::A=>bool`; `s::A=>bool`;`-b::real`; `-a::real`]
    URYSOHN_COMPLETELY_REGULAR_CLOSED_COMPACT) THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; \<subseteq>; REAL_LE_NEG2] THEN
  ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
  REWRITE_TAC[REAL_ARITH `-b \<le> x \<and> x \<le>-a \<longleftrightarrow> a \<le>-x \<and>-x \<le> b`] THEN
  REWRITE_TAC[REAL_ARITH `x::real =-a \<longleftrightarrow>-x = a`] THEN
  DISCH_THEN(X_CHOOSE_THEN `f::A=>real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\<lambda>x. --(f x)` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_REAL_NEG_EQ]);;

lemma Urysohn_completely_regular_compact_closed_alt:
   "\<And>X s (t::A=>bool) a b.
        completely_regular_space X \<and>
        compactin X s \<and> closedin X t \<and> disjnt s t
        \<Longrightarrow> \<exists>f. continuous_map X euclideanreal f \<and>
                (\<forall>x. x \<in> t \<Longrightarrow> f x = a) \<and>
                (\<forall>x. x \<in> s \<Longrightarrow> f x = b)"
oops
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `a \<le> b \<or> b \<le> a`) THENL
   [MP_TAC(ISPECL
     [`X::A topology`; `s::A=>bool`; `t::A=>bool`; `a::real`; `b::real`]
     URYSOHN_COMPLETELY_REGULAR_COMPACT_CLOSED);
    MP_TAC(ISPECL
     [`X::A topology`; `t::A=>bool`; `s::A=>bool`; `b::real`; `a::real`]
     URYSOHN_COMPLETELY_REGULAR_CLOSED_COMPACT)] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN MESON_TAC[]);;

lemma Tietze_extension_completely_regular:
   "\<And>X f s t.
         completely_regular_space X \<and>
         compactin X s \<and> is_interval t \<and> (t \<noteq> {}) \<and>
         continuous_map (subtopology X s,euclideanreal) f \<and>
         (\<forall>x. x \<in> s \<Longrightarrow> f x \<in> t)
         \<Longrightarrow> \<exists>g. continuous_map X euclideanreal g \<and>
                 (\<forall>x. x \<in> topspace X \<Longrightarrow> g x \<in> t) \<and>
                 (\<forall>x. x \<in> s \<Longrightarrow> g x = f x)"
oops
  lemma lemma:
   "\<And>X f s t.
           completely_regular_space X \<and> Hausdorff_space X \<and>
           compactin X s \<and> is_interval t \<and> (t \<noteq> {}) \<and>
           continuous_map (subtopology X s,euclideanreal) f \<and>
           (\<forall>x. x \<in> s \<Longrightarrow> f x \<in> t)
           \<Longrightarrow> \<exists>g. continuous_map X euclideanreal g \<and>
                   (\<forall>x. x \<in> topspace X \<Longrightarrow> g x \<in> t) \<and>
                   (\<forall>x. x \<in> s \<Longrightarrow> g x = f x)"
oops
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `X::A topology` COMPLETELY_REGULAR_SPACE_CUBE_EMBEDDING) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:((A=>real)->bool)`; `e::A->(A=>real)->real`] THEN
    REWRITE_TAC[embedding_map; HOMEOMORPHIC_MAP_MAPS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `e':((A=>real)->real)->A` THEN ABBREV_TAC
     `cube:((A=>real)->real)topology =
      product_topology k
       (\<lambda>f. subtopology euclideanreal (real_interval [0,1]))` THEN
    REWRITE_TAC[homeomorphic_maps] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`cube:((A=>real)->real)topology`;
      `f \<circ> (e':((A=>real)->real)->A)`;
      `image (e::A->(A=>real)->real) s`;
      `t::real=>bool`] TIETZE_EXTENSION_REALINTERVAL) THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_HAUSDORFF_OR_REGULAR_IMP_NORMAL_SPACE THEN
        EXPAND_TAC "cube" THEN
        REWRITE_TAC[COMPACT_SPACE_PRODUCT_TOPOLOGY;
                    HAUSDORFF_SPACE_PRODUCT_TOPOLOGY] THEN
        SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY;
                 HAUSDORFF_SPACE_EUCLIDEANREAL] THEN
        SIMP_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL; COMPACT_SPACE_SUBTOPOLOGY];
        MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN CONJ_TAC THENL
         [EXPAND_TAC "cube" THEN
          SIMP_TAC[HAUSDORFF_SPACE_PRODUCT_TOPOLOGY;
                   HAUSDORFF_SPACE_SUBTOPOLOGY;
                   HAUSDORFF_SPACE_EUCLIDEANREAL];
          MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `X::A topology` THEN
          ASM_MESON_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY]];
        MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
        EXISTS_TAC `subtopology X (s::A=>bool)` THEN
        ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ]
            CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO)) THEN
          ASM_SIMP_TAC[COMPACT_IN_SUBSET_TOPSPACE; IMAGE_SUBSET];
          REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
          MATCH_MP_TAC(SET_RULE
           `(\<forall>x. x \<in> s \<Longrightarrow> f(g x) = x)
            \<Longrightarrow> image f (u \<inter> g ` s) \<subseteq> s`) THEN
          FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
          ASM SET_TAC[]];
        FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
        ASM SET_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `g:((A=>real)->real)->real`
        STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(g:((A=>real)->real)->real) \<circ> (e::A->(A=>real)->real)` THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_COMPOSE];
        REWRITE_TAC[o_THM] THEN
        FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP
          CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE)) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]]])
in

  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q::A=>bool = image (Kolmogorov_quotient X) (topspace X)` THEN
  MP_TAC(ISPECL
   [`X::A topology`; `euclideanreal`; `f::A=>real`; `s::A=>bool`]
   KOLMOGOROV_QUOTIENT_LIFT_EXISTS) THEN
  SIMP_TAC[HAUSDORFF_IMP_T0_SPACE; HAUSDORFF_SPACE_EUCLIDEANREAL] THEN
  ASM_SIMP_TAC[COMPACT_IN_SUBSET_TOPSPACE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g::A=>real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`subtopology X (q::A=>bool)`; `g::A=>real`;
    `image (Kolmogorov_quotient X) (s::A=>bool)`;
    `t::real=>bool`]
   lemma) THEN
  ASM_SIMP_TAC[COMPLETELY_REGULAR_SPACE_SUBTOPOLOGY; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY] THEN
  EXPAND_TAC "q" THEN REWRITE_TAC[IN_INTER; IMP_CONJ_ALT; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[COMPACT_IN_SUBSET_TOPSPACE; SET_RULE
   `s \<subseteq> u \<Longrightarrow> f ` u \<inter> f ` s = f ` s`] THEN
  SIMP_TAC[KOLMOGOROV_QUOTIENT_IN_TOPSPACE] THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC `X::A topology` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
      REWRITE_TAC[CONTINUOUS_MAP_KOLMOGOROV_QUOTIENT];
      MATCH_MP_TAC REGULAR_T0_IMP_HAUSDORFF_SPACE THEN
      ASM_SIMP_TAC[REGULAR_SPACE_SUBTOPOLOGY;
                   COMPLETELY_REGULAR_IMP_REGULAR_SPACE] THEN
      EXPAND_TAC "q" THEN REWRITE_TAC[T0_SPACE_KOLMOGOROV_QUOTIENT]];
    DISCH_THEN(X_CHOOSE_THEN `h::A=>real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(h::A=>real) \<circ> Kolmogorov_quotient X` THEN
    ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology X (q::A=>bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    REWRITE_TAC[CONTINUOUS_MAP_KOLMOGOROV_QUOTIENT]]);;


subsection\<open>Embedding in products and hence more about completely metrizable spaces\<close>


lemma gdelta_homeomorphic_space_closedin_product:
   "\<And>X (s::K=>A->bool) k.
        metrizable_space X \<and> (\<forall>i. i \<in> k \<Longrightarrow> openin X(s i))
        \<Longrightarrow> \<exists>t. closedin
                 (prod_topology X (product_topology k (\<lambda>i. euclideanreal)))
                 t \<and>
                 subtopology X (\<Inter> {s i | i \<in> k}) homeomorphic_space
                 subtopology
                  (prod_topology X (product_topology k (\<lambda>i. euclideanreal)))
                  t"
oops
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_METRIZABLE_SPACE] THEN
  MAP_EVERY X_GEN_TAC [`m::A metric`; `s::K=>A->bool`; `k::K=>bool`] THEN
  DISCH_TAC THEN ASM_CASES_TAC `k::K=>bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; SET_RULE `{f x |x| False} = {}`] THEN
    REWRITE_TAC[INTERS_0; SUBTOPOLOGY_UNIV;
                PRODUCT_TOPOLOGY_EMPTY_DISCRETE] THEN
    EXISTS_TAC
     `(M::A=>bool) \<times> {(\<lambda>x. undefined):K=>real}` THEN
    REWRITE_TAC[CLOSED_IN_CROSS; CLOSED_IN_MSPACE] THEN
    REWRITE_TAC[CLOSED_IN_DISCRETE_TOPOLOGY; SUBSET_REFL] THEN
    REWRITE_TAC[SUBTOPOLOGY_CROSS; SUBTOPOLOGY_MSPACE] THEN
    MATCH_MP_TAC(CONJUNCT1 HOMEOMORPHIC_SPACE_PROD_TOPOLOGY_SING) THEN
    REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; IN_SING];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `\<forall>i. i \<in> k \<Longrightarrow> (s::K=>A->bool) i \<subseteq> M`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET; TOPSPACE_MTOPOLOGY]; ALL_TAC] THEN
  SUBGOAL_THEN `\<Inter> {(s::K=>A->bool) i | i \<in> k} \<subseteq> M`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN ABBREV_TAC
   `d::K=>A->real =
    \<lambda>i. if (i \<notin> k) \<or> s i = M then \<lambda>a. 1
        else \<lambda>a. inf {d a x |x| x \<in> M - s i}` THEN
  SUBGOAL_THEN
   `\<forall>i. continuous_map (subtopology mtopology (s i),euclideanreal)
        ((d::K=>A->real) i)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i::K` THEN EXPAND_TAC "d" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET; IMP_CONJ; GSYM TOPSPACE_MTOPOLOGY; SET_RULE
                  `s \<subseteq> u \<Longrightarrow> ((s \<noteq> u) \<longleftrightarrow> \<not> (u - s = {}))`] THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM MTOPOLOGY_SUBMETRIC;
                GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
    MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_IMP_CONTINUOUS_MAP THEN
    REWRITE_TAC[Lipschitz_continuous_map; REAL_EUCLIDEAN_METRIC] THEN
    REWRITE_TAC[SUBSET_UNIV; SUBMETRIC] THEN EXISTS_TAC `1::real` THEN
    MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN
    REWRITE_TAC[IN_INTER; REAL_MUL_LID] THEN STRIP_TAC THEN
    EXPAND_TAC "d" THEN REWRITE_TAC[REAL_ARITH
     `abs(x - y) \<le> d \<longleftrightarrow> x - d \<le> y \<and> y - d \<le> x`] THEN
    CONJ_TAC THEN
    W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand) REAL_LE_INF_EQ \<circ> snd) THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_DIFF] THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[MDIST_POS_LE]; DISCH_THEN SUBST1_TAC]) THEN
    X_GEN_TAC `z::A` THEN STRIP_TAC THEN REWRITE_TAC[REAL_LE_SUB_RADD] THENL
     [TRANS_TAC REAL_LE_TRANS `d y::A z`;
      TRANS_TAC REAL_LE_TRANS `d x::A z`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC INF_LE_ELEMENT THEN
       CONJ_TAC THENL [EXISTS_TAC `0`; ASM SET_TAC[]] THEN
       ASM_SIMP_TAC[FORALL_IN_IMAGE; IN_DIFF; MDIST_POS_LE];
       MAP_EVERY UNDISCH_TAC
        [`(x::A) \<in> M`; `(y::A) \<in> M`; `(z::A) \<in> M`] THEN
       CONV_TAC METRIC_ARITH]);
    ALL_TAC] THEN
  SUBGOAL_THEN `\<forall>i x. x \<in> s i \<Longrightarrow> 0 < (d::K=>A->real) i x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "d" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_01] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [DE_MORGAN_THM]) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET; IMP_CONJ; GSYM TOPSPACE_MTOPOLOGY; SET_RULE
                  `s \<subseteq> u \<Longrightarrow> ((s \<noteq> u) \<longleftrightarrow> \<not> (u - s = {}))`] THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`m::A metric`; `(s::K=>A->bool) i`] OPEN_IN_MTOPOLOGY) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `x::A`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[\<subseteq>; IN_MBALL; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r::real` THEN STRIP_TAC THEN
    TRANS_TAC REAL_LTE_TRANS `r::real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INF THEN
    ASM_REWRITE_TAC[FORALL_IN_GSPEC; GSYM REAL_NOT_LT] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> SPEC `i::K`) THEN ASM_REWRITE_TAC[]) THEN
    REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `f = \<lambda>x. x,(\<lambda>i\<in>k. inverse((d::K=>A->real) i x))` THEN
  EXISTS_TAC `image (f::A=>A#(K=>real)) (\<Inter> {s(i::K) | i \<in> k})` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(snd(EQ_IMP_RULE(ISPECL
     [`subtopology mtopology (\<Inter> {(s::K=>A->bool) i | i \<in> k})`;
      `product_topology (k::K=>bool) (\<lambda>i. euclideanreal)`;
      `\<lambda>x. (\<lambda>i\<in>k. inverse((d::K=>A->real) i x))`]
        EMBEDDING_MAP_GRAPH))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE; \<subseteq>; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[RESTRICTION_IN_EXTENSIONAL] THEN X_GEN_TAC `i::K` THEN
      SIMP_TAC[RESTRICTION] THEN DISCH_TAC THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_INV THEN CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP
         (REWRITE_RULE[IMP_CONJ] CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO) \<circ>
         SPEC `i::K`) THEN
        ASM SET_TAC[];
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; INTERS_GSPEC] THEN
        ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_NZ]];
      DISCH_THEN(MP_TAC \<circ> MATCH_MP EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; TOPSPACE_MTOPOLOGY] THEN
      REWRITE_TAC[PROD_TOPOLOGY_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
       `(\<forall>x. x \<in> s \<Longrightarrow> f x \<in> t) \<Longrightarrow> t \<inter> f ` s = f ` s`) THEN
      SIMP_TAC[TOPSPACE_PRODUCT_TOPOLOGY; o_DEF; TOPSPACE_EUCLIDEANREAL] THEN
      EXPAND_TAC "f" THEN SIMP_TAC[IN_CROSS] THEN
      REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT; IN_UNIV]]] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN CONJ_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
    REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; IN_CROSS] THEN
    REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT; IN_UNIV] THEN
    ASM_REWRITE_TAC[GSYM \<subseteq>; TOPSPACE_MTOPOLOGY];
    ALL_TAC] THEN
  GEN_REWRITE_TAC id [\<subseteq>] THEN REWRITE_TAC[closure_of] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY] THEN
  MAP_EVERY X_GEN_TAC [`x::A`; `ds::K=>real`] THEN
  REWRITE_TAC[IN_CROSS; TOPSPACE_MTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[o_THM; TOPSPACE_EUCLIDEANREAL; IN_UNIV; PiE] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC \<circ> GENL [`u::A=>bool`; `v:(K=>real)->bool`] \<circ>
    SPEC `(u::A=>bool) \<times> (v:(K=>real)->bool)`) THEN
  REWRITE_TAC[IN_CROSS; OPEN_IN_CROSS; SET_RULE
   `(x \<in> s \<and> y \<in> t) \<and> (s = {} \<or> t = {} \<or> R s t) \<longleftrightarrow>
    x \<in> s \<and> y \<in> t \<and> R s t`] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x \<in> \<Inter> {(s::K=>A->bool) i | i \<in> k}` ASSUME_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `i::K` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC id [TAUT `p \<longleftrightarrow> \<not> p \<Longrightarrow> False`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPECL
     [`mball m (x::A,inverse(abs(ds(i::K)) + 1))`;
      `{z. z \<in> topspace(product_topology k (\<lambda>i. euclideanreal)) \<and>
            (z::K=>real) i \<in> real_interval(ds i - 1,ds i + 1)}`]) THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CENTRE_IN_MBALL THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; TOPSPACE_EUCLIDEANREAL; o_DEF;
                      PiE; IN_ELIM_THM; IN_UNIV];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[OPEN_IN_MBALL];
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `euclideanreal` THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION] THEN
      REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL];
      ALL_TAC] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM; IN_CROSS; IN_ELIM_THM] THEN
    X_GEN_TAC `y::A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC \<circ> SPEC `i::K`) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    DISCH_THEN(MP_TAC \<circ> CONJUNCT2) THEN ASM_REWRITE_TAC[RESTRICTION] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[IN_MBALL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN
    TRANS_TAC REAL_LE_TRANS `(d::K=>A->real) i y` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LINV THEN ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [IN_REAL_INTERVAL]) THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "d" THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]] THEN
      MATCH_MP_TAC INF_LE_ELEMENT THEN CONJ_TAC THENL
       [EXISTS_TAC `0` THEN
        ASM_SIMP_TAC[FORALL_IN_GSPEC; IN_DIFF; MDIST_POS_LE];
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `x::A` THEN
        ASM_REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[MDIST_SYM]]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x::A` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "f" THEN REWRITE_TAC[PAIR_EQ] THEN
    GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC `i::K` THEN
    REWRITE_TAC[RESTRICTION] THEN
    COND_CASES_TAC THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[EXTENSIONAL]) THEN ASM SET_TAC[]] THEN
    REWRITE_TAC[REAL_ARITH `x = y \<longleftrightarrow> \<not> (0 < abs(x - y))`] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC \<circ>
      MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_MAP_REAL_INV) \<circ>
      SPEC `i::K`) THEN
    ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; REAL_LT_IMP_NZ; IN_INTER] THEN
    ABBREV_TAC `e = abs (ds i - inverse((d::K=>A->real) i x))` THEN
    REWRITE_TAC[continuous_map] THEN DISCH_THEN(MP_TAC \<circ> SPEC
     `real_interval(inverse((d::K=>A->real) i x) - e / 2,inverse(d i x) + e / 2)` \<circ>
     CONJUNCT2) THEN
    REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL] THEN
    ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; TOPSPACE_MTOPOLOGY] THEN
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
    DISCH_THEN(X_CHOOSE_THEN `u::A=>bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPECL
     [`u::A=>bool`;
      `{z. z \<in> topspace(product_topology k (\<lambda>i::K. euclideanreal)) \<and>
            z i \<in> real_interval(ds i - e / 2,ds i + e / 2)}`]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (SET_RULE
       `s = u \<inter> t \<Longrightarrow> x \<in> s \<Longrightarrow>  x \<in> u`)) THEN
      REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
      REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; PiE] THEN
      ASM_REWRITE_TAC[o_THM; TOPSPACE_EUCLIDEANREAL; IN_UNIV; IN_ELIM_THM];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `euclideanreal` THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION] THEN
      REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL];
      ALL_TAC] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[IN_CROSS; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[RESTRICTION; NOT_EXISTS_THM] THEN X_GEN_TAC `y::A` THEN
    GEN_REWRITE_TAC RAND_CONV [CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    FIRST_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (SET_RULE
     `t = u \<inter> s i
      \<Longrightarrow> i \<in> k \<and> (y \<notin> t)
          \<Longrightarrow> y \<in> \<Inter> {s i | i  \<in> k} \<and> y \<in> u \<Longrightarrow> False`)) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC \<circ> CONJUNCT2) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> CONJUNCT2) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN
    EXPAND_TAC "e" THEN REAL_ARITH_TAC]);;

lemma open_homeomorphic_space_closedin_product:
   "\<And>X (s::A=>bool).
        metrizable_space X \<and> openin X s
        \<Longrightarrow> \<exists>t. closedin (prod_topology X euclideanreal) t \<and>
                subtopology X s homeomorphic_space
                subtopology (prod_topology X euclideanreal) t"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X::A topology`; `(\<lambda>x. s):1=>A->bool`; `{()}`]
        GDELTA_HOMEOMORPHIC_SPACE_CLOSED_IN_PRODUCT) THEN
  ASM_REWRITE_TAC[SET_RULE `\<Inter> {s.i| i \<in> {a}} = s`] THEN
  DISCH_THEN(X_CHOOSE_THEN `t::A#(1=>real)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `prod_topology X (product_topology {()} (\<lambda>i. euclideanreal))
    homeomorphic_space prod_topology X euclideanreal`
  MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_SPACE_PROD_TOPOLOGY THEN
    REWRITE_TAC[HOMEOMORPHIC_SPACE_SINGLETON_PRODUCT; HOMEOMORPHIC_SPACE_REFL];
    REWRITE_TAC[HOMEOMORPHIC_SPACE; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `f::A#(1=>real)->A#real` THEN DISCH_TAC THEN
  EXISTS_TAC `image (f::A#(1=>real)->A#real) t` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_MAP_CLOSEDNESS_EQ]; ALL_TAC] THEN
  REWRITE_TAC[GSYM HOMEOMORPHIC_SPACE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      HOMEOMORPHIC_SPACE_TRANS)) THEN
  REWRITE_TAC[HOMEOMORPHIC_SPACE] THEN EXISTS_TAC `f::A#(1=>real)->A#real` THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP]) THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET) THEN ASM SET_TAC[]);;

lemma completely_metrizable_space_gdelta_in_alt:
   "completely_metrizable_space X \<and>
        (countable intersection_of openin X) s
        \<Longrightarrow> completely_metrizable_space (subtopology X s)"
oops
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_INTERSECTION_OF] THEN
  X_GEN_TAC `X::A topology` THEN DISCH_TAC THEN
  X_GEN_TAC `u:(A=>bool)->bool` THEN REPEAT DISCH_TAC THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X::A topology`; `(\<lambda>x::A=>bool. x)`; `u:(A=>bool)->bool`]
        GDELTA_HOMEOMORPHIC_SPACE_CLOSED_IN_PRODUCT) THEN
  ASM_SIMP_TAC[COMPLETELY_METRIZABLE_IMP_METRIZABLE_SPACE; IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c::A#((A=>bool)->real)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC \<circ>
    MATCH_MP HOMEOMORPHIC_COMPLETELY_METRIZABLE_SPACE) THEN
  MATCH_MP_TAC COMPLETELY_METRIZABLE_SPACE_CLOSED_IN THEN
  ASM_REWRITE_TAC[COMPLETELY_METRIZABLE_SPACE_PROD_TOPOLOGY] THEN
  REWRITE_TAC[COMPLETELY_METRIZABLE_SPACE_EUCLIDEANREAL;
              COMPLETELY_METRIZABLE_SPACE_PRODUCT_TOPOLOGY] THEN
  ASM_SIMP_TAC[COUNTABLE_RESTRICT]);;

lemma completely_metrizable_space_gdelta_in:
   "completely_metrizable_space X \<and> gdelta_in X s
        \<Longrightarrow> completely_metrizable_space (subtopology X s)"
oops
  SIMP_TAC[GDELTA_IN_ALT; COMPLETELY_METRIZABLE_SPACE_GDELTA_IN_ALT]);;

lemma completely_metrizable_space_openin:
   "completely_metrizable_space X \<and> openin X s
        \<Longrightarrow> completely_metrizable_space (subtopology X s)"
oops
  SIMP_TAC[COMPLETELY_METRIZABLE_SPACE_GDELTA_IN; OPEN_IMP_GDELTA_IN]);;

lemma locally_compact_imp_completely_metrizable_space:
   "metrizable_space X \<and> locally_compact_space X
        \<Longrightarrow> completely_metrizable_space X"
oops
  REWRITE_TAC[IMP_CONJ; FORALL_METRIZABLE_SPACE] THEN
  X_GEN_TAC `m::A metric` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `m::A metric` METRIC_COMPLETION) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m':(A=>real)metric`; `f::A=>A->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `mtopology homeomorphic_space
    subtopology (mtopology m') (image (f::A=>A->real) (M))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m::A metric`; `m':(A=>real)metric`; `f::A=>A->real`]
        ISOMETRY_IMP_EMBEDDING_MAP) THEN
    ASM_SIMP_TAC[SUBSET_REFL] THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC \<circ>
    MATCH_MP HOMEOMORPHIC_COMPLETELY_METRIZABLE_SPACE) THEN
  FIRST_X_ASSUM(MP_TAC \<circ>
    MATCH_MP HOMEOMORPHIC_LOCALLY_COMPACT_SPACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC \<circ> MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ_ALT] (REWRITE_RULE[CONJ_ASSOC]
        LOCALLY_COMPACT_SUBSPACE_OPEN_IN_CLOSURE_OF))) THEN
  ASM_REWRITE_TAC[HAUSDORFF_SPACE_MTOPOLOGY; SUBTOPOLOGY_MSPACE] THEN
  ASM_REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN DISCH_TAC THEN
  MATCH_MP_TAC COMPLETELY_METRIZABLE_SPACE_OPEN_IN THEN
  ASM_SIMP_TAC[COMPLETELY_METRIZABLE_SPACE_MTOPOLOGY]);;

lemma completely_metrizable_space_imp_gdelta_in:
   "metrizable_space X \<and> s \<subseteq> topspace X \<and>
        completely_metrizable_space (subtopology X s)
        \<Longrightarrow> gdelta_in X s"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X::A topology`; `s::A=>bool`;
                 `subtopology X s::A topology`; `\<lambda>x::A. x`]
        LAVRENTIEV_EXTENSION) THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_ID; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u::A=>bool`; `f::A=>A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s::A=>bool = u` (fun th -> ASM_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; GDELTA_IN_SUBSET] THEN
  MATCH_MP_TAC(SET_RULE
    `(\<forall>x. x \<in> u \<Longrightarrow> f x = x) \<Longrightarrow> f ` u \<subseteq> s \<Longrightarrow> u \<subseteq> s`) THEN
  MP_TAC(ISPECL
   [`subtopology X u::A topology`; `subtopology X u::A topology`;
   `f::A=>A`; `\<lambda>x::A. x`] FORALL_IN_CLOSURE_OF_EQ) THEN
  ASM_SIMP_TAC[CLOSURE_OF_SUBTOPOLOGY; CONTINUOUS_MAP_ID; SET_RULE
   `s \<subseteq> u \<Longrightarrow> u \<inter> s = s`] THEN
  ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY;
               METRIZABLE_IMP_HAUSDORFF_SPACE] THEN
  UNDISCH_TAC
   `continuous_map (subtopology X u,subtopology X s) (f::A=>A)` THEN
  SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

lemma completely_metrizable_space_eq_gdelta_in:
   "completely_metrizable_space X \<and> s \<subseteq> topspace X
        \<Longrightarrow> (completely_metrizable_space (subtopology X s) \<longleftrightarrow>
             gdelta_in X s)"
oops
  MESON_TAC[COMPLETELY_METRIZABLE_SPACE_GDELTA_IN;
            COMPLETELY_METRIZABLE_SPACE_IMP_GDELTA_IN;
            COMPLETELY_METRIZABLE_IMP_METRIZABLE_SPACE]);;

lemma gdelta_in_eq_completely_metrizable_space:
   "completely_metrizable_space X
        \<Longrightarrow> (gdelta_in X s \<longleftrightarrow>
             s \<subseteq> topspace X \<and>
             completely_metrizable_space (subtopology X s))"
oops
  MESON_TAC[GDELTA_IN_ALT; COMPLETELY_METRIZABLE_SPACE_EQ_GDELTA_IN]);;


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


text\<open> Theorems from Kuratowski's "Remark on an Invariance Theorem", Fundamenta  \<close>
(* Mathematicae vol 37 (1950), pp. 251-252. The idea is that in suitable     *)
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
