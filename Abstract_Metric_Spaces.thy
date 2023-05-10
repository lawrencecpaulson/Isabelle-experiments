section \<open>Abstract Metric Spaces\<close>

theory Abstract_Metric_Spaces
  imports
    "HOL-Analysis.Analysis" "HOL-ex.Sketch_and_Explore"
begin

lemma ball_iff_cball: "(\<exists>r>0. ball x r \<subseteq> U) \<longleftrightarrow> (\<exists>r>0. cball x r \<subseteq> U)"
  by (meson mem_interior mem_interior_cball)

thm closedin_subtopology
lemma closedin_subset_topspace:
   "\<lbrakk>closedin X S; S \<subseteq> T\<rbrakk> \<Longrightarrow> closedin (subtopology X T) S"
  using closedin_subtopology by fastforce

lemma open_subset_closure_of_interval:
  assumes "open U" "is_interval S"
  shows "U \<subseteq> closure S \<longleftrightarrow> U \<subseteq> interior S"
  by (metis assms convex_interior_closure is_interval_convex open_subset_interior)

thm real_grow_shrink
lemma real_shrink_Galois:
  fixes x::real
  shows "(x / (1 + \<bar>x\<bar>) = y) \<longleftrightarrow> (\<bar>y\<bar> < 1 \<and> y / (1 - \<bar>y\<bar>) = x)"
  using real_grow_shrink by (fastforce simp add: distrib_left)

lemma real_shrink_lt:
  fixes x::real
  shows "x / (1 + \<bar>x\<bar>) < y / (1 + \<bar>y\<bar>) \<longleftrightarrow> x < y"
  using zero_less_mult_iff [of x y] by (auto simp: field_simps abs_if not_less)

lemma real_shrink_le:
  fixes x::real
  shows "x / (1 + \<bar>x\<bar>) \<le> y / (1 + \<bar>y\<bar>) \<longleftrightarrow> x \<le> y"
  by (meson linorder_not_le real_shrink_lt)

lemma real_shrink_grow:
  fixes x::real
  shows "\<bar>x\<bar> < 1 \<Longrightarrow> x / (1 - \<bar>x\<bar>) / (1 + \<bar>x / (1 - \<bar>x\<bar>)\<bar>) = x"
  using real_shrink_Galois by blast

lemma continuous_shrink:
  "continuous_on UNIV (\<lambda>x::real. x / (1 + \<bar>x\<bar>))"
  by (intro continuous_intros) auto

lemma strict_mono_shrink:
  "strict_mono (\<lambda>x::real. x / (1 + \<bar>x\<bar>))"
  by (simp add: monotoneI real_shrink_lt)

lemma shrink_range: "(\<lambda>x::real. x / (1 + \<bar>x\<bar>)) ` S \<subseteq> {-1<..<1}"
  by (auto simp: divide_simps)

lemma is_interval_shrink:
  fixes S :: "real set"
  shows "is_interval ((\<lambda>x. x / (1 + \<bar>x\<bar>)) ` S) \<longleftrightarrow> is_interval S"  (is "?lhs = ?rhs")
proof 
  assume "?lhs"
  then have "is_interval ((\<lambda>x. x / (1 - \<bar>x\<bar>)) ` (\<lambda>x. x / (1 + \<bar>x\<bar>)) ` S)"
    by (metis continuous_on_real_grow shrink_range connected_continuous_image 
              is_interval_connected_1 continuous_on_subset)
  then show "?rhs"
    using real_grow_shrink by (force simp add: image_comp)
next
  assume ?rhs
  then show ?lhs
    using connected_continuous_image is_interval_connected_1
    by (metis continuous_on_subset continuous_shrink subset_UNIV)
qed


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
  "eventually P (atin_within X a S) \<longleftrightarrow> a \<notin> topspace X \<or>
   (\<exists>T. openin X T \<and> a \<in> T \<and> (\<forall>x\<in>T. x \<in> S \<and> x \<noteq> a \<longrightarrow> P x))"
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
      
subsection\<open>Metric spaces\<close>

(*Avoid a clash with the existing metric_space locale (from the type class)*)
locale Metric_space =
  fixes M :: "'a set" and d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes nonneg [simp]: "\<And>x y. 0 \<le> d x y"
  assumes commute: "\<And>x y. d x y = d y x"
  assumes zero [simp]: "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> d x y = 0 \<longleftrightarrow> x=y"
  assumes triangle: "\<And>x y z. \<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> d x z \<le> d x y + d y z"

text \<open>Link with the type class version\<close>
interpretation Met: Metric_space UNIV dist
  by (simp add: dist_commute dist_triangle Metric_space.intro)

(*NOT CLEAR WHETHER WE NEED/WANT THIS type definition*)
typedef 'a metric = "{(M::'a set,d). Metric_space M d}"
  morphisms "dest_metric" "metric"
proof -
  have "Metric_space {} (\<lambda>x y. 0)"
    by (auto simp: Metric_space_def)
  then show ?thesis
    by blast
qed

definition mspace where "mspace m = fst (dest_metric m)"

definition mdist where "mdist m = snd (dest_metric m)"

lemma metric_space_mspace_mdist: "Metric_space (mspace m) (mdist m)"
  by (metis Product_Type.Collect_case_prodD dest_metric mdist_def mspace_def)

context Metric_space
begin

(*
lemma metric [simp]:
   "mspace (metric (M,d)) = M \<and> mdist (metric (M,d)) = d"
  by (simp add: local.Metric_space_axioms mdist_def metric_inverse mspace_def)
*)

lemma subspace: "M' \<subseteq> M \<Longrightarrow> Metric_space M' d"
  by (simp add: commute in_mono Metric_space.intro triangle)

lemma abs_mdist [simp] : "\<bar>d x y\<bar> = d x y"
  by simp

lemma mdist_pos_less: "\<lbrakk>x \<noteq> y; x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> 0 < d x y"
  by (metis less_eq_real_def nonneg zero)

lemma mdist_zero [simp]: "x \<in> M \<Longrightarrow> d x x = 0"
  by simp

lemma mdist_pos_eq [simp]: "\<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> 0 < d x y \<longleftrightarrow> x \<noteq> y"
  using mdist_pos_less zero by fastforce

lemma triangle': "\<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> d x z \<le> d x y + d z y"
  by (simp add: commute triangle)

lemma triangle'': "\<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> d x z \<le> d y x + d y z"
  by (simp add: commute triangle)

lemma mdist_reverse_triangle: "\<lbrakk>x \<in> M; y \<in> M; z \<in> M\<rbrakk> \<Longrightarrow> \<bar>d x y - d y z\<bar> \<le> d x z"
  by (smt (verit) commute triangle)

text\<open> Open and closed balls                                                                \<close>

definition mball where "mball x r \<equiv> {y. x \<in> M \<and> y \<in> M \<and> d x y < r}"
definition mcball where "mcball x r \<equiv> {y. x \<in> M \<and> y \<in> M \<and> d x y \<le> r}"

lemma in_mball [simp]: "y \<in> mball x r \<longleftrightarrow> x \<in> M \<and> y \<in> M \<and> d x y < r"
  by (simp add: local.Metric_space_axioms Metric_space.mball_def)

lemma centre_in_mball_iff [iff]: "x \<in> mball x r \<longleftrightarrow> x \<in> M \<and> 0 < r"
  using in_mball mdist_zero by force

lemma mball_subset_mspace: "mball x r \<subseteq> M"
  by auto

lemma mball_eq_empty: "mball x r = {} \<longleftrightarrow> (x \<notin> M) \<or> r \<le> 0"
  by (smt (verit, best) Collect_empty_eq centre_in_mball_iff mball_def nonneg)

lemma mball_subset: "\<lbrakk>d x y + a \<le> b; y \<in> M\<rbrakk> \<Longrightarrow> mball x a \<subseteq> mball y b"
  by (smt (verit) commute in_mball subsetI triangle)

lemma disjoint_mball: "r + r' \<le> d x x' \<Longrightarrow> disjnt (mball x r) (mball x' r')"
  by (smt (verit) commute disjnt_iff in_mball triangle)

lemma mball_subset_concentric: "r \<le> s \<Longrightarrow> mball x r \<subseteq> mball x s"
  by auto

lemma in_mcball [simp]: "y \<in> mcball x r \<longleftrightarrow> x \<in> M \<and> y \<in> M \<and> d x y \<le> r"
  by (simp add: local.Metric_space_axioms Metric_space.mcball_def)

lemma centre_in_mcball_iff [iff]: "x \<in> mcball x r \<longleftrightarrow> x \<in> M \<and> 0 \<le> r"
  using mdist_zero by force

lemma mcball_eq_empty: "mcball x r = {} \<longleftrightarrow> (x \<notin> M) \<or> r < 0"
  by (smt (verit, best) Collect_empty_eq centre_in_mcball_iff empty_iff mcball_def nonneg)

lemma mcball_subset_mspace: "mcball x r \<subseteq> M"
  by auto

lemma mball_subset_mcball: "mball x r \<subseteq> mcball x r"
  by auto

lemma mcball_subset: "\<lbrakk>d x y + a \<le> b; y \<in> M\<rbrakk> \<Longrightarrow> mcball x a \<subseteq> mcball y b"
  by (smt (verit) in_mcball mdist_reverse_triangle subsetI)

lemma mcball_subset_concentric: "r \<le> s \<Longrightarrow> mcball x r \<subseteq> mcball x s"
  by force

lemma mcball_subset_mball: "\<lbrakk>d x y + a < b; y \<in> M\<rbrakk> \<Longrightarrow> mcball x a \<subseteq> mball y b"
  by (smt (verit) commute in_mball in_mcball subsetI triangle)

lemma mcball_subset_mball_concentric: "a < b \<Longrightarrow> mcball x a \<subseteq> mball x b"
  by force

end



subsection \<open>Metric topology                                                           \<close>

context Metric_space
begin

definition mopen where 
  "mopen U \<equiv> U \<subseteq> M \<and> (\<forall>x. x \<in> U \<longrightarrow> (\<exists>r>0. mball x r \<subseteq> U))"

definition mtopology :: "'a topology" where 
  "mtopology \<equiv> topology mopen"

lemma is_topology_metric_topology [iff]: "istopology mopen"
proof -
  have "\<And>S T. \<lbrakk>mopen S; mopen T\<rbrakk> \<Longrightarrow> mopen (S \<inter> T)"
    by (smt (verit, del_insts) Int_iff in_mball mopen_def subset_eq)
  moreover have "\<And>\<K>. (\<forall>K\<in>\<K>. mopen K) \<longrightarrow> mopen (\<Union>\<K>)"
    using mopen_def by fastforce
  ultimately show ?thesis
    by (simp add: istopology_def)
qed

lemma openin_mtopology: "openin mtopology U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>x. x \<in> U \<longrightarrow> (\<exists>r>0. mball x r \<subseteq> U))"
  by (simp add: mopen_def mtopology_def)

lemma topspace_mtopology [simp]: "topspace mtopology = M"
  by (meson order.refl mball_subset_mspace openin_mtopology openin_subset openin_topspace subset_antisym zero_less_one)

lemma subtopology_mspace [simp]: "subtopology mtopology M = mtopology"
  by (metis subtopology_topspace topspace_mtopology)

lemma open_in_mspace [iff]: "openin mtopology M"
  by (metis openin_topspace topspace_mtopology)

lemma closedin_mspace [iff]: "closedin mtopology M"
  by (metis closedin_topspace topspace_mtopology)

lemma openin_mball [iff]: "openin mtopology (mball x r)"
proof -
  have "\<And>y. \<lbrakk>x \<in> M; d x y < r\<rbrakk> \<Longrightarrow> \<exists>s>0. mball y s \<subseteq> mball x r"
    by (metis add_diff_cancel_left' add_diff_eq commute less_add_same_cancel1 mball_subset order_refl)
  then show ?thesis
    by (auto simp: openin_mtopology)
qed

lemma mcball_eq_cball [simp]: "Met.mcball = cball"
  by force

lemma mball_eq_ball [simp]: "Met.mball = ball"
  by force

lemma mopen_eq_open [simp]: "Met.mopen = open"
  by (force simp: open_contains_ball Met.mopen_def)

lemma limitin_iff_tendsto [iff]: "limitin Met.mtopology \<sigma> x F = tendsto \<sigma> x F"
  by (simp add: Met.mtopology_def)

lemma mtopology_is_euclideanreal [simp]: "Met.mtopology = euclideanreal"
  by (simp add: Met.mtopology_def)

(*
lemma metric_injective_image:
   "\<And>f m s.
        f ` s \<subseteq> M \<and>
        (\<forall>x y. x \<in> s \<and> y \<in> s \<and> f x = f y \<Longrightarrow> x = y)
        \<Longrightarrow> (mspace(metric(s,\<lambda>(x,y). d (f x) (f y))) = s) \<and>
            (d(metric(s,\<lambda>(x,y). d (f x) (f y))) =
             \<lambda>(x,y). d (f x) (f y))"
oops
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; INJECTIVE_ON_ALT] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mspace; d; GSYM PAIR_EQ] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 metric_tybij); is_metric_space] THEN
  REWRITE_TAC[GSYM mspace; GSYM d] THEN
  ASM_SIMP_TAC[MDIST_POS_LE; MDIST_TRIANGLE; MDIST_0] THEN
  ASM_MESON_TAC[MDIST_SYM]);;
*)

lemma mtopology_base:
   "mtopology = topology(arbitrary union_of (\<lambda>U. \<exists>x \<in> M. \<exists>r>0. U = mball x r))"
proof -
  have "\<And>S. \<exists>x r. x \<in> M \<and> 0 < r \<and> S = mball x r \<Longrightarrow> openin mtopology S"
    using openin_mball by blast
  moreover have "\<And>U x. \<lbrakk>openin mtopology U; x \<in> U\<rbrakk> \<Longrightarrow> \<exists>B. (\<exists>x r. x \<in> M \<and> 0 < r \<and> B = mball x r) \<and> x \<in> B \<and> B \<subseteq> U"
    by (metis centre_in_mball_iff in_mono openin_mtopology)
  ultimately show ?thesis
    by (smt (verit) topology_base_unique)
qed

lemma closedin_metric:
   "closedin mtopology C \<longleftrightarrow> C \<subseteq> M \<and> (\<forall>x. x \<in> M - C \<longrightarrow> (\<exists>r>0. disjnt C (mball x r)))"  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding closedin_def openin_mtopology
    by (metis Diff_disjoint disjnt_def disjnt_subset2 topspace_mtopology)
  show "?rhs \<Longrightarrow> ?lhs"
    unfolding closedin_def openin_mtopology disjnt_def
    by (metis Diff_subset Diff_triv Int_Diff Int_commute inf.absorb_iff2 mball_subset_mspace topspace_mtopology)
qed

lemma closedin_mcball [iff]: "closedin mtopology (mcball x r)"
proof -
  have "\<exists>ra>0. disjnt (mcball x r) (mball y ra)" if "x \<notin> M" for y
    by (metis disjnt_empty1 gt_ex mcball_eq_empty that)
  moreover have "disjnt (mcball x r) (mball y (d x y - r))" if "y \<in> M" "d x y > r" for y
    using that disjnt_iff in_mball in_mcball mdist_reverse_triangle by force
  ultimately show ?thesis
    using closedin_metric mcball_subset_mspace by fastforce
qed

lemma mball_iff_mcball: "(\<exists>r>0. mball x r \<subseteq> U) = (\<exists>r>0. mcball x r \<subseteq> U)"
  by (meson dense mball_subset_mcball mcball_subset_mball_concentric order_trans)

lemma openin_mtopology_mcball:
  "openin mtopology U \<longleftrightarrow> U \<subseteq> M \<and> (\<forall>x. x \<in> U \<longrightarrow> (\<exists>r. 0 < r \<and> mcball x r \<subseteq> U))"
  using mball_iff_mcball openin_mtopology by presburger

lemma metric_derived_set_of:
  "mtopology derived_set_of S = {x \<in> M. \<forall>r>0. \<exists>y\<in>S. y\<noteq>x \<and> y \<in> mball x r}" (is "?lhs=?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    unfolding openin_mtopology derived_set_of_def 
    by clarsimp (metis in_mball openin_mball openin_mtopology zero)
  show "?rhs \<subseteq> ?lhs"
    unfolding openin_mtopology derived_set_of_def 
    by clarify (metis subsetD topspace_mtopology)
qed

lemma metric_closure_of:
   "mtopology closure_of S = {x \<in> M. \<forall>r>0. \<exists>y \<in> S. y \<in> mball x r}"
proof -
  have "\<And>x r. \<lbrakk>0 < r; x \<in> mtopology closure_of S\<rbrakk> \<Longrightarrow> \<exists>y\<in>S. y \<in> mball x r"
    by (metis centre_in_mball_iff in_closure_of openin_mball topspace_mtopology)
  moreover have "\<And>x T. \<lbrakk>x \<in> M; \<forall>r>0. \<exists>y\<in>S. y \<in> mball x r\<rbrakk> \<Longrightarrow> x \<in> mtopology closure_of S"
    by (smt (verit) in_closure_of in_mball openin_mtopology subsetD topspace_mtopology)
  ultimately show ?thesis
    by (auto simp: in_closure_of)
qed

lemma metric_closure_of_alt:
  "mtopology closure_of S = {x \<in> M. \<forall>r>0. \<exists>y \<in> S. y \<in> mcball x r}"
proof -
  have "\<And>x r. \<lbrakk>\<forall>r>0. x \<in> M \<and> (\<exists>y\<in>S. y \<in> mcball x r); 0 < r\<rbrakk> \<Longrightarrow> \<exists>y\<in>S. y \<in> M \<and> d x y < r"
    by (meson dense in_mcball le_less_trans)
  then show ?thesis
    by (fastforce simp: metric_closure_of in_closure_of)
qed

lemma metric_interior_of:
   "mtopology interior_of S = {x \<in> M. \<exists>\<epsilon>>0. mball x \<epsilon> \<subseteq> S}" (is "?lhs=?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    using interior_of_maximal_eq openin_mtopology by fastforce
  show "?rhs \<subseteq> ?lhs"
    using interior_of_def openin_mball by fastforce
qed

lemma metric_interior_of_alt:
   "mtopology interior_of S = {x \<in> M. \<exists>\<epsilon>>0. mcball x \<epsilon> \<subseteq> S}"
  by (fastforce simp: mball_iff_mcball metric_interior_of)

lemma in_interior_of_mball:
   "x \<in> mtopology interior_of S \<longleftrightarrow> x \<in> M \<and> (\<exists>\<epsilon>>0. mball x \<epsilon> \<subseteq> S)"
  using metric_interior_of by force

lemma in_interior_of_mcball:
   "x \<in> mtopology interior_of S \<longleftrightarrow> x \<in> M \<and> (\<exists>\<epsilon>>0. mcball x \<epsilon> \<subseteq> S)"
  using metric_interior_of_alt by force

lemma Hausdorff_space_mtopology: "Hausdorff_space mtopology"
  unfolding Hausdorff_space_def
proof clarify
  fix x y
  assume x: "x \<in> topspace mtopology" and y: "y \<in> topspace mtopology" and "x \<noteq> y"
  then have gt0: "d x y / 2 > 0"
    by auto
  have "disjnt (mball x (d x y / 2)) (mball y (d x y / 2))"
    by (simp add: disjoint_mball)
  then show "\<exists>U V. openin mtopology U \<and> openin mtopology V \<and> x \<in> U \<and> y \<in> V \<and> disjnt U V"
    by (metis centre_in_mball_iff gt0 openin_mball topspace_mtopology x y)
qed



subsection\<open>Bounded sets\<close>

definition mbounded where "mbounded S \<longleftrightarrow> (\<exists>x B. S \<subseteq> mcball x B)"

lemma mbounded_pos: "mbounded S \<longleftrightarrow> (\<exists>x B. 0 < B \<and> S \<subseteq> mcball x B)"
proof -
  have "\<exists>x' r'. 0 < r' \<and> S \<subseteq> mcball x' r'" if "S \<subseteq> mcball x r" for x r
    by (metis gt_ex less_eq_real_def linorder_not_le mcball_subset_concentric order_trans that)
  then show ?thesis
    by (auto simp: mbounded_def)
qed

lemma mbounded_alt:
  "mbounded S \<longleftrightarrow> S \<subseteq> M \<and> (\<exists>B. \<forall>x \<in> S. \<forall>y \<in> S. d x y \<le> B)"
proof -
  have "\<And>x B. S \<subseteq> mcball x B \<Longrightarrow> \<forall>x\<in>S. \<forall>y\<in>S. d x y \<le> 2 * B"
    by (smt (verit, best) commute in_mcball subsetD triangle)
  then show ?thesis
    apply (auto simp: mbounded_def subset_iff)
     apply blast+
    done
qed


lemma mbounded_alt_pos:
  "mbounded S \<longleftrightarrow> S \<subseteq> M \<and> (\<exists>B>0. \<forall>x \<in> S. \<forall>y \<in> S. d x y \<le> B)"
  by (smt (verit, del_insts) gt_ex mbounded_alt)

lemma mbounded_subset: "\<lbrakk>mbounded T; S \<subseteq> T\<rbrakk> \<Longrightarrow> mbounded S"
  by (meson mbounded_def order_trans)

lemma mbounded_subset_mspace: "mbounded S \<Longrightarrow> S \<subseteq> M"
  by (simp add: mbounded_alt)

lemma mbounded:
   "mbounded S \<longleftrightarrow> S = {} \<or> (\<forall>x \<in> S. x \<in> M) \<and> (\<exists>y B. y \<in> M \<and> (\<forall>x \<in> S. d y x \<le> B))"
  by (meson all_not_in_conv in_mcball mbounded_def subset_iff)

lemma mbounded_empty [iff]: "mbounded {}"
  by (simp add: mbounded)

lemma mbounded_mcball: "mbounded (mcball x r)"
  using mbounded_def by auto

lemma mbounded_mball [iff]: "mbounded (mball x r)"
  by (meson mball_subset_mcball mbounded_def)

lemma mbounded_insert: "mbounded (insert a S) \<longleftrightarrow> a \<in> M \<and> mbounded S"
proof -
  have "\<And>y B. \<lbrakk>y \<in> M; \<forall>x\<in>S. d y x \<le> B\<rbrakk>
           \<Longrightarrow> \<exists>y. y \<in> M \<and> (\<exists>B \<ge> d y a. \<forall>x\<in>S. d y x \<le> B)"
    by (metis order.trans nle_le)
  then show ?thesis
    by (auto simp: mbounded)
qed

lemma mbounded_Int: "mbounded S \<Longrightarrow> mbounded (S \<inter> T)"
  by (meson inf_le1 mbounded_subset)

lemma mbounded_Un: "mbounded (S \<union> T) \<longleftrightarrow> mbounded S \<and> mbounded T" (is "?lhs=?rhs")
proof
  assume R: ?rhs
  show ?lhs
  proof (cases "S={} \<or> T={}")
    case True then show ?thesis
      using R by auto
  next
    case False
    obtain x y B C where "S \<subseteq> mcball x B" "T \<subseteq> mcball y C" "B > 0" "C > 0" "x \<in> M" "y \<in> M"
      using R mbounded_pos
      by (metis False mcball_eq_empty subset_empty)
    then have "S \<union> T \<subseteq> mcball x (B + C + d x y)"
      by (smt (verit) commute dual_order.trans le_supI mcball_subset mdist_pos_eq)
    then show ?thesis
      using mbounded_def by blast
  qed
next
  show "?lhs \<Longrightarrow> ?rhs"
    using mbounded_def by auto
qed

lemma mbounded_Union:
  "\<lbrakk>finite \<F>; \<And>X. X \<in> \<F> \<Longrightarrow> mbounded X\<rbrakk> \<Longrightarrow> mbounded (\<Union>\<F>)"
  by (induction \<F> rule: finite_induct) (auto simp: mbounded_Un)

lemma mbounded_closure_of:
   "mbounded S \<Longrightarrow> mbounded (mtopology closure_of S)"
  by (meson closedin_mcball closure_of_minimal mbounded_def)

lemma mbounded_closure_of_eq:
   "S \<subseteq> M \<Longrightarrow> (mbounded (mtopology closure_of S) \<longleftrightarrow> mbounded S)"
  by (metis closure_of_subset mbounded_closure_of mbounded_subset topspace_mtopology)


lemma maxdist_thm:
  assumes "mbounded S"
      and "x \<in> S"
      and "y \<in> S"
    shows  "d x y = (SUP z\<in>S. \<bar>d x z - d z y\<bar>)"
proof -
  have "\<bar>d x z - d z y\<bar> \<le> d x y" if "z \<in> S" for z
    by (metis all_not_in_conv assms mbounded mdist_reverse_triangle that) 
  moreover have "d x y \<le> r"
    if "\<And>z. z \<in> S \<Longrightarrow> \<bar>d x z - d z y\<bar> \<le> r" for r :: real
    using that assms mbounded_subset_mspace mdist_zero by fastforce
  ultimately show ?thesis
    by (intro cSup_eq [symmetric]) auto
qed


lemma metric_eq_thm: "\<lbrakk>S \<subseteq> M; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> (x = y) = (\<forall>z\<in>S. d x z = d y z)"
  by (metis commute  subset_iff zero)

lemma compactin_imp_mbounded:
  assumes "compactin mtopology S"
  shows "mbounded S"
proof -
  have "S \<subseteq> M"
    and com: "\<And>\<U>. \<lbrakk>\<forall>U\<in>\<U>. openin mtopology U; S \<subseteq> \<Union>\<U>\<rbrakk> \<Longrightarrow> \<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> S \<subseteq> \<Union>\<F>"
    using assms by (auto simp: compactin_def mbounded_def)
  show ?thesis
  proof (cases "S = {}")
    case False
    with \<open>S \<subseteq> M\<close> obtain a where "a \<in> S" "a \<in> M"
      by blast
    with \<open>S \<subseteq> M\<close> gt_ex have "S \<subseteq> \<Union>(range (mball a))"
      by force
    moreover have "\<forall>U \<in> range (mball a). openin mtopology U"
      by (simp add: openin_mball)
    ultimately obtain \<F> where "finite \<F>" "\<F> \<subseteq> range (mball a)" "S \<subseteq> \<Union>\<F>"
      by (meson com)
  then show ?thesis
      using mbounded_Union mbounded_subset by fastforce
  qed auto
qed

end


subsection\<open>Subspace of a metric space\<close>

locale submetric = Metric_space + 
  fixes A
  assumes subset: "A \<subseteq> M"

sublocale submetric \<subseteq> sub: Metric_space A d
  by (simp add: subset subspace)

context submetric
begin 

lemma mball_submetric_eq: "sub.mball a r = (if a \<in> A then A \<inter> mball a r else {})"
and mcball_submetric_eq: "sub.mcball a r = (if a \<in> A then A \<inter> mcball a r else {})"
  using subset by force+

lemma mtopology_submetric: "sub.mtopology = subtopology mtopology A"
  unfolding topology_eq
proof (intro allI iffI)
  fix S
  assume "openin sub.mtopology S"
  then have "\<exists>T. openin (subtopology mtopology A) T \<and> x \<in> T \<and> T \<subseteq> S" if "x \<in> S" for x
    by (metis mball_submetric_eq openin_mball openin_subtopology_Int2 sub.centre_in_mball_iff sub.openin_mtopology subsetD that)
  then show "openin (subtopology mtopology A) S"
    by (meson openin_subopen)
next
  fix S
  assume "openin (subtopology mtopology A) S"
  then obtain T where "openin mtopology T" "S = T \<inter> A"
    by (meson openin_subtopology)
  then have "mopen T"
    by (simp add: mopen_def openin_mtopology)
  then have "sub.mopen (T \<inter> A)"
    unfolding sub.mopen_def mopen_def
    by (metis inf.coboundedI2 mball_submetric_eq Int_iff \<open>S = T \<inter> A\<close> inf.bounded_iff subsetI)
  then show "openin sub.mtopology S"
    using \<open>S = T \<inter> A\<close> sub.mopen_def sub.openin_mtopology by force
qed

lemma mbounded_submetric: "sub.mbounded T \<longleftrightarrow> mbounded T \<and> T \<subseteq> A"
  by (meson mbounded_alt sub.mbounded_alt subset subset_trans)

end
  

(**
lemma submetric_submetric:
   "\<And>m A t::A=>bool.
        submetric (submetric A) t = submetric (A \<inter> t)"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[submetric] THEN
  REWRITE_TAC[SUBMETRIC] THEN
  REWRITE_TAC[SET_RULE `(A \<inter> t) \<inter> m = t \<inter> A \<inter> m`]);;

lemma submetric_restrict:
   "\<And>m A::A=>bool. submetric A = submetric (M \<inter> A)"
oops
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV \<circ> LAND_CONV) [GSYM SUBMETRIC_MSPACE] THEN
  REWRITE_TAC[SUBMETRIC_SUBMETRIC]);;
**)


subsection\<open>The discrete metric\<close>


locale discrete_metric =
  fixes M :: "'a set"

definition (in discrete_metric) dd :: "'a \<Rightarrow> 'a \<Rightarrow> real"
  where "dd \<equiv> \<lambda>x y::'a. if x=y then 0 else 1"

lemma metric_M_dd: "Metric_space M discrete_metric.dd"
  by (simp add: discrete_metric.dd_def Metric_space.intro)

sublocale discrete_metric \<subseteq> disc: Metric_space M dd
  by (simp add: metric_M_dd)


lemma (in discrete_metric) mopen_singleton:
  assumes "x \<in> M" shows "disc.mopen {x}"
proof -
  have "disc.mball x (1/2) \<subseteq> {x}"
    by (smt (verit) dd_def disc.in_mball less_divide_eq_1_pos singleton_iff subsetI)
  with assms show ?thesis
    using disc.mopen_def half_gt_zero_iff zero_less_one by blast
qed

lemma (in discrete_metric) mtopology_discrete_metric:
   "disc.mtopology = discrete_topology M"
proof -
  have "\<And>x. x \<in> M \<Longrightarrow> openin disc.mtopology {x}"
    by (simp add: disc.mtopology_def mopen_singleton)
  then show ?thesis
    by (metis disc.topspace_mtopology discrete_topology_unique)
qed

lemma (in discrete_metric) discrete_ultrametric:
   "dd x z \<le> max (dd x y) (dd y z)"
  by (simp add: dd_def)


lemma (in discrete_metric) dd_le1: "dd x y \<le> 1"
  by (simp add: dd_def)

lemma (in discrete_metric) mbounded_discrete_metric: "disc.mbounded S \<longleftrightarrow> S \<subseteq> M"
  by (meson dd_le1 disc.mbounded_alt)



subsection\<open>Metrizable spaces\<close>


definition metrizable_space where
  "metrizable_space X \<equiv> (\<exists>M d. Metric_space M d \<and> X = Metric_space.mtopology M d)"

lemma (in Metric_space) metrizable_space_mtopology: "metrizable_space mtopology"
  using local.Metric_space_axioms metrizable_space_def by blast

lemma openin_mtopology_eq_open [simp]: "openin Met.mtopology = open"
  by (simp add: Met.mtopology_def)

lemma closedin_mtopology_eq_closed [simp]: "closedin Met.mtopology = closed"
proof -
  have "(euclidean::'a topology) = Met.mtopology"
    by (simp add: Met.mtopology_def)
  then show ?thesis
    using closed_closedin by fastforce
qed

lemma compactin_mtopology_eq_compact [simp]: "compactin Met.mtopology = compact"
  by (simp add: compactin_def compact_eq_Heine_Borel fun_eq_iff) meson

lemma metrizable_space_discrete_topology:
   "metrizable_space(discrete_topology U)"
  by (metis discrete_metric.mtopology_discrete_metric metric_M_dd metrizable_space_def)

lemma metrizable_space_subtopology:
  assumes "metrizable_space X"
  shows "metrizable_space(subtopology X S)"
proof -
  obtain M d where "Metric_space M d" and X: "X = Metric_space.mtopology M d"
    using assms metrizable_space_def by blast
  then interpret submetric M d "M \<inter> S"
    by (simp add: submetric.intro submetric_axioms_def)
  show ?thesis
    unfolding metrizable_space_def
    by (metis X mtopology_submetric sub.Metric_space_axioms subtopology_restrict topspace_mtopology)
qed

lemma homeomorphic_metrizable_space_aux:
  assumes "X homeomorphic_space Y" "metrizable_space X"
  shows "metrizable_space Y"
proof -
  obtain M d where "Metric_space M d" and X: "X = Metric_space.mtopology M d"
    using assms by (auto simp: metrizable_space_def)
  then interpret m: Metric_space M d 
    by simp
  obtain f g where hmf: "homeomorphic_map X Y f" and hmg: "homeomorphic_map Y X g"
    and fg: "(\<forall>x \<in> M. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"
    using assms X homeomorphic_maps_map homeomorphic_space_def by fastforce
  define d' where "d' x y \<equiv> d (g x) (g y)" for x y
  interpret m': Metric_space "topspace Y" "d'"
    unfolding d'_def
  proof
    show "(d (g x) (g y) = 0) = (x = y)" if "x \<in> topspace Y" "y \<in> topspace Y" for x y
      by (metis fg X hmg homeomorphic_imp_surjective_map imageI m.topspace_mtopology m.zero that)
    show "d (g x) (g z) \<le> d (g x) (g y) + d (g y) (g z)"
      if "x \<in> topspace Y" and "y \<in> topspace Y" and "z \<in> topspace Y" for x y z
      by (metis X that hmg homeomorphic_eq_everything_map imageI m.topspace_mtopology m.triangle)
  qed (auto simp: m.nonneg m.commute)
  have "Y = Metric_space.mtopology (topspace Y) d'"
    unfolding topology_eq
  proof (intro allI)
    fix S
    have "openin m'.mtopology S" if S: "S \<subseteq> topspace Y" and "openin X (g ` S)"
      unfolding m'.openin_mtopology
    proof (intro conjI that strip)
      fix y
      assume "y \<in> S"
      then obtain r where "r>0" and r: "m.mball (g y) r \<subseteq> g ` S" 
        using X \<open>openin X (g ` S)\<close> m.openin_mtopology using \<open>y \<in> S\<close> by auto
      then have "g ` m'.mball y r \<subseteq> m.mball (g y) r"
        using X d'_def hmg homeomorphic_imp_surjective_map by fastforce
      with S fg have "m'.mball y r \<subseteq> S"
        by (smt (verit, del_insts) image_iff m'.in_mball r subset_iff)
      then show "\<exists>r>0. m'.mball y r \<subseteq> S"
        using \<open>0 < r\<close> by blast 
    qed
    moreover have "openin X (g ` S)" if ope': "openin m'.mtopology S"
    proof -
      have "\<exists>r>0. m.mball (g y) r \<subseteq> g ` S" if "y \<in> S" for y
      proof -
        have y: "y \<in> topspace Y"
          using m'.openin_mtopology ope' that by blast
        obtain r where "r > 0" and r: "m'.mball y r \<subseteq> S"
          using ope' by (meson \<open>y \<in> S\<close> m'.openin_mtopology)
        moreover have "\<And>x. \<lbrakk>x \<in> M; d (g y) x < r\<rbrakk> \<Longrightarrow> \<exists>u. u \<in> topspace Y \<and> d' y u < r \<and> x = g u"
          using fg X d'_def hmf homeomorphic_imp_surjective_map by fastforce
        ultimately have "m.mball (g y) r \<subseteq> g ` m'.mball y r"
          using y by (force simp: m'.openin_mtopology)
        then show ?thesis
          using \<open>0 < r\<close> r by blast
      qed
      then show ?thesis
        using X hmg homeomorphic_imp_surjective_map m.openin_mtopology ope' openin_subset by fastforce
    qed
    ultimately have "(S \<subseteq> topspace Y \<and> openin X (g ` S)) = openin m'.mtopology S"
      using m'.topspace_mtopology openin_subset by blast
    then show "openin Y S = openin m'.mtopology S"
      by (simp add: m'.mopen_def homeomorphic_map_openness_eq [OF hmg])
  qed
  then show ?thesis
    using m'.metrizable_space_mtopology by force
qed

lemma homeomorphic_metrizable_space:
  assumes "X homeomorphic_space Y"
  shows "metrizable_space X \<longleftrightarrow> metrizable_space Y"
  using assms homeomorphic_metrizable_space_aux homeomorphic_space_sym by metis

lemma metrizable_space_retraction_map_image:
   "retraction_map X Y r \<and> metrizable_space X
        \<Longrightarrow> metrizable_space Y"
  using hereditary_imp_retractive_property metrizable_space_subtopology homeomorphic_metrizable_space
  by blast


lemma metrizable_imp_Hausdorff_space:
   "metrizable_space X \<Longrightarrow> Hausdorff_space X"
  by (metis Metric_space.Hausdorff_space_mtopology metrizable_space_def)

(**
lemma metrizable_imp_kc_space:
   "metrizable_space X \<Longrightarrow> kc_space X"
oops
  MESON_TAC[METRIZABLE_IMP_HAUSDORFF_SPACE; HAUSDORFF_IMP_KC_SPACE]);;

lemma kc_space_mtopology:
   "kc_space mtopology"
oops
  REWRITE_TAC[GSYM FORALL_METRIZABLE_SPACE; METRIZABLE_IMP_KC_SPACE]);;
**)

lemma metrizable_imp_t1_space:
   "metrizable_space X \<Longrightarrow> t1_space X"
  by (simp add: Hausdorff_imp_t1_space metrizable_imp_Hausdorff_space)

lemma closed_imp_gdelta_in:
  assumes X: "metrizable_space X" and S: "closedin X S"
  shows "gdelta_in X S"
proof -
  obtain M d where "Metric_space M d" and Xeq: "X = Metric_space.mtopology M d"
    using X metrizable_space_def by blast
  then interpret M: Metric_space M d
    by blast
  have "S \<subseteq> M"
    using M.closedin_metric \<open>X = M.mtopology\<close> S by blast
  show ?thesis
  proof (cases "S = {}")
    case True
    then show ?thesis
      by simp
  next
    case False
    have "\<exists>y\<in>S. d x y < inverse (1 + real n)" if "x \<in> S" for x n
      using \<open>S \<subseteq> M\<close> M.mdist_zero [of x] that by force
    moreover
    have "x \<in> S" if "x \<in> M" and \<section>: "\<And>n. \<exists>y\<in>S. d x y < inverse(Suc n)" for x
    proof -
      have *: "\<exists>y\<in>S. d x y < \<epsilon>" if "\<epsilon> > 0" for \<epsilon>
        by (metis \<section> that not0_implies_Suc order_less_le order_less_le_trans real_arch_inverse)
      have "closedin M.mtopology S"
        using S by (simp add: Xeq)
      then show ?thesis
        apply (simp add: M.closedin_metric)
        by (metis * \<open>x \<in> M\<close> M.in_mball disjnt_insert1 insert_absorb subsetD)
    qed
    ultimately have Seq: "S = \<Inter>(range (\<lambda>n. {x\<in>M. \<exists>y\<in>S. d x y < inverse(Suc n)}))"
      using \<open>S \<subseteq> M\<close> by force
    have "openin M.mtopology {xa \<in> M. \<exists>y\<in>S. d xa y < inverse (1 + real n)}" for n
    proof (clarsimp simp: M.openin_mtopology)
      fix x y
      assume "x \<in> M" "y \<in> S" and dxy: "d x y < inverse (1 + real n)"
      then have "\<And>z. \<lbrakk>z \<in> M; d x z < inverse (1 + real n) - d x y\<rbrakk> \<Longrightarrow> \<exists>y\<in>S. d z y < inverse (1 + real n)"
        by (smt (verit) M.commute M.triangle \<open>S \<subseteq> M\<close> in_mono)
      with dxy show "\<exists>r>0. M.mball x r \<subseteq> {z \<in> M. \<exists>y\<in>S. d z y < inverse (1 + real n)}"
        by (rule_tac x="inverse(Suc n) - d x y" in exI) auto
    qed
    then show ?thesis
      apply (subst Seq)
      apply (force simp: Xeq intro: gdelta_in_Inter open_imp_gdelta_in)
      done
  qed
qed

lemma open_imp_fsigma_in:
   "\<lbrakk>metrizable_space X; openin X S\<rbrakk> \<Longrightarrow> fsigma_in X S"
  by (meson closed_imp_gdelta_in fsigma_in_gdelta_in openin_closedin openin_subset)

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

lemma mball_eq_ball [simp]: "Met.mball = ball"
  by force

lemma mopen_eq_open [simp]: "Met.mopen = open"
  by (force simp: open_contains_ball Met.mopen_def)

lemma metrizable_space_euclidean:
  "metrizable_space (euclidean :: 'a::metric_space topology)"
  unfolding metrizable_space_def
  by (metis Met.Metric_space_axioms Met.mtopology_def mopen_eq_open)

lemma (in Metric_space) regular_space_mtopology:
   "regular_space mtopology"
unfolding regular_space_def
proof clarify
  fix C a
  assume C: "closedin mtopology C" and a: "a \<in> topspace mtopology" and "a \<notin> C"
  have "openin mtopology (topspace mtopology - C)"
    by (simp add: C openin_diff)
  then obtain r where "r>0" and r: "mball a r \<subseteq> topspace mtopology - C"
    unfolding openin_mtopology using \<open>a \<notin> C\<close> a by auto
  show "\<exists>U V. openin mtopology U \<and> openin mtopology V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V"
  proof (intro exI conjI)
    show "a \<in> mball a (r/2)"
      using \<open>0 < r\<close> a by force
    show "C \<subseteq> topspace mtopology - mcball a (r/2)"
      using C \<open>0 < r\<close> r by (fastforce simp: closedin_metric)
  qed (auto simp: openin_mball closedin_mcball openin_diff disjnt_iff)
qed

lemma metrizable_imp_regular_space:
   "metrizable_space X \<Longrightarrow> regular_space X"
  by (metis Metric_space.regular_space_mtopology metrizable_space_def)

lemma regular_space_euclidean:
 "regular_space (euclidean :: 'a::metric_space topology)"
  by (simp add: metrizable_imp_regular_space metrizable_space_euclidean)


subsection\<open>Limits at a point in a topological space\<close>

lemma (in Metric_space) eventually_atin_metric:
   "eventually P (atin mtopology a) \<longleftrightarrow>
        (a \<in> M \<longrightarrow> (\<exists>\<delta>>0. \<forall>x. x \<in> M \<and> 0 < d x a \<and> d x a < \<delta> \<longrightarrow> P x))"  (is "?lhs=?rhs")
proof (cases "a \<in> M")
  case True
  show ?thesis
  proof
    assume L: ?lhs 
    with True obtain U where "openin mtopology U" "a \<in> U" and U: "\<forall>x\<in>U - {a}. P x"
      by (auto simp: eventually_atin)
    then obtain r where "r>0" and "mball a r \<subseteq> U"
      by (meson openin_mtopology)
    with U show ?rhs
      by (smt (verit, ccfv_SIG) commute in_mball insert_Diff_single insert_iff subset_iff)
  next
    assume ?rhs 
    then obtain \<delta> where "\<delta>>0" and \<delta>: "\<forall>x. x \<in> M \<and> 0 < d x a \<and> d x a < \<delta> \<longrightarrow> P x"
      using True by blast
    then have "\<forall>x \<in> mball a \<delta> - {a}. P x"
      by (simp add: commute)
    then show ?lhs
      unfolding eventually_atin openin_mtopology
      by (metis True \<open>0 < \<delta>\<close> centre_in_mball_iff openin_mball openin_mtopology) 
  qed
qed auto

subsection \<open>Normal spaces and metric spaces\<close>

lemma (in Metric_space) normal_space_mtopology:
   "normal_space mtopology"
  unfolding normal_space_def
proof clarify
  fix S T
  assume "closedin mtopology S"
  then have "\<And>x. x \<in> M - S \<Longrightarrow> (\<exists>r>0. mball x r \<subseteq> M - S)"
    by (simp add: closedin_def openin_mtopology)
  then obtain \<delta> where d0: "\<And>x. x \<in> M - S \<Longrightarrow> \<delta> x > 0 \<and> mball x (\<delta> x) \<subseteq> M - S"
    by metis
  assume "closedin mtopology T"
  then have "\<And>x. x \<in> M - T \<Longrightarrow> (\<exists>r>0. mball x r \<subseteq> M - T)"
    by (simp add: closedin_def openin_mtopology)
  then obtain \<epsilon> where e: "\<And>x. x \<in> M - T \<Longrightarrow> \<epsilon> x > 0 \<and> mball x (\<epsilon> x) \<subseteq> M - T"
    by metis
  assume "disjnt S T"
  have "S \<subseteq> M" "T \<subseteq> M"
    using \<open>closedin mtopology S\<close> \<open>closedin mtopology T\<close> closedin_metric by blast+
  have \<delta>: "\<And>x. x \<in> T \<Longrightarrow> \<delta> x > 0 \<and> mball x (\<delta> x) \<subseteq> M - S"
    by (meson DiffI \<open>T \<subseteq> M\<close> \<open>disjnt S T\<close> d0 disjnt_iff subsetD)
  have \<epsilon>: "\<And>x. x \<in> S \<Longrightarrow> \<epsilon> x > 0 \<and> mball x (\<epsilon> x) \<subseteq> M - T"
    by (meson Diff_iff \<open>S \<subseteq> M\<close> \<open>disjnt S T\<close> disjnt_iff e subsetD)
  show "\<exists>U V. openin mtopology U \<and> openin mtopology V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
  proof (intro exI conjI)
    show "openin mtopology (\<Union>x\<in>S. mball x (\<epsilon> x / 2))" "openin mtopology (\<Union>x\<in>T. mball x (\<delta> x / 2))"
      by force+
    show "S \<subseteq> (\<Union>x\<in>S. mball x (\<epsilon> x / 2))"
      using \<epsilon> \<open>S \<subseteq> M\<close> by force
    show "T \<subseteq> (\<Union>x\<in>T. mball x (\<delta> x / 2))"
      using \<delta> \<open>T \<subseteq> M\<close> by force
    show "disjnt (\<Union>x\<in>S. mball x (\<epsilon> x / 2)) (\<Union>x\<in>T. mball x (\<delta> x / 2))"
      using \<epsilon> \<delta> 
      apply (clarsimp simp: disjnt_iff subset_iff)
      by (smt (verit, ccfv_SIG) field_sum_of_halves triangle')
  qed 
qed

lemma metrizable_imp_normal_space:
   "metrizable_space X \<Longrightarrow> normal_space X"
  by (metis Metric_space.normal_space_mtopology metrizable_space_def)

subsection\<open>Topological limitin in metric spaces\<close>


lemma (in Metric_space) limitin_mspace:
   "limitin mtopology f l F \<Longrightarrow> l \<in> M"
  using limitin_topspace by fastforce

lemma (in Metric_space) limitin_metric_unique:
   "\<lbrakk>limitin mtopology f l1 F; limitin mtopology f l2 F; F \<noteq> bot\<rbrakk> \<Longrightarrow> l1 = l2"
  by (meson Hausdorff_space_mtopology limitin_Hausdorff_unique)

lemma (in Metric_space) limitin_metric:
   "limitin mtopology f l F \<longleftrightarrow> l \<in> M \<and> (\<forall>\<epsilon>>0. eventually (\<lambda>x. f x \<in> M \<and> d (f x) l < \<epsilon>) F)"  
   (is "?lhs=?rhs")
proof
  assume L: ?lhs
  show ?rhs
    unfolding limitin_def
  proof (intro conjI strip)
    show "l \<in> M"
      using L limitin_mspace by blast
    fix \<epsilon>::real
    assume "\<epsilon>>0"
    then have "\<forall>\<^sub>F x in F. f x \<in> mball l \<epsilon>"
      using L openin_mball by (fastforce simp: limitin_def)
    then show "\<forall>\<^sub>F x in F. f x \<in> M \<and> d (f x) l < \<epsilon>"
      using commute eventually_mono by fastforce
  qed
next
  assume R: ?rhs 
  then show ?lhs
    by (force simp: limitin_def commute openin_mtopology subset_eq elim: eventually_mono)
qed

lemma (in Metric_space) limit_metric_sequentially:
   "limitin mtopology f l sequentially \<longleftrightarrow>
     l \<in> M \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. f n \<in> M \<and> d (f n) l < \<epsilon>)"
  by (auto simp: limitin_metric eventually_sequentially)

lemma (in submetric) limitin_submetric_iff:
   "limitin sub.mtopology f l F \<longleftrightarrow>
     l \<in> A \<and> eventually (\<lambda>x. f x \<in> A) F \<and> limitin mtopology f l F" (is "?lhs=?rhs")
  by (simp add: limitin_subtopology mtopology_submetric)

lemma (in Metric_space) metric_closedin_iff_sequentially_closed:
   "closedin mtopology S \<longleftrightarrow>
    S \<subseteq> M \<and> (\<forall>\<sigma> l. range \<sigma> \<subseteq> S \<and> limitin mtopology \<sigma> l sequentially \<longrightarrow> l \<in> S)" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (force simp: closedin_metric limitin_closedin range_subsetD)
next
  assume R: ?rhs
  show ?lhs
    unfolding closedin_metric
  proof (intro conjI strip)
    show "S \<subseteq> M"
      using R by blast
    fix x
    assume "x \<in> M - S"
    have False if "\<forall>r>0. \<exists>y. y \<in> M \<and> y \<in> S \<and> d x y < r"
    proof -
      have "\<forall>n. \<exists>y. y \<in> M \<and> y \<in> S \<and> d x y < inverse(Suc n)"
        using that by auto
      then obtain \<sigma> where \<sigma>: "\<And>n. \<sigma> n \<in> M \<and> \<sigma> n \<in> S \<and> d x (\<sigma> n) < inverse(Suc n)"
        by metis
      then have "range \<sigma> \<subseteq> M"
        by blast
      have "\<exists>N. \<forall>n\<ge>N. d x (\<sigma> n) < \<epsilon>" if "\<epsilon>>0" for \<epsilon>
      proof -
        have "real (Suc (nat \<lceil>inverse \<epsilon>\<rceil>)) \<ge> inverse \<epsilon>"
          by linarith
        then have "\<forall>n \<ge> nat \<lceil>inverse \<epsilon>\<rceil>. d x (\<sigma> n) < \<epsilon>"
          by (metis \<sigma> inverse_inverse_eq inverse_le_imp_le nat_ceiling_le_eq nle_le not_less_eq_eq order.strict_trans2 that)
        then show ?thesis ..
      qed
      with \<sigma> have "limitin mtopology \<sigma> x sequentially"
        using \<open>x \<in> M - S\<close> commute limit_metric_sequentially by auto
      then show ?thesis
        by (metis R DiffD2 \<sigma> image_subset_iff \<open>x \<in> M - S\<close>)
    qed
    then show "\<exists>r>0. disjnt S (mball x r)"
      by (meson disjnt_iff in_mball)
  qed
qed

lemma (in Metric_space) limit_atin_metric:
   "limitin X f y (atin mtopology x) \<longleftrightarrow>
      y \<in> topspace X \<and>
      (x \<in> M
       \<longrightarrow> (\<forall>V. openin X V \<and> y \<in> V
               \<longrightarrow> (\<exists>\<delta>>0.  \<forall>x'. x' \<in> M \<and> 0 < d x' x \<and> d x' x < \<delta> \<longrightarrow> f x' \<in> V)))"
  by (force simp: limitin_def eventually_atin_metric)

lemma (in Metric_space) limitin_metric_dist_null:
   "limitin mtopology f l F \<longleftrightarrow> l \<in> M \<and> eventually (\<lambda>x. f x \<in> M) F \<and> ((\<lambda>x. d (f x) l) \<longlongrightarrow> 0) F"
  by (simp add: limitin_metric tendsto_iff eventually_conj_iff all_conj_distrib imp_conjR gt_ex)


subsection\<open>More sequential characterizations in a metric space\<close>

context Metric_space
begin

lemma submetric_empty [iff]: "submetric M d {}"
  by (simp add: Metric_space_axioms submetric.intro submetric_axioms_def)

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


subsection\<open>Cauchy sequences and complete metric spaces\<close>

context Metric_space
begin

definition MCauchy :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "MCauchy \<sigma> \<equiv> range \<sigma> \<subseteq> M \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>)"

definition mcomplete
  where "mcomplete \<equiv> (\<forall>\<sigma>. MCauchy \<sigma> \<longrightarrow> (\<exists>x. limitin mtopology \<sigma> x sequentially))"

lemma mcomplete_empty [iff]: "Metric_space.mcomplete {} d"
  by (simp add: Metric_space.MCauchy_def Metric_space.mcomplete_def subspace)

lemma MCauchy_imp_MCauchy_suffix: "MCauchy \<sigma> \<Longrightarrow> MCauchy (\<sigma> \<circ> (+)n)"
  unfolding MCauchy_def image_subset_iff comp_apply
  by (metis UNIV_I add.commute trans_le_add1) 

lemma mcomplete:
   "mcomplete \<longleftrightarrow>
    (\<forall>\<sigma>. (\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M) \<and>
     (\<forall>\<epsilon>>0. \<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>) \<longrightarrow>
     (\<exists>x. limitin mtopology \<sigma> x sequentially))" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof clarify
    fix \<sigma>
    assume "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M"
      and \<sigma>: "\<forall>\<epsilon>>0. \<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
    then obtain N where "\<And>n. n\<ge>N \<Longrightarrow> \<sigma> n \<in> M"
      by (auto simp: eventually_sequentially)
    with \<sigma> have "MCauchy (\<sigma> \<circ> (+)N)"
      unfolding MCauchy_def image_subset_iff comp_apply by (meson le_add1 trans_le_add2)
    then obtain x where "limitin mtopology (\<sigma> \<circ> (+)N) x sequentially"
      using L MCauchy_imp_MCauchy_suffix mcomplete_def by blast
    then have "limitin mtopology \<sigma> x sequentially"
      unfolding o_def by (auto simp: add.commute limitin_sequentially_offset_rev)
    then show "\<exists>x. limitin mtopology \<sigma> x sequentially" ..
  qed
qed (simp add: mcomplete_def MCauchy_def image_subset_iff)

lemma mcomplete_empty_mspace: "M = {} \<Longrightarrow> mcomplete"
  using MCauchy_def mcomplete_def by blast

lemma MCauchy_const [simp]: "MCauchy (\<lambda>n. a) \<longleftrightarrow> a \<in> M"
  using MCauchy_def mdist_zero by auto

lemma convergent_imp_MCauchy:
  assumes "range \<sigma> \<subseteq> M" and lim: "limitin mtopology \<sigma> l sequentially"
  shows "MCauchy \<sigma>"
  unfolding MCauchy_def image_subset_iff
proof (intro conjI strip)
  fix \<epsilon>::real
  assume "\<epsilon> > 0"
  then have "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M \<and> d (\<sigma> n) l < \<epsilon>/2"
    using half_gt_zero lim limitin_metric by blast
  then obtain N where "\<And>n. n\<ge>N \<Longrightarrow> \<sigma> n \<in> M \<and> d (\<sigma> n) l < \<epsilon>/2"
    by (force simp: eventually_sequentially)
  then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
    by (smt (verit) Metric_space.limitin_mspace Metric_space.mdist_reverse_triangle Metric_space_axioms field_sum_of_halves lim)
qed (use assms in blast)


lemma mcomplete_alt:
   "mcomplete \<longleftrightarrow> (\<forall>\<sigma>. MCauchy \<sigma> \<longleftrightarrow> range \<sigma> \<subseteq> M \<and> (\<exists>x. limitin mtopology \<sigma> x sequentially))"
  using MCauchy_def convergent_imp_MCauchy mcomplete_def by blast

lemma MCauchy_subsequence:
  assumes "strict_mono r" "MCauchy \<sigma>"
  shows "MCauchy (\<sigma> \<circ> r)"
proof -
  have "d (\<sigma> (r n)) (\<sigma> (r n')) < \<epsilon>"
    if "N \<le> n" "N \<le> n'" "strict_mono r" "\<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
    for \<epsilon> N n n'
    using that by (meson le_trans strict_mono_imp_increasing)
  then show ?thesis
    using assms 
    by (simp add: MCauchy_def) blast
qed

lemma MCauchy_offset:
  assumes cau: "MCauchy (\<sigma> \<circ> (+)k)" and \<sigma>: "\<And>n. n < k \<Longrightarrow> \<sigma> n \<in> M" 
  shows "MCauchy \<sigma>"
  unfolding MCauchy_def image_subset_iff
proof (intro conjI strip)
  fix n
  show "\<sigma> n \<in> M"
    using assms
    unfolding MCauchy_def image_subset_iff
    by (metis UNIV_I comp_apply le_iff_add linorder_not_le)
next
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  obtain N where "\<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d ((\<sigma> \<circ> (+)k) n) ((\<sigma> \<circ> (+)k) n') < \<epsilon>"
    using cau \<open>\<epsilon> > 0\<close> by (fastforce simp: MCauchy_def)
  then show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
    unfolding o_def
    apply (rule_tac x="k+N" in exI)
    by (smt (verit, del_insts) add.assoc le_add1 less_eqE)
qed

lemma MCauchy_convergent_subsequence:
  assumes cau: "MCauchy \<sigma>" and "strict_mono r" 
     and lim: "limitin mtopology (\<sigma> \<circ> r) a sequentially"
  shows "limitin mtopology \<sigma> a sequentially"
  unfolding limitin_metric
proof (intro conjI strip)
  show "a \<in> M"
    by (meson assms limitin_mspace)
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  then obtain N1 where N1: "\<And>n n'. \<lbrakk>n\<ge>N1; n'\<ge>N1\<rbrakk> \<Longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>/2"
    using cau unfolding MCauchy_def by (meson half_gt_zero)
  obtain N2 where N2: "\<And>n. n \<ge> N2 \<Longrightarrow> (\<sigma> \<circ> r) n \<in> M \<and> d ((\<sigma> \<circ> r) n) a < \<epsilon>/2"
    by (metis (no_types, lifting) lim \<open>\<epsilon> > 0\<close> half_gt_zero limit_metric_sequentially)
  have "\<sigma> n \<in> M \<and> d (\<sigma> n) a < \<epsilon>" if "n \<ge> max N1 N2" for n
  proof (intro conjI)
    show "\<sigma> n \<in> M"
      using MCauchy_def cau by blast
    have "N1 \<le> r n"
      by (meson \<open>strict_mono r\<close> le_trans max.cobounded1 strict_mono_imp_increasing that)
    then show "d (\<sigma> n) a < \<epsilon>"
      using N1[of n "r n"] N2[of n] \<open>\<sigma> n \<in> M\<close> \<open>a \<in> M\<close> triangle that by fastforce
  qed
  then show "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M \<and> d (\<sigma> n) a < \<epsilon>"
    using eventually_sequentially by blast
qed

lemma MCauchy_interleaving_gen:
  "MCauchy (\<lambda>n. if even n then x(n div 2) else y(n div 2)) \<longleftrightarrow>
    (MCauchy x \<and> MCauchy y \<and> (\<lambda>n. d (x n) (y n)) \<longlonglongrightarrow> 0)" (is "?lhs=?rhs")
proof
  assume L: ?lhs
  have evens: "strict_mono (\<lambda>n::nat. 2 * n)" and odds: "strict_mono (\<lambda>n::nat. Suc (2 * n))"
    by (auto simp: strict_mono_def)
  show ?rhs
  proof (intro conjI)
    show "MCauchy x" "MCauchy y"
      using MCauchy_subsequence [OF evens L] MCauchy_subsequence [OF odds L] by (auto simp: o_def)
    show "(\<lambda>n. d (x n) (y n)) \<longlonglongrightarrow> 0"
      unfolding LIMSEQ_iff
    proof (intro strip)
      fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      then obtain N where N: 
        "\<And>n n'. \<lbrakk>n\<ge>N; n'\<ge>N\<rbrakk> \<Longrightarrow> d (if even n then x (n div 2) else y (n div 2))
                                   (if even n' then x (n' div 2) else y (n' div 2))  < \<epsilon>"
        using L MCauchy_def by fastforce
      have "d (x n) (y n) < \<epsilon>" if "n\<ge>N" for n
        using N [of "2*n" "Suc(2*n)"] that by auto
      then show "\<exists>N. \<forall>n\<ge>N. norm (d (x n) (y n) - 0) < \<epsilon>"
        by auto
    qed
  qed
next
  assume R: ?rhs
  show ?lhs
    unfolding MCauchy_def
  proof (intro conjI strip)
    show "range (\<lambda>n. if even n then x (n div 2) else y (n div 2)) \<subseteq> M"
      using R by (auto simp: MCauchy_def)
    fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    obtain Nx where Nx: "\<And>n n'. \<lbrakk>n\<ge>Nx; n'\<ge>Nx\<rbrakk> \<Longrightarrow> d (x n) (x n')  < \<epsilon>/2"
      by (meson half_gt_zero MCauchy_def R \<open>\<epsilon> > 0\<close>)
    obtain Ny where Ny: "\<And>n n'. \<lbrakk>n\<ge>Ny; n'\<ge>Ny\<rbrakk> \<Longrightarrow> d (y n) (y n')  < \<epsilon>/2"
      by (meson half_gt_zero MCauchy_def R \<open>\<epsilon> > 0\<close>)
    obtain Nxy where Nxy: "\<And>n. n\<ge>Nxy \<Longrightarrow> d (x n) (y n) < \<epsilon>/2"
      using R \<open>\<epsilon> > 0\<close> half_gt_zero unfolding LIMSEQ_iff
      by (metis abs_mdist diff_zero real_norm_def)
    define N where "N \<equiv> 2 * Max{Nx,Ny,Nxy}"
    show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (if even n then x (n div 2) else y (n div 2)) (if even n' then x (n' div 2) else y (n' div 2)) < \<epsilon>"
    proof (intro exI strip)
      fix n n'
      assume "N \<le> n" and "N \<le> n'"
      then have "n div 2 \<ge> Nx" "n div 2 \<ge> Ny" "n div 2 \<ge> Nxy" "n' div 2 \<ge> Nx" "n' div 2 \<ge> Ny" 
        by (auto simp: N_def)
      then have dxyn: "d (x (n div 2)) (y (n div 2)) < \<epsilon>/2" 
            and dxnn': "d (x (n div 2)) (x (n' div 2)) < \<epsilon>/2"
            and dynn': "d (y (n div 2)) (y (n' div 2)) < \<epsilon>/2"
        using Nx Ny Nxy by blast+
      have inM: "x (n div 2) \<in> M" "x (n' div 2) \<in> M""y (n div 2) \<in> M" "y (n' div 2) \<in> M"
        using Metric_space.MCauchy_def Metric_space_axioms R by blast+
      show "d (if even n then x (n div 2) else y (n div 2)) (if even n' then x (n' div 2) else y (n' div 2)) < \<epsilon>"
      proof (cases "even n")
        case nt: True
        show ?thesis
        proof (cases "even n'")
          case True
          with \<open>\<epsilon> > 0\<close> nt dxnn' show ?thesis by auto
        next
          case False
          with nt dxyn dynn' inM triangle show ?thesis
            by fastforce
        qed
      next
        case nf: False
        show ?thesis 
        proof (cases "even n'")
          case True
          then show ?thesis
            by (smt (verit) \<open>\<epsilon> > 0\<close> dxyn dxnn' triangle commute inM field_sum_of_halves)
        next
          case False
          with \<open>\<epsilon> > 0\<close> nf dynn' show ?thesis by auto
        qed
      qed
    qed
  qed
qed

lemma MCauchy_interleaving:
   "MCauchy (\<lambda>n. if even n then \<sigma>(n div 2) else a) \<longleftrightarrow>
    range \<sigma> \<subseteq> M \<and> limitin mtopology \<sigma> a sequentially"  (is "?lhs=?rhs")
proof -
  have "?lhs \<longleftrightarrow> (MCauchy \<sigma> \<and> a \<in> M \<and> (\<lambda>n. d (\<sigma> n) a) \<longlonglongrightarrow> 0)"
    by (simp add: MCauchy_interleaving_gen [where y = "\<lambda>n. a"])
  also have "... = ?rhs"
    by (metis MCauchy_def always_eventually convergent_imp_MCauchy limitin_metric_dist_null range_subsetD)
  finally show ?thesis .
qed

lemma mcomplete_nest:
   "mcomplete \<longleftrightarrow>
      (\<forall>C::nat \<Rightarrow>'a set. (\<forall>n. closedin mtopology (C n)) \<and>
          (\<forall>n. C n \<noteq> {}) \<and> decseq C \<and> (\<forall>\<epsilon>>0. \<exists>n a. C n \<subseteq> mcball a \<epsilon>)
          \<longrightarrow> \<Inter> (range C) \<noteq> {})" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof (intro strip conjI , elim conjE)
    fix C :: "nat \<Rightarrow> 'a set"
    assume clo: "\<forall>n. closedin mtopology (C n)"
      and ne: "\<forall>n. C n \<noteq> ({}::'a set)"
      and dec: "decseq C"
      and cover [rule_format]: "\<forall>\<epsilon>>0. \<exists>n a. C n \<subseteq> mcball a \<epsilon>"
    obtain \<sigma> where \<sigma>: "\<And>n. \<sigma> n \<in> C n"
      by (meson ne empty_iff set_eq_iff)
    have "MCauchy \<sigma>"
      unfolding MCauchy_def
    proof (intro conjI strip)
      show "range \<sigma> \<subseteq> M"
        using \<sigma> clo metric_closedin_iff_sequentially_closed by auto 
      fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      then obtain N a where N: "C N \<subseteq> mcball a (\<epsilon>/3)"
        using cover by fastforce
      have "d (\<sigma> m) (\<sigma> n) < \<epsilon>" if "N \<le> m" "N \<le> n" for m n
      proof -
        have "d a (\<sigma> m) \<le> \<epsilon>/3" "d a (\<sigma> n) \<le> \<epsilon>/3"
          using dec N \<sigma> that by (fastforce simp: decseq_def)+
        then have "d (\<sigma> m) (\<sigma> n) \<le> \<epsilon>/3 + \<epsilon>/3"
          using triangle \<sigma> commute dec decseq_def subsetD that N
          by (smt (verit, ccfv_threshold) in_mcball)
        also have "... < \<epsilon>"
          using \<open>\<epsilon> > 0\<close> by auto
        finally show ?thesis .
      qed
      then show "\<exists>N. \<forall>m n. N \<le> m \<longrightarrow> N \<le> n \<longrightarrow> d (\<sigma> m) (\<sigma> n) < \<epsilon>"
        by blast
    qed
    then obtain x where x: "limitin mtopology \<sigma> x sequentially"
      using L mcomplete_def by blast
    have "x \<in> C n" for n
    proof (rule limitin_closedin [OF x])
      show "closedin mtopology (C n)"
        by (simp add: clo)
      show "\<forall>\<^sub>F x in sequentially. \<sigma> x \<in> C n"
        by (metis \<sigma> dec decseq_def eventually_sequentiallyI subsetD)
    qed auto
    then show "\<Inter> (range C) \<noteq> {}"
      by blast
qed
next
  assume R: ?rhs  
  show ?lhs
    unfolding mcomplete_def
  proof (intro strip)
    fix \<sigma>
    assume "MCauchy \<sigma>"
    then have "range \<sigma> \<subseteq> M"
      using MCauchy_def by blast
    define C where "C \<equiv> \<lambda>n. mtopology closure_of (\<sigma> ` {n..})"
    have "\<forall>n. closedin mtopology (C n)" 
      by (auto simp: C_def)
    moreover
    have ne: "\<And>n. C n \<noteq> {}"
      using \<open>MCauchy \<sigma>\<close> by (auto simp: C_def MCauchy_def disjnt_iff closure_of_eq_empty_gen)
    moreover
    have dec: "decseq C"
      unfolding monotone_on_def
    proof (intro strip)
      fix m n::nat
      assume "m \<le> n"
      then have "{n..} \<subseteq> {m..}"
        by auto
      then show "C n \<subseteq> C m"
        unfolding C_def by (meson closure_of_mono image_mono)
    qed
    moreover
    have C: "\<exists>N u. C N \<subseteq> mcball u \<epsilon>" if "\<epsilon>>0" for \<epsilon>
    proof -
      obtain N where "\<And>m n. N \<le> m \<and> N \<le> n \<Longrightarrow> d (\<sigma> m) (\<sigma> n) < \<epsilon>"
        by (meson MCauchy_def \<open>0 < \<epsilon>\<close> \<open>MCauchy \<sigma>\<close>)
      then have "\<sigma> ` {N..} \<subseteq> mcball (\<sigma> N) \<epsilon>"
        using MCauchy_def \<open>MCauchy \<sigma>\<close> by (force simp: less_eq_real_def)
      then have "C N \<subseteq> mcball (\<sigma> N) \<epsilon>"
        by (simp add: C_def closure_of_minimal)
      then show ?thesis
        by blast
    qed
    ultimately obtain l where x: "l \<in> \<Inter> (range C)"
      by (metis R ex_in_conv)
    then have *: "\<And>\<epsilon> N. 0 < \<epsilon> \<Longrightarrow> \<exists>n'. N \<le> n' \<and> l \<in> M \<and> \<sigma> n' \<in> M \<and> d l (\<sigma> n') < \<epsilon>"
      by (force simp: C_def metric_closure_of)
    then have "l \<in> M"
      using gt_ex by blast
    show "\<exists>l. limitin mtopology \<sigma> l sequentially"
      unfolding limitin_metric
    proof (intro conjI strip exI)
      show "l \<in> M"
        using \<open>\<forall>n. closedin mtopology (C n)\<close> closedin_subset x by fastforce
      fix \<epsilon>::real
      assume "\<epsilon> > 0"
      obtain N where N: "\<And>m n. N \<le> m \<and> N \<le> n \<Longrightarrow> d (\<sigma> m) (\<sigma> n) < \<epsilon>/2"
        by (meson MCauchy_def \<open>0 < \<epsilon>\<close> \<open>MCauchy \<sigma>\<close> half_gt_zero)
      with * [of "\<epsilon>/2" N]
      have "\<forall>n\<ge>N. \<sigma> n \<in> M \<and> d (\<sigma> n) l < \<epsilon>"
        by (smt (verit) \<open>range \<sigma> \<subseteq> M\<close> commute field_sum_of_halves range_subsetD triangle)
      then show "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> M \<and> d (\<sigma> n) l < \<epsilon>"
        using eventually_sequentially by blast
    qed
  qed
qed


lemma mcomplete_nest_sing:
   "mcomplete \<longleftrightarrow>
    (\<forall>C. (\<forall>n. closedin mtopology (C n)) \<and>
          (\<forall>n. C n \<noteq> {}) \<and> decseq C \<and> (\<forall>e>0. \<exists>n a. C n \<subseteq> mcball a e)
         \<longrightarrow> (\<exists>l. l \<in> M \<and> \<Inter> (range C) = {l}))"
proof -
  have *: False
    if clo: "\<forall>n. closedin mtopology (C n)"
      and cover: "\<forall>\<epsilon>>0. \<exists>n a. C n \<subseteq> mcball a \<epsilon>"
      and no_sing: "\<And>y. y \<in> M \<Longrightarrow> \<Inter> (range C) \<noteq> {y}"
      and l: "\<forall>n. l \<in> C n"
    for C :: "nat \<Rightarrow> 'a set" and l
  proof -
    have inM: "\<And>x. x \<in> \<Inter> (range C) \<Longrightarrow> x \<in> M"
      using closedin_metric clo by fastforce
    then have "l \<in> M"
      by (simp add: l)
    have False if l': "l' \<in> \<Inter> (range C)" and "l' \<noteq> l" for l'
    proof -
      have "l' \<in> M"
        using inM l' by blast
      obtain n a where na: "C n \<subseteq> mcball a (d l l' / 3)"
        using inM \<open>l \<in> M\<close> l' \<open>l' \<noteq> l\<close> cover by force
      then have "d a l \<le> (d l l' / 3)" "d a l' \<le> (d l l' / 3)" "a \<in> M"
        using l l' na in_mcball by auto
      then have "d l l' \<le> (d l l' / 3) + (d l l' / 3)"
        using \<open>l \<in> M\<close> \<open>l' \<in> M\<close> mdist_reverse_triangle by fastforce
      then show False
        using nonneg [of l l'] \<open>l' \<noteq> l\<close> \<open>l \<in> M\<close> \<open>l' \<in> M\<close> zero by force
    qed
    then show False
      by (metis l \<open>l \<in> M\<close> no_sing INT_I empty_iff insertI1 is_singletonE is_singletonI')
  qed
  show ?thesis
    unfolding mcomplete_nest imp_conjL 
    apply (intro all_cong1 imp_cong refl)
    using * 
    by (smt (verit) Inter_iff ex_in_conv range_constant range_eqI)
qed

lemma mcomplete_fip:
   "mcomplete \<longleftrightarrow>
    (\<forall>\<C>. (\<forall>C \<in> \<C>. closedin mtopology C) \<and>
         (\<forall>e>0. \<exists>C a. C \<in> \<C> \<and> C \<subseteq> mcball a e) \<and> (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<C> \<longrightarrow> \<Inter> \<F> \<noteq> {})
        \<longrightarrow> \<Inter> \<C> \<noteq> {})" 
   (is "?lhs = ?rhs")
proof
  assume L: ?lhs 
  show ?rhs
    unfolding mcomplete_nest_sing
  proof (intro strip, elim conjE)
    fix \<C> :: "'a set set"
    assume clo: "\<forall>C\<in>\<C>. closedin mtopology C"
      and cover: "\<forall>e>0. \<exists>C a. C \<in> \<C> \<and> C \<subseteq> mcball a e"
      and fip: "\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<C> \<longrightarrow> \<Inter> \<F> \<noteq> {}"
    then have "\<forall>n. \<exists>C. C \<in> \<C> \<and> (\<exists>a. C \<subseteq> mcball a (inverse (Suc n)))"
      by simp
    then obtain C where C: "\<And>n. C n \<in> \<C>" 
          and coverC: "\<And>n. \<exists>a. C n \<subseteq> mcball a (inverse (Suc n))"
      by metis
    define D where "D \<equiv> \<lambda>n. \<Inter> (C ` {..n})"
    have cloD: "closedin mtopology (D n)" for n
      unfolding D_def using clo C by blast
    have neD: "D n \<noteq> {}" for n
      using fip C by (simp add: D_def image_subset_iff)
    have decD: "decseq D"
      by (force simp: D_def decseq_def)
    have coverD: "\<exists>n a. D n \<subseteq> mcball a \<epsilon>" if " \<epsilon> >0" for \<epsilon>
    proof -
      obtain n where "inverse (Suc n) < \<epsilon>"
        using \<open>0 < \<epsilon>\<close> reals_Archimedean by blast
      then obtain a where "C n \<subseteq> mcball a \<epsilon>"
        by (meson coverC less_eq_real_def mcball_subset_concentric order_trans)
      then show ?thesis
        unfolding D_def by blast
    qed
    have *: "a \<in> \<Inter>\<C>" if a: "\<Inter> (range D) = {a}" and "a \<in> M" for a
    proof -
      have aC: "a \<in> C n" for n
        using that by (auto simp: D_def)
      have eqa: "\<And>u. (\<forall>n. u \<in> C n) \<Longrightarrow> a = u"
        using that by (auto simp: D_def)
      have "a \<in> T" if "T \<in> \<C>" for T
      proof -
        have cloT: "closedin mtopology (T \<inter> D n)" for n
          using clo cloD that by blast
        have "\<Inter> (insert T (C ` {..n})) \<noteq> {}" for n
          using that C by (intro fip [rule_format]) force
        then have neT: "T \<inter> D n \<noteq> {}" for n
          by (simp add: D_def)
        have decT: "decseq (\<lambda>n. T \<inter> D n)"
          by (force simp: D_def decseq_def)
        have coverT: "\<exists>n a. T \<inter> D n \<subseteq> mcball a \<epsilon>" if " \<epsilon> >0" for \<epsilon>
          by (meson coverD le_infI2 that)
        show ?thesis
          using L [unfolded mcomplete_nest_sing, rule_format, of "\<lambda>n. T \<inter> D n"] a
          by (force simp: cloT neT decT coverT)
      qed
      then show ?thesis by auto
    qed
    show "\<Inter> \<C> \<noteq> {}"
      by (metis L cloD neD decD coverD * empty_iff mcomplete_nest_sing)
  qed
next
  assume R [rule_format]: ?rhs
  show ?lhs
    unfolding mcomplete_nest
  proof (intro strip, elim conjE)
    fix C :: "nat \<Rightarrow> 'a set"
    assume clo: "\<forall>n. closedin mtopology (C n)"
      and ne: "\<forall>n. C n \<noteq> {}"
      and dec: "decseq C"
      and cover: "\<forall>\<epsilon>>0. \<exists>n a. C n \<subseteq> mcball a \<epsilon>"
    have "\<Inter>(C ` N) \<noteq> {}" if "finite N" for N
    proof -
      obtain k where "N \<subseteq> {..k}"
        using \<open>finite N\<close> finite_nat_iff_bounded_le by auto
      with dec have "C k \<subseteq> \<Inter>(C ` N)" by (auto simp: decseq_def)
      then show ?thesis
        using ne by force
    qed
    with clo cover R [of "range C"] show "\<Inter> (range C) \<noteq> {}"
      by (metis (no_types, opaque_lifting) finite_subset_image image_iff UNIV_I)
  qed
qed


lemma mcomplete_fip_sing:
   "mcomplete \<longleftrightarrow>
    (\<forall>\<C>. (\<forall>C\<in>\<C>. closedin mtopology C) \<and>
     (\<forall>e>0. \<exists>c a. c \<in> \<C> \<and> c \<subseteq> mcball a e) \<and>
     (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<C> \<longrightarrow> \<Inter> \<F> \<noteq> {}) \<longrightarrow>
     (\<exists>l. l \<in> M \<and> \<Inter> \<C> = {l}))"
   (is "?lhs = ?rhs")
proof
  have *: "l \<in> M" "\<Inter> \<C> = {l}"
    if clo: "Ball \<C> (closedin mtopology)"
      and cover: "\<forall>e>0. \<exists>C a. C \<in> \<C> \<and> C \<subseteq> mcball a e"
      and fin: "\<forall>\<F>. finite \<F> \<longrightarrow> \<F> \<subseteq> \<C> \<longrightarrow> \<Inter> \<F> \<noteq> {}"
      and l: "l \<in> \<Inter> \<C>"
    for \<C> :: "'a set set" and l
  proof -
    show "l \<in> M"
      by (meson Inf_lower2 clo cover gt_ex metric_closedin_iff_sequentially_closed subsetD that(4))
    show  "\<Inter> \<C> = {l}"
    proof (cases "\<C> = {}")
      case True
      then show ?thesis
        using cover mbounded_pos by auto
    next
      case False
      have CM: "\<And>a. a \<in> \<Inter>\<C> \<Longrightarrow> a \<in> M"
        using False clo closedin_subset by fastforce
      have "l' \<notin> \<Inter> \<C>" if "l' \<noteq> l" for l'
      proof 
        assume l': "l' \<in> \<Inter> \<C>"
        with CM have "l' \<in> M" by blast
        with that \<open>l \<in> M\<close> have gt0: "0 < d l l'"
          by simp
        then obtain C a where "C \<in> \<C>" and C: "C \<subseteq> mcball a (d l l' / 3)"
          using cover [rule_format, of "d l l' / 3"] by auto
        then have "d a l \<le> (d l l' / 3)" "d a l' \<le> (d l l' / 3)" "a \<in> M"
          using l l' in_mcball by auto
        then have "d l l' \<le> (d l l' / 3) + (d l l' / 3)"
          using \<open>l \<in> M\<close> \<open>l' \<in> M\<close> mdist_reverse_triangle by fastforce
        with gt0 show False by auto
      qed
      then show ?thesis
        using l by fastforce
    qed
  qed
  assume L: ?lhs
  with * show ?rhs
    unfolding mcomplete_fip imp_conjL ex_in_conv [symmetric]
    by (elim all_forward imp_forward2 asm_rl) (blast intro:  elim: )
next
  assume ?rhs then show ?lhs
    unfolding mcomplete_fip by (force elim!: all_forward)
qed

end

lemma MCauchy_iff_Cauchy [iff]: "Met.MCauchy = Cauchy"
  by (force simp: Cauchy_def Met.MCauchy_def)

lemma mcomplete_iff_complete [iff]:
  "Met.mcomplete (Pure.type ::'a::metric_space itself) \<longleftrightarrow> complete (UNIV::'a set)"
  by (auto simp: Met.mcomplete_def complete_def)

lemma euclidean_metric: "Met.mcomplete (Pure.type ::'a::euclidean_space itself)"
  by blast

context submetric
begin 

lemma MCauchy_submetric:
   "sub.MCauchy \<sigma> \<longleftrightarrow> range \<sigma> \<subseteq> A \<and> MCauchy \<sigma>"
  using MCauchy_def sub.MCauchy_def subset by force

lemma closedin_mcomplete_imp_mcomplete:
  assumes clo: "closedin mtopology A" and "mcomplete"
  shows "sub.mcomplete"
  unfolding sub.mcomplete_def
proof (intro strip)
  fix \<sigma>
  assume "sub.MCauchy \<sigma>"
  then have \<sigma>: "MCauchy \<sigma>" "range \<sigma> \<subseteq> A"
    using MCauchy_submetric by blast+
  then obtain x where x: "limitin mtopology \<sigma> x sequentially"
    using \<open>mcomplete\<close> unfolding mcomplete_def by blast
  then have "x \<in> A"
    using \<sigma> clo metric_closedin_iff_sequentially_closed by force
  with \<sigma> x show "\<exists>x. limitin sub.mtopology \<sigma> x sequentially"
    using limitin_submetric_iff range_subsetD by fastforce
qed


lemma sequentially_closedin_mcomplete_imp_mcomplete:
  assumes "mcomplete" and "\<And>\<sigma> l. range \<sigma> \<subseteq> A \<and> limitin mtopology \<sigma> l sequentially \<Longrightarrow> l \<in> A"
  shows "sub.mcomplete"
  using assms closedin_mcomplete_imp_mcomplete metric_closedin_iff_sequentially_closed subset by blast

end


context Metric_space
begin

lemma mcomplete_Un:
  assumes A: "submetric M d A" "Metric_space.mcomplete A d" 
      and B: "submetric M d B" "Metric_space.mcomplete B d"
  shows   "submetric M d (A \<union> B)" "Metric_space.mcomplete (A \<union> B) d" 
proof -
  show "submetric M d (A \<union> B)"
    by (meson assms le_sup_iff submetric_axioms_def submetric_def) 
  then interpret MAB: Metric_space "A \<union> B" d
    by (meson submetric.subset subspace)
  interpret MA: Metric_space A d
    by (meson A submetric.subset subspace)
  interpret MB: Metric_space B d
    by (meson B submetric.subset subspace)
  show "Metric_space.mcomplete (A \<union> B) d"
    unfolding MAB.mcomplete_def
  proof (intro strip)
    fix \<sigma>
    assume "MAB.MCauchy \<sigma>"
    then have "range \<sigma> \<subseteq> A \<union> B"
      using MAB.MCauchy_def by blast
    then have "UNIV \<subseteq> \<sigma> -` A \<union> \<sigma> -` B"
      by blast
    then consider "infinite (\<sigma> -` A)" | "infinite (\<sigma> -` B)"
      using finite_subset by auto
    then show "\<exists>x. limitin MAB.mtopology \<sigma> x sequentially"
    proof cases
      case 1
      then obtain r where "strict_mono r" and r: "\<And>n::nat. r n \<in> \<sigma> -` A"
        using infinite_enumerate by blast 
      then have "MA.MCauchy (\<sigma> \<circ> r)"
        using MA.MCauchy_def MAB.MCauchy_def MAB.MCauchy_subsequence \<open>MAB.MCauchy \<sigma>\<close> by auto
      with A obtain x where "limitin MA.mtopology (\<sigma> \<circ> r) x sequentially"
        using MA.mcomplete_def by blast
      then have "limitin MAB.mtopology (\<sigma> \<circ> r) x sequentially"
        by (metis MA.limit_metric_sequentially MAB.limit_metric_sequentially UnCI)
      then show ?thesis
        using MAB.MCauchy_convergent_subsequence \<open>MAB.MCauchy \<sigma>\<close> \<open>strict_mono r\<close> by blast
    next
      case 2
      then obtain r where "strict_mono r" and r: "\<And>n::nat. r n \<in> \<sigma> -` B"
        using infinite_enumerate by blast 
      then have "MB.MCauchy (\<sigma> \<circ> r)"
        using MB.MCauchy_def MAB.MCauchy_def MAB.MCauchy_subsequence \<open>MAB.MCauchy \<sigma>\<close> by auto
      with B obtain x where "limitin MB.mtopology (\<sigma> \<circ> r) x sequentially"
        using MB.mcomplete_def by blast
      then have "limitin MAB.mtopology (\<sigma> \<circ> r) x sequentially"
        by (metis MB.limit_metric_sequentially MAB.limit_metric_sequentially UnCI)
      then show ?thesis
        using MAB.MCauchy_convergent_subsequence \<open>MAB.MCauchy \<sigma>\<close> \<open>strict_mono r\<close> by blast
    qed
  qed
qed

lemma mcomplete_Union:
  assumes "finite \<S>"
    and "\<And>A. A \<in> \<S> \<Longrightarrow> submetric M d A" "\<And>A. A \<in> \<S> \<Longrightarrow> Metric_space.mcomplete A d"
  shows   "submetric M d (\<Union>\<S>)" "Metric_space.mcomplete (\<Union>\<S>) d" 
  using assms
  by (induction rule: finite_induct) (auto simp: mcomplete_Un)

lemma mcomplete_Inter:
  assumes "finite \<S>" "\<S> \<noteq> {}"
    and sub: "\<And>A. A \<in> \<S> \<Longrightarrow> submetric M d A" 
    and comp: "\<And>A. A \<in> \<S> \<Longrightarrow> Metric_space.mcomplete A d"
  shows "submetric M d (\<Inter>\<S>)" "Metric_space.mcomplete (\<Inter>\<S>) d"
proof -
  show "submetric M d (\<Inter>\<S>)"
    using assms unfolding submetric_def submetric_axioms_def
    by (metis Inter_lower equals0I inf.orderE le_inf_iff) 
  then interpret MS: submetric M d "\<Inter>\<S>" 
    by (meson submetric.subset subspace)
  show "Metric_space.mcomplete (\<Inter>\<S>) d"
    unfolding MS.sub.mcomplete_def
  proof (intro strip)
    fix \<sigma>
    assume "MS.sub.MCauchy \<sigma>"
    then have "range \<sigma> \<subseteq> \<Inter>\<S>"
      using MS.MCauchy_submetric by blast
    obtain A where "A \<in> \<S>" and A: "Metric_space.mcomplete A d"
      using assms by blast
    then have "range \<sigma> \<subseteq> A"
      using \<open>range \<sigma> \<subseteq> \<Inter>\<S>\<close> by blast
    interpret SA: submetric M d A
      by (meson \<open>A \<in> \<S>\<close> sub submetric.subset subspace)
    have "MCauchy \<sigma>"
      using MS.MCauchy_submetric \<open>MS.sub.MCauchy \<sigma>\<close> by blast
    then obtain x where x: "limitin SA.sub.mtopology \<sigma> x sequentially"
      by (metis A SA.sub.MCauchy_def SA.sub.mcomplete_alt MCauchy_def \<open>range \<sigma> \<subseteq> A\<close>)
    show "\<exists>x. limitin MS.sub.mtopology \<sigma> x sequentially"
      apply (rule_tac x="x" in exI)
      unfolding MS.limitin_submetric_iff
    proof (intro conjI)
      show "x \<in> \<Inter> \<S>"
      proof clarsimp
        fix U
        assume "U \<in> \<S>"
        interpret SU: submetric M d U 
          by (meson \<open>U \<in> \<S>\<close> sub submetric.subset subspace)
        have "range \<sigma> \<subseteq> U"
          using \<open>U \<in> \<S>\<close> \<open>range \<sigma> \<subseteq> \<Inter> \<S>\<close> by blast
        moreover have "Metric_space.mcomplete U d"
          by (simp add: \<open>U \<in> \<S>\<close> comp)
        ultimately obtain x' where x': "limitin SU.sub.mtopology \<sigma> x' sequentially"
          using MCauchy_def SU.sub.MCauchy_def SU.sub.mcomplete_alt \<open>MCauchy \<sigma>\<close> by meson 
        have "x' = x"
        proof (intro limitin_metric_unique)
          show "limitin mtopology \<sigma> x' sequentially"
            by (meson SU.submetric_axioms submetric.limitin_submetric_iff x')
          show "limitin mtopology \<sigma> x sequentially"
            by (meson SA.submetric_axioms submetric.limitin_submetric_iff x)
        qed auto
        then show "x \<in> U"
          using SU.sub.limitin_mspace x' by blast
      qed
      show "\<forall>\<^sub>F n in sequentially. \<sigma> n \<in> \<Inter>\<S>"
        by (meson \<open>range \<sigma> \<subseteq> \<Inter> \<S>\<close> always_eventually range_subsetD)
      show "limitin mtopology \<sigma> x sequentially"
        by (meson SA.submetric_axioms submetric.limitin_submetric_iff x)
    qed
  qed
qed


lemma mcomplete_Int:
  assumes A: "submetric M d A" "Metric_space.mcomplete A d" 
      and B: "submetric M d B" "Metric_space.mcomplete B d"
    shows   "submetric M d (A \<inter> B)" "Metric_space.mcomplete (A \<inter> B) d"
  using mcomplete_Inter [of "{A,B}"] assms by force+


subsection\<open>Totally bounded subsets of metric spaces\<close>

definition mtotally_bounded 
  where "mtotally_bounded S \<equiv> \<forall>\<epsilon>>0. \<exists>K. finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"

lemma mtotally_bounded_empty [iff]: "mtotally_bounded {}"
by (simp add: mtotally_bounded_def)

lemma finite_imp_mtotally_bounded:
   "\<lbrakk>finite S; S \<subseteq> M\<rbrakk> \<Longrightarrow> mtotally_bounded S"
  by (auto simp: mtotally_bounded_def)

lemma mtotally_bounded_imp_subset: "mtotally_bounded S \<Longrightarrow> S \<subseteq> M"
  by (force simp: mtotally_bounded_def intro!: zero_less_one)

lemma mtotally_bounded_sing [simp]:
   "mtotally_bounded {x} \<longleftrightarrow> x \<in> M"
  by (meson empty_subsetI finite.simps finite_imp_mtotally_bounded insert_subset mtotally_bounded_imp_subset)

lemma mtotally_bounded_Un:
  assumes  "mtotally_bounded S" "mtotally_bounded T"
  shows "mtotally_bounded (S \<union> T)"
proof -
  have "\<exists>K. finite K \<and> K \<subseteq> S \<union> T \<and> S \<union> T \<subseteq> (\<Union>x\<in>K. mball x e)"
    if  "e>0" and K: "finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x e)"
      and L: "finite L \<and> L \<subseteq> T \<and> T \<subseteq> (\<Union>x\<in>L. mball x e)" for K L e
    using that by (rule_tac x="K \<union> L" in exI) auto
  with assms show ?thesis
    unfolding mtotally_bounded_def by presburger
qed
 
lemma mtotally_bounded_Union:
  assumes "finite f" "\<And>S. S \<in> f \<Longrightarrow> mtotally_bounded S"
  shows "mtotally_bounded (\<Union>f)"
  using assms by (induction f) (auto simp: mtotally_bounded_Un)

lemma mtotally_bounded_imp_mbounded:
  assumes "mtotally_bounded S"
  shows "mbounded S"
proof -
  obtain K where "finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x 1)" 
    using assms by (force simp: mtotally_bounded_def)
  then show ?thesis
    by (smt (verit) finite_imageI image_iff mbounded_Union mbounded_mball mbounded_subset)
qed


lemma mtotally_bounded_sequentially:
  "mtotally_bounded S \<longleftrightarrow>
    S \<subseteq> M \<and> (\<forall>\<sigma>::nat \<Rightarrow> 'a. range \<sigma> \<subseteq> S \<longrightarrow> (\<exists>r. strict_mono r \<and> MCauchy (\<sigma> \<circ> r)))"
  (is "_ \<longleftrightarrow> _ \<and> ?rhs")
proof (cases "S \<subseteq> M")
  case True
  show ?thesis
  proof -
    { fix \<sigma> :: "nat \<Rightarrow> 'a"                                                            
      assume L: "mtotally_bounded S" and \<sigma>: "range \<sigma> \<subseteq> S"
      have "\<exists>j > i. d (\<sigma> i) (\<sigma> j) < 3*\<epsilon>/2 \<and> infinite (\<sigma> -` mball (\<sigma> j) (\<epsilon>/2))"
        if inf: "infinite (\<sigma> -` mball (\<sigma> i) \<epsilon>)" and "\<epsilon> > 0" for i \<epsilon>
      proof -
        obtain K where "finite K" "K \<subseteq> S" and K: "S \<subseteq> (\<Union>x\<in>K. mball x (\<epsilon>/4))"
          by (metis L mtotally_bounded_def \<open>\<epsilon> > 0\<close> zero_less_divide_iff zero_less_numeral)
        then have K_imp_ex: "\<And>y. y \<in> S \<Longrightarrow> \<exists>x\<in>K. d x y < \<epsilon>/4"
          by fastforce
        have False if "\<forall>x\<in>K. d x (\<sigma> i) < \<epsilon> + \<epsilon>/4 \<longrightarrow> finite (\<sigma> -` mball x (\<epsilon>/4))"
        proof -
          have "\<exists>w. w \<in> K \<and> d w (\<sigma> i) < 5 * \<epsilon>/4 \<and> d w (\<sigma> j) < \<epsilon>/4"
            if "d (\<sigma> i) (\<sigma> j) < \<epsilon>" for j
          proof -
            obtain w where w: "d w (\<sigma> j) < \<epsilon>/4" "w \<in> K"
              using K_imp_ex \<sigma> by blast
            then have "d w (\<sigma> i) < \<epsilon> + \<epsilon>/4"
              by (smt (verit, ccfv_SIG) True \<open>K \<subseteq> S\<close> \<sigma> rangeI subset_eq that triangle')
            with w show ?thesis
              using in_mball by auto
          qed
          then have "(\<sigma> -` mball (\<sigma> i) \<epsilon>) \<subseteq> (\<Union>x\<in>K. if d x (\<sigma> i) < \<epsilon> + \<epsilon>/4 then \<sigma> -` mball x (\<epsilon>/4) else {})"
            using True \<open>K \<subseteq> S\<close> by force
          then show False
            using finite_subset inf \<open>finite K\<close> that by fastforce
        qed
        then obtain x where "x \<in> K" and dxi: "d x (\<sigma> i) < \<epsilon> + \<epsilon>/4" and infx: "infinite (\<sigma> -` mball x (\<epsilon>/4))"
          by blast
        then obtain j where "j \<in> (\<sigma> -` mball x (\<epsilon>/4)) - {..i}"
          using bounded_nat_set_is_finite by (meson Diff_infinite_finite finite_atMost)
        then have "j > i" and dxj: "d x (\<sigma> j) < \<epsilon>/4" 
          by auto
        have "(\<sigma> -` mball x (\<epsilon>/4)) \<subseteq> (\<sigma> -` mball y (\<epsilon>/2))" if "d x y < \<epsilon>/4" "y \<in> M" for y
          using that by (simp add: mball_subset Metric_space_axioms vimage_mono)
        then have infj: "infinite (\<sigma> -` mball (\<sigma> j) (\<epsilon>/2))"
          by (meson True \<open>d x (\<sigma> j) < \<epsilon>/4\<close> \<sigma> in_mono infx rangeI finite_subset)
        have "\<sigma> i \<in> M" "\<sigma> j \<in> M" "x \<in> M"  
          using True \<open>K \<subseteq> S\<close> \<open>x \<in> K\<close> \<sigma> by force+
        then have "d (\<sigma> i) (\<sigma> j) \<le> d x (\<sigma> i) + d x (\<sigma> j)"
          using triangle'' by blast
        also have "\<dots> < 3*\<epsilon>/2"
          using dxi dxj by auto
        finally have "d (\<sigma> i) (\<sigma> j) < 3*\<epsilon>/2" .
        with \<open>i < j\<close> infj show ?thesis by blast
      qed
      then obtain nxt where nxt: "\<And>i \<epsilon>. \<lbrakk>\<epsilon> > 0; infinite (\<sigma> -` mball (\<sigma> i) \<epsilon>)\<rbrakk> \<Longrightarrow> 
                 nxt i \<epsilon> > i \<and> d (\<sigma> i) (\<sigma> (nxt i \<epsilon>)) < 3*\<epsilon>/2 \<and> infinite (\<sigma> -` mball (\<sigma> (nxt i \<epsilon>)) (\<epsilon>/2))"
        by metis
      have "mbounded S"
        using L by (simp add: mtotally_bounded_imp_mbounded)
      then obtain B where B: "\<forall>y \<in> S. d (\<sigma> 0) y \<le> B" and "B > 0"
        by (meson \<sigma> mbounded_alt_pos range_subsetD)
      define eps where "eps \<equiv> \<lambda>n. (B+1) / 2^n"
      have [simp]: "eps (Suc n) = eps n / 2" "eps n > 0" for n
        using \<open>B > 0\<close> by (auto simp: eps_def)
      have "UNIV \<subseteq> \<sigma> -` mball (\<sigma> 0) (B+1)"
        using B True \<sigma> unfolding image_iff subset_iff
        by (smt (verit, best) UNIV_I in_mball vimageI)
      then have inf0: "infinite (\<sigma> -` mball (\<sigma> 0) (eps 0))"
        using finite_subset by (auto simp: eps_def)
      define r where "r \<equiv> rec_nat 0 (\<lambda>n rec. nxt rec (eps n))"
      have [simp]: "r 0 = 0" "r (Suc n) = nxt (r n) (eps n)" for n
        by (auto simp: r_def)
      have \<sigma>rM[simp]: "\<sigma> (r n) \<in> M" for n
        using True \<sigma> by blast
      have inf: "infinite (\<sigma> -` mball (\<sigma> (r n)) (eps n))" for n
      proof (induction n)
        case 0 then show ?case  
          by (simp add: inf0)
      next
        case (Suc n) then show ?case
          using nxt [of "eps n" "r n"] by simp
      qed
      then have "r (Suc n) > r n" for n
        by (simp add: nxt)
      then have "strict_mono r"
        using strict_monoI_Suc by blast
      have d_less: "d (\<sigma> (r n)) (\<sigma> (r (Suc n))) < 3 * eps n / 2" for n
        using nxt [OF _ inf] by simp
      have eps_plus: "eps (k + n) = eps n * (1/2)^k" for k n
        by (simp add: eps_def power_add field_simps)
      have *: "d (\<sigma> (r n)) (\<sigma> (r (k + n))) < 3 * eps n" for n k
      proof -
        have "d (\<sigma> (r n)) (\<sigma> (r (k+n))) \<le> 3/2 * eps n * (\<Sum>i<k. (1/2)^i)"
        proof (induction k)
          case 0 then show ?case 
            by simp
        next
          case (Suc k)
          have "d (\<sigma> (r n)) (\<sigma> (r (Suc k + n))) \<le> d (\<sigma> (r n)) (\<sigma> (r (k + n))) + d (\<sigma> (r (k + n))) (\<sigma> (r (Suc (k + n))))"
            by (metis \<sigma>rM add.commute add_Suc_right triangle)
          with d_less[of "k+n"] Suc show ?case
            by (simp add: algebra_simps eps_plus)
        qed
        also have "\<dots> < 3/2 * eps n * 2"
          using geometric_sum [of "1/2::real" k] by simp
        finally show ?thesis by simp
      qed
      have "\<exists>N. \<forall>n\<ge>N. \<forall>n'\<ge>N. d (\<sigma> (r n)) (\<sigma> (r n')) < \<epsilon>" if "\<epsilon> > 0" for \<epsilon>
      proof -
        define N where "N \<equiv> nat \<lceil>(log 2 (6*(B+1) / \<epsilon>))\<rceil>"
        have \<section>: "b \<le> 2 ^ nat \<lceil>log 2 b\<rceil>" for b
          by (smt (verit) less_log_of_power real_nat_ceiling_ge)
        have N: "6 * eps N \<le> \<epsilon>"
          using \<section> [of "(6*(B+1) / \<epsilon>)"] that by (auto simp: N_def eps_def field_simps)
        have "d (\<sigma> (r N)) (\<sigma> (r n)) < 3 * eps N" if "n \<ge> N" for n
          by (metis * add.commute nat_le_iff_add that)
        then have "\<forall>n\<ge>N. \<forall>n'\<ge>N. d (\<sigma> (r n)) (\<sigma> (r n')) < 3 * eps N + 3 * eps N"
          by (smt (verit, best) \<sigma>rM triangle'')
        with N show ?thesis
          by fastforce
      qed
      then have "MCauchy (\<sigma> \<circ> r)"
        unfolding MCauchy_def using True \<sigma> by auto
      then have "\<exists>r. strict_mono r \<and> MCauchy (\<sigma> \<circ> r)"
        using \<open>strict_mono r\<close> by blast      
    }
    moreover
    { assume R: ?rhs
      have "mtotally_bounded S"
        unfolding mtotally_bounded_def
      proof (intro strip)
        fix \<epsilon> :: real
        assume "\<epsilon> > 0"
        have False if \<section>: "\<And>K. \<lbrakk>finite K; K \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>s\<in>S. s \<notin> (\<Union>x\<in>K. mball x \<epsilon>)"
        proof -
          obtain f where f: "\<And>K. \<lbrakk>finite K; K \<subseteq> S\<rbrakk> \<Longrightarrow> f K \<in> S \<and> f K \<notin> (\<Union>x\<in>K. mball x \<epsilon>)"
            using \<section> by metis
          define \<sigma> where "\<sigma> \<equiv> wfrec less_than (\<lambda>seq n. f (seq ` {..<n}))"
          have \<sigma>_eq: "\<sigma> n = f (\<sigma> ` {..<n})" for n
            by (simp add: cut_apply def_wfrec [OF \<sigma>_def])
          have [simp]: "\<sigma> n \<in> S" for n
            using wf_less_than
          proof (induction n rule: wf_induct_rule)
            case (less n) with f show ?case
              by (auto simp: \<sigma>_eq [of n])
          qed
          then have "range \<sigma> \<subseteq> S" by blast
          have \<sigma>: "p < n \<Longrightarrow> \<epsilon> \<le> d (\<sigma> p) (\<sigma> n)" for n p
            using f[of "\<sigma> ` {..<n}"] True by (fastforce simp: \<sigma>_eq [of n] Ball_def)
          then obtain r where "strict_mono r" "MCauchy (\<sigma> \<circ> r)"
            by (meson R \<open>range \<sigma> \<subseteq> S\<close>)
          with \<open>0 < \<epsilon>\<close> obtain N 
            where N: "\<And>n n'. \<lbrakk>n\<ge>N; n'\<ge>N\<rbrakk> \<Longrightarrow> d (\<sigma> (r n)) (\<sigma> (r n')) < \<epsilon>"
            by (force simp: MCauchy_def)
          show ?thesis
            using N [of N "Suc (r N)"] \<open>strict_mono r\<close>
            by (smt (verit) Suc_le_eq \<sigma> le_SucI order_refl strict_mono_imp_increasing)
        qed
        then show "\<exists>K. finite K \<and> K \<subseteq> S \<and> S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
          by blast
      qed
    }
    ultimately show ?thesis 
      using True by blast
  qed
qed (use mtotally_bounded_imp_subset in auto)


lemma mtotally_bounded_subset:
   "\<lbrakk>mtotally_bounded S; T \<subseteq> S\<rbrakk> \<Longrightarrow> mtotally_bounded T"
  by (meson mtotally_bounded_sequentially order_trans) 

lemma mtotally_bounded_submetric:
  assumes "mtotally_bounded S" "S \<subseteq> T" "T \<subseteq> M"
  shows "Metric_space.mtotally_bounded T d S"
proof -
  interpret submetric M d T
    by (simp add: Metric_space_axioms assms submetric.intro submetric_axioms.intro)
  show ?thesis
    using assms
    unfolding sub.mtotally_bounded_def mtotally_bounded_def
    by (force simp: subset_iff elim!: all_forward ex_forward)
qed

lemma mtotally_bounded_absolute:
   "mtotally_bounded S \<longleftrightarrow> S \<subseteq> M \<and> Metric_space.mtotally_bounded S d S "
proof -
  have "mtotally_bounded S" if "S \<subseteq> M" "Metric_space.mtotally_bounded S d S"
  proof -
    interpret submetric M d S
      by (simp add: Metric_space_axioms submetric_axioms.intro submetric_def \<open>S \<subseteq> M\<close>)
    show ?thesis
      using that
      by (metis MCauchy_submetric Metric_space.mtotally_bounded_sequentially Metric_space_axioms subspace)
  qed
  moreover have "mtotally_bounded S \<Longrightarrow> Metric_space.mtotally_bounded S d S"
    by (simp add: mtotally_bounded_imp_subset mtotally_bounded_submetric)
  ultimately show ?thesis
    using mtotally_bounded_imp_subset by blast
qed

lemma mtotally_bounded_closure_of:
  assumes "mtotally_bounded S"
  shows "mtotally_bounded (mtopology closure_of S)"
proof -
  have "S \<subseteq> M"
    by (simp add: assms mtotally_bounded_imp_subset)
  have "mtotally_bounded(mtopology closure_of S)"
    unfolding mtotally_bounded_def
  proof (intro strip)
    fix \<epsilon>::real
    assume "\<epsilon> > 0"
    then obtain K where "finite K" "K \<subseteq> S" and K: "S \<subseteq> (\<Union>x\<in>K. mball x (\<epsilon>/2))"
      by (metis assms mtotally_bounded_def half_gt_zero)
    have "mtopology closure_of S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
      unfolding metric_closure_of
    proof clarsimp
      fix x
      assume "x \<in> M" and x: "\<forall>r>0. \<exists>y\<in>S. y \<in> M \<and> d x y < r"
      then obtain y where "y \<in> S" and y: "d x y < \<epsilon>/2"
        using \<open>0 < \<epsilon>\<close> half_gt_zero by blast
      then obtain x' where "x' \<in> K" "y \<in> mball x' (\<epsilon>/2)"
        using K by auto
      then have "d x' x < \<epsilon>/2 + \<epsilon>/2"
        using triangle y \<open>x \<in> M\<close> commute by fastforce
      then show "\<exists>x'\<in>K. x' \<in> M \<and> d x' x < \<epsilon>"
        using \<open>K \<subseteq> S\<close> \<open>S \<subseteq> M\<close> \<open>x' \<in> K\<close> by force
    qed
    then show "\<exists>K. finite K \<and> K \<subseteq> mtopology closure_of S \<and> mtopology closure_of S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
      using closure_of_subset_Int  \<open>K \<subseteq> S\<close> \<open>finite K\<close> K by fastforce
  qed
  then show ?thesis
    by (simp add: assms inf.absorb2 mtotally_bounded_imp_subset)
qed

lemma mtotally_bounded_closure_of_eq:
   "S \<subseteq> M \<Longrightarrow> mtotally_bounded (mtopology closure_of S) \<longleftrightarrow> mtotally_bounded S"
  by (metis closure_of_subset mtotally_bounded_closure_of mtotally_bounded_subset topspace_mtopology)

lemma mtotally_bounded_cauchy_sequence:
  assumes "MCauchy \<sigma>"
  shows "mtotally_bounded (range \<sigma>)"
  unfolding MCauchy_def mtotally_bounded_def
proof (intro strip)
  fix \<epsilon>::real
  assume "\<epsilon> > 0"
  then obtain N where "\<And>n. N \<le> n \<Longrightarrow> d (\<sigma> N) (\<sigma> n) < \<epsilon>"
    using assms by (force simp: MCauchy_def)
  then have "\<And>m. \<exists>n\<le>N. \<sigma> n \<in> M \<and> \<sigma> m \<in> M \<and> d (\<sigma> n) (\<sigma> m) < \<epsilon>"
    by (metis MCauchy_def assms mdist_zero nle_le range_subsetD)
  then
  show "\<exists>K. finite K \<and> K \<subseteq> range \<sigma> \<and> range \<sigma> \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
    by (rule_tac x="\<sigma> ` {0..N}" in exI) force
qed

lemma MCauchy_imp_mbounded:
   "MCauchy \<sigma> \<Longrightarrow> mbounded (range \<sigma>)"
  by (simp add: mtotally_bounded_cauchy_sequence mtotally_bounded_imp_mbounded)


subsection\<open>Compactness in metric spaces\<close>

lemma Bolzano_Weierstrass_property:
  assumes "S \<subseteq> U" "S \<subseteq> M"
  shows
   "(\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> S
         \<longrightarrow> (\<exists>l r. l \<in> U \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially)) \<longleftrightarrow>
    (\<forall>T. T \<subseteq> S \<and> infinite T \<longrightarrow> U \<inter> mtopology derived_set_of T \<noteq> {})"  (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof clarify
    fix T
    assume "T \<subseteq> S" and "infinite T"
      and T: "U \<inter> mtopology derived_set_of T = {}"
    then obtain \<sigma> :: "nat\<Rightarrow>'a" where "inj \<sigma>" "range \<sigma> \<subseteq> T"
      by (meson infinite_countable_subset)
    with L obtain l r where "l \<in> U" "strict_mono r" 
           and lr: "limitin mtopology (\<sigma> \<circ> r) l sequentially"
      by (meson \<open>T \<subseteq> S\<close> subset_trans)
    then obtain \<epsilon> where "\<epsilon> > 0" and \<epsilon>: "\<And>y. y \<in> T \<Longrightarrow> y = l \<or> \<not> d l y < \<epsilon>"
      using T \<open>T \<subseteq> S\<close> \<open>S \<subseteq> M\<close> 
      by (force simp: metric_derived_set_of limitin_metric disjoint_iff)
    with lr have "\<forall>\<^sub>F n in sequentially. \<sigma> (r n) \<in> M \<and> d (\<sigma> (r n)) l < \<epsilon>"
      by (auto simp: limitin_metric)
    then obtain N where N: "d (\<sigma> (r N)) l < \<epsilon>" "d (\<sigma> (r (Suc N))) l < \<epsilon>"
      using less_le_not_le by (auto simp: eventually_sequentially)
    moreover have "\<sigma> (r N) \<noteq> l \<or> \<sigma> (r (Suc N)) \<noteq> l"
      by (meson \<open>inj \<sigma>\<close> \<open>strict_mono r\<close> injD n_not_Suc_n strict_mono_eq)
    ultimately
    show False
       using \<epsilon> \<open>range \<sigma> \<subseteq> T\<close> commute by fastforce
  qed
next
  assume R: ?rhs 
  show ?lhs
  proof (intro strip)
    fix \<sigma> :: "nat \<Rightarrow> 'a"
    assume "range \<sigma> \<subseteq> S"
    show "\<exists>l r. l \<in> U \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially"
    proof (cases "finite (range \<sigma>)")
      case True
      then obtain m where "infinite (\<sigma> -` {\<sigma> m})"
        by (metis image_iff inf_img_fin_dom nat_not_finite)
      then obtain r where [iff]: "strict_mono r" and r: "\<And>n::nat. r n \<in> \<sigma> -` {\<sigma> m}"
        using infinite_enumerate by blast 
      have [iff]: "\<sigma> m \<in> U" "\<sigma> m \<in> M"
        using \<open>range \<sigma> \<subseteq> S\<close> assms by blast+
      show ?thesis
      proof (intro conjI exI)
        show "limitin mtopology (\<sigma> \<circ> r) (\<sigma> m) sequentially"
          using r by (simp add: limitin_metric)
      qed auto
    next
      case False
      then obtain l where "l \<in> U" and l: "l \<in> mtopology derived_set_of (range \<sigma>)"
        by (meson R \<open>range \<sigma> \<subseteq> S\<close> disjoint_iff)
      then obtain g where g: "\<And>\<epsilon>. \<epsilon>>0 \<Longrightarrow> \<sigma> (g \<epsilon>) \<noteq> l \<and> d l (\<sigma> (g \<epsilon>)) < \<epsilon>"
        by (simp add: metric_derived_set_of) metis
      have "range \<sigma> \<subseteq> M"
        using \<open>range \<sigma> \<subseteq> S\<close> assms by auto
      have "l \<in> M"
        using derived_set_of_sequentially_decreasing l by blast
      define E where  \<comment>\<open>a construction to ensure monotonicity\<close>
        "E \<equiv> \<lambda>rec n. insert (inverse (Suc n)) ((\<lambda>i. d l (\<sigma> i)) ` (\<Union>k<n. {0..rec k})) - {0}"
      define r where "r \<equiv> wfrec less_than (\<lambda>rec n. g (Min (E rec n)))"
      have "(\<Union>k<n. {0..cut r less_than n k}) = (\<Union>k<n. {0..r k})" for n
        by (auto simp: cut_apply)
      then have r_eq: "r n = g (Min (E r n))" for n
        by (metis E_def def_wfrec [OF r_def] wf_less_than)
      have dl_pos[simp]: "d l (\<sigma> (r n)) > 0" for n
        using wf_less_than
      proof (induction n rule: wf_induct_rule)
        case (less n) 
        then have *: "Min (E r n) > 0"
          using \<open>l \<in> M\<close> \<open>range \<sigma> \<subseteq> M\<close> by (auto simp: E_def image_subset_iff)
        show ?case
          using g [OF *] r_eq [of n]
          by (metis \<open>l \<in> M\<close> \<open>range \<sigma> \<subseteq> M\<close> mdist_pos_less range_subsetD)
      qed
      then have non_l: "\<sigma> (r n) \<noteq> l" for n
        using \<open>range \<sigma> \<subseteq> M\<close> mdist_pos_eq by blast
      have Min_pos: "Min (E r n) > 0" for n
        using dl_pos \<open>l \<in> M\<close> \<open>range \<sigma> \<subseteq> M\<close> by (auto simp: E_def image_subset_iff)
      have d_small: "d (\<sigma>(r n)) l < inverse(Suc n)" for n
      proof -
        have "d (\<sigma>(r n)) l < Min (E r n)"
          by (simp add: \<open>0 < Min (E r n)\<close> commute g r_eq) 
        also have "... \<le> inverse(Suc n)"
          by (simp add: E_def)
        finally show ?thesis .
      qed
      have d_lt_d: "d l (\<sigma> (r n)) < d l (\<sigma> i)" if \<section>: "p < n" "i \<le> r p" "\<sigma> i \<noteq> l" for i p n
      proof -
        have 1: "d l (\<sigma> i) \<in> E r n"
          using \<section> \<open>l \<in> M\<close> \<open>range \<sigma> \<subseteq> M\<close> 
          by (force simp: E_def image_subset_iff image_iff)
        have "d l (\<sigma> (g (Min (E r n)))) < Min (E r n)"
          by (rule conjunct2 [OF g [OF Min_pos]])
        also have "Min (E r n) \<le> d l (\<sigma> i)"
          using 1 unfolding E_def by (force intro!: Min.coboundedI)
        finally show ?thesis
          by (simp add: r_eq) 
      qed
      have r: "r p < r n" if "p < n" for p n
        using d_lt_d [OF that] non_l by (meson linorder_not_le order_less_irrefl) 
      show ?thesis
      proof (intro exI conjI)
        show "strict_mono r"
          by (simp add: r strict_monoI)
        show "limitin mtopology (\<sigma> \<circ> r) l sequentially"
          unfolding limitin_metric
        proof (intro conjI strip)
          show "l \<in> M"
            using derived_set_of_sequentially_inj l by blast
          fix \<epsilon> :: real
          assume "\<epsilon> > 0"
          then have "\<forall>\<^sub>F n in sequentially. inverse(Suc n) < \<epsilon>"
            using Archimedean_eventually_inverse by auto
          then show "\<forall>\<^sub>F n in sequentially. (\<sigma> \<circ> r) n \<in> M \<and> d ((\<sigma> \<circ> r) n) l < \<epsilon>"
            by (smt (verit) \<open>range \<sigma> \<subseteq> M\<close> commute comp_apply d_small eventually_mono range_subsetD)
        qed
      qed (use \<open>l \<in> U\<close> in auto)
    qed
  qed
qed

subsubsection \<open>More on Bolzano Weierstrass\<close>

lemma Bolzano_Weierstrass_A: 
  assumes "compactin mtopology S" "T \<subseteq> S" "infinite T"
  shows "S \<inter> mtopology derived_set_of T \<noteq> {}"
  by (simp add: assms compactin_imp_Bolzano_Weierstrass)

lemma Bolzano_Weierstrass_B:
  fixes \<sigma> :: "nat \<Rightarrow> 'a"
  assumes "S \<subseteq> M" "range \<sigma> \<subseteq> S"
    and "\<And>T. \<lbrakk>T \<subseteq> S \<and> infinite T\<rbrakk> \<Longrightarrow> S \<inter> mtopology derived_set_of T \<noteq> {}"
  shows "\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> o r) l sequentially"
  using Bolzano_Weierstrass_property assms by blast

lemma Bolzano_Weierstrass_C:
  assumes "S \<subseteq> M"
  assumes "\<And>\<sigma>:: nat \<Rightarrow> 'a. range \<sigma> \<subseteq> S \<Longrightarrow>
                (\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> o r) l sequentially)"
  shows "mtotally_bounded S"
  unfolding mtotally_bounded_sequentially
  by (metis convergent_imp_MCauchy assms image_comp image_mono subset_UNIV subset_trans)

lemma Bolzano_Weierstrass_D:
  assumes "S \<subseteq> M" "S \<subseteq> \<Union>\<C>" and opeU: "\<And>U. U \<in> \<C> \<Longrightarrow> openin mtopology U"
  assumes \<section>: "(\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> S
         \<longrightarrow> (\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially))"
  shows "\<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U"
proof (rule ccontr)
  assume "\<not> (\<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U)"
  then have "\<forall>n. \<exists>x\<in>S. \<forall>U\<in>\<C>. \<not> mball x (inverse (Suc n)) \<subseteq> U"
    by simp
  then obtain \<sigma> where "\<And>n. \<sigma> n \<in> S" 
       and \<sigma>: "\<And>n U. U \<in> \<C> \<Longrightarrow> \<not> mball (\<sigma> n) (inverse (Suc n)) \<subseteq> U"
    by metis
  then obtain l r where "l \<in> S" "strict_mono r" 
         and lr: "limitin mtopology (\<sigma> \<circ> r) l sequentially"
    by (meson \<section> image_subsetI)
  with \<open>S \<subseteq> \<Union>\<C>\<close> obtain B where "l \<in> B" "B \<in> \<C>"
    by auto
  then obtain \<epsilon> where "\<epsilon> > 0" and \<epsilon>: "\<And>z. \<lbrakk>z \<in> M; d z l < \<epsilon>\<rbrakk> \<Longrightarrow> z \<in> B"
    by (metis opeU [OF \<open>B \<in> \<C>\<close>] commute in_mball openin_mtopology subset_iff)
  then have "\<forall>\<^sub>F n in sequentially. \<sigma> (r n) \<in> M \<and> d (\<sigma> (r n)) l < \<epsilon>/2"
    using lr half_gt_zero unfolding limitin_metric o_def by blast
  moreover have "\<forall>\<^sub>F n in sequentially. inverse (real (Suc n)) < \<epsilon>/2"
    using Archimedean_eventually_inverse \<open>0 < \<epsilon>\<close> half_gt_zero by blast
  ultimately obtain n where n: "d (\<sigma> (r n)) l < \<epsilon>/2" "inverse (real (Suc n)) < \<epsilon>/2"
    by (smt (verit, del_insts) eventually_sequentially le_add1 le_add2)
  have "x \<in> B" if "d (\<sigma> (r n)) x < inverse (Suc(r n))" "x \<in> M" for x
  proof -
    have rle: "inverse (real (Suc (r n))) \<le> inverse (real (Suc n))"
      using \<open>strict_mono r\<close> strict_mono_imp_increasing by auto
    have "d x l \<le> d (\<sigma> (r n)) x + d (\<sigma> (r n)) l"
      using that by (metis triangle \<open>\<And>n. \<sigma> n \<in> S\<close> \<open>l \<in> S\<close> \<open>S \<subseteq> M\<close> commute subsetD)
    also have "... < \<epsilon>"
      using that n rle by linarith
    finally show ?thesis
      by (simp add: \<epsilon> that)
  qed
  then show False
    using \<sigma> [of B "r n"] by (simp add: \<open>B \<in> \<C>\<close> subset_iff)
qed


lemma Bolzano_Weierstrass_E:
  assumes "mtotally_bounded S" "S \<subseteq> M"
  and S: "\<And>\<C>. \<lbrakk>\<And>U. U \<in> \<C> \<Longrightarrow> openin mtopology U; S \<subseteq> \<Union>\<C>\<rbrakk> \<Longrightarrow> \<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U"
  shows "compactin mtopology S"
proof (clarsimp simp: compactin_def assms)
  fix \<U> :: "'a set set"
  assume \<U>: "\<forall>x\<in>\<U>. openin mtopology x" and "S \<subseteq> \<Union> \<U>"
  then obtain \<epsilon> where "\<epsilon>>0" and \<epsilon>: "\<And>x. x \<in> S \<Longrightarrow> \<exists>U \<in> \<U>. mball x \<epsilon> \<subseteq> U"
    by (metis S)
  then obtain f where f: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> \<U> \<and> mball x \<epsilon> \<subseteq> f x"
    by metis
  then obtain K where "finite K" "K \<subseteq> S" and K: "S \<subseteq> (\<Union>x\<in>K. mball x \<epsilon>)"
    by (metis \<open>0 < \<epsilon>\<close> \<open>mtotally_bounded S\<close> mtotally_bounded_def)
  show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> S \<subseteq> \<Union> \<F>"
  proof (intro conjI exI)
    show "finite (f ` K)"
      by (simp add: \<open>finite K\<close>)
    show "f ` K \<subseteq> \<U>"
      using \<open>K \<subseteq> S\<close> f by blast
    show "S \<subseteq> \<Union> (f ` K)"
      using K \<open>K \<subseteq> S\<close> by (force dest: f)
  qed
qed


lemma compactin_eq_Bolzano_Weierstrass:
  "compactin mtopology S \<longleftrightarrow>
   S \<subseteq> M \<and> (\<forall>T. T \<subseteq> S \<and> infinite T \<longrightarrow> S \<inter> mtopology derived_set_of T \<noteq> {})"
  using Bolzano_Weierstrass_C Bolzano_Weierstrass_D Bolzano_Weierstrass_E
  by (smt (verit, del_insts) Bolzano_Weierstrass_property compactin_imp_Bolzano_Weierstrass compactin_subspace subset_refl topspace_mtopology)

lemma compactin_sequentially:
  shows "compactin mtopology S \<longleftrightarrow>
        S \<subseteq> M \<and>
        ((\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> S
         \<longrightarrow> (\<exists>l r. l \<in> S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially)))"
  by (metis Bolzano_Weierstrass_property compactin_eq_Bolzano_Weierstrass subset_refl)

lemma compactin_imp_mtotally_bounded: 
  "compactin mtopology S \<Longrightarrow> mtotally_bounded S"
  by (simp add: Bolzano_Weierstrass_C compactin_sequentially)

lemma lebesgue_number:
    "\<lbrakk>compactin mtopology S; S \<subseteq> \<Union>\<C>; \<And>U. U \<in> \<C> \<Longrightarrow> openin mtopology U\<rbrakk>
    \<Longrightarrow> \<exists>\<epsilon>>0. \<forall>x \<in> S. \<exists>U \<in> \<C>. mball x \<epsilon> \<subseteq> U"
  by (simp add: Bolzano_Weierstrass_D compactin_sequentially)

lemma compact_space_sequentially:
   "compact_space mtopology \<longleftrightarrow>
    (\<forall>\<sigma>::nat\<Rightarrow>'a. range \<sigma> \<subseteq> M
         \<longrightarrow> (\<exists>l r. l \<in> M \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially))"
  by (simp add: compact_space_def compactin_sequentially)

lemma compact_space_eq_Bolzano_Weierstrass:
   "compact_space mtopology \<longleftrightarrow>
    (\<forall>S. S \<subseteq> M \<and> infinite S \<longrightarrow> mtopology derived_set_of S \<noteq> {})"
  using Int_absorb1 [OF derived_set_of_subset_topspace [of mtopology]]
  by (force simp: compact_space_def compactin_eq_Bolzano_Weierstrass)

lemma compact_space_nest:
   "compact_space mtopology \<longleftrightarrow>
    (\<forall>C. (\<forall>n::nat. closedin mtopology (C n)) \<and> (\<forall>n. C n \<noteq> {}) \<and> decseq C \<longrightarrow> \<Inter>(range C) \<noteq> {})"
   (is "?lhs=?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof clarify
    fix C :: "nat \<Rightarrow> 'a set"
    assume "\<forall>n. closedin mtopology (C n)"
      and "\<forall>n. C n \<noteq> {}"
      and "decseq C"
      and "\<Inter> (range C) = {}"
    then obtain K where K: "finite K" "\<Inter>(C ` K) = {}"
      by (metis L compact_space_imp_nest)
    then obtain k where "K \<subseteq> {..k}"
      using finite_nat_iff_bounded_le by auto
    then have "C k \<subseteq> \<Inter>(C ` K)"
      using \<open>decseq C\<close> by (auto simp:decseq_def)
    then show False
      by (simp add: K \<open>\<forall>n. C n \<noteq> {}\<close>)
  qed
next
  assume R [rule_format]: ?rhs
  show ?lhs
    unfolding compact_space_sequentially
  proof (intro strip)
    fix \<sigma> :: "nat \<Rightarrow> 'a"
    assume \<sigma>: "range \<sigma> \<subseteq> M"
    have "mtopology closure_of \<sigma> ` {n..} \<noteq> {}" for n
      using \<open>range \<sigma> \<subseteq> M\<close> by (auto simp: closure_of_eq_empty image_subset_iff)
    moreover have "decseq (\<lambda>n. mtopology closure_of \<sigma> ` {n..})"
      using closure_of_mono image_mono by (smt (verit) atLeast_subset_iff decseq_def) 
    ultimately obtain l where l: "\<And>n. l \<in> mtopology closure_of \<sigma> ` {n..}"
      using R [of "\<lambda>n. mtopology closure_of (\<sigma> ` {n..})"] by auto
    then have "l \<in> M" and "\<And>n. \<forall>r>0. \<exists>k\<ge>n. \<sigma> k \<in> M \<and> d l (\<sigma> k) < r"
      using metric_closure_of by fastforce+
    then obtain f where f: "\<And>n r. r>0 \<Longrightarrow> f n r \<ge> n \<and> \<sigma> (f n r) \<in> M \<and> d l (\<sigma> (f n r)) < r"
      by metis
    define r where "r = rec_nat (f 0 1) (\<lambda>n rec. (f (Suc rec) (inverse (Suc (Suc n)))))"
    have r: "d l (\<sigma>(r n)) < inverse(Suc n)" for n
      by (induction n) (auto simp: rec_nat_0_imp [OF r_def] rec_nat_Suc_imp [OF r_def] f)
    have "r n < r(Suc n)" for n
      by (simp add: Suc_le_lessD f r_def)
    then have "strict_mono r"
      using strict_monoI_Suc by blast
    moreover have "limitin mtopology (\<sigma> \<circ> r) l sequentially"
      proof (clarsimp simp: limitin_metric \<open>l \<in> M\<close>)
        fix \<epsilon> :: real
        assume "\<epsilon> > 0"
        then have "(\<forall>\<^sub>F n in sequentially. inverse (real (Suc n)) < \<epsilon>)"
          using Archimedean_eventually_inverse by blast
        then show "\<forall>\<^sub>F n in sequentially. \<sigma> (r n) \<in> M \<and> d (\<sigma> (r n)) l < \<epsilon>"
          by eventually_elim (metis commute \<open>range \<sigma> \<subseteq> M\<close>  order_less_trans r range_subsetD)
      qed
    ultimately show "\<exists>l r. l \<in> M \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially"
      using \<open>l \<in> M\<close> by blast
  qed
qed


lemma (in discrete_metric) mcomplete_discrete_metric: "disc.mcomplete"
proof (clarsimp simp: disc.mcomplete_def)
  fix \<sigma> :: "nat \<Rightarrow> 'a"
  assume "disc.MCauchy \<sigma>"
  then obtain N where "\<And>n. N \<le> n \<Longrightarrow> \<sigma> N = \<sigma> n"
    unfolding disc.MCauchy_def by (metis dd_def dual_order.refl order_less_irrefl zero_less_one)
  moreover have "range \<sigma> \<subseteq> M"
    using \<open>disc.MCauchy \<sigma>\<close> disc.MCauchy_def by blast
  ultimately have "limitin disc.mtopology \<sigma> (\<sigma> N) sequentially"
    by (metis disc.limit_metric_sequentially disc.zero range_subsetD)
  then show "\<exists>x. limitin disc.mtopology \<sigma> x sequentially" ..
qed

lemma compact_space_imp_mcomplete: "compact_space mtopology \<Longrightarrow> mcomplete"
  by (simp add: compact_space_nest mcomplete_nest)

lemma (in submetric) compactin_imp_mcomplete:
   "compactin mtopology A \<Longrightarrow> sub.mcomplete"
  by (simp add: compactin_subspace mtopology_submetric sub.compact_space_imp_mcomplete)

lemma (in submetric) mcomplete_imp_closedin:
  assumes "sub.mcomplete"
  shows "closedin mtopology A"
proof -
  have "l \<in> A"
    if "range \<sigma> \<subseteq> A" and l: "limitin mtopology \<sigma> l sequentially"
    for \<sigma> :: "nat \<Rightarrow> 'a" and l
  proof -
    have "sub.MCauchy \<sigma>"
      using convergent_imp_MCauchy subset that by (force simp: MCauchy_submetric)
    then have "limitin sub.mtopology \<sigma> l sequentially"
      using assms unfolding sub.mcomplete_def
      using l limitin_metric_unique limitin_submetric_iff trivial_limit_sequentially by blast
    then show ?thesis
      using limitin_submetric_iff by blast
  qed
  then show ?thesis
    using metric_closedin_iff_sequentially_closed subset by auto
qed

lemma (in submetric) closedin_eq_mcomplete:
   "mcomplete \<Longrightarrow> (closedin mtopology A \<longleftrightarrow> sub.mcomplete)"
  using closedin_mcomplete_imp_mcomplete mcomplete_imp_closedin by blast

lemma compact_space_eq_mcomplete_mtotally_bounded:
   "compact_space mtopology \<longleftrightarrow> mcomplete \<and> mtotally_bounded M"
  by (meson Bolzano_Weierstrass_C compact_space_imp_mcomplete compact_space_sequentially limitin_mspace 
            mcomplete_alt mtotally_bounded_sequentially subset_refl)


lemma compact_closure_of_imp_mtotally_bounded:
   "\<lbrakk>compactin mtopology (mtopology closure_of S); S \<subseteq> M\<rbrakk>
      \<Longrightarrow> mtotally_bounded S"
  using compactin_imp_mtotally_bounded mtotally_bounded_closure_of_eq by blast

lemma mtotally_bounded_eq_compact_closure_of:
  assumes "mcomplete"
  shows "mtotally_bounded S \<longleftrightarrow> S \<subseteq> M \<and> compactin mtopology (mtopology closure_of S)"
  (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
    unfolding compactin_subspace
  proof (intro conjI)
    show "S \<subseteq> M"
      using L by (simp add: mtotally_bounded_imp_subset)
    show "mtopology closure_of S \<subseteq> topspace mtopology"
      by (simp add: \<open>S \<subseteq> M\<close> closure_of_minimal)
    then have MSM: "mtopology closure_of S \<subseteq> M"
      by auto
    interpret S: submetric M d "mtopology closure_of S"
    proof qed (use MSM in auto)
    have "S.sub.mtotally_bounded (mtopology closure_of S)"
      using L mtotally_bounded_absolute mtotally_bounded_closure_of by blast
    then
    show "compact_space (subtopology mtopology (mtopology closure_of S))"
      using S.closedin_mcomplete_imp_mcomplete S.mtopology_submetric S.sub.compact_space_eq_mcomplete_mtotally_bounded assms by force
  qed
qed (auto simp: compact_closure_of_imp_mtotally_bounded)



lemma compact_closure_of_eq_Bolzano_Weierstrass:
   "compactin mtopology (mtopology closure_of S) \<longleftrightarrow>
    (\<forall>T. infinite T \<and> T \<subseteq> S \<and> T \<subseteq> M \<longrightarrow> mtopology derived_set_of T \<noteq> {})"  (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof (intro strip, elim conjE)
    fix T
    assume T: "infinite T" "T \<subseteq> S" "T \<subseteq> M"
    show "mtopology derived_set_of T \<noteq> {}"
    proof (intro compact_closure_of_imp_Bolzano_Weierstrass)
      show "compactin mtopology (mtopology closure_of S)"
        by (simp add: L)
    qed (use T in auto)
  qed
next
  have "compactin mtopology (mtopology closure_of S)"
    if \<section>: "\<And>T. \<lbrakk>infinite T; T \<subseteq> S\<rbrakk> \<Longrightarrow> mtopology derived_set_of T \<noteq> {}" and "S \<subseteq> M" for S
    unfolding compactin_sequentially
  proof (intro conjI strip)
    show MSM: "mtopology closure_of S \<subseteq> M"
      using closure_of_subset_topspace by fastforce
    fix \<sigma> :: "nat \<Rightarrow> 'a"
    assume \<sigma>: "range \<sigma> \<subseteq> mtopology closure_of S"
    then have "\<exists>y \<in> S. d (\<sigma> n) y < inverse(Suc n)" for n
      by (simp add: metric_closure_of image_subset_iff) (metis inverse_Suc of_nat_Suc)
    then obtain \<tau> where \<tau>: "\<And>n. \<tau> n \<in> S \<and> d (\<sigma> n) (\<tau> n) < inverse(Suc n)"
      by metis
    then have "range \<tau> \<subseteq> S"
      by blast
    moreover
    have *: "\<forall>T. T \<subseteq> S \<and> infinite T \<longrightarrow> mtopology closure_of S \<inter> mtopology derived_set_of T \<noteq> {}"
      using "\<section>"(1) derived_set_of_mono derived_set_of_subset_closure_of by fastforce
    moreover have "S \<subseteq> mtopology closure_of S"
      by (simp add: \<open>S \<subseteq> M\<close> closure_of_subset)
    ultimately obtain l r where lr:
      "l \<in> mtopology closure_of S" "strict_mono r" "limitin mtopology (\<tau> \<circ> r) l sequentially"
      using Bolzano_Weierstrass_property \<open>S \<subseteq> M\<close> by metis
    then have "l \<in> M"
      using limitin_mspace by blast
    have dr_less: "d ((\<sigma> \<circ> r) n) ((\<tau> \<circ> r) n) < inverse(Suc n)" for n
    proof -
      have "d ((\<sigma> \<circ> r) n) ((\<tau> \<circ> r) n) < inverse(Suc (r n))"
        using \<tau> by auto
      also have "... \<le> inverse(Suc n)"
        using lr strict_mono_imp_increasing by auto
      finally show ?thesis .
    qed
    have "limitin mtopology (\<sigma> \<circ> r) l sequentially"
      unfolding limitin_metric
    proof (intro conjI strip)
      show "l \<in> M"
        using limitin_mspace lr by blast
      fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      then have "\<forall>\<^sub>F n in sequentially. (\<tau> \<circ> r) n \<in> M \<and> d ((\<tau> \<circ> r) n) l < \<epsilon>/2"
        using lr half_gt_zero limitin_metric by blast 
      moreover have "\<forall>\<^sub>F n in sequentially. inverse (real (Suc n)) < \<epsilon>/2"
        using Archimedean_eventually_inverse \<open>0 < \<epsilon>\<close> half_gt_zero by blast
      then have "\<forall>\<^sub>F n in sequentially. d ((\<sigma> \<circ> r) n) ((\<tau> \<circ> r) n) < \<epsilon>/2"
        by eventually_elim (smt (verit, del_insts) dr_less)
      ultimately have "\<forall>\<^sub>F n in sequentially. d ((\<sigma> \<circ> r) n) l < \<epsilon>/2 + \<epsilon>/2"
        by eventually_elim (smt (verit) triangle \<open>l \<in> M\<close> MSM \<sigma> comp_apply order_trans range_subsetD)      
      then show "\<forall>\<^sub>F n in sequentially. (\<sigma> \<circ> r) n \<in> M \<and> d ((\<sigma> \<circ> r) n) l < \<epsilon>"
        apply eventually_elim
        using \<open>mtopology closure_of S \<subseteq> M\<close> \<sigma> by auto
    qed
    with lr show "\<exists>l r. l \<in> mtopology closure_of S \<and> strict_mono r \<and> limitin mtopology (\<sigma> \<circ> r) l sequentially"
      by blast
  qed
  then show "?rhs \<Longrightarrow> ?lhs"
    by (metis Int_subset_iff closure_of_restrict inf_le1 topspace_mtopology)
qed

end

lemma (in discrete_metric) mtotally_bounded_discrete_metric:
   "disc.mtotally_bounded S \<longleftrightarrow> finite S \<and> S \<subseteq> M" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
  proof
    show "finite S"
      by (metis (no_types) L closure_of_subset_Int compactin_discrete_topology disc.mtotally_bounded_eq_compact_closure_of
          disc.topspace_mtopology discrete_metric.mcomplete_discrete_metric inf.absorb_iff2 mtopology_discrete_metric finite_subset)
    show "S \<subseteq> M"
      by (simp add: L disc.mtotally_bounded_imp_subset)
  qed
qed (simp add: disc.finite_imp_mtotally_bounded)


context Metric_space
begin

lemma derived_set_of_infinite_openin_metric:
   "mtopology derived_set_of S =
    {x \<in> M. \<forall>U. x \<in> U \<and> openin mtopology U \<longrightarrow> infinite(S \<inter> U)}"
  by (simp add: derived_set_of_infinite_openin Hausdorff_space_mtopology)

lemma derived_set_of_infinite_1: 
  assumes "infinite (S \<inter> mball x \<epsilon>)" 
  shows "infinite (S \<inter> mcball x \<epsilon>)"
  by (meson Int_mono assms finite_subset mball_subset_mcball subset_refl)

lemma derived_set_of_infinite_2:
  assumes "openin mtopology U" "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> infinite (S \<inter> mcball x \<epsilon>)" and "x \<in> U"
  shows "infinite (S \<inter> U)"
  by (metis assms openin_mtopology_mcball finite_Int inf.absorb_iff2 inf_assoc)

lemma derived_set_of_infinite_mball:
  "mtopology derived_set_of S = {x \<in> M. \<forall>e>0. infinite(S \<inter> mball x e)}"
  unfolding derived_set_of_infinite_openin_metric
  by (meson centre_in_mball_iff openin_mball derived_set_of_infinite_1 derived_set_of_infinite_2)

lemma derived_set_of_infinite_mcball:
  "mtopology derived_set_of S = {x \<in> M. \<forall>e>0. infinite(S \<inter> mcball x e)}"
  unfolding derived_set_of_infinite_openin_metric
  by (meson centre_in_mball_iff openin_mball derived_set_of_infinite_1 derived_set_of_infinite_2)

end

subsection\<open>Continuous functions on metric spaces\<close>

context Metric_space
begin

lemma continuous_map_to_metric:
   "continuous_map X mtopology f \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<forall>\<epsilon>>0. \<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y\<in>U. f y \<in> mball (f x) \<epsilon>))"
   (is "?lhs=?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding continuous_map_eq_topcontinuous_at topcontinuous_at_def
    by (metis centre_in_mball_iff openin_mball topspace_mtopology)
next
  assume R: ?rhs
  then have "\<forall>x\<in>topspace X. f x \<in> M"
    by (meson gt_ex in_mball)
  moreover 
  have "\<And>x V. \<lbrakk>x \<in> topspace X; openin mtopology V; f x \<in> V\<rbrakk> \<Longrightarrow> \<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y\<in>U. f y \<in> V)"
    unfolding openin_mtopology by (metis Int_iff R inf.orderE)
  ultimately
  show ?lhs
    by (simp add: continuous_map_eq_topcontinuous_at topcontinuous_at_def)
qed 

lemma continuous_map_from_metric:
   "continuous_map mtopology X f \<longleftrightarrow>
    f ` M \<subseteq> topspace X \<and>
    (\<forall>a \<in> M. \<forall>U. openin X U \<and> f a \<in> U \<longrightarrow> (\<exists>r>0. \<forall>x. x \<in> M \<and> d a x < r \<longrightarrow> f x \<in> U))"
proof (cases "f ` M \<subseteq> topspace X")
  case True
  then show ?thesis
    by (fastforce simp: continuous_map openin_mtopology subset_eq)
next
  case False
  then show ?thesis
    by (simp add: continuous_map_eq_image_closure_subset_gen)
qed

text \<open>An abstract formulation, since the limits do not have to be sequential\<close>
lemma continuous_map_uniform_limit:
  assumes contf: "\<forall>\<^sub>F \<xi> in F. continuous_map X mtopology (f \<xi>)"
    and dfg: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F \<xi> in F. \<forall>x \<in> topspace X. g x \<in> M \<and> d (f \<xi> x) (g x) < \<epsilon>"
    and nontriv: "\<not> trivial_limit F"
  shows "continuous_map X mtopology g"
  unfolding continuous_map_to_metric
proof (intro strip)
  fix x and \<epsilon>::real
  assume "x \<in> topspace X" and "\<epsilon> > 0"
  then obtain \<xi> where k: "continuous_map X mtopology (f \<xi>)" 
    and gM: "\<forall>x \<in> topspace X. g x \<in> M" 
    and third: "\<forall>x \<in> topspace X. d (f \<xi> x) (g x) < \<epsilon>/3"
    using eventually_conj [OF contf] contf dfg [of "\<epsilon>/3"] eventually_happens' [OF nontriv]
    by (smt (verit, ccfv_SIG) zero_less_divide_iff)
  then obtain U where U: "openin X U" "x \<in> U" and Uthird: "\<forall>y\<in>U. d (f \<xi> y) (f \<xi> x) < \<epsilon>/3"
    unfolding continuous_map_to_metric
    by (metis \<open>0 < \<epsilon>\<close> \<open>x \<in> topspace X\<close> commute divide_pos_pos in_mball zero_less_numeral)
  have f_inM: "f \<xi> y \<in> M" if "y\<in>U" for y
    using U k openin_subset that by (fastforce simp: continuous_map_def)
  have "d (g y) (g x) < \<epsilon>" if "y\<in>U" for y
  proof -
    have "g y \<in> M"
      using U gM openin_subset that by blast
    have "d (g y) (g x) \<le> d (g y) (f \<xi> x) + d (f \<xi> x) (g x)"
      by (simp add: U \<open>g y \<in> M\<close> \<open>x \<in> topspace X\<close> f_inM gM triangle)
    also have "\<dots> \<le> d (g y) (f \<xi> y) + d (f \<xi> y) (f \<xi> x) + d (f \<xi> x) (g x)"
      by (simp add: U \<open>g y \<in> M\<close> commute f_inM that triangle')
    also have "\<dots> < \<epsilon>/3 + \<epsilon>/3 + \<epsilon>/3"
      by (smt (verit) U(1) Uthird \<open>x \<in> topspace X\<close> commute openin_subset subsetD that third)
    finally show ?thesis by simp
  qed
  with U gM show "\<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>y\<in>U. g y \<in> mball (g x) \<epsilon>)"
    by (metis commute in_mball in_mono openin_subset)
qed


lemma continuous_map_uniform_limit_alt:
  assumes contf: "\<forall>\<^sub>F \<xi> in F. continuous_map X mtopology (f \<xi>)"
    and gim: "g ` (topspace X) \<subseteq> M"
    and dfg: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F \<xi> in F. \<forall>x \<in> topspace X. d (f \<xi> x) (g x) < \<epsilon>"
    and nontriv: "\<not> trivial_limit F"
  shows "continuous_map X mtopology g"
proof (rule continuous_map_uniform_limit [OF contf])
  fix \<epsilon> :: real
  assume "\<epsilon> > 0"
  with gim dfg show "\<forall>\<^sub>F \<xi> in F. \<forall>x\<in>topspace X. g x \<in> M \<and> d (f \<xi> x) (g x) < \<epsilon>"
    by (simp add: image_subset_iff)
qed (use nontriv in auto)


lemma continuous_map_uniformly_Cauchy_limit:
  assumes "mcomplete"
  assumes contf: "\<forall>\<^sub>F n in sequentially. continuous_map X mtopology (f n)"
    and Cauchy': "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>N. \<forall>m n x. N \<le> m \<longrightarrow> N \<le> n \<longrightarrow> x \<in> topspace X \<longrightarrow> d (f m x) (f n x) < \<epsilon>"
  obtains g where
    "continuous_map X mtopology g"
    "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>topspace X. d (f n x) (g x) < \<epsilon>"
proof -
  have "\<And>x. x \<in> topspace X \<Longrightarrow> \<exists>l. limitin mtopology (\<lambda>n. f n x) l sequentially"
    using \<open>mcomplete\<close> [unfolded mcomplete, rule_format] assms
    by (smt (verit) contf continuous_map_def eventually_mono topspace_mtopology)
  then obtain g where g: "\<And>x. x \<in> topspace X \<Longrightarrow> limitin mtopology (\<lambda>n. f n x) (g x) sequentially"
    by metis
  show thesis
  proof
    show "\<forall>\<^sub>F n in sequentially. \<forall>x\<in>topspace X. d (f n x) (g x) < \<epsilon>"
      if "\<epsilon> > 0" for \<epsilon> :: real
    proof -
      obtain N where N: "\<And>m n x. \<lbrakk>N \<le> m; N \<le> n; x \<in> topspace X\<rbrakk> \<Longrightarrow> d (f m x) (f n x) < \<epsilon>/2"
        by (meson Cauchy' \<open>0 < \<epsilon>\<close> half_gt_zero)
      obtain P where P: "\<And>n x. \<lbrakk>n \<ge> P; x \<in> topspace X\<rbrakk> \<Longrightarrow> f n x \<in> M"
        using contf by (auto simp: eventually_sequentially continuous_map_def)
      show ?thesis
      proof (intro eventually_sequentiallyI strip)
        fix n x
        assume "max N P \<le> n" and x: "x \<in> topspace X"
        obtain L where "g x \<in> M" and L: "\<forall>n\<ge>L. f n x \<in> M \<and> d (f n x) (g x) < \<epsilon>/2"
          using g [OF x] \<open>\<epsilon> > 0\<close> unfolding limitin_metric
          by (metis (no_types, lifting) eventually_sequentially half_gt_zero)
        define n' where "n' \<equiv> Max{L,N,P}"
        have L': "\<forall>m \<ge> n'. f m x \<in> M \<and> d (f m x) (g x) < \<epsilon>/2"
          using L by (simp add: n'_def)
        moreover
        have "d (f n x) (f n' x) < \<epsilon>/2"
          using N [of n n' x] \<open>max N P \<le> n\<close> n'_def x by fastforce
        ultimately have "d (f n x) (g x) < \<epsilon>/2 + \<epsilon>/2"
          by (smt (verit, ccfv_SIG) P \<open>g x \<in> M\<close> \<open>max N P \<le> n\<close> le_refl max.bounded_iff mdist_zero triangle' x)
        then show "d (f n x) (g x) < \<epsilon>" by simp
      qed
    qed
    then show "continuous_map X mtopology g"
      by (smt (verit, del_insts) eventually_mono g limitin_mspace trivial_limit_sequentially continuous_map_uniform_limit [OF contf])
  qed
qed

lemma metric_continuous_map:
  assumes "Metric_space M' d'"
  shows
   "continuous_map mtopology (Metric_space.mtopology M' d') f \<longleftrightarrow>
    f ` M \<subseteq> M' \<and> (\<forall>a \<in> M. \<forall>\<epsilon>>0. \<exists>\<delta>>0.  (\<forall>x. x \<in> M \<and> d a x < \<delta> \<longrightarrow> d' (f a) (f x) < \<epsilon>))"
   (is "?lhs = ?rhs")
proof -
  interpret M': Metric_space M' d'
    by (simp add: assms)
  show ?thesis
  proof
    assume L: ?lhs
    show ?rhs
    proof (intro conjI strip)
      show "f ` M \<subseteq> M'"
        using L by (auto simp: continuous_map_def)
      fix a and \<epsilon> :: real
      assume "a \<in> M" and "\<epsilon> > 0"
      then have "openin mtopology {x \<in> M. f x \<in> M'.mball (f a) \<epsilon>}" "f a \<in> M'"
        using L unfolding continuous_map_def by fastforce+
      then obtain \<delta> where "\<delta> > 0" "mball a \<delta> \<subseteq> {x \<in> M. f x \<in> M' \<and> d' (f a) (f x) < \<epsilon>}"
        using \<open>0 < \<epsilon>\<close> \<open>a \<in> M\<close> openin_mtopology by auto
      then show "\<exists>\<delta>>0. \<forall>x. x \<in> M \<and> d a x < \<delta> \<longrightarrow> d' (f a) (f x) < \<epsilon>"
        using \<open>a \<in> M\<close> in_mball by blast
    qed
  next
    assume R: ?rhs    
    show ?lhs
      unfolding continuous_map_def
    proof (intro conjI strip)
      fix U
      assume "openin M'.mtopology U"
      then show "openin mtopology {x \<in> topspace mtopology. f x \<in> U}"
        apply (simp add: continuous_map_def openin_mtopology M'.openin_mtopology subset_iff)
        by (metis R image_subset_iff)
    qed (use R in auto)
  qed
qed

end (*Metric_space*)

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
    by (force simp add: Met.continuous_map_to_metric dist_real_def continuous_map_in_subtopology fim simp flip: Met.mtopology_is_euclideanreal)
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
  obtain h where conth:  "continuous_map X Met.mtopology h"
    and h: "\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<forall>\<^sub>F n in sequentially. \<forall>x\<in>topspace X. dist (g n x) (h x) < \<epsilon>"
  proof (rule Met.continuous_map_uniformly_Cauchy_limit)
    show "\<forall>\<^sub>F n in sequentially. continuous_map X (Met.mtopology) (g n)"
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
      proof (rule Met.limitin_metric_unique)
        show "limitin Met.mtopology (\<lambda>n. g n x) (h x) sequentially"
          using h x by (force simp: tendsto_iff eventually_sequentially)
        show "limitin Met.mtopology (\<lambda>n. g n x) (f x) sequentially"
        proof (clarsimp simp: tendsto_iff)
          fix \<epsilon>::real
          assume "\<epsilon> > 0"
          then have "\<forall>\<^sub>F n in sequentially. \<bar>(2/3) ^ n\<bar> < \<epsilon>/c"
            by (intro Archimedean_eventually_pow_inverse) (auto simp: \<open>c > 0\<close>)
          then show "\<forall>\<^sub>F n in sequentially. dist (g n x) (f x) < \<epsilon>"
            apply eventually_elim
            using good x
            apply (simp add: good_def \<open>c > 0\<close> dist_real_def)
            by (smt (verit, ccfv_SIG) \<open>0 < c\<close> mult.commute pos_less_divide_eq that)
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
        using is_interval_shrink that(2) by blast
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
   (is "?lhs=?rhs")
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
        by (auto simp add: disjnt_iff)
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
    "\<And>n. openin X (h n)" "\<And>n. disjnt T (X closure_of (h n))" and  "S \<subseteq> \<Union> (range h)"
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
  then obtain \<U> where \<U>: "countable \<U> \<and> \<U> \<subseteq> h ` S \<and> S \<subseteq> \<Union> \<U>"
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
    show "S \<subseteq> \<Union> (range (from_nat_into \<U>))"
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
      and Sh: "S \<subseteq> \<Union> (range h)"
      by (metis Lindelof_cover False \<open>disjnt S T\<close> assms clo)
    obtain k :: "nat \<Rightarrow> 'a set" where 
      opek: "\<And>n. openin X (k n)" and disk: "\<And>n. disjnt S (X closure_of (k n))"
      and Tk: "T \<subseteq> \<Union> (range k)"
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
   (is "?lhs=?rhs")
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
    then have "continuous_map Y (top_of_set {0..1::real}) (\<phi> o g)"
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
     (\<forall>S x. closedin X S \<and> x \<in> topspace X - S
           \<longrightarrow> (\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}))"
proof -
  have "\<exists>f. continuous_map X (top_of_set {0..1::real}) f \<and> f x = 0 \<and> f ` A \<subseteq> {1}" 
    if "closedin X A" "x \<in> topspace X - A" and f: "continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` A \<subseteq> {1}"
    for A x f
  proof (intro exI conjI)
    show "continuous_map X (top_of_set {0..1}) (\<lambda>x. max 0 (min (f x) 1))"
      using that
      by (auto simp: continuous_map_in_subtopology intro!: continuous_map_real_max continuous_map_real_min)
  qed (use that in auto)
  with continuous_map_in_subtopology show ?thesis
    unfolding completely_regular_space_def by metis 
qed


lemma completely_regular_space_gen_alt:
  fixes a b::real
  assumes "a \<noteq> b"
  shows "completely_regular_space X \<longleftrightarrow>
         (\<forall>A x. closedin X A \<and> x \<in> topspace X - A
               \<longrightarrow> (\<exists>f. continuous_map X euclidean f \<and> f x = a \<and> (f ` A \<subseteq> {b})))"
proof -
  have "\<exists>f. continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}" 
    if "closedin X S" "x \<in> topspace X - S" 
        and f: "continuous_map X euclidean f \<and> f x = a \<and> f ` S \<subseteq> {b}"
    for S x f
  proof (intro exI conjI)
    show "continuous_map X euclideanreal ((\<lambda>x. inverse(b - a) * (x - a)) o f)"
      using that by (intro continuous_intros) auto
  qed (use that assms in auto)
  moreover
  have "\<exists>f. continuous_map X euclidean f \<and> f x = a \<and> f ` S \<subseteq> {b}" 
    if "closedin X S" "x \<in> topspace X - S" 
        and f: "continuous_map X euclideanreal f \<and> f x = 0 \<and> f ` S \<subseteq> {1}"
    for S x f
  proof (intro exI conjI)
    show "continuous_map X euclideanreal ((\<lambda>x. a + (b - a) * x) o f)"
      using that by (intro continuous_intros) auto
  qed (use that in auto)
  ultimately show ?thesis
    unfolding completely_regular_space_alt by meson
qed

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
    if contf: "continuous_map X euclideanreal f" and "a \<in> topspace X - C" and "closedin X C"
      and fim: "f ` topspace X \<subseteq> {0..1}" and f0: "f a = 0" and f1: "f ` C \<subseteq> {1}"
    for C a f
    apply (rule_tac x="{x \<in> topspace X. f x \<in> {..<1/2}}" in exI)
    apply (rule_tac x="{x \<in> topspace X. f x \<in> {1/2<..}}" in exI)
    apply (intro conjI openin_continuous_map_preimage [OF contf])
        apply simp
       apply (simp add: )
      apply (auto simp: )
    using that(2) apply blast
       apply (simp add: f0)
    using closedin_subset that(3) apply blast
    using f1 apply fastforce
    apply (auto simp: disjnt_iff)
    done
  show ?thesis
    using assms
    unfolding completely_regular_space_def regular_space_def continuous_map_in_subtopology
    by (meson "*")
qed


lemma locally_compact_regular_imp_completely_regular_space:
   "locally_compact_space X \<and> (Hausdorff_space X \<or> regular_space X)
        \<Longrightarrow> completely_regular_space X"
oops
  REWRITE_TAC[LOCALLY_COMPACT_HAUSDORFF_OR_REGULAR] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[completely_regular_space; IN_DIFF] THEN
  MAP_EVERY X_GEN_TAC [`s::A=>bool`; `x::A`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `X::A topology`
   LOCALLY_COMPACT_REGULAR_SPACE_NEIGHBOURHOOD_BASE) THEN
  ASM_REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN
  DISCH_THEN(MP_TAC \<circ> SPECL [`topspace X - s::A=>bool`; `x::A`]) THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; IN_DIFF;
               LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u::A=>bool`; `m::A=>bool`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM
   NEIGHBOURHOOD_BASE_OF_CLOSED_IN]) THEN
  REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN
  DISCH_THEN(MP_TAC \<circ> SPECL [`u::A=>bool`; `x::A`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v::A=>bool`; `k::A=>bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology X (m::A=>bool)`;
                 `k::A=>bool`; `m - u::A=>bool`; `0::real`; `1::real`]
        URYSOHN_LEMMA) THEN
  REWRITE_TAC[REAL_POS; IN_DIFF] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_HAUSDORFF_OR_REGULAR_IMP_NORMAL_SPACE THEN
      ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; REGULAR_SPACE_SUBTOPOLOGY];
      MATCH_MP_TAC CLOSED_IN_SUBSET_TOPSPACE THEN ASM SET_TAC[];
      REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
      EXISTS_TAC `topspace X - u::A=>bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE] THEN
      FIRST_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
      ASM SET_TAC[];
      ASM SET_TAC[]];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; \<subseteq>; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[COMPACT_IN_SUBSET_TOPSPACE; TOPSPACE_SUBTOPOLOGY;
                 SET_RULE `s \<subseteq> u \<Longrightarrow> u \<inter> s = s`] THEN
    DISCH_THEN(X_CHOOSE_THEN `g::A=>real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `\<lambda>x. if x \<in> m then (g::A=>real) x else 1` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM SET_TAC[]] THEN
  CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[ENDS_IN_UNIT_REAL_INTERVAL]] THEN
  REWRITE_TAC[CONTINUOUS_MAP_CLOSED_IN; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
  X_GEN_TAC `c::real=>bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x \<in> topspace X. (if x \<in> m then g x else 1) \<in> c} =
    {x \<in> m. (g::A=>real) x \<in> c} \<union>
    (if 1 \<in> c then topspace X - u else {})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `y::A` THEN ASM_CASES_TAC `(y::A) \<in> m` THEN
    ASM_REWRITE_TAC[] THENL [ALL_TAC; ASM SET_TAC[]] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_DIFF; NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_TRANS_FULL THEN EXISTS_TAC `m::A=>bool` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE_GEN THEN
      EXISTS_TAC `euclideanreal` THEN
      ASM_SIMP_TAC[CLOSED_IN_SUBSET_TOPSPACE; SUBSET_REFL];
      COND_CASES_TAC THEN REWRITE_TAC[CLOSED_IN_EMPTY] THEN
      ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE]]]);;

lemma completely_regular_eq_regular_space:
   "locally_compact_space X
        \<Longrightarrow> (completely_regular_space X \<longleftrightarrow> regular_space X)"
oops
  MESON_TAC[COMPLETELY_REGULAR_IMP_REGULAR_SPACE;
            LOCALLY_COMPACT_REGULAR_IMP_COMPLETELY_REGULAR_SPACE]);;

lemma completely_regular_space_prod_topology:
   "\<And>(top1::A topology) (top2::B topology).
        completely_regular_space (prod_topology top1 top2) \<longleftrightarrow>
        topspace (prod_topology top1 top2) = {} \<or>
        completely_regular_space top1 \<and> completely_regular_space top2"
oops
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC TOPOLOGICAL_PROPERTY_OF_PROD_COMPONENT THEN
    REWRITE_TAC[HOMEOMORPHIC_COMPLETELY_REGULAR_SPACE] THEN
    SIMP_TAC[COMPLETELY_REGULAR_SPACE_SUBTOPOLOGY];
    ALL_TAC] THEN
  ASM_CASES_TAC `topspace(prod_topology top1 top2):A#B=>bool = {}` THENL
   [ASM_REWRITE_TAC[completely_regular_space; IN_DIFF; NOT_IN_EMPTY];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[COMPLETELY_REGULAR_SPACE_ALT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_CLOSED_IN] THEN SIMP_TAC[IN_DIFF; IMP_CONJ] THEN
  GEN_REWRITE_TAC (BINOP_CONV \<circ> TOP_DEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
  MAP_EVERY X_GEN_TAC [`w::A#B=>bool`; `x::A`; `y::B`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [OPEN_IN_PROD_TOPOLOGY_ALT]) THEN
  DISCH_THEN(MP_TAC \<circ> SPECL [`x::A`; `y::B`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u::A=>bool`; `v::B=>bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`v::B=>bool`; `y::B`]) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`u::A=>bool`; `x::A`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `f::A=>real` THEN STRIP_TAC THEN
  X_GEN_TAC `g::B=>real` THEN STRIP_TAC THEN
  EXISTS_TAC `\<lambda>(x,y). 1 - (1 - f x) * (1 - (g::B=>real) y)` THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
   [REWRITE_TAC[LAMBDA_PAIR] THEN
    REPEAT((MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB ORELSE
            MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL) THEN CONJ_TAC) THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_OF_FST; CONTINUOUS_MAP_OF_SND];
    REWRITE_TAC[REAL_RING
     `1 - (1 - x) * (1 - y) = 1 \<longleftrightarrow> x = 1 \<or> y = 1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[\<subseteq>; FORALL_PAIR_THM; IN_CROSS]) THEN
    ASM SET_TAC[]]);;

lemma completely_regular_space_product_topology:
   "\<And>(tops::K=>A topology) k.
        completely_regular_space (product_topology k tops) \<longleftrightarrow>
        topspace (product_topology k tops) = {} \<or>
        \<forall>i. i \<in> k \<Longrightarrow> completely_regular_space (tops i)"
oops
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC TOPOLOGICAL_PROPERTY_OF_PRODUCT_COMPONENT THEN
    REWRITE_TAC[HOMEOMORPHIC_COMPLETELY_REGULAR_SPACE] THEN
    SIMP_TAC[COMPLETELY_REGULAR_SPACE_SUBTOPOLOGY];
    ALL_TAC] THEN
  ASM_CASES_TAC `topspace (product_topology k (tops::K=>A topology)) = {}` THENL
   [ASM_REWRITE_TAC[completely_regular_space; NOT_IN_EMPTY; IN_DIFF];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[COMPLETELY_REGULAR_SPACE_ALT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_CLOSED_IN] THEN SIMP_TAC[IN_DIFF; IMP_CONJ] THEN
  GEN_REWRITE_TAC (BINOP_CONV \<circ> TOP_DEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS] THEN
  MAP_EVERY X_GEN_TAC [`w:(K=>A)->bool`; `x::K=>A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id
   [OPEN_IN_PRODUCT_TOPOLOGY_ALT]) THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `x::K=>A`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u::K=>A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN `i::K` \<circ> SPECL
   [`i::K`; `(u::K=>A->bool) i`; `(x::K=>A) i`]) THEN
  REWRITE_TAC[MESON[\<subseteq>; OPEN_IN_SUBSET]
   `(P \<and> openin X u \<and> x \<in> topspace X \<and> x \<in> u \<Longrightarrow> Q) \<longleftrightarrow>
    P \<Longrightarrow> openin X u \<and> x \<in> u \<Longrightarrow> Q`] THEN
  MP_TAC(ASSUME `(x::K=>A) \<in> PiE k u`) THEN
  REWRITE_TAC[PiE; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV \<circ> BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `f::K=>A->real` THEN DISCH_TAC THEN
  EXISTS_TAC
   `\<lambda>z. 1 - product {i. i \<in> k \<and> \<not> (u i :A=>bool = topspace(tops i))}
                     (\<lambda>i. 1 - (f::K=>A->real) i (z i))` THEN
  REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; PiE; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_PRODUCT THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `i::K` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `(tops::K=>A topology) i` THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION];
    REWRITE_TAC[REAL_ARITH `1 - x = 0 \<longleftrightarrow> x = 1`] THEN
    MATCH_MP_TAC PRODUCT_EQ_1 THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_ARITH `1 - x = 1 \<longleftrightarrow> x = 0`];
    X_GEN_TAC `y::K=>A` THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `1 - x = 1 \<longleftrightarrow> x = 0`] THEN
    ASM_SIMP_TAC[PRODUCT_EQ_0; REAL_ARITH `1 - x = 0 \<longleftrightarrow> x = 1`] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `y::K=>A` \<circ> GEN_REWRITE_RULE id [\<subseteq>]) THEN
    ASM_REWRITE_TAC[PiE; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;



lemma locally_path_connected_is_realinterval:
   "is_interval s
       \<Longrightarrow> locally_path_connected_space(subtopology euclideanreal s)"
  using locally_path_connected_space_euclideanreal
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[locally_path_connected_space] THEN
  REWRITE_TAC[NEIGHBOURHOOD_BASE_OF; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_ALT; IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC; IN_INTER; INTER_SUBSET] THEN
  X_GEN_TAC `u::real=>bool` THEN DISCH_TAC THEN
  X_GEN_TAC `a::real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE LAND_CONV
   [GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC]) THEN
  REWRITE_TAC[OPEN_IN_MTOPOLOGY; MBALL_REAL_INTERVAL] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `a::real` \<circ> CONJUNCT2) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r::real` THEN STRIP_TAC THEN
  EXISTS_TAC `real_interval(a - r,a + r)` THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL] THEN
  EXISTS_TAC `s \<inter> real_interval(a - r,a + r)` THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL; PATH_CONNECTED_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[INTER_SUBSET; SUBSET_INTER] THEN
  ASM_REWRITE_TAC[REAL_ARITH `a - r::real < a \<and> a < a + r \<longleftrightarrow> 0 < r`] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[PATH_CONNECTED_IN_EUCLIDEANREAL] THEN
  MATCH_MP_TAC IS_REALINTERVAL_INTER THEN
  ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL]);;

lemma locally_path_connected_real_interval:
 (`(\<forall>a b. locally_path_connected_space
           (subtopology euclideanreal{a..b})) \<and>
   (\<forall>a b. locally_path_connected_space
           (subtopology euclideanreal{a<..<b}))"
oops
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LOCALLY_PATH_CONNECTED_IS_REALINTERVAL THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL]);;`


lemma locally_path_connected_space_prod_topology:
   "locally_path_connected_space (prod_topology X Y) \<longleftrightarrow>
      topspace (prod_topology X Y) = {} \<or>
      locally_path_connected_space X \<and> locally_path_connected_space Y"
oops
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `topspace(prod_topology X Y):A#B=>bool = {}` THENL
   [ASM_REWRITE_TAC[locally_path_connected_space; NEIGHBOURHOOD_BASE_OF] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; \<subseteq>; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE
   [TOPSPACE_PROD_TOPOLOGY; CROSS_EQ_EMPTY; DE_MORGAN_THM]) THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
      LOCALLY_PATH_CONNECTED_SPACE_QUOTIENT_MAP_IMAGE))
    THENL [EXISTS_TAC `fst::A#B=>A`; EXISTS_TAC `snd::A#B=>B`] THEN
    ASM_REWRITE_TAC[QUOTIENT_MAP_FST; QUOTIENT_MAP_SND];
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `z::B` THEN DISCH_TAC THEN X_GEN_TAC `w::A` THEN DISCH_TAC THEN
    REWRITE_TAC[locally_path_connected_space; FORALL_PAIR_THM; IN_CROSS;
      NEIGHBOURHOOD_BASE_OF; TOPSPACE_PROD_TOPOLOGY] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`uv::A#B=>bool`; `x::A`; `y::B`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [OPEN_IN_PROD_TOPOLOGY_ALT] THEN
    DISCH_THEN(MP_TAC \<circ> SPECL [`x::A`; `y::B`]) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`w1::A=>bool`; `w2::B=>bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`w2::B=>bool`; `y::B`]) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`w1::A=>bool`; `x::A`]) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u1::A=>bool`; `k1::A=>bool`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`u2::B=>bool`; `k2::B=>bool`] THEN STRIP_TAC THEN
    EXISTS_TAC `(u1::A=>bool) \<times> (u2::B=>bool)` THEN
    EXISTS_TAC `(k1::A=>bool) \<times> (k2::B=>bool)` THEN
    ASM_SIMP_TAC[OPEN_IN_CROSS; PATH_CONNECTED_IN_CROSS;
                IN_CROSS; SUBSET_CROSS] THEN
    TRANS_TAC SUBSET_TRANS `(w1 \<times> w2):A#B=>bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[SUBSET_CROSS]]);;

lemma locally_path_connected_space_sum_topology:
   "\<And>k (X::K=>A topology).
        locally_path_connected_space(sum_topology k X) \<longleftrightarrow>
        \<forall>i. i \<in> k \<Longrightarrow> locally_path_connected_space(X i)"
oops
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC TOPOLOGICAL_PROPERTY_OF_SUM_COMPONENT THEN
    REWRITE_TAC[HOMEOMORPHIC_LOCALLY_PATH_CONNECTED_SPACE] THEN
    SIMP_TAC[LOCALLY_PATH_CONNECTED_SPACE_OPEN_SUBSET];
    REWRITE_TAC[locally_path_connected_space; NEIGHBOURHOOD_BASE_OF] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_OPEN_IN_SUM_TOPOLOGY] THEN
    DISCH_TAC THEN X_GEN_TAC `w::K=>A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[FORALL_PAIR_THM; Sigma; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`i::K`; `x::A`] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> SPEC `i::K`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(w::K=>A->bool) i`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `x::A`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u::A=>bool`; `v::A=>bool`] THEN STRIP_TAC THEN
    EXISTS_TAC `image (\<lambda>x. (i::K),(x::A)) u` THEN
    EXISTS_TAC `image (\<lambda>x. (i::K),(x::A)) v` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_ELIM_PAIR_THM] THEN
    ASM_REWRITE_TAC[GSYM \<subseteq>] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[open_map; RIGHT_IMP_FORALL_THM; IMP_IMP]
        OPEN_MAP_COMPONENT_INJECTION) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PATH_CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `(X::K=>A topology) i` THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_COMPONENT_INJECTION];
      ASM SET_TAC[]]]);;


subsection\<open>Locally connected spaces\<close>


let weakly_locally_connected_at = new_definition
 `weakly_locally_connected_at x X \<longleftrightarrow>
    neighbourhood_base_at x (connectedin X) X`;;

let locally_connected_at = new_definition
 `locally_connected_at x X \<longleftrightarrow>
    neighbourhood_base_at x
      (\<lambda>u. openin X u \<and> connectedin X u ) X`;;

let locally_connected_space = new_definition
 `locally_connected_space X \<longleftrightarrow>
        neighbourhood_base_of (connectedin X) X`;;

let LOCALLY_CONNECTED_SPACE_ALT,
    LOCALLY_CONNECTED_SPACE_EQ_OPEN_CONNECTED_COMPONENT_OF =
 (CONJ_PAIR \<circ> prove)
 (`(\<forall>X::A topology.
        locally_connected_space X \<longleftrightarrow>
        neighbourhood_base_of
          (\<lambda>u. openin X u \<and> connectedin X u) X) \<and>
   (\<forall>X::A topology.
        locally_connected_space X \<longleftrightarrow>
        \<forall>u x. openin X u \<and> x \<in> u
              \<Longrightarrow> openin X (connected_component_of (subtopology X u) x))"
oops
  SIMP_TAC[OPEN_NEIGHBOURHOOD_BASE_OF] THEN
  REWRITE_TAC[AND_FORALL_THM; locally_connected_space] THEN
  REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN
  X_GEN_TAC `X::A topology` THEN
  MATCH_MP_TAC(TAUT
   `(q \<Longrightarrow> p) \<and> (p \<Longrightarrow> r) \<and> (r \<Longrightarrow> q) \<Longrightarrow> (p \<longleftrightarrow> q) \<and> (p \<longleftrightarrow> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[SUBSET_REFL];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u::A=>bool`; `y::A`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    X_GEN_TAC `x::A` THEN DISCH_TAC THEN
    FIRST_ASSUM(SUBST1_TAC \<circ> last \<circ> CONJUNCTS \<circ>
     GEN_REWRITE_RULE id [CONNECTED_COMPONENT_OF_EQUIV] \<circ>
     GEN_REWRITE_RULE id [\<in>]) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`u::A=>bool`; `x::A`]) THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP (REWRITE_RULE[\<subseteq>]
        CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE)) THEN
      ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`v::A=>bool`; `w::A=>bool`] THEN STRIP_TAC THEN
    EXISTS_TAC `v::A=>bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `w::A=>bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u::A=>bool`; `x::A`] THEN STRIP_TAC THEN
    EXISTS_TAC `connected_component_of (subtopology X u) (x::A)` THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [W(MP_TAC \<circ> PART_MATCH rand CONNECTED_IN_CONNECTED_COMPONENT_OF \<circ>
        rand \<circ> snd) THEN
      SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY];
      REWRITE_TAC[\<in>] THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET; \<subseteq>];
      W(MP_TAC \<circ> PART_MATCH lhand CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE \<circ>
        lhand \<circ> snd) THEN
      SIMP_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER]]]);;

lemma locally_connected_space:
   "locally_connected_space X \<longleftrightarrow>
        \<forall>v x. openin X v \<and> x \<in> v
              \<Longrightarrow> \<exists>u. openin X u \<and>
                      connectedin X u \<and>
                      x \<in> u \<and> u \<subseteq> v"
oops
  SIMP_TAC[LOCALLY_CONNECTED_SPACE_ALT; OPEN_NEIGHBOURHOOD_BASE_OF] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC]);;

lemma locally_path_connected_imp_locally_connected_space:
   "locally_path_connected_space X \<Longrightarrow> locally_connected_space X"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[locally_path_connected_space; locally_connected_space] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] NEIGHBOURHOOD_BASE_OF_MONO) THEN
  SIMP_TAC[PATH_CONNECTED_IN_IMP_CONNECTED_IN]);;

lemma locally_connected_space_open_connected_components:
   "locally_connected_space X \<longleftrightarrow>
        \<forall>u c. openin X u \<and> c \<in> connected_components_of(subtopology X u)
              \<Longrightarrow> openin X c"
oops
  REWRITE_TAC[LOCALLY_CONNECTED_SPACE_EQ_OPEN_CONNECTED_COMPONENT_OF] THEN
  REWRITE_TAC[connected_components_of; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  MESON_TAC[\<subseteq>; OPEN_IN_SUBSET]);;

lemma openin_connected_component_of_locally_connected_space:
   "locally_connected_space X
             \<Longrightarrow> openin X (connected_component_of X x)"
oops
  METIS_TAC[LOCALLY_CONNECTED_SPACE_EQ_OPEN_CONNECTED_COMPONENT_OF;
            SUBTOPOLOGY_TOPSPACE; OPEN_IN_TOPSPACE;
            OPEN_IN_EMPTY; CONNECTED_COMPONENT_OF_EQ_EMPTY]);;

lemma openin_connected_components_of_locally_connected_space:
   "locally_connected_space X \<and> c \<in> connected_components_of X
        \<Longrightarrow> openin X c"
oops
  REWRITE_TAC[LOCALLY_CONNECTED_SPACE_OPEN_CONNECTED_COMPONENTS] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `topspace X::A=>bool` THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE]);;

lemma weakly_locally_connected_at:
   "weakly_locally_connected_at x X \<longleftrightarrow>
        \<forall>v. openin X v \<and> x \<in> v
            \<Longrightarrow> \<exists>u. openin X u \<and>
                    x \<in> u \<and> u \<subseteq> v \<and>
                    \<forall>y. y \<in> u
                        \<Longrightarrow> \<exists>c. connectedin X c \<and>
                                c \<subseteq> v \<and> x \<in> c \<and> y \<in> c"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[neighbourhood_base_at; weakly_locally_connected_at] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `v::A=>bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `v::A=>bool`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `u::A=>bool` THENL [ASM_MESON_TAC[\<subseteq>]; STRIP_TAC] THEN
  EXISTS_TAC `connected_component_of (subtopology X v) (x::A)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF;
              CONNECTED_IN_SUBTOPOLOGY];
    REWRITE_TAC[\<subseteq>] THEN X_GEN_TAC `y::A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `y::A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c::A=>bool` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC(SET_RULE `s \<subseteq> t \<Longrightarrow> x \<in> s \<Longrightarrow> x \<in> t`) THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
    ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY];
    MESON_TAC[CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE; TOPSPACE_SUBTOPOLOGY;
              SUBSET_INTER]]);;

lemma locally_connected_space_im_kleinen:
   "locally_connected_space X \<longleftrightarrow>
        \<forall>v x. openin X v \<and> x \<in> v
            \<Longrightarrow> \<exists>u. openin X u \<and>
                    x \<in> u \<and> u \<subseteq> v \<and>
                    \<forall>y. y \<in> u
                        \<Longrightarrow> \<exists>c. connectedin X c \<and>
                                c \<subseteq> v \<and> x \<in> c \<and> y \<in> c"
oops
  REWRITE_TAC[locally_connected_space; neighbourhood_base_of] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM weakly_locally_connected_at] THEN
  REWRITE_TAC[WEAKLY_LOCALLY_CONNECTED_AT] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[REWRITE_RULE[\<subseteq>] OPEN_IN_SUBSET]);;

lemma locally_connected_space_open_subset:
   "locally_connected_space X \<and> openin X s
        \<Longrightarrow> locally_connected_space (subtopology X s)"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_connected_space] THEN
  DISCH_THEN(MP_TAC \<circ> MATCH_MP NEIGHBOURHOOD_BASE_OF_OPEN_SUBSET) THEN
  GEN_REWRITE_TAC LAND_CONV [NEIGHBOURHOOD_BASE_OF_WITH_SUBSET] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] NEIGHBOURHOOD_BASE_OF_MONO) THEN
  SIMP_TAC[TOPSPACE_SUBTOPOLOGY; CONNECTED_IN_SUBTOPOLOGY;
           SUBSET_INTER]);;

lemma locally_connected_space_quotient_map_image:
   "\<And>X Y f::A=>B.
        quotient_map X Y f \<and> locally_connected_space X
        \<Longrightarrow> locally_connected_space Y"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[quotient_map] THEN
  REWRITE_TAC[LOCALLY_CONNECTED_SPACE_OPEN_CONNECTED_COMPONENTS] THEN
  STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`v::B=>bool`; `c::B=>bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th -> W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand) th \<circ> snd)) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER] THEN ASM SET_TAC[];
    DISCH_THEN(SUBST1_TAC \<circ> SYM)] THEN
  GEN_REWRITE_TAC id [OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x::A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  EXISTS_TAC
   `connected_component_of
      (subtopology X {z. z \<in> topspace X \<and> f z \<in> v}) x` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `{z. z \<in> topspace X \<and> f z \<in> v}` THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET; connected_components_of] THEN
    REWRITE_TAC[SIMPLE_IMAGE; ETA_AX] THEN MATCH_MP_TAC FUN_IN_IMAGE;
    GEN_REWRITE_TAC id [\<in>] THEN REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL];
    MATCH_MP_TAC(SET_RULE
     `\<forall>v. s \<subseteq> u \<inter> {x \<in> u. f x \<in> v} \<and> f ` s \<subseteq> c
          \<Longrightarrow> s \<subseteq> {x \<in> u. f x \<in> c}`) THEN
    EXISTS_TAC `v::B=>bool` THEN
    REWRITE_TAC[CONNECTED_COMPONENT_OF_SUBSET_TOPSPACE;
                GSYM TOPSPACE_SUBTOPOLOGY] THEN
    MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `subtopology X' (v::B=>bool)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN EXISTS_TAC
       `subtopology X {z. z \<in> topspace X \<and> f z \<in> v}` THEN
      REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF] THEN
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; \<subseteq>; FORALL_IN_IMAGE] THEN
      SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MATCH_MP_TAC QUOTIENT_IMP_CONTINUOUS_MAP THEN
      ASM_REWRITE_TAC[quotient_map];
      REWRITE_TAC[SET_RULE
       `\<not> disjnt t (f ` s) \<longleftrightarrow> \<exists>x. x \<in> s \<and> f x \<in> t`] THEN
      EXISTS_TAC `x::A` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC id [\<in>] THEN
      REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL]]] THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER] THEN ASM SET_TAC[]);;

lemma locally_connected_space_retraction_map_image:
   "\<And>X X' r.
        retraction_map X X' r \<and> locally_connected_space X
        \<Longrightarrow> locally_connected_space X'"
oops
  MESON_TAC[LOCALLY_CONNECTED_SPACE_QUOTIENT_MAP_IMAGE;
            RETRACTION_IMP_QUOTIENT_MAP]);;

lemma homeomorphic_locally_connected_space:
   "\<And>(X::A topology) (X':B topology).
        X homeomorphic_space X'
        \<Longrightarrow> (locally_connected_space X \<longleftrightarrow>
             locally_connected_space X')"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic_space] THEN
  REWRITE_TAC[HOMEOMORPHIC_MAPS_MAP; homeomorphic_map] THEN
  MESON_TAC[LOCALLY_CONNECTED_SPACE_QUOTIENT_MAP_IMAGE]);;

lemma locally_connected_space_euclideanreal:
 (`locally_connected_space euclideanreal"
oops
  SIMP_TAC[LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE;
           LOCALLY_PATH_CONNECTED_SPACE_EUCLIDEANREAL]);;

lemma locally_connected_is_realinterval:
   "is_interval s
       \<Longrightarrow> locally_connected_space(subtopology euclideanreal s)"
oops
  MESON_TAC[LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE;
            LOCALLY_PATH_CONNECTED_IS_REALINTERVAL]);;

lemma locally_connected_real_interval:
 (`(\<forall>a b. locally_connected_space
           (subtopology euclideanreal{a..b})) \<and>
   (\<forall>a b. locally_connected_space
           (subtopology euclideanreal{a<..<b}))"
oops
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LOCALLY_CONNECTED_IS_REALINTERVAL THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL]);;

lemma locally_connected_space_discrete_topology:
   "\<And>u::A=>bool. locally_connected_space (discrete_topology u)"
oops
  GEN_TAC THEN REWRITE_TAC[LOCALLY_CONNECTED_SPACE] THEN
  SIMP_TAC[OPEN_IN_DISCRETE_TOPOLOGY; CONNECTED_IN_DISCRETE_TOPOLOGY] THEN
  MAP_EVERY X_GEN_TAC [`v::A=>bool`; `x::A`] THEN STRIP_TAC THEN
  EXISTS_TAC `{x::A}` THEN ASM SET_TAC[]);;

lemma locally_path_connected_imp_locally_connected_at:
   "locally_path_connected_at x X \<Longrightarrow> locally_connected_at x X"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[locally_path_connected_at; locally_connected_at] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] NEIGHBOURHOOD_BASE_AT_MONO) THEN
  SIMP_TAC[PATH_CONNECTED_IN_IMP_CONNECTED_IN]);;

lemma weakly_locally_path_connected_imp_weakly_locally_connected_at:
   "weakly_locally_path_connected_at x X
             \<Longrightarrow> weakly_locally_connected_at x X"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[weakly_locally_path_connected_at;
              weakly_locally_connected_at] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] NEIGHBOURHOOD_BASE_AT_MONO) THEN
  SIMP_TAC[PATH_CONNECTED_IN_IMP_CONNECTED_IN]);;

lemma interior_of_locally_connected_subspace_component:
   "\<And>X s c::A=>bool.
        locally_connected_space X \<and>
        c \<in> connected_components_of (subtopology X s)
        \<Longrightarrow> X interior_of c = c \<inter> X interior_of s"
oops
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[SUBSET_INTER; INTERIOR_OF_MONO; INTERIOR_OF_SUBSET] THEN
  MP_TAC(ISPEC `subtopology X (X interior_of s::A=>bool)`
        UNIONS_CONNECTED_COMPONENTS_OF) THEN
  SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; INTERIOR_OF_SUBSET_TOPSPACE] THEN
  DISCH_THEN(SUBST1_TAC \<circ> SYM) THEN
  REWRITE_TAC[UNIONS_SUBSET; INTER_UNIONS; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `d::A=>bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `c \<inter> d::A=>bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
  MATCH_MP_TAC(SET_RULE `d \<subseteq> e \<Longrightarrow> c \<inter> d \<subseteq> e`) THEN
  MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `subtopology X (s::A=>bool)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP
      CONNECTED_IN_CONNECTED_COMPONENTS_OF)) THEN
    ASM_SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
    ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_OF_SUBSET];
    FIRST_X_ASSUM(MATCH_MP_TAC \<circ> GEN_REWRITE_RULE id
     [LOCALLY_CONNECTED_SPACE_OPEN_CONNECTED_COMPONENTS]) THEN
    EXISTS_TAC `X interior_of (s::A=>bool)` THEN
    ASM_REWRITE_TAC[OPEN_IN_INTERIOR_OF]]);;

lemma frontier_of_locally_connected_subspace_component:
   "\<And>X s c::A=>bool.
        locally_connected_space X \<and>
        closedin X s \<and>
        c \<in> connected_components_of (subtopology X s)
        \<Longrightarrow> X frontier_of c = c \<inter> X frontier_of s"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier_of] THEN
  REWRITE_TAC[SET_RULE `s \<inter> (t - u) = s \<inter> t - s \<inter> u`] THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CLOSED_IN_CONNECTED_COMPONENTS_OF) THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_SUBTOPOLOGY] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CLOSURE_OF_CLOSED_IN] THEN
  ASM_SIMP_TAC[GSYM INTERIOR_OF_LOCALLY_CONNECTED_SUBSPACE_COMPONENT] THEN
  ASM SET_TAC[]);;

lemma locally_connected_space_prod_topology:
   "locally_connected_space (prod_topology top1 top2) \<longleftrightarrow>
      topspace (prod_topology top1 top2) = {} \<or>
      locally_connected_space top1 \<and> locally_connected_space top2"
oops
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `topspace(prod_topology top1 top2):A#B=>bool = {}` THENL
   [ASM_REWRITE_TAC[locally_connected_space; NEIGHBOURHOOD_BASE_OF] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; \<subseteq>; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE
   [TOPSPACE_PROD_TOPOLOGY; CROSS_EQ_EMPTY; DE_MORGAN_THM]) THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
      LOCALLY_CONNECTED_SPACE_QUOTIENT_MAP_IMAGE))
    THENL [EXISTS_TAC `fst::A#B=>A`; EXISTS_TAC `snd::A#B=>B`] THEN
    ASM_REWRITE_TAC[QUOTIENT_MAP_FST; QUOTIENT_MAP_SND];
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `z::B` THEN DISCH_TAC THEN X_GEN_TAC `w::A` THEN DISCH_TAC THEN
    REWRITE_TAC[locally_connected_space; FORALL_PAIR_THM; IN_CROSS;
      NEIGHBOURHOOD_BASE_OF; TOPSPACE_PROD_TOPOLOGY] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`uv::A#B=>bool`; `x::A`; `y::B`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [OPEN_IN_PROD_TOPOLOGY_ALT] THEN
    DISCH_THEN(MP_TAC \<circ> SPECL [`x::A`; `y::B`]) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`w1::A=>bool`; `w2::B=>bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`w2::B=>bool`; `y::B`]) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`w1::A=>bool`; `x::A`]) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u1::A=>bool`; `k1::A=>bool`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`u2::B=>bool`; `k2::B=>bool`] THEN STRIP_TAC THEN
    EXISTS_TAC `(u1::A=>bool) \<times> (u2::B=>bool)` THEN
    EXISTS_TAC `(k1::A=>bool) \<times> (k2::B=>bool)` THEN
    ASM_SIMP_TAC[OPEN_IN_CROSS; CONNECTED_IN_CROSS;
                IN_CROSS; SUBSET_CROSS] THEN
    TRANS_TAC SUBSET_TRANS `(w1 \<times> w2):A#B=>bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[SUBSET_CROSS]]);;

lemma locally_connected_space_product_topology:
   "\<And>(tops::K=>A topology) k.
        locally_connected_space(product_topology k tops) \<longleftrightarrow>
        topspace(product_topology k tops) = {} \<or>
        finite {i. i \<in> k \<and> \<not> connected_space(tops i)} \<and>
        \<forall>i. i \<in> k \<Longrightarrow> locally_connected_space(tops i)"
oops
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `topspace(product_topology k (tops::K=>A topology)) = {}` THENL
   [ASM_REWRITE_TAC[locally_connected_space; NEIGHBOURHOOD_BASE_OF] THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; \<subseteq>; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[locally_connected_space; NEIGHBOURHOOD_BASE_OF] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `z::K=>A`) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC \<circ> SPECL
       [`topspace(product_topology k (tops::K=>A topology))`; `z::K=>A`]) THEN
      ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:(K=>A)->bool`; `c:(K=>A)->bool`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC \<circ> SPEC `z::K=>A` \<circ>
        REWRITE_RULE[OPEN_IN_PRODUCT_TOPOLOGY_ALT]) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `v::K=>A->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
      REWRITE_TAC[\<subseteq>; IN_ELIM_THM] THEN X_GEN_TAC `i::K` THEN
      ASM_CASES_TAC `(i::K) \<in> k` THEN ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
      DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC \<circ> ISPECL [`\<lambda>x::K=>A. x i`; `(tops::K=>A topology) i`] \<circ>
        MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
            CONNECTED_IN_CONTINUOUS_MAP_IMAGE)) THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION;
                   GSYM CONNECTED_IN_TOPSPACE] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC \<circ>
       MATCH_MP (SET_RULE `v = u \<Longrightarrow> v \<subseteq> s \<and> s \<subseteq> u \<Longrightarrow> s = u`)) THEN
      CONJ_TAC THENL
       [TRANS_TAC SUBSET_TRANS `image (\<lambda>x::K=>A. x i) u` THEN
        ASM_SIMP_TAC[IMAGE_SUBSET] THEN TRANS_TAC SUBSET_TRANS
         `image (\<lambda>x::K=>A. x i) (PiE k v)` THEN
        ASM_SIMP_TAC[IMAGE_SUBSET] THEN
        REWRITE_TAC[IMAGE_PROJECTION_CARTESIAN_PRODUCT] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
        ASM SET_TAC[];
        TRANS_TAC SUBSET_TRANS
          `image (\<lambda>x::K=>A. x i) (topspace(product_topology k tops))` THEN
        ASM_SIMP_TAC[IMAGE_SUBSET; CONNECTED_IN_SUBSET_TOPSPACE] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_PRODUCT_TOPOLOGY]) THEN
        ASM_REWRITE_TAC[IMAGE_PROJECTION_CARTESIAN_PRODUCT;
                        TOPSPACE_PRODUCT_TOPOLOGY] THEN
        REWRITE_TAC[o_THM; SUBSET_REFL]];
      X_GEN_TAC `i::K` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM locally_connected_space; ETA_AX;
                  GSYM NEIGHBOURHOOD_BASE_OF] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM locally_connected_space; ETA_AX;
                                  GSYM NEIGHBOURHOOD_BASE_OF]) THEN
      FIRST_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        (REWRITE_RULE[CONJ_ASSOC]
                LOCALLY_CONNECTED_SPACE_QUOTIENT_MAP_IMAGE)))  THEN
      EXISTS_TAC `\<lambda>x::K=>A. x i` THEN
      ASM_SIMP_TAC[OPEN_MAP_PRODUCT_PROJECTION; TOPSPACE_PRODUCT_TOPOLOGY;
                   QUOTIENT_MAP_PRODUCT_PROJECTION;
                   IMAGE_PROJECTION_CARTESIAN_PRODUCT] THEN
      ASM_REWRITE_TAC[GSYM TOPSPACE_PRODUCT_TOPOLOGY; o_THM]];
    STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`ww:(K=>A)->bool`; `z::K=>A`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [OPEN_IN_PRODUCT_TOPOLOGY_ALT] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `z::K=>A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w::K=>A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `\<forall>i. i \<in> k
          \<Longrightarrow> \<exists>u c. openin (tops i) u \<and>
                    connectedin (tops i) c \<and>
                    ((z::K=>A) i) \<in> u \<and>
                    u \<subseteq> c \<and>
                    c \<subseteq> w i \<and>
                    (w i = topspace(tops i) \<and> connected_space(tops i)
                     \<Longrightarrow> u = topspace(tops i) \<and> c = topspace(tops i))`
    MP_TAC THENL
     [X_GEN_TAC `i::K` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`i::K`; `(w::K=>A->bool) i`] \<circ>
        GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_FORALL_THM]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC \<circ> SPEC `(z::K=>A) i`) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MP_TAC \<circ>
         GEN_REWRITE_RULE RAND_CONV [PiE]) THEN
        ASM_SIMP_TAC[IN_ELIM_THM];
        ASM_CASES_TAC `connected_space((tops::K=>A topology) i)` THEN
        ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `(w::K=>A->bool) i = topspace(tops i)` THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
        REPEAT(EXISTS_TAC `topspace((tops::K=>A topology) i)`) THEN
        ASM_REWRITE_TAC[CONNECTED_IN_TOPSPACE; SUBSET_REFL] THEN
        REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[PiE; IN_ELIM_THM]) THEN
        ASM SET_TAC[]];
      GEN_REWRITE_TAC (LAND_CONV \<circ> TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`u::K=>A->bool`; `c::K=>A->bool`] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`PiE k (u::K=>A->bool)`;
      `PiE k (c::K=>A->bool)`] THEN
    ASM_SIMP_TAC[CONNECTED_IN_CARTESIAN_PRODUCT] THEN
    ASM_SIMP_TAC[SUBSET_CARTESIAN_PRODUCT] THEN
    REWRITE_TAC[OPEN_IN_CARTESIAN_PRODUCT_GEN] THEN REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{i. i \<in> k \<and> \<not> connected_space (tops i)} \<union>
                  {i. i \<in> k \<and> \<not> ((w::K=>A->bool) i = topspace (tops i))}` THEN
      ASM_REWRITE_TAC[FINITE_UNION] THEN ASM SET_TAC[];
      UNDISCH_TAC `(z::K=>A) \<in> PiE k w` THEN
      REWRITE_TAC[PiE; IN_ELIM_THM] THEN ASM SET_TAC[];
      TRANS_TAC SUBSET_TRANS `PiE k (w::K=>A->bool)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_CARTESIAN_PRODUCT] THEN
      ASM SET_TAC[]]]);;

lemma locally_connected_space_sum_topology:
   "\<And>k (X::K=>A topology).
        locally_connected_space(sum_topology k X) \<longleftrightarrow>
        \<forall>i. i \<in> k \<Longrightarrow> locally_connected_space(X i)"
oops
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MATCH_MP_TAC TOPOLOGICAL_PROPERTY_OF_SUM_COMPONENT THEN
    REWRITE_TAC[HOMEOMORPHIC_LOCALLY_CONNECTED_SPACE] THEN
    SIMP_TAC[LOCALLY_CONNECTED_SPACE_OPEN_SUBSET];
    REWRITE_TAC[locally_connected_space; NEIGHBOURHOOD_BASE_OF] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_OPEN_IN_SUM_TOPOLOGY] THEN
    DISCH_TAC THEN X_GEN_TAC `w::K=>A->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[FORALL_PAIR_THM; Sigma; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`i::K`; `x::A`] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> SPEC `i::K`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(w::K=>A->bool) i`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `x::A`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u::A=>bool`; `v::A=>bool`] THEN STRIP_TAC THEN
    EXISTS_TAC `image (\<lambda>x. (i::K),(x::A)) u` THEN
    EXISTS_TAC `image (\<lambda>x. (i::K),(x::A)) v` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; IN_ELIM_PAIR_THM] THEN
    ASM_REWRITE_TAC[GSYM \<subseteq>] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[open_map; RIGHT_IMP_FORALL_THM; IMP_IMP]
        OPEN_MAP_COMPONENT_INJECTION) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONNECTED_IN_CONTINUOUS_MAP_IMAGE THEN
      EXISTS_TAC `(X::K=>A topology) i` THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_COMPONENT_INJECTION];
      ASM SET_TAC[]]]);;


subsection\<open>Quasi-components\<close>


let quasi_component_of = new_definition
 `quasi_component_of X x y \<longleftrightarrow>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        \<forall>t. closedin X t \<and> openin X t \<Longrightarrow> (x \<in> t \<longleftrightarrow> y \<in> t)`;;

let quasi_components_of = new_definition
 `quasi_components_of X =
    {quasi_component_of X x |x| x \<in> topspace X}`;;

lemma quasi_component_in_topspace:
   "quasi_component_of X x y
        \<Longrightarrow> x \<in> topspace X \<and> y \<in> topspace X"
oops
  REWRITE_TAC[quasi_component_of] THEN MESON_TAC[]);;

lemma quasi_component_of_refl:
   "quasi_component_of X x x \<longleftrightarrow> x \<in> topspace X"
oops
  REWRITE_TAC[quasi_component_of] THEN MESON_TAC[]);;

lemma quasi_component_of_sym:
   "quasi_component_of X x y \<longleftrightarrow> quasi_component_of X y x"
oops
  REWRITE_TAC[quasi_component_of] THEN MESON_TAC[]);;

lemma quasi_component_of_trans:
   "quasi_component_of X x y \<and> quasi_component_of X y z
        \<Longrightarrow> quasi_component_of X x z"
oops
  REWRITE_TAC[quasi_component_of] THEN MESON_TAC[]);;

lemma quasi_component_of_subset_topspace:
   "(quasi_component_of X x) \<subseteq> topspace X"
oops
  REWRITE_TAC[\<subseteq>; \<in>] THEN MESON_TAC[QUASI_COMPONENT_IN_TOPSPACE; \<in>]);;

lemma quasi_component_of_eq_empty:
   "quasi_component_of X x = {} \<longleftrightarrow> (x \<notin> topspace X)"
oops
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[\<in>; QUASI_COMPONENT_OF_REFL; QUASI_COMPONENT_IN_TOPSPACE]);;

lemma quasi_component_of:
   "quasi_component_of X x y \<longleftrightarrow>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        \<forall>t. x \<in> t \<and> closedin X t \<and> openin X t \<Longrightarrow> y \<in> t"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[quasi_component_of] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s::A=>bool` THEN STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN
  GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `topspace X - s::A=>bool`) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN
  ASM_MESON_TAC[OPEN_IN_CLOSED_IN_EQ; closedin]);;

lemma quasi_component_of_alt:
   "quasi_component_of X x y \<longleftrightarrow>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        \<not> (\<exists>u v. openin X u \<and> openin X v \<and>
                u \<union> v = topspace X \<and>
                disjnt u v \<and> x \<in> u \<and> y \<in> v)"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[QUASI_COMPONENT_OF] THEN
  ASM_CASES_TAC `(x::A) \<in> topspace X` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(y::A) \<in> topspace X` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[SET_RULE
   `u \<union> v = s \<and> disjnt u v \<and> x \<in> u \<and> y \<in> v \<longleftrightarrow>
    u \<subseteq> s \<and> v = s - u \<and> x \<in> u \<and> y \<in> s \<and> (y \<notin> u)`] THEN
  ONCE_REWRITE_TAC[TAUT `p \<and> q \<and> r \<and> s \<and> t \<longleftrightarrow> s \<and> p \<and> q \<and> r \<and> t`] THEN
  REWRITE_TAC[UNWIND_THM2; closedin] THEN SET_TAC[]);;

lemma quasi_component_of_set:
   "quasi_component_of X x =
        if x \<in> topspace X
        then \<Inter> {t. closedin X t \<and> openin X t \<and> x \<in> t}
        else {}"
oops
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC `y::A` THEN
  GEN_REWRITE_TAC LAND_CONV [\<in>] THEN REWRITE_TAC[QUASI_COMPONENT_OF] THEN
  ASM_CASES_TAC `(x::A) \<in> topspace X` THEN
  ASM_REWRITE_TAC[IN_INTERS; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  ASM_MESON_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_TOPSPACE]);;

lemma quasi_component_of_separated:
   "quasi_component_of X x y \<longleftrightarrow>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        \<not> (\<exists>u v. separatedin X u v \<and> u \<union> v = topspace X \<and>
                x \<in> u \<and> y \<in> v)"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[QUASI_COMPONENT_OF_ALT] THEN
  MESON_TAC[SEPARATED_IN_OPEN_SETS; SEPARATED_IN_FULL]);;

lemma quasi_component_of_subtopology:
   "quasi_component_of (subtopology X s) x y
        \<Longrightarrow> quasi_component_of X x y"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[quasi_component_of] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t::A=>bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `s \<inter> t::A=>bool`) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN] THEN
  ASM_SIMP_TAC[CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED]);;

lemma quasi_component_of_mono:
   "quasi_component_of (subtopology X s) x y \<and> s \<subseteq> t
        \<Longrightarrow> quasi_component_of (subtopology X t) x y"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_THEN(SUBST1_TAC \<circ>
   MATCH_MP (SET_RULE `s \<subseteq> t \<Longrightarrow> s = t \<inter> s`)) THEN
  REWRITE_TAC[GSYM SUBTOPOLOGY_SUBTOPOLOGY] THEN
  REWRITE_TAC[QUASI_COMPONENT_OF_SUBTOPOLOGY]);;

lemma quasi_component_of_equiv:
   "quasi_component_of X x y \<longleftrightarrow>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        quasi_component_of X x = quasi_component_of X y"
oops
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[QUASI_COMPONENT_OF_REFL; QUASI_COMPONENT_OF_TRANS;
            QUASI_COMPONENT_OF_SYM]);;

lemma quasi_component_of_disjoint:
   "disjnt (quasi_component_of X x)
                 (quasi_component_of X y) \<longleftrightarrow>
        \<not> (quasi_component_of X x y)"
oops
  REWRITE_TAC[disjnt; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  REWRITE_TAC[\<in>] THEN
  MESON_TAC[QUASI_COMPONENT_OF_SYM; QUASI_COMPONENT_OF_TRANS]);;

lemma quasi_component_of_eq:
   "quasi_component_of X x = quasi_component_of X y \<longleftrightarrow>
        (x \<notin> topspace X) \<and> (y \<notin> topspace X) \<or>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        quasi_component_of X x y"
oops
  MESON_TAC[QUASI_COMPONENT_OF_REFL; QUASI_COMPONENT_OF_EQUIV;
            QUASI_COMPONENT_OF_EQ_EMPTY]);;

lemma unions_quasi_components_of:
   "\<Union> (quasi_components_of X) = topspace X"
oops
  GEN_TAC THEN REWRITE_TAC[quasi_components_of] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC;
              QUASI_COMPONENT_OF_SUBSET_TOPSPACE] THEN
  REWRITE_TAC[\<subseteq>; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x::A` THEN DISCH_TAC THEN EXISTS_TAC `x::A` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[\<in>] THEN
  ASM_REWRITE_TAC[QUASI_COMPONENT_OF_REFL]);;

lemma pairwise_disjoint_quasi_components_of:
   "pairwise disjnt (quasi_components_of X)"
oops
  SIMP_TAC[pairwise; IMP_CONJ; quasi_components_of;
           RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[QUASI_COMPONENT_OF_EQ; QUASI_COMPONENT_OF_DISJOINT]);;

lemma complement_quasi_components_of_unions:
   "c \<in> quasi_components_of X
      \<Longrightarrow> topspace X - c = \<Union> (quasi_components_of X - {c})"
oops
  REWRITE_TAC[SET_RULE `s - {a} = s - {a}`] THEN
  ASM_SIMP_TAC[GSYM DIFF_UNIONS_PAIRWISE_DISJOINT;
               PAIRWISE_DISJOINT_QUASI_COMPONENTS_OF; SING_SUBSET] THEN
  REWRITE_TAC[UNIONS_QUASI_COMPONENTS_OF; UNIONS_1]);;

lemma nonempty_quasi_components_of:
   "c \<in> quasi_components_of X \<Longrightarrow> (c \<noteq> {})"
oops
  SIMP_TAC[quasi_components_of; FORALL_IN_GSPEC;
           QUASI_COMPONENT_OF_EQ_EMPTY]);;

lemma quasi_components_of_subset:
   "c \<in> quasi_components_of X \<Longrightarrow> c \<subseteq> topspace X"
oops
  SIMP_TAC[quasi_components_of; FORALL_IN_GSPEC;
           QUASI_COMPONENT_OF_SUBSET_TOPSPACE]);;

lemma quasi_component_in_quasi_components_of:
   "quasi_component_of X a \<in> quasi_components_of X \<longleftrightarrow>
        a \<in> topspace X"
oops
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN
    SIMP_TAC[GSYM QUASI_COMPONENT_OF_EQ_EMPTY] THEN
    MESON_TAC[NONEMPTY_QUASI_COMPONENTS_OF];
    REWRITE_TAC[quasi_components_of] THEN SET_TAC[]]);;

lemma quasi_components_of_eq_empty:
   "quasi_components_of X = {} \<longleftrightarrow> topspace X = {}"
oops
  REWRITE_TAC[quasi_components_of] THEN SET_TAC[]);;

lemma quasi_components_of_empty_space:
   "topspace X = {} \<Longrightarrow> quasi_components_of X = {}"
oops
  REWRITE_TAC[QUASI_COMPONENTS_OF_EQ_EMPTY]);;

lemma closedin_quasi_component_of:
   "closedin X (quasi_component_of X x)"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[QUASI_COMPONENT_OF_SET] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CLOSED_IN_EMPTY] THEN
  MATCH_MP_TAC CLOSED_IN_INTERS THEN
  SIMP_TAC[IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `topspace X::A=>bool` THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_TOPSPACE]);;

lemma closedin_quasi_components_of:
   "c \<in> quasi_components_of X \<Longrightarrow> closedin X c"
oops
  REWRITE_TAC[quasi_components_of; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[CLOSED_IN_QUASI_COMPONENT_OF]);;

lemma openin_finite_quasi_components:
   "finite(quasi_components_of X) \<and>
        c \<in> quasi_components_of X
        \<Longrightarrow> openin X c"
oops
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[OPEN_IN_CLOSED_IN_EQ; QUASI_COMPONENTS_OF_SUBSET] THEN
  ASM_SIMP_TAC[COMPLEMENT_QUASI_COMPONENTS_OF_UNIONS] THEN
  MATCH_MP_TAC CLOSED_IN_UNIONS THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; CLOSED_IN_QUASI_COMPONENTS_OF]);;

lemma quasi_component_of_eq_overlap:
   "quasi_component_of X x = quasi_component_of X y \<longleftrightarrow>
      (x \<notin> topspace X) \<and> (y \<notin> topspace X) \<or>
      \<not> (quasi_component_of X x \<inter> quasi_component_of X y = {})"
oops
  REWRITE_TAC[GSYM disjnt; QUASI_COMPONENT_OF_DISJOINT] THEN
  REWRITE_TAC[QUASI_COMPONENT_OF_EQ] THEN
  MESON_TAC[QUASI_COMPONENT_IN_TOPSPACE]);;

lemma quasi_component_of_nonoverlap:
   "quasi_component_of X x \<inter> quasi_component_of X y = {} \<longleftrightarrow>
     (x \<notin> topspace X) \<or> (y \<notin> topspace X) \<or>
     \<not> (quasi_component_of X x = quasi_component_of X y)"
oops
  REWRITE_TAC[GSYM disjnt; QUASI_COMPONENT_OF_DISJOINT] THEN
  REWRITE_TAC[QUASI_COMPONENT_OF_EQ] THEN
  MESON_TAC[QUASI_COMPONENT_IN_TOPSPACE]);;

lemma quasi_component_of_overlap:
   "\<not> (quasi_component_of X x \<inter> quasi_component_of X y = {}) \<longleftrightarrow>
    x \<in> topspace X \<and> y \<in> topspace X \<and>
    quasi_component_of X x = quasi_component_of X y"
oops
  REWRITE_TAC[GSYM disjnt; QUASI_COMPONENT_OF_DISJOINT] THEN
  REWRITE_TAC[QUASI_COMPONENT_OF_EQ] THEN
  MESON_TAC[QUASI_COMPONENT_IN_TOPSPACE]);;

lemma quasi_components_of_disjoint:
   "\<And>X c c'.
        c \<in> quasi_components_of X \<and> c' \<in> quasi_components_of X
        \<Longrightarrow> (disjnt c c' \<longleftrightarrow> (c \<noteq> c'))"
oops
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; quasi_components_of] THEN
  SIMP_TAC[FORALL_IN_GSPEC; disjnt; QUASI_COMPONENT_OF_NONOVERLAP]);;

lemma quasi_components_of_overlap:
   "\<And>X c c'.
        c \<in> quasi_components_of X \<and> c' \<in> quasi_components_of X
        \<Longrightarrow> (\<not> (c \<inter> c' = {}) \<longleftrightarrow> c = c')"
oops
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; quasi_components_of] THEN
  SIMP_TAC[FORALL_IN_GSPEC; disjnt; QUASI_COMPONENT_OF_NONOVERLAP]);;

lemma pairwise_separated_quasi_components_of:
   "pairwise (separatedin X) (quasi_components_of X)"
oops
  REWRITE_TAC[pairwise] THEN
  SIMP_TAC[CLOSED_IN_QUASI_COMPONENTS_OF; SEPARATED_IN_CLOSED_SETS] THEN
  REWRITE_TAC[GSYM pairwise; PAIRWISE_DISJOINT_QUASI_COMPONENTS_OF]);;

lemma card_le_quasi_components_of_topspace:
   "quasi_components_of X \<lesssim> topspace X"
oops
  GEN_TAC THEN MATCH_MP_TAC CARD_LE_RELATIONAL_FULL THEN
  EXISTS_TAC `(\<in>):A->(A=>bool)->bool` THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP QUASI_COMPONENTS_OF_SUBSET) THEN
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP NONEMPTY_QUASI_COMPONENTS_OF) THEN
    SET_TAC[];
    MESON_TAC[REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]
                QUASI_COMPONENTS_OF_OVERLAP]]);;

lemma finite_quasi_components_of_finite:
   "finite(topspace X) \<Longrightarrow> finite(quasi_components_of X)"
oops
  GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CARD_LE_FINITE) THEN
  REWRITE_TAC[CARD_LE_QUASI_COMPONENTS_OF_TOPSPACE]);;

lemma connected_imp_quasi_component_of:
   "connected_component_of X x y \<Longrightarrow> quasi_component_of X x y"
oops
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC \<circ> MATCH_MP CONNECTED_COMPONENT_IN_TOPSPACE) THEN
  ASM_REWRITE_TAC[QUASI_COMPONENT_OF] THEN
  X_GEN_TAC `t::A=>bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [connected_component_of]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c::A=>bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X::A topology`; `c::A=>bool`; `t::A=>bool`]
        CONNECTED_IN_CLOPEN_CASES) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

lemma connected_component_subset_quasi_component_of:
   "connected_component_of X x \<subseteq> quasi_component_of X x"
oops
  REWRITE_TAC[\<subseteq>; \<in>; CONNECTED_IMP_QUASI_COMPONENT_OF]);;

lemma quasi_component_as_connected_component_unions:
   "quasi_component_of X x =
        \<Union> {connected_component_of X y |y| quasi_component_of X x y}"
oops
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC id [\<subseteq>] THEN X_GEN_TAC `y::A` THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    REWRITE_TAC[\<in>] THEN DISCH_TAC THEN EXISTS_TAC `y::A` THEN
    ASM_MESON_TAC[CONNECTED_COMPONENT_OF_REFL; QUASI_COMPONENT_IN_TOPSPACE];
    X_GEN_TAC `y::A` THEN SIMP_TAC[QUASI_COMPONENT_OF_EQUIV] THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET_QUASI_COMPONENT_OF]]);;

lemma quasi_components_as_connected_components_unions:
   "c \<in> quasi_components_of X
        \<Longrightarrow> \<exists>t. t \<subseteq> connected_components_of X \<and> \<Union> t = c"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[quasi_components_of; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x::A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  EXISTS_TAC
   `{connected_component_of X (y::A) |y| quasi_component_of X x y}` THEN
  REWRITE_TAC[GSYM QUASI_COMPONENT_AS_CONNECTED_COMPONENT_UNIONS] THEN
  REWRITE_TAC[\<subseteq>; connected_components_of; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `y::A` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[QUASI_COMPONENT_IN_TOPSPACE]);;

lemma path_imp_quasi_component_of:
   "path_component_of X x y \<Longrightarrow> quasi_component_of X x y"
oops
  MESON_TAC[CONNECTED_IMP_QUASI_COMPONENT_OF;
            PATH_IMP_CONNECTED_COMPONENT_OF]);;

lemma path_component_subset_quasi_component_of:
   "path_component_of X x \<subseteq> quasi_component_of X x"
oops
  REWRITE_TAC[\<subseteq>; \<in>; PATH_IMP_QUASI_COMPONENT_OF]);;

lemma connected_space_iff_quasi_component:
   "connected_space X \<longleftrightarrow>
        \<forall>x y. x \<in> topspace X \<and> y \<in> topspace X
              \<Longrightarrow> quasi_component_of X x y"
oops
  GEN_TAC THEN REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN
  REWRITE_TAC[QUASI_COMPONENT_OF] THEN
  REWRITE_TAC[closedin] THEN SET_TAC[]);;

lemma connected_space_imp_quasi_component_of:
   "connected_space X \<and> a \<in> topspace X \<and> b \<in> topspace X
        \<Longrightarrow> quasi_component_of X a b"
oops
  MESON_TAC[CONNECTED_SPACE_IFF_QUASI_COMPONENT]);;

lemma connected_space_quasi_component_set:
   "connected_space X \<longleftrightarrow>
         \<forall>x::A. x \<in> topspace X
               \<Longrightarrow> quasi_component_of X x = topspace X"
oops
  REWRITE_TAC[CONNECTED_SPACE_IFF_QUASI_COMPONENT;
              GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[QUASI_COMPONENT_OF_SUBSET_TOPSPACE] THEN SET_TAC[]);;

lemma connected_space_iff_quasi_components_eq:
   "connected_space X \<longleftrightarrow>
        !c c'. c \<in> quasi_components_of X \<and>
               c' \<in> quasi_components_of X
               \<Longrightarrow> c = c'"
oops
  REWRITE_TAC[quasi_components_of; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; CONNECTED_SPACE_IFF_QUASI_COMPONENT] THEN
  SIMP_TAC[QUASI_COMPONENT_OF_EQ] THEN MESON_TAC[]);;

lemma quasi_components_of_subset_sing:
   "quasi_components_of X \<subseteq> {s} \<longleftrightarrow>
        connected_space X \<and> (topspace X = {} \<or> topspace X = s)"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONNECTED_SPACE_IFF_QUASI_COMPONENTS_EQ; SET_RULE
   `(\<forall>x y. x \<in> s \<and> y \<in> s \<Longrightarrow> x = y) \<longleftrightarrow> s = {} \<or> \<exists>a. s = {a}`] THEN
  ASM_CASES_TAC `topspace X::A=>bool = {}` THEN
  ASM_SIMP_TAC[QUASI_COMPONENTS_OF_EMPTY_SPACE; EMPTY_SUBSET] THEN
  ASM_REWRITE_TAC[QUASI_COMPONENTS_OF_EQ_EMPTY; SET_RULE
   `s \<subseteq> {a} \<longleftrightarrow> s = {} \<or> s = {a}`] THEN
  MESON_TAC[UNIONS_QUASI_COMPONENTS_OF; UNIONS_1]);;

lemma connected_space_iff_quasi_components_subset_sing:
   "connected_space X \<longleftrightarrow> \<exists>a. quasi_components_of X \<subseteq> {a}"
oops
  MESON_TAC[QUASI_COMPONENTS_OF_SUBSET_SING]);;

lemma quasi_components_of_eq_sing:
   "quasi_components_of X = {s} \<longleftrightarrow>
        connected_space X \<and> \<not> (topspace X = {}) \<and> s = topspace X"
oops
  REWRITE_TAC[QUASI_COMPONENTS_OF_SUBSET_SING;
              QUASI_COMPONENTS_OF_EQ_EMPTY;
              SET_RULE `s = {a} \<longleftrightarrow> s \<subseteq> {a} \<and> (s \<noteq> {})`] THEN
  MESON_TAC[]);;

lemma quasi_components_of_connected_space:
   "connected_space X
        \<Longrightarrow> quasi_components_of X =
            if topspace X = {} then {} else {topspace X}"
oops
  ASM_MESON_TAC[QUASI_COMPONENTS_OF_EMPTY_SPACE;
                QUASI_COMPONENTS_OF_EQ_SING]);;

lemma separated_between_sings:
   "separated_between X {x} {y} \<longleftrightarrow>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        \<not> (quasi_component_of X x y)"
oops
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(x::A) \<in> topspace X` THENL
   [ALL_TAC; ASM_MESON_TAC[SEPARATED_BETWEEN_IMP_SUBSET; SING_SUBSET]] THEN
  ASM_CASES_TAC `(y::A) \<in> topspace X` THENL
   [ALL_TAC; ASM_MESON_TAC[SEPARATED_BETWEEN_IMP_SUBSET; SING_SUBSET]] THEN
  ASM_REWRITE_TAC[separated_between; QUASI_COMPONENT_OF_ALT; SING_SUBSET]);;

lemma quasi_component_nonseparated:
   "quasi_component_of X x y \<longleftrightarrow>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        \<not> (separated_between X {x} {y})"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SEPARATED_BETWEEN_SINGS] THEN
  MESON_TAC[QUASI_COMPONENT_IN_TOPSPACE]);;

lemma separated_between_quasi_component_pointwise_left:
   "\<And>X c s::A=>bool.
        c \<in> quasi_components_of X
        \<Longrightarrow> (separated_between X c s \<longleftrightarrow>
             \<exists>x. x \<in> c \<and> separated_between X {x} s)"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[NONEMPTY_QUASI_COMPONENTS_OF; SING_SUBSET; MEMBER_NOT_EMPTY;
                  SEPARATED_BETWEEN_MONO; SUBSET_REFL];
    DISCH_THEN(X_CHOOSE_THEN `y::A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))] THEN
  REWRITE_TAC[SEPARATED_BETWEEN; SING_SUBSET] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u::A=>bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE RAND_CONV [quasi_components_of]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x::A` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(y::A) \<in> c` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [\<in>] THEN REWRITE_TAC[quasi_component_of] THEN
  DISCH_TAC THEN REWRITE_TAC[\<subseteq>] THEN X_GEN_TAC `z::A` THEN
  GEN_REWRITE_TAC LAND_CONV [\<in>] THEN REWRITE_TAC[quasi_component_of] THEN
  ASM_MESON_TAC[]);;

lemma separated_between_quasi_component_pointwise_right:
   "\<And>X s c::A=>bool.
        c \<in> quasi_components_of X
        \<Longrightarrow> (separated_between X s c \<longleftrightarrow>
             \<exists>x. x \<in> c \<and> separated_between X s {x})"
oops
  ONCE_REWRITE_TAC[SEPARATED_BETWEEN_SYM] THEN
  REWRITE_TAC[SEPARATED_BETWEEN_QUASI_COMPONENT_POINTWISE_LEFT]);;

lemma separated_between_quasi_component_point:
   "c \<in> quasi_components_of X
        \<Longrightarrow> (separated_between X c {x} \<longleftrightarrow> x \<in> topspace X - c)"
oops
  REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[SEPARATED_BETWEEN_IMP_DISJOINT; DISJOINT_SING;
                  SEPARATED_BETWEEN_IMP_SUBSET; SING_SUBSET];
    ASM_SIMP_TAC[SEPARATED_BETWEEN_QUASI_COMPONENT_POINTWISE_LEFT]] THEN
  REWRITE_TAC[SEPARATED_BETWEEN_SINGS; RIGHT_IMP_EXISTS_THM] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE RAND_CONV [quasi_components_of]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `y::A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[\<in>] THEN ASM_REWRITE_TAC[quasi_component_of]);;

lemma separated_between_point_quasi_component:
   "\<And>X (x::A) c.
        c \<in> quasi_components_of X
        \<Longrightarrow> (separated_between X {x} c \<longleftrightarrow> x \<in> topspace X - c)"
oops
  ONCE_REWRITE_TAC[SEPARATED_BETWEEN_SYM] THEN
  REWRITE_TAC[SEPARATED_BETWEEN_QUASI_COMPONENT_POINT]);;

lemma separated_between_quasi_component_compact:
   "\<And>X c k::A=>bool.
        c \<in> quasi_components_of X \<and> compactin X k
        \<Longrightarrow> (separated_between X c k \<longleftrightarrow> disjnt c k)"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[SEPARATED_BETWEEN_IMP_DISJOINT] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[SEPARATED_BETWEEN_POINTWISE_RIGHT] THEN
  ASM_SIMP_TAC[SEPARATED_BETWEEN_QUASI_COMPONENT_POINT] THEN
  FIRST_X_ASSUM(ASSUME_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
  FIRST_X_ASSUM(ASSUME_TAC \<circ> MATCH_MP QUASI_COMPONENTS_OF_SUBSET) THEN
  ASM SET_TAC[]);;

lemma separated_between_compact_quasi_component:
   "\<And>X k c::A=>bool.
        compactin X k \<and> c \<in> quasi_components_of X
        \<Longrightarrow> (separated_between X k c \<longleftrightarrow> disjnt k c)"
oops
  ONCE_REWRITE_TAC[SEPARATED_BETWEEN_SYM; DISJOINT_SYM] THEN
  SIMP_TAC[SEPARATED_BETWEEN_QUASI_COMPONENT_COMPACT]);;

lemma separated_between_quasi_components:
   "\<And>X c c':A=>bool.
        c \<in> quasi_components_of X \<and> c' \<in> quasi_components_of X
        \<Longrightarrow> (separated_between X c c' \<longleftrightarrow> disjnt c c')"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[SEPARATED_BETWEEN_IMP_DISJOINT] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[SEPARATED_BETWEEN_QUASI_COMPONENT_POINTWISE_RIGHT;
               SEPARATED_BETWEEN_QUASI_COMPONENT_POINTWISE_LEFT] THEN
  UNDISCH_TAC `(c::A=>bool) \<in> quasi_components_of X` THEN
  REWRITE_TAC[quasi_components_of; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x::A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[QUASI_COMPONENT_OF_REFL; \<in>]; ALL_TAC] THEN
  UNDISCH_TAC `(c':A=>bool) \<in> quasi_components_of X` THEN
  REWRITE_TAC[quasi_components_of; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y::A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[QUASI_COMPONENT_OF_REFL; \<in>]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SEPARATED_BETWEEN_SINGS] THEN
  ASM_REWRITE_TAC[GSYM QUASI_COMPONENT_OF_DISJOINT]);;

lemma quasi_eq_connected_component_of_eq:
   "quasi_component_of X x = connected_component_of X x \<longleftrightarrow>
             connectedin X (quasi_component_of X x)"
oops
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x::A) \<in> topspace X` THENL
   [ALL_TAC;
    ASM_MESON_TAC[QUASI_COMPONENT_OF_EQ_EMPTY; CONNECTED_COMPONENT_OF_EQ_EMPTY;
                  CONNECTED_IN_EMPTY]] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[CONNECTED_IN_CONNECTED_COMPONENT_OF];
    DISCH_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[CONNECTED_COMPONENT_SUBSET_QUASI_COMPONENT_OF] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_OF_MAXIMAL THEN
  ASM_REWRITE_TAC[\<in>] THEN
  ASM_REWRITE_TAC[QUASI_COMPONENT_OF_REFL]);;

lemma connected_quasi_component_of:
   "c \<in> quasi_components_of X
        \<Longrightarrow> (c \<in> connected_components_of X \<longleftrightarrow> connectedin X c)"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[CONNECTED_IN_CONNECTED_COMPONENTS_OF] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `(c::A=>bool) \<in> quasi_components_of X` THEN
  REWRITE_TAC[quasi_components_of; connected_components_of] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_MESON_TAC[QUASI_EQ_CONNECTED_COMPONENT_OF_EQ]);;

lemma quasi_component_of_clopen_cases:
   "\<And>X c t::A=>bool.
        c \<in> quasi_components_of X \<and> closedin X t \<and> openin X t
        \<Longrightarrow> c \<subseteq> t \<or> disjnt c t"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; quasi_components_of; IN_ELIM_THM; LEFT_IMP_EXISTS_THM;
              SET_RULE `c = s \<longleftrightarrow> \<forall>x. x \<in> c \<longleftrightarrow> s x`] THEN
  REWRITE_TAC[quasi_component_of] THEN
  REWRITE_TAC[closedin] THEN SET_TAC[]);;

lemma quasi_components_of_set:
   "c \<in> quasi_components_of X
        \<Longrightarrow> \<Inter> {t. closedin X t \<and> openin X t \<and> c \<subseteq> t} = c"
oops
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  SIMP_TAC[SUBSET_INTERS; FORALL_IN_GSPEC] THEN
  GEN_REWRITE_TAC id [\<subseteq>] THEN X_GEN_TAC `x::A` THEN
  REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `p \<Longrightarrow> q \<longleftrightarrow> p \<Longrightarrow> \<not> q \<Longrightarrow> \<not> p`] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `topspace X::A=>bool`) THEN
  ASM_SIMP_TAC[QUASI_COMPONENTS_OF_SUBSET] THEN
  REWRITE_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_TOPSPACE] THEN
  REWRITE_TAC[GSYM IN_DIFF; IMP_IMP] THEN
  ASM_SIMP_TAC[GSYM SEPARATED_BETWEEN_QUASI_COMPONENT_POINT] THEN
  REWRITE_TAC[SEPARATED_BETWEEN] THEN SET_TAC[]);;

lemma open_quasi_eq_connected_components_of:
   "openin X c
        \<Longrightarrow> (c \<in> quasi_components_of X \<longleftrightarrow>
             c \<in> connected_components_of X)"
oops
  REPEAT GEN_TAC THEN ASM_CASES_TAC `closedin X (c::A=>bool)` THENL
   [STRIP_TAC;
    ASM_MESON_TAC[CLOSED_IN_CONNECTED_COMPONENTS_OF;
                  CLOSED_IN_QUASI_COMPONENTS_OF]] THEN
  EQ_TAC THENL
   [SIMP_TAC[CONNECTED_QUASI_COMPONENT_OF] THEN
    SIMP_TAC[connectedin; QUASI_COMPONENTS_OF_SUBSET] THEN DISCH_TAC THEN
    REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY; CLOSED_IN_CLOSED_SUBTOPOLOGY] THEN
    X_GEN_TAC `t::A=>bool` THEN STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
     `(\<forall>x. x \<in> s \<Longrightarrow> P) \<Longrightarrow> s = {} \<or> P`) THEN
    X_GEN_TAC `z::A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; QUASI_COMPONENTS_OF_SUBSET] THEN
    ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
    MP_TAC(ISPECL [`X::A topology`; `c::A=>bool`; `t::A=>bool`]
        QUASI_COMPONENT_OF_CLOPEN_CASES) THEN
    ASM SET_TAC[];
    REWRITE_TAC[connected_components_of; quasi_components_of] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x::A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET_QUASI_COMPONENT_OF] THEN
    ASM_SIMP_TAC[QUASI_COMPONENT_OF_SET] THEN
    MATCH_MP_TAC INTERS_SUBSET_STRONG THEN
    EXISTS_TAC `c::A=>bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN REWRITE_TAC[\<in>] THEN
    ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL]]);;

lemma quasi_component_of_continuous_image:
   "\<And>X X' f x y.
        continuous_map X X' f \<and>
        quasi_component_of X x y
        \<Longrightarrow> quasi_component_of X' (f x) (f y)"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[quasi_component_of] THEN
  STRIP_TAC THEN
  REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[continuous_map]; ALL_TAC]) THEN
  X_GEN_TAC `t::B=>bool` THEN STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC \<circ> SPEC `{x \<in> topspace X. f x \<in> t}`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE;
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE] THEN
  ASM_MESON_TAC[]);;

lemma quasi_component_of_discrete_topology:
   "quasi_component_of (discrete_topology u) x =
           if x \<in> u then {x} else {}"
oops
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN
  X_GEN_TAC `y::A` THEN GEN_REWRITE_TAC LAND_CONV [\<in>] THEN
  REWRITE_TAC[quasi_component_of; TOPSPACE_DISCRETE_TOPOLOGY] THEN
  REWRITE_TAC[OPEN_IN_DISCRETE_TOPOLOGY; CLOSED_IN_DISCRETE_TOPOLOGY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY] THEN
  EQ_TAC THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `{x::A}`) THEN
  ASM_REWRITE_TAC[IN_SING; SING_SUBSET]);;

lemma quasi_components_of_discrete_topology:
   "\<And>u::A=>bool.
        quasi_components_of (discrete_topology u) = {{x} | x \<in> u}"
oops
  GEN_TAC THEN REWRITE_TAC[quasi_components_of] THEN
  REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY;
              QUASI_COMPONENT_OF_DISCRETE_TOPOLOGY] THEN
  SET_TAC[]);;

lemma homeomorphic_map_quasi_component_of:
   "\<And>f X X' x.
        homeomorphic_map X X' f \<and> x \<in> topspace X
        \<Longrightarrow> quasi_component_of X' (f x) =
            f ` (quasi_component_of X x)"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `g::B=>A` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN REWRITE_TAC[\<in>] THEN
  MP_TAC(ISPEC `X':B topology` QUASI_COMPONENT_IN_TOPSPACE) THEN
  MP_TAC(ISPECL [`X::A topology`; `X':B topology`; `f::A=>B`]
        QUASI_COMPONENT_OF_CONTINUOUS_IMAGE) THEN
  MP_TAC(ISPECL [`X':B topology`; `X::A topology`; `g::B=>A`]
        QUASI_COMPONENT_OF_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT
   (FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE)) THEN
  ASM SET_TAC[]);;

lemma homeomorphic_map_quasi_components_of:
   "\<And>f X X'.
      homeomorphic_map X X' f
      \<Longrightarrow> quasi_components_of X' =
          image (image f) (quasi_components_of X)"
oops
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[quasi_components_of; SIMPLE_IMAGE] THEN
  FIRST_ASSUM(SUBST1_TAC \<circ> SYM \<circ> MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN MATCH_MP_TAC(SET_RULE
   `(\<forall>x. x \<in> s \<Longrightarrow> f x = g x) \<Longrightarrow> f ` s = g ` s`) THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[HOMEOMORPHIC_MAP_QUASI_COMPONENT_OF]);;

lemma openin_quasi_component_of_locally_connected_space:
   "locally_connected_space X
        \<Longrightarrow> openin X (quasi_component_of X x)"
oops
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[QUASI_COMPONENT_AS_CONNECTED_COMPONENT_UNIONS] THEN
  MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[OPEN_IN_CONNECTED_COMPONENT_OF_LOCALLY_CONNECTED_SPACE]);;

lemma openin_quasi_components_of_locally_connected_space:
   "locally_connected_space X \<and> c \<in> quasi_components_of X
        \<Longrightarrow> openin X c"
oops
  REWRITE_TAC[quasi_components_of; IN_ELIM_THM] THEN
  MESON_TAC[OPEN_IN_QUASI_COMPONENT_OF_LOCALLY_CONNECTED_SPACE]);;

lemma quasi_eq_connected_components_of_alt:
   "quasi_components_of X = connected_components_of X \<longleftrightarrow>
        \<forall>c. c \<in> quasi_components_of X \<Longrightarrow> connectedin X c"
oops
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[CONNECTED_IN_CONNECTED_COMPONENTS_OF] THEN
  DISCH_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `c::A=>bool` THEN
  REWRITE_TAC[quasi_components_of; connected_components_of] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC id [FUN_EQ_THM] THEN X_GEN_TAC `x::A` THEN
  ASM_CASES_TAC `(x::A) \<in> topspace X` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[QUASI_EQ_CONNECTED_COMPONENT_OF_EQ] THEN
  ASM_SIMP_TAC[QUASI_COMPONENT_IN_QUASI_COMPONENTS_OF]);;

lemma connected_subset_quasi_components_of_pointwise:
   "connected_components_of X \<subseteq> quasi_components_of X \<longleftrightarrow>
        \<forall>x. x \<in> topspace X
            \<Longrightarrow> quasi_component_of X x = connected_component_of X x"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[quasi_components_of; connected_components_of] THEN EQ_TAC THENL
   [ALL_TAC; REWRITE_TAC[EXTENSION; \<subseteq>; IN_ELIM_THM] THEN MESON_TAC[]] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC(SET_RULE
   `(\<forall>x. x \<in> s \<Longrightarrow> x \<in> f x \<and> f x \<subseteq> g x) \<and>
    (\<forall>x y. x \<in> s \<and> y \<in> s \<Longrightarrow> g x = g y \<or> disjnt (g x) (g y))
    \<Longrightarrow> {f x | x \<in> s} \<subseteq> {g x | x \<in> s} \<Longrightarrow> \<forall>x. x \<in> s \<Longrightarrow> f x = g x`) THEN
  SIMP_TAC[QUASI_COMPONENT_OF_DISJOINT; QUASI_COMPONENT_OF_EQ] THEN
  SIMP_TAC[CONNECTED_COMPONENT_SUBSET_QUASI_COMPONENT_OF; EXCLUDED_MIDDLE] THEN
  REWRITE_TAC[\<in>; CONNECTED_COMPONENT_OF_REFL]);;

lemma quasi_subset_connected_components_of_pointwise:
   "quasi_components_of X \<subseteq> connected_components_of X \<longleftrightarrow>
        \<forall>x. x \<in> topspace X
            \<Longrightarrow> quasi_component_of X x = connected_component_of X x"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[quasi_components_of; connected_components_of] THEN EQ_TAC THENL
   [ALL_TAC; REWRITE_TAC[EXTENSION; \<subseteq>; IN_ELIM_THM] THEN MESON_TAC[]] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN MATCH_MP_TAC(SET_RULE
   `(\<forall>x. x \<in> s \<Longrightarrow> x \<in> f x \<and> f x \<subseteq> g x) \<and>
    (\<forall>x y. x \<in> s \<and> y \<in> s \<Longrightarrow> f x = f y \<or> disjnt (f x) (f y))
    \<Longrightarrow> {g x | x \<in> s} \<subseteq> {f x | x \<in> s} \<Longrightarrow> \<forall>x. x \<in> s \<Longrightarrow> f x = g x`) THEN
  SIMP_TAC[CONNECTED_COMPONENT_OF_DISJOINT; CONNECTED_COMPONENT_OF_EQ] THEN
  SIMP_TAC[CONNECTED_COMPONENT_SUBSET_QUASI_COMPONENT_OF; EXCLUDED_MIDDLE] THEN
  REWRITE_TAC[\<in>; CONNECTED_COMPONENT_OF_REFL]);;

lemma quasi_eq_connected_components_of_pointwise:
   "quasi_components_of X = connected_components_of X \<longleftrightarrow>
        \<forall>x. x \<in> topspace X
            \<Longrightarrow> quasi_component_of X x = connected_component_of X x"
oops
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[GSYM CONNECTED_SUBSET_QUASI_COMPONENTS_OF_POINTWISE; SUBSET_REFL];
    REWRITE_TAC[quasi_components_of; connected_components_of] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]]);;

lemma quasi_eq_connected_components_of_pointwise_alt:
   "quasi_components_of X = connected_components_of X \<longleftrightarrow>
        \<forall>x. quasi_component_of X x = connected_component_of X x"
oops
  GEN_TAC THEN REWRITE_TAC[QUASI_EQ_CONNECTED_COMPONENTS_OF_POINTWISE] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `x::A` THEN
  ASM_CASES_TAC `(x::A) \<in> topspace X` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_OF_EQ_EMPTY;
                QUASI_COMPONENT_OF_EQ_EMPTY]);;

lemma quasi_eq_connected_components_of_inclusion:
   "quasi_components_of X = connected_components_of X \<longleftrightarrow>
        connected_components_of X \<subseteq> quasi_components_of X \<or>
        quasi_components_of X \<subseteq> connected_components_of X"
oops
  REWRITE_TAC[CONNECTED_SUBSET_QUASI_COMPONENTS_OF_POINTWISE;
              QUASI_SUBSET_CONNECTED_COMPONENTS_OF_POINTWISE;
              QUASI_EQ_CONNECTED_COMPONENTS_OF_POINTWISE]);;

lemma quasi_eq_connected_components_of:
   "finite(connected_components_of X) \<or>
      finite(quasi_components_of X) \<or>
      locally_connected_space X \<or>
      compact_space X \<and>
      (Hausdorff_space X \<or> regular_space X \<or> normal_space X)
      \<Longrightarrow> quasi_components_of X = connected_components_of X"
oops
  REPEAT GEN_TAC THEN DISCH_THEN
   (REPEAT_TCL DISJ_CASES_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))
  THENL
   [REWRITE_TAC[QUASI_EQ_CONNECTED_COMPONENTS_OF_INCLUSION] THEN
    DISJ1_TAC THEN REWRITE_TAC[\<subseteq>] THEN
    ASM_MESON_TAC[OPEN_QUASI_EQ_CONNECTED_COMPONENTS_OF;
                  OPEN_IN_FINITE_CONNECTED_COMPONENTS];
    REWRITE_TAC[QUASI_EQ_CONNECTED_COMPONENTS_OF_INCLUSION] THEN
    DISJ2_TAC THEN REWRITE_TAC[\<subseteq>] THEN
    ASM_MESON_TAC[OPEN_QUASI_EQ_CONNECTED_COMPONENTS_OF;
                  OPEN_IN_FINITE_QUASI_COMPONENTS];
    REWRITE_TAC[EXTENSION] THEN
    ASM_MESON_TAC[OPEN_QUASI_EQ_CONNECTED_COMPONENTS_OF;
                  OPEN_IN_CONNECTED_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE;
                  OPEN_IN_QUASI_COMPONENTS_OF_LOCALLY_CONNECTED_SPACE];
    REWRITE_TAC[QUASI_EQ_CONNECTED_COMPONENTS_OF_ALT]] THEN
  X_GEN_TAC `c::A=>bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP QUASI_COMPONENTS_OF_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP CLOSED_IN_QUASI_COMPONENTS_OF) THEN
  ASM_REWRITE_TAC[connectedin; CONNECTED_SPACE_CLOSED_IN_EQ] THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_SUBTOPOLOGY; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s::A=>bool`; `t::A=>bool`] THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; GSYM disjnt] THEN STRIP_TAC THEN
  MP_TAC(fst(EQ_IMP_RULE(ISPEC `X::A topology` normal_space))) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[COMPACT_HAUSDORFF_OR_REGULAR_IMP_NORMAL_SPACE];
    DISCH_THEN(MP_TAC \<circ> SPECL [`s::A=>bool`; `t::A=>bool`])] THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u::A=>bool`; `v::A=>bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`X::A topology`; `c::A=>bool`; `topspace X - (u \<union> v):A=>bool`]
   SEPARATED_BETWEEN_QUASI_COMPONENT_COMPACT) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_UNION; CLOSED_IN_TOPSPACE];
    DISCH_THEN(MP_TAC \<circ> snd \<circ> EQ_IMP_RULE)] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[separated_between]] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e::A=>bool`; `g::A=>bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ>
   SPEC `g \<union> u::A=>bool` \<circ>
   MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] QUASI_COMPONENT_OF_CLOPEN_CASES)) THEN
  ASM_SIMP_TAC[OPEN_IN_UNION; NOT_IMP] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  SUBGOAL_THEN `g \<union> u::A=>bool = topspace X - (e \<inter> v)`
  SUBST1_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET)) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET)) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_DIFF THEN
    ASM_SIMP_TAC[CLOSED_IN_TOPSPACE; OPEN_IN_INTER]]);;

lemma quasi_eq_connected_component_of:
   "\<And>X (x::A).
      finite(connected_components_of X) \<or>
      finite(quasi_components_of X) \<or>
      locally_connected_space X \<or>
      compact_space X \<and>
      (Hausdorff_space X \<or> regular_space X \<or> normal_space X)
      \<Longrightarrow> quasi_component_of X x = connected_component_of X x"
oops
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC \<circ> MATCH_MP QUASI_EQ_CONNECTED_COMPONENTS_OF) THEN
  SIMP_TAC[QUASI_EQ_CONNECTED_COMPONENTS_OF_POINTWISE_ALT]);;


subsection\<open>Additional quasicomponent and continuum properties like Boundary Bumping\<close>


lemma cut_wire_fence_theorem_gen:
   "\<And>X s t::A=>bool.
        compact_space X \<and>
        (Hausdorff_space X \<or> regular_space X \<or> normal_space X) \<and>
        compactin X s \<and> closedin X t \<and>
        (\<forall>c. connectedin X c \<Longrightarrow> disjnt c s \<or> disjnt c t)
        \<Longrightarrow> separated_between X s t"
oops
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[SEPARATED_BETWEEN_POINTWISE_LEFT; CLOSED_IN_COMPACT_SPACE] THEN
  ASM_SIMP_TAC[SEPARATED_BETWEEN_POINTWISE_RIGHT; CLOSED_IN_COMPACT_SPACE] THEN
  ASM_SIMP_TAC[CLOSED_IN_SUBSET; SING_SUBSET] THEN
  X_GEN_TAC `x::A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x::A) \<in> topspace X` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; \<subseteq>]] THEN
  X_GEN_TAC `y::A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(y::A) \<in> topspace X` THENL
   [ASM_REWRITE_TAC[SEPARATED_BETWEEN_SINGS];
    ASM_MESON_TAC[CLOSED_IN_SUBSET; \<subseteq>]] THEN
  ASM_SIMP_TAC[QUASI_EQ_CONNECTED_COMPONENT_OF] THEN
  REWRITE_TAC[connected_component_of; NOT_EXISTS_THM] THEN
  X_GEN_TAC `c::A=>bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `c::A=>bool`) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

lemma cut_wire_fence_theorem:
   "\<And>X s t::A=>bool.
        compact_space X \<and> Hausdorff_space X \<and>
        closedin X s \<and> closedin X t \<and>
        (\<forall>c. connectedin X c \<Longrightarrow> disjnt c s \<or> disjnt c t)
        \<Longrightarrow> separated_between X s t"
oops
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CUT_WIRE_FENCE_THEOREM_GEN THEN
  ASM_SIMP_TAC[CLOSED_IN_COMPACT_SPACE]);;

lemma separated_between_from_closed_subtopology:
   "\<And>X s t c::A=>bool.
        separated_between (subtopology X c) s (X frontier_of c) \<and>
        separated_between (subtopology X c) s t
        \<Longrightarrow> separated_between X s t"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM SEPARATED_BETWEEN_UNION] THEN
  REWRITE_TAC[SEPARATED_BETWEEN] THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL
      [`X::A topology`; `topspace X \<inter> c::A=>bool`; `u::A=>bool`]
      CLOSED_IN_CLOSED_SUBTOPOLOGY) THEN
    ASM_REWRITE_TAC[GSYM SUBTOPOLOGY_RESTRICT] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    SIMP_TAC[GSYM FRONTIER_OF_SUBSET_EQ; INTER_SUBSET] THEN
    REWRITE_TAC[GSYM FRONTIER_OF_RESTRICT] THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`X::A topology`; `c::A=>bool`; `u::A=>bool`]
      OPEN_IN_SUBSET_TOPSPACE_EQ) THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

lemma separated_between_from_closed_subtopology_frontier:
   "\<And>X s t::A=>bool.
        separated_between (subtopology X t) s (X frontier_of t)
        \<Longrightarrow> separated_between X s (X frontier_of t)"
oops
  ASM_MESON_TAC[SEPARATED_BETWEEN_FROM_CLOSED_SUBTOPOLOGY]);;

lemma separated_between_from_frontier_of_closed_subtopology:
   "\<And>X s t::A=>bool.
        separated_between (subtopology X t) s (X frontier_of t)
        \<Longrightarrow> separated_between X s (topspace X - t)"
oops
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC id [CONJUNCT2 SEPARATED_BETWEEN_FRONTIER_OF_EQ] THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP SEPARATED_BETWEEN_IMP_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
    REWRITE_TAC[FRONTIER_OF_COMPLEMENT]] THEN
  MATCH_MP_TAC SEPARATED_BETWEEN_FROM_CLOSED_SUBTOPOLOGY_FRONTIER THEN
  ASM_REWRITE_TAC[]);;

lemma separated_between_compact_connected_component:
   "\<And>X c t::A=>bool.
        locally_compact_space X \<and> Hausdorff_space X \<and>
        c \<in> connected_components_of X \<and> compactin X c \<and>
        closedin X t \<and> disjnt c t
        \<Longrightarrow> separated_between X c t"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `\<exists>n l::A=>bool.
        openin X n \<and>
        compactin X l \<and>
        closedin X l \<and>
        c \<subseteq> n \<and> n \<subseteq> l \<and> l \<subseteq> topspace X - t`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `subtopology X (topspace X - t::A=>bool)`
        LOCALLY_COMPACT_SPACE_COMPACT_CLOSED_COMPACT) THEN
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; COMPACT_IN_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[LOCALLY_COMPACT_SPACE_OPEN_SUBSET; OPEN_IN_OPEN_SUBTOPOLOGY;
                 OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `c::A=>bool`) THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
      ASM SET_TAC[];
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`X::A topology`; `c::A=>bool`;
                 `topspace X - l::A=>bool`]
           (CONJUNCT2 SEPARATED_BETWEEN_FRONTIER_OF)) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(MP_TAC \<circ> fst \<circ> EQ_IMP_RULE)] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[separated_between] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET)) THEN
    ASM SET_TAC[]] THEN
  MATCH_MP_TAC SEPARATED_BETWEEN_FROM_CLOSED_SUBTOPOLOGY THEN
  EXISTS_TAC `l::A=>bool` THEN
  ASM_REWRITE_TAC[FRONTIER_OF_COMPLEMENT] THEN
  MATCH_MP_TAC CUT_WIRE_FENCE_THEOREM THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[FRONTIER_OF_SUBSET_CLOSED_IN; COMPACT_IN_IMP_CLOSED_IN] THEN
  REWRITE_TAC[CLOSED_IN_FRONTIER_OF; CONNECTED_IN_SUBTOPOLOGY] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `d::A=>bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X::A topology`; `d::A=>bool`; `c::A=>bool`]
        CONNECTED_COMPONENTS_OF_MAXIMAL) THEN
  ASM_REWRITE_TAC[TAUT `p \<or> q \<longleftrightarrow> \<not> p \<Longrightarrow> q`] THEN
  MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[frontier_of] THEN MATCH_MP_TAC(SET_RULE
   `c \<subseteq> v \<Longrightarrow> d \<subseteq> c \<Longrightarrow> disjnt d (u - v)`) THEN
  TRANS_TAC SUBSET_TRANS `n::A=>bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INTERIOR_OF_MAXIMAL]);;

lemma wilder_locally_compact_component_thm:
   "\<And>X c w::A=>bool.
        locally_compact_space X \<and> Hausdorff_space X \<and>
        c \<in> connected_components_of X \<and> compactin X c \<and>
        openin X w \<and> c \<subseteq> w
        \<Longrightarrow> \<exists>u v. openin X u \<and> openin X v \<and>
                  disjnt u v \<and> u \<union> v = topspace X \<and>
                  c \<subseteq> u \<and> u \<subseteq> w"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X::A topology`; `c::A=>bool`; `topspace X - w::A=>bool`]
        SEPARATED_BETWEEN_COMPACT_CONNECTED_COMPONENT) THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[separated_between]] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN ASM SET_TAC[]);;

lemma compact_quasi_eq_connected_components_of:
   "locally_compact_space X \<and> Hausdorff_space X \<and>
        compactin X c
        \<Longrightarrow> (c \<in> quasi_components_of X \<longleftrightarrow>
             c \<in> connected_components_of X)"
oops
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[quasi_components_of; connected_components_of] THEN
  MATCH_MP_TAC(SET_RULE
   `(\<forall>x. P x \<and> Q(g x) \<Longrightarrow> Q(f x)) \<and>
    (\<forall>x. P x \<and> Q(f x) \<Longrightarrow> f x = g x)
    \<Longrightarrow> \<forall>c. Q c \<Longrightarrow> (c \<in> {g x | P x} \<longleftrightarrow> c \<in> {f x | P x})`) THEN
  REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `x::A` THEN STRIP_TAC THENL
   [MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `quasi_component_of X (x::A)` THEN
    ASM_REWRITE_TAC[CLOSED_IN_CONNECTED_COMPONENT_OF;
                    CONNECTED_COMPONENT_SUBSET_QUASI_COMPONENT_OF];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[CONNECTED_COMPONENT_SUBSET_QUASI_COMPONENT_OF] THEN
  REWRITE_TAC[\<subseteq>] THEN X_GEN_TAC `y::A` THEN
  REWRITE_TAC[TAUT `p \<Longrightarrow> q \<longleftrightarrow> \<not> (p \<and> \<not> q)`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`X::A topology`; `connected_component_of X (x::A)`; `{y::A}`]
        SEPARATED_BETWEEN_COMPACT_CONNECTED_COMPONENT) THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_CONNECTED_COMPONENTS_OF] THEN
  ASM_REWRITE_TAC[NOT_IMP; DISJOINT_SING] THEN
  SUBGOAL_THEN `(y::A) \<in> topspace X` ASSUME_TAC THENL
   [ASM_MESON_TAC[\<subseteq>; QUASI_COMPONENT_OF_SUBSET_TOPSPACE];
    ASM_SIMP_TAC[CLOSED_IN_HAUSDORFF_SING]] THEN
  DISCH_THEN(MP_TAC \<circ> SPECL [`{x::A}`; `{y::A}`] \<circ> MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] SEPARATED_BETWEEN_MONO)) THEN
  ASM_REWRITE_TAC[SUBSET_REFL; SEPARATED_BETWEEN_SINGS; SING_SUBSET] THEN
  REWRITE_TAC[IN_SING] THEN REWRITE_TAC[\<in>] THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_OF_REFL] THEN ASM_MESON_TAC[\<in>]);;

lemma boundary_bumping_theorem_closed_gen:
   "\<And>X s c::A=>bool.
        connected_space X \<and>
        locally_compact_space X \<and>
        Hausdorff_space X \<and>
        closedin X s \<and>
        (s \<noteq> topspace X) \<and>
        compactin X c \<and>
        c \<in> connected_components_of(subtopology X s)
        \<Longrightarrow> \<not> (c \<inter> X frontier_of s = {})"
oops
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`subtopology X (s::A=>bool)`; `c::A=>bool`; `X frontier_of s::A=>bool`]
       SEPARATED_BETWEEN_COMPACT_CONNECTED_COMPONENT) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LOCALLY_COMPACT_SPACE_CLOSED_SUBSET THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY];
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
    SIMP_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER];
    ASM_SIMP_TAC[CLOSED_IN_CLOSED_SUBTOPOLOGY; CLOSED_IN_FRONTIER_OF] THEN
    ASM_SIMP_TAC[FRONTIER_OF_SUBSET_CLOSED_IN];
    ASM SET_TAC[];
    DISCH_THEN(MP_TAC \<circ> MATCH_MP
     SEPARATED_BETWEEN_FROM_CLOSED_SUBTOPOLOGY_FRONTIER)] THEN
  ASM_SIMP_TAC[CONNECTED_SPACE_IMP_SEPARATED_BETWEEN_TRIVIAL] THEN
  ASM_SIMP_TAC[CONNECTED_SPACE_FRONTIER_EQ_EMPTY; CLOSED_IN_SUBSET] THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP NONEMPTY_CONNECTED_COMPONENTS_OF) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP (SET_RULE `c \<in> s \<Longrightarrow> (s \<noteq> {})`)) THEN
  REWRITE_TAC[CONNECTED_COMPONENTS_OF_EQ_EMPTY; TOPSPACE_SUBTOPOLOGY] THEN
  SET_TAC[]);;

lemma boundary_bumping_theorem_closed:
   "\<And>X s c::A=>bool.
        connected_space X \<and> compact_space X \<and> Hausdorff_space X \<and>
        closedin X s \<and> (s \<noteq> topspace X) \<and>
        c \<in> connected_components_of(subtopology X s)
        \<Longrightarrow> \<not> (c \<inter> X frontier_of s = {})"
oops
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC BOUNDARY_BUMPING_THEOREM_CLOSED_GEN THEN
  ASM_SIMP_TAC[COMPACT_IMP_LOCALLY_COMPACT_SPACE] THEN
  MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP CLOSED_IN_CONNECTED_COMPONENTS_OF) THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_SUBTOPOLOGY]);;

lemma intermediate_continuum_exists:
   "\<And>X c u::A=>bool.
        connected_space X \<and>
        locally_compact_space X \<and>
        Hausdorff_space X \<and>
        compactin X c \<and> connectedin X c \<and>
        (c \<noteq> {}) \<and> (c \<noteq> topspace X) \<and>
        openin X u \<and> c \<subseteq> u
        \<Longrightarrow> \<exists>d. compactin X d \<and> connectedin X d \<and>
                c \<subset> d \<and> d \<subset> u"
oops
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP CONNECTED_IN_SUBSET_TOPSPACE) THEN
  SUBGOAL_THEN `\<exists>a::A. a \<in> topspace X \<and> (a \<notin> c)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `subtopology X (u DELETE (a::A))`
        LOCALLY_COMPACT_SPACE_COMPACT_CLOSED_COMPACT) THEN
  ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; COMPACT_IN_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[LOCALLY_COMPACT_SPACE_OPEN_SUBSET; OPEN_IN_OPEN_SUBTOPOLOGY;
               OPEN_IN_HAUSDORFF_DELETE; SUBSET_DELETE] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `c::A=>bool`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v::A=>bool`; `k::A=>bool`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`subtopology X (k::A=>bool)`; `c::A=>bool`]
        EXISTS_CONNECTED_COMPONENT_OF_SUPERSET) THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d::A=>bool` THEN
  STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CLOSED_IN_CONNECTED_COMPONENTS_OF) THEN
  DISCH_THEN(MP_TAC \<circ> MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] CLOSED_IN_COMPACT_SPACE)) THEN
  ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONNECTED_IN_CONNECTED_COMPONENTS_OF) THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[\<subset>] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ASM SET_TAC[];
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `u::A=>bool` \<circ>
        GEN_REWRITE_RULE id [CONNECTED_SPACE_CLOPEN_IN]) THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN] THEN ASM SET_TAC[]] THEN
  DISCH_THEN(SUBST_ALL_TAC \<circ> SYM) THEN
  MP_TAC(ISPECL [`X::A topology`; `k::A=>bool`; `c::A=>bool`]
        BOUNDARY_BUMPING_THEOREM_CLOSED_GEN) THEN
  ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN; NOT_IMP] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[frontier_of]] THEN
  MATCH_MP_TAC(SET_RULE `s \<subseteq> u \<Longrightarrow> s \<inter> (t - u) = {}`) THEN
  TRANS_TAC SUBSET_TRANS `v::A=>bool` THEN
  ASM_SIMP_TAC[INTERIOR_OF_MAXIMAL_EQ]);;

lemma boundary_bumping_theorem_gen:
   "\<And>X s c::A=>bool.
        connected_space X \<and>
        locally_compact_space X \<and>
        Hausdorff_space X \<and>
        s \<subset> topspace X \<and>
        c \<in> connected_components_of(subtopology X s) \<and>
        compactin X (X closure_of c)
        \<Longrightarrow> \<not> (X frontier_of c \<inter> X frontier_of s = {})"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[\<subset>] THEN STRIP_TAC THEN
  REWRITE_TAC[frontier_of] THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONNECTED_COMPONENTS_OF_SUBSET) THEN
  REWRITE_TAC[SUBSET_INTER; TOPSPACE_SUBTOPOLOGY] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CONNECTED_IN_CONNECTED_COMPONENTS_OF) THEN
  REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP NONEMPTY_CONNECTED_COMPONENTS_OF) THEN
  MATCH_MP_TAC(SET_RULE
   `i \<subseteq> i' \<and> c \<subseteq> c' \<and> \<not> (c \<subseteq> i')
    \<Longrightarrow> \<not> ((c - i) \<inter> (c' - i') = {})`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[INTERIOR_OF_MONO];
    ASM_MESON_TAC[CLOSURE_OF_MONO];
    DISCH_TAC] THEN
  SUBGOAL_THEN `X closure_of c::A=>bool = c` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_SIMP_TAC[CLOSURE_OF_SUBSET] THEN
    MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `subtopology X (s::A=>bool)`THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_CLOSURE_OF] THEN
      MP_TAC(ISPECL [`X::A topology`; `s::A=>bool`] INTERIOR_OF_SUBSET) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC(SET_RULE `c \<subseteq> d \<and> (c \<noteq> {}) \<Longrightarrow> \<not> disjnt c d`) THEN
      ASM_SIMP_TAC[CLOSURE_OF_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`X::A topology`; `c::A=>bool`; `X interior_of s::A=>bool`]
        INTERMEDIATE_CONTINUUM_EXISTS) THEN
  ASM_REWRITE_TAC[OPEN_IN_INTERIOR_OF; NOT_IMP] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d::A=>bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SET_RULE `(c::A=>bool) \<subset> d \<Longrightarrow> \<not> (d \<subseteq> c)`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONNECTED_COMPONENTS_OF_MAXIMAL THEN
  EXISTS_TAC `subtopology X (s::A=>bool)` THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY] THEN
  MP_TAC(ISPECL [`X::A topology`; `s::A=>bool`] INTERIOR_OF_SUBSET) THEN
  ASM SET_TAC[]);;

lemma boundary_bumping_theorem:
   "\<And>X s c::A=>bool.
        connected_space X \<and>
        compact_space X \<and>
        Hausdorff_space X \<and>
        s \<subset> topspace X \<and>
        c \<in> connected_components_of(subtopology X s)
        \<Longrightarrow> \<not> (X frontier_of c \<inter> X frontier_of s = {})"
oops
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC BOUNDARY_BUMPING_THEOREM_GEN THEN
  ASM_SIMP_TAC[COMPACT_IMP_LOCALLY_COMPACT_SPACE] THEN
  ASM_SIMP_TAC[CLOSED_IN_COMPACT_SPACE; CLOSED_IN_CLOSURE_OF]);;


lemma Hausdorff_space_mtopology:
   "Hausdorff_space mtopology"
oops
  REWRITE_TAC[Hausdorff_space; TOPSPACE_MTOPOLOGY] THEN
  MAP_EVERY X_GEN_TAC [`m::A metric`; `x::A`; `y::A`] THEN STRIP_TAC THEN
  EXISTS_TAC `mball m (x::A,d x y / 2)` THEN
  EXISTS_TAC `mball m (y::A,d x y / 2)` THEN
  REWRITE_TAC[SET_RULE `disjnt s t \<longleftrightarrow> \<forall>x. x \<in> s \<and> x \<in> t \<Longrightarrow> False`] THEN
  REWRITE_TAC[OPEN_IN_MBALL; IN_MBALL] THEN
  POP_ASSUM_LIST(MP_TAC \<circ> end_itlist CONJ) THEN CONV_TAC METRIC_ARITH);;

lemma t1_space_mtopology:
   "t1_space mtopology"
oops
  SIMP_TAC[HAUSDORFF_IMP_T1_SPACE; HAUSDORFF_SPACE_MTOPOLOGY]);;




(* k-spaces (with no Hausdorff-ness assumptions built in).                   *)


let k_space = new_definition
 `k_space (X::A topology) \<longleftrightarrow>
        \<forall>s. s \<subseteq> topspace X
            \<Longrightarrow> (closedin X s \<longleftrightarrow>
                 \<forall>k. compactin X k
                     \<Longrightarrow> closedin (subtopology X k) (k \<inter> s))`;;

lemma k_space:
   "k_space X \<longleftrightarrow>
        \<forall>s. s \<subseteq> topspace X \<and>
            (\<forall>k. compactin X k
                 \<Longrightarrow> closedin (subtopology X k) (k \<inter> s))
            \<Longrightarrow> closedin X s"
oops
  GEN_TAC THEN REWRITE_TAC[k_space] THEN
  MESON_TAC[CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED]);;

lemma k_space_open:
   "k_space X \<longleftrightarrow>
        \<forall>s. s \<subseteq> topspace X \<and>
            (\<forall>k. compactin X k
                 \<Longrightarrow> openin (subtopology X k) (k \<inter> s))
            \<Longrightarrow> openin X s"
oops
  GEN_TAC THEN REWRITE_TAC[K_SPACE] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `s::A=>bool` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC id [OPEN_IN_CLOSED_IN_EQ; closedin] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET_DIFF] THEN X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC id [OPEN_IN_CLOSED_IN_EQ; closedin] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  (CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `k::A=>bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

lemma k_space_alt:
   "k_space X \<longleftrightarrow>
        \<forall>s. s \<subseteq> topspace X
            \<Longrightarrow> (openin X s \<longleftrightarrow>
                 \<forall>k. compactin X k
                     \<Longrightarrow> openin (subtopology X k) (k \<inter> s))"
oops
  GEN_TAC THEN REWRITE_TAC[K_SPACE_OPEN] THEN
  MESON_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN]);;

lemma k_space_quotient_map_image:
   "\<And>X X' (q::A=>B).
        quotient_map X X' q \<and> k_space X \<Longrightarrow> k_space X'"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[K_SPACE] THEN
  STRIP_TAC THEN X_GEN_TAC `s::B=>bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> CONJUNCT2 \<circ> GEN_REWRITE_RULE id [QUOTIENT_MAP]) THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `s::B=>bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC \<circ> SYM) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SUBSET_RESTRICT] THEN
  X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `subtopology X k =
    subtopology
     (subtopology X {x \<in> topspace X. (q::A=>B) x \<in> q ` k}) k`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `k \<inter> {x \<in> topspace X. q x \<in> s} =
    k \<inter> {x. x \<in> topspace(subtopology X
                  {x \<in> topspace X. (q::A=>B) x \<in> q ` k}) \<and>
                 q x \<in> (image (q::A=>B) k \<inter> s)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED THEN
  MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
  EXISTS_TAC `subtopology X' (image (q::A=>B) k)` THEN CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    ASM_MESON_TAC[QUOTIENT_IMP_CONTINUOUS_MAP];
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    ASM_MESON_TAC[QUOTIENT_IMP_CONTINUOUS_MAP]]);;

lemma k_space_retraction_map_image:
   "\<And>X X' r.
        retraction_map X X' r \<and> k_space X \<Longrightarrow> k_space X'"
oops
  MESON_TAC[K_SPACE_QUOTIENT_MAP_IMAGE;
            RETRACTION_IMP_QUOTIENT_MAP]);;

lemma homeomorphic_k_space:
   "\<And>(X::A topology) (X':B topology).
      X homeomorphic_space X'
      \<Longrightarrow> (k_space X \<longleftrightarrow> k_space X')"
oops
  REWRITE_TAC[homeomorphic_space; HOMEOMORPHIC_MAPS_MAP] THEN
  REWRITE_TAC[GSYM SECTION_AND_RETRACTION_EQ_HOMEOMORPHIC_MAP] THEN
  MESON_TAC[K_SPACE_RETRACTION_MAP_IMAGE]);;

lemma k_space_perfect_map_image:
   "\<And>X X' f.
        k_space X \<and> perfect_map X X' f
        \<Longrightarrow> k_space X'"
oops
  MESON_TAC[PERFECT_IMP_QUOTIENT_MAP; K_SPACE_QUOTIENT_MAP_IMAGE]);;

lemma locally_compact_imp_k_space:
   "locally_compact_space X \<Longrightarrow> k_space X"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[K_SPACE] THEN
  X_GEN_TAC `s::A=>bool` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN
  GEN_REWRITE_TAC (LAND_CONV \<circ> RAND_CONV) [GSYM CLOSURE_OF_SUBSET_EQ] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[\<subseteq>; NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `x::A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x::A) \<in> topspace X` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSURE_OF_SUBSET_TOPSPACE; \<subseteq>]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [locally_compact_space]) THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `x::A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u::A=>bool` MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k::A=>bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `x::A` \<circ> REWRITE_RULE[\<subseteq>] \<circ> CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_INTER; CLOSURE_OF_SUBTOPOLOGY] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SET_RULE `k \<inter> k \<inter> s = s \<inter> k`; IN_CLOSURE_OF] THEN
  X_GEN_TAC `v::A=>bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [IN_CLOSURE_OF]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC \<circ> SPEC `u \<inter> v::A=>bool`) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[]);;

lemma compact_imp_k_space:
   "compact_space X \<Longrightarrow> k_space X"
oops
  MESON_TAC[LOCALLY_COMPACT_IMP_K_SPACE;
            COMPACT_IMP_LOCALLY_COMPACT_SPACE]);;

lemma k_space_discrete_topology:
   "\<And>u::A=>bool. k_space(discrete_topology u)"
oops
  SIMP_TAC[K_SPACE; CLOSED_IN_DISCRETE_TOPOLOGY;
           TOPSPACE_DISCRETE_TOPOLOGY]);;

lemma metrizable_imp_k_space:
   "metrizable_space X \<Longrightarrow> k_space X"
oops
  REWRITE_TAC[FORALL_METRIZABLE_SPACE] THEN X_GEN_TAC `m::A metric` THEN
  REWRITE_TAC[K_SPACE] THEN X_GEN_TAC `s::A=>bool` THEN
  REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[METRIC_CLOSED_IN_IFF_SEQUENTIALLY_CLOSED] THEN
  MAP_EVERY X_GEN_TAC [`a::num=>A`; `l::A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(l::A) insert image a UNIV`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_SEQUENCE_WITH_LIMIT THEN
    EXISTS_TAC `a::num=>A` THEN REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    ASM SET_TAC[];
    REWRITE_TAC[GSYM MTOPOLOGY_SUBMETRIC] THEN
    REWRITE_TAC[METRIC_CLOSED_IN_IFF_SEQUENTIALLY_CLOSED] THEN
    DISCH_THEN(MP_TAC \<circ> SPECL [`a::num=>A`; `l::A`] \<circ> CONJUNCT2) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[IN_INTER]] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LIMIT_SUBTOPOLOGY; MTOPOLOGY_SUBMETRIC] THEN
    REWRITE_TAC[IN_INSERT] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    REWRITE_TAC[] THEN SET_TAC[]]);;

lemma k_space_mtopology:
   "k_spacemtopology"
oops
  REWRITE_TAC[GSYM FORALL_METRIZABLE_SPACE; METRIZABLE_IMP_K_SPACE]);;

lemma k_space_euclideanreal:
 (`k_space euclideanreal"
oops
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC; K_SPACE_MTOPOLOGY]);;

lemma k_space_closed_subtopology:
   "k_space X \<and> closedin X s \<Longrightarrow> k_space(subtopology X s)"
oops
  MAP_EVERY X_GEN_TAC [`X::A topology`; `c::A=>bool`] THEN
  REWRITE_TAC[K_SPACE] THEN STRIP_TAC THEN
  X_GEN_TAC `s::A=>bool` THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER; COMPACT_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `k \<inter> c::A=>bool`) THEN
  REWRITE_TAC[INTER_SUBSET] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`subtopology X (k::A=>bool)`; `k \<inter> c::A=>bool`]
        CLOSED_IN_COMPACT_SPACE) THEN
    ASM_SIMP_TAC[CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED] THEN
    ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; COMPACT_IN_SUBTOPOLOGY];
    ASM_SIMP_TAC[SET_RULE `s \<subseteq> c \<Longrightarrow> (k \<inter> c) \<inter> s = k \<inter> s`;
                 SUBTOPOLOGY_SUBTOPOLOGY] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] CLOSED_IN_TRANS) THEN
    REWRITE_TAC[SET_RULE `c \<inter> k \<inter> c = k \<inter> c`] THEN
    ASM_SIMP_TAC[CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED]]);;

lemma k_space_subtopology:
   "(\<forall>t. t \<subseteq> topspace X \<and> t \<subseteq> s \<and>
             (\<forall>k. compactin X k
                  \<Longrightarrow> closedin (subtopology X (k \<inter> s)) (k \<inter> t))
             \<Longrightarrow> closedin (subtopology X s) t) \<and>
        (\<forall>k. compactin X k
             \<Longrightarrow> k_space(subtopology X (k \<inter> s)))
        \<Longrightarrow> k_space(subtopology X s)"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[K_SPACE] THEN
  X_GEN_TAC `u::A=>bool` THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER; COMPACT_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC \<circ>
    GEN_REWRITE_RULE RAND_CONV [K_SPACE] \<circ>
    SPEC `k::A=>bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `c::A=>bool`] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY; SUBSET_INTER] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC \<circ> SPEC `c::A=>bool`) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN
  ASM SET_TAC[]);;

lemma k_space_subtopology_open:
   "(\<forall>t. t \<subseteq> topspace X \<and> t \<subseteq> s \<and>
             (\<forall>k. compactin X k
                  \<Longrightarrow> openin (subtopology X (k \<inter> s)) (k \<inter> t))
             \<Longrightarrow> openin (subtopology X s) t) \<and>
        (\<forall>k. compactin X k
             \<Longrightarrow> k_space(subtopology X (k \<inter> s)))
        \<Longrightarrow> k_space(subtopology X s)"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[K_SPACE_OPEN] THEN
  X_GEN_TAC `u::A=>bool` THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER; COMPACT_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC \<circ>
    GEN_REWRITE_RULE RAND_CONV [K_SPACE_OPEN] \<circ>
    SPEC `k::A=>bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; X_GEN_TAC `c::A=>bool`] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY; SUBSET_INTER] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC \<circ> SPEC `c::A=>bool`) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL [AP_TERM_TAC; ALL_TAC] THEN
  ASM SET_TAC[]);;

lemma k_space_open_subtopology:
   "(kc_space X \<or> Hausdorff_space X \<or> regular_space X) \<and>
        k_space X \<and> openin X s
        \<Longrightarrow> k_space(subtopology X s)"
oops
  lemma lemma:
   "\<And>X (v::A=>bool).
          kc_space X \<and> compact_space X \<and> openin X v
          \<Longrightarrow> k_space(subtopology X v)"
oops
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[K_SPACE; TOPSPACE_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY;
                COMPACT_IN_SUBTOPOLOGY; SUBSET_INTER] THEN
    X_GEN_TAC `s::A=>bool` THEN
    SIMP_TAC[SET_RULE `k \<subseteq> v \<Longrightarrow> v \<inter> k = k`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "*")) THEN
    FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP OPEN_IN_SUBSET) THEN
    SUBGOAL_THEN
     `s::A=>bool = v \<inter> ((topspace X - v) \<union> s)` SUBST1_TAC
    THENL [ASM SET_TAC[]; MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED] THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN_GEN THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[compactin; UNION_SUBSET; SUBSET_DIFF] THEN
    X_GEN_TAC `U:(A=>bool)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `compactin X (topspace X - v::A=>bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
      ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE];
      REWRITE_TAC[compactin; SUBSET_DIFF]] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `U:(A=>bool)->bool`) THEN
    ASM_SIMP_TAC[SET_RULE `s \<subseteq> t \<Longrightarrow> (t - u) \<inter> s = s - u`] THEN
    DISCH_THEN(X_CHOOSE_THEN `V1:(A=>bool)->bool` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "*" (MP_TAC \<circ> SPEC `topspace X - \<Union> V1::A=>bool`) THEN
    SUBGOAL_THEN `openin X (\<Union> V1::A=>bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_UNIONS; \<subseteq>]; ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSED_IN_COMPACT_SPACE; CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE;
                 CLOSED_IN_CLOSED_SUBTOPOLOGY] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      CLOSED_IN_COMPACT_SPACE) \<circ> CONJUNCT1) THEN
    ASM_REWRITE_TAC[compactin] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `U:(A=>bool)->bool` \<circ> CONJUNCT2) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `V2:(A=>bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `V1 \<union> V2:(A=>bool)->bool` THEN
    ASM_REWRITE_TAC[FINITE_UNION] THEN ASM SET_TAC[])
in

  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC K_SPACE_SUBTOPOLOGY_OPEN THEN CONJ_TAC THENL
   [X_GEN_TAC `t::A=>bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC \<circ> GEN_REWRITE_RULE id
     [K_SPACE_OPEN]) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `k::A=>bool`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] OPEN_IN_TRANS) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN];
    X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MP_TAC(ISPECL [`subtopology X (k::A=>bool)`; `k \<inter> s::A=>bool`]
        lemma) THEN
      ASM_SIMP_TAC[KC_SPACE_SUBTOPOLOGY; OPEN_IN_SUBTOPOLOGY_INTER_OPEN] THEN
      ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY] THEN
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; INTER_ACI];
      MATCH_MP_TAC LOCALLY_COMPACT_IMP_K_SPACE THEN
      ONCE_REWRITE_TAC[SET_RULE `k \<inter> s = k \<inter> (k \<inter> s)`] THEN
      ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_SUBTOPOLOGY] THEN
      MATCH_MP_TAC LOCALLY_COMPACT_SPACE_OPEN_SUBSET THEN
      ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN] THEN
      ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY;
                   COMPACT_IMP_LOCALLY_COMPACT_SPACE] THEN
      ASM_MESON_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY;
                    REGULAR_SPACE_SUBTOPOLOGY]]]);;

lemma k_kc_space_subtopology:
   "k_space X \<and> kc_space X \<and>
        (openin X s \<or> closedin X s)
        \<Longrightarrow> k_space(subtopology X s) \<and> kc_space(subtopology X s)"
oops
  MESON_TAC[K_SPACE_OPEN_SUBTOPOLOGY; K_SPACE_CLOSED_SUBTOPOLOGY;
            KC_SPACE_SUBTOPOLOGY]);;

lemma k_space_as_quotient_explicit:
   "k_space X \<longleftrightarrow>
        quotient_map (sum_topology {k. compactin X k} (subtopology X),
                      X)
                     snd"
oops
  REWRITE_TAC[quotient_map; OPEN_IN_SUM_TOPOLOGY] THEN
  REWRITE_TAC[IN_ELIM_THM; TOPSPACE_SUM_TOPOLOGY; SUBSET_RESTRICT] THEN
  REWRITE_TAC[Sigma; IN_ELIM_PAIR_THM] THEN
  GEN_TAC THEN SIMP_TAC[K_SPACE_ALT; IN_ELIM_THM] THEN
  SIMP_TAC[o_THM; TOPSPACE_SUBTOPOLOGY_SUBSET; COMPACT_IN_SUBSET_TOPSPACE] THEN
  REWRITE_TAC[GSYM \<inter>] THEN MATCH_MP_TAC(TAUT
   `(p \<longleftrightarrow> p') \<and> q \<Longrightarrow> (p \<longleftrightarrow> q \<and> p')`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `image f {x,y | P x y} = {f(x,y) | P x y}`] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[\<subseteq>; FORALL_IN_GSPEC] THEN
  SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `x::A` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`{x::A}`; `x::A`] THEN
  ASM_REWRITE_TAC[COMPACT_IN_SING; IN_SING]);;

lemma k_space_as_quotient:
   "k_space X \<longleftrightarrow>
        ?q (X':((A=>bool)#A)topology).
                locally_compact_space X' \<and> quotient_map X' X q"
oops
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY EXISTS_TAC
     [`snd:(A=>bool)#A=>A`;
      `sum_topology {k::A=>bool | compactin X k} (subtopology X)`] THEN
    ASM_REWRITE_TAC[GSYM K_SPACE_AS_QUOTIENT_EXPLICIT] THEN
    REWRITE_TAC[LOCALLY_COMPACT_SPACE_SUM_TOPOLOGY; IN_ELIM_THM] THEN
    SIMP_TAC[COMPACT_IMP_LOCALLY_COMPACT_SPACE; COMPACT_SPACE_SUBTOPOLOGY];
    MESON_TAC[LOCALLY_COMPACT_IMP_K_SPACE; K_SPACE_QUOTIENT_MAP_IMAGE]]);;

lemma k_space_prod_topology_left:
   "\<And>(X::A topology) (X':B topology).
        locally_compact_space X \<and>
        (Hausdorff_space X \<or> regular_space X) \<and>
        k_space X'
        \<Longrightarrow> k_space(prod_topology X X')"
oops
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [K_SPACE_AS_QUOTIENT]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:(B=>bool)#B=>B`; `top'':((B=>bool)#B)topology`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`X::A topology`; `top'':((B=>bool)#B)topology`; `X':B topology`;
    `q:(B=>bool)#B=>B`] QUOTIENT_MAP_PROD_RIGHT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] K_SPACE_QUOTIENT_MAP_IMAGE) THEN
  MATCH_MP_TAC LOCALLY_COMPACT_IMP_K_SPACE THEN
  ASM_REWRITE_TAC[LOCALLY_COMPACT_SPACE_PROD_TOPOLOGY]);;

lemma k_space_prod_topology_right:
   "\<And>(X::A topology) (X':B topology).
        k_space X \<and>
        locally_compact_space X' \<and>
        (Hausdorff_space X' \<or> regular_space X')
        \<Longrightarrow> k_space(prod_topology X X')"
oops
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [K_SPACE_AS_QUOTIENT]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:(A=>bool)#A=>A`; `top'':((A=>bool)#A)topology`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`top'':((A=>bool)#A)topology`; `X::A topology`; `X':B topology`;
    `q:(A=>bool)#A=>A`] QUOTIENT_MAP_PROD_LEFT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] K_SPACE_QUOTIENT_MAP_IMAGE) THEN
  MATCH_MP_TAC LOCALLY_COMPACT_IMP_K_SPACE THEN
  ASM_REWRITE_TAC[LOCALLY_COMPACT_SPACE_PROD_TOPOLOGY]);;

lemma continuous_map_from_k_space:
   "\<And>X X' f.
        k_space X \<and>
        (\<forall>k. compactin X k \<Longrightarrow> continuous_map(subtopology X k,X') f)
        \<Longrightarrow> continuous_map X X' f"
oops
  REWRITE_TAC[K_SPACE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_MAP_CLOSED_IN] THEN
  MATCH_MP_TAC(TAUT `p \<and> (p \<Longrightarrow> q) \<Longrightarrow> p \<and> q`) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x::A` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> SPEC `{x::A}`)) THEN
    ASM_REWRITE_TAC[SING_SUBSET; COMPACT_IN_SING] THEN
    REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  X_GEN_TAC `c::B=>bool` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET_RESTRICT] THEN X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `k \<inter> {x \<in> topspace X. f x \<in> c} =
    {x. x \<in> topspace(subtopology X k) \<and> f x \<in> (f ` k \<inter> c)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
  EXISTS_TAC `subtopology X' (image f k)` THEN
  ASM_SIMP_TAC[CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED] THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  SET_TAC[]);;

lemma closed_map_into_k_space:
   "\<And>X X' f.
      k_space X' \<and>
      f ` (topspace X) \<subseteq> topspace X' \<and>
      (\<forall>k. compactin X' k
           \<Longrightarrow> closed_map(subtopology X {x \<in> topspace X. f x \<in> k},
                          subtopology X' k) f)
      \<Longrightarrow> closed_map X X' f"
oops
  REWRITE_TAC[K_SPACE] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[closed_map] THEN X_GEN_TAC `c::A=>bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET) THEN ASM SET_TAC[];
    X_GEN_TAC `k::B=>bool` THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `k \<inter> f ` c =
    image f ({x \<in> topspace X. f x \<in> k} \<inter> c)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `k::B=>bool`) THEN
  ASM_REWRITE_TAC[closed_map] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED]);;

lemma open_map_into_k_space:
   "\<And>X X' f.
      k_space X' \<and>
      f ` (topspace X) \<subseteq> topspace X' \<and>
      (\<forall>k. compactin X' k
           \<Longrightarrow> open_map(subtopology X {x \<in> topspace X. f x \<in> k},
                        subtopology X' k) f)
      \<Longrightarrow> open_map X X' f"
oops
  REWRITE_TAC[K_SPACE_OPEN] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[open_map] THEN X_GEN_TAC `c::A=>bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    X_GEN_TAC `k::B=>bool` THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `k \<inter> f ` c =
    image f ({x \<in> topspace X. f x \<in> k} \<inter> c)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `k::B=>bool`) THEN
  ASM_REWRITE_TAC[open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN]);;

lemma quotient_map_into_k_space:
   "\<And>X X' f.
     k_space X' \<and>
     continuous_map X X' f \<and>
     f ` (topspace X) = topspace X' \<and>
     (\<forall>k. compactin X' k
          \<Longrightarrow> quotient_map(subtopology X {x \<in> topspace X. f x \<in> k},
                           subtopology X' k) f)
     \<Longrightarrow> quotient_map X X' f"
oops
  REWRITE_TAC[K_SPACE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[QUOTIENT_MAP] THEN X_GEN_TAC `c::B=>bool` THEN DISCH_TAC THEN
  EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[CLOSED_IN_CONTINUOUS_MAP_PREIMAGE]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k::B=>bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `k::B=>bool`) THEN
  ASM_REWRITE_TAC[QUOTIENT_MAP; TOPSPACE_SUBTOPOLOGY; SUBSET_INTER] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `k \<inter> c::B=>bool` \<circ> CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC \<circ> SYM)] THEN
  REWRITE_TAC[SET_RULE
   `{x. x \<in> topspace X \<inter> {x \<in> topspace X. f x \<in> k} \<and>
         f x \<in> k \<inter> c} =
    {x \<in> topspace X. f x \<in> k} \<inter>
    {x \<in> topspace X. f x \<in> c}`] THEN
  ASM_SIMP_TAC[CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED]);;

lemma quotient_map_into_k_space_eq:
   "\<And>X X' f.
        k_space X' \<and> kc_space X'
        \<Longrightarrow> (quotient_map X X' f \<longleftrightarrow>
             continuous_map X X' f \<and>
             f ` (topspace X) = topspace X' \<and>
             \<forall>k. compactin X' k
                  \<Longrightarrow> quotient_map
                       (subtopology X {x \<in> topspace X. f x \<in> k},
                        subtopology X' k) f)"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_IMP_SURJECTIVE_MAP; QUOTIENT_IMP_CONTINUOUS_MAP] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC QUOTIENT_MAP_RESTRICTION THEN
    RULE_ASSUM_TAC(REWRITE_RULE[kc_space]) THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC QUOTIENT_MAP_INTO_K_SPACE THEN ASM_REWRITE_TAC[]]);;

lemma open_map_into_k_space_eq:
   "\<And>X X' f.
        k_space X'
        \<Longrightarrow> (open_map X X' f \<longleftrightarrow>
             f ` (topspace X) \<subseteq> topspace X' \<and>
             \<forall>k. compactin X' k
                  \<Longrightarrow> open_map
                       (subtopology X {x \<in> topspace X. f x \<in> k},
                        subtopology X' k) f)"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[OPEN_MAP_INTO_K_SPACE] THEN
  ASM_SIMP_TAC[OPEN_MAP_IMP_SUBSET_TOPSPACE] THEN
  ASM_SIMP_TAC[OPEN_MAP_RESTRICTION]);;

lemma closed_map_into_k_space_eq:
   "\<And>X X' f.
        k_space X'
        \<Longrightarrow> (closed_map X X' f \<longleftrightarrow>
             f ` (topspace X) \<subseteq> topspace X' \<and>
             \<forall>k. compactin X' k
                  \<Longrightarrow> closed_map
                       (subtopology X {x \<in> topspace X. f x \<in> k},
                        subtopology X' k) f)"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CLOSED_MAP_INTO_K_SPACE] THEN
  ASM_SIMP_TAC[CLOSED_MAP_IMP_SUBSET_TOPSPACE] THEN
  ASM_SIMP_TAC[CLOSED_MAP_RESTRICTION]);;

lemma proper_map_into_k_space:
   "\<And>X X' f.
      k_space X' \<and>
      f ` (topspace X) \<subseteq> topspace X' \<and>
      (\<forall>k. compactin X' k
           \<Longrightarrow> proper_map(subtopology X {x \<in> topspace X. f x \<in> k},
                          subtopology X' k) f)
      \<Longrightarrow> proper_map X X' f"
oops
  REWRITE_TAC[proper_map] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CLOSED_MAP_INTO_K_SPACE THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `{y::B}`) THEN
    ASM_REWRITE_TAC[COMPACT_IN_SING] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `y::B` \<circ> CONJUNCT2) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER; TOPSPACE_SUBTOPOLOGY; IN_SING] THEN
    REWRITE_TAC[TAUT  `(p \<and> p \<and> q) \<and> q \<longleftrightarrow> p \<and> q`] THEN
    SIMP_TAC[COMPACT_IN_SUBTOPOLOGY]]);;

lemma proper_map_into_k_space_eq:
   "\<And>X X' f.
        k_space X'
        \<Longrightarrow> (proper_map X X' f \<longleftrightarrow>
             f ` (topspace X) \<subseteq> topspace X' \<and>
             \<forall>k. compactin X' k
                  \<Longrightarrow> proper_map
                       (subtopology X {x \<in> topspace X. f x \<in> k},
                        subtopology X' k) f)"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PROPER_MAP_INTO_K_SPACE] THEN
  ASM_SIMP_TAC[PROPER_MAP_IMP_SUBSET_TOPSPACE] THEN
  ASM_SIMP_TAC[PROPER_MAP_RESTRICTION]);;

lemma compact_imp_proper_map:
   "\<And>X X' f.
        k_space X' \<and> kc_space X' \<and>
        f ` (topspace X) \<subseteq> topspace X' \<and>
        (continuous_map X X' f \<or> kc_space X) \<and>
        (\<forall>k. compactin X' k
             \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> k})
        \<Longrightarrow> proper_map X X' f"
oops
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
   COMPACT_IMP_PROPER_MAP_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC \<circ> REWRITE_RULE[K_SPACE]) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `k::B=>bool` THEN
  DISCH_TAC THEN MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN_GEN THEN
  ASM_SIMP_TAC[KC_SPACE_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY; INTER_SUBSET] THEN
  ASM_MESON_TAC[INTER_COMM]);;

lemma proper_eq_compact_map:
   "\<And>X X' f.
        k_space X' \<and> kc_space X' \<and>
        (continuous_map X X' f \<or> kc_space X)
        \<Longrightarrow> (proper_map X X' f \<longleftrightarrow>
             f ` (topspace X) \<subseteq> topspace X' \<and>
             \<forall>k. compactin X' k
                 \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> k})"
oops
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [SIMP_TAC[PROPER_MAP_IMP_SUBSET_TOPSPACE] THEN
    SIMP_TAC[PROPER_MAP_ALT];
    STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_PROPER_MAP THEN
    ASM_REWRITE_TAC[]]);;

lemma compact_imp_perfect_map:
   "\<And>X X' f.
        k_space X' \<and> kc_space X' \<and>
        continuous_map X X' f \<and> f ` (topspace X) = topspace X' \<and>
        (\<forall>k. compactin X' k
             \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> k})
        \<Longrightarrow> perfect_map X X' f"
oops
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[perfect_map] THEN
  FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
  MATCH_MP_TAC COMPACT_IMP_PROPER_MAP THEN ASM_REWRITE_TAC[]);;


subsection\<open>More generally, the k-ification functor\<close>


let kification = define
 `kification (X::A topology) =
        topology {s. s \<subseteq> topspace X \<and>
                      \<forall>k. compactin X k
                           \<Longrightarrow> openin (subtopology X k) (k \<inter> s)}`;;

lemma openin_kification:
   "\<And>X (u::A=>bool).
        openin (kification X) u \<longleftrightarrow>
        u \<subseteq> topspace X \<and>
        \<forall>k. compactin X k  \<Longrightarrow> openin (subtopology X k) (k \<inter> u)"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[kification] THEN
  W(MP_TAC \<circ> fst \<circ> EQ_IMP_RULE \<circ>
      PART_MATCH (lhand \<circ> rand) (CONJUNCT2 topology_tybij) \<circ>
        rator \<circ> lhand \<circ> snd) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[IN_ELIM_THM]] THEN
  REWRITE_TAC[istopology; IN_ELIM_THM; INTER_EMPTY; EMPTY_SUBSET] THEN
  SIMP_TAC[OPEN_IN_EMPTY; UNIONS_SUBSET; INTER_UNIONS] THEN CONJ_TAC THEN
  (REPEAT STRIP_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THENL
   [ONCE_REWRITE_TAC[SET_RULE
     `k \<inter> s \<inter> t = (k \<inter> s) \<inter> (k \<inter> t)`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER];
    MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    ASM SET_TAC[]]);;

lemma openin_kification_finer:
   "\<And>X (s::A=>bool).
        openin X s \<Longrightarrow> openin (kification X) s"
oops
  SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN;
           OPEN_IN_KIFICATION; OPEN_IN_SUBSET]);;

lemma topspace_kification:
   "topspace(kification X) = topspace X"
oops
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [topspace] THEN
  MATCH_MP_TAC(SET_RULE
   `s \<in> u \<and> (\<forall>t. t \<in> u \<Longrightarrow> t \<subseteq> s) \<Longrightarrow> \<Union> u = s`) THEN
  SIMP_TAC[IN_ELIM_THM; OPEN_IN_KIFICATION; SUBSET_REFL] THEN
  SIMP_TAC[COMPACT_IN_SUBSET_TOPSPACE; OPEN_IN_SUBTOPOLOGY_REFL;
           SET_RULE `s \<subseteq> u \<Longrightarrow> s \<inter> u = s`]);;

lemma closedin_kification:
   "\<And>X (u::A=>bool).
        closedin (kification X) u \<longleftrightarrow>
        u \<subseteq> topspace X \<and>
        \<forall>k. compactin X k  \<Longrightarrow> closedin (subtopology X k) (k \<inter> u)"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[closedin; TOPSPACE_KIFICATION] THEN
  ASM_CASES_TAC `(u::A=>bool) \<subseteq> topspace X` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[OPEN_IN_KIFICATION; TOPSPACE_SUBTOPOLOGY; SUBSET_DIFF] THEN
  ASM_SIMP_TAC[SET_RULE `u \<subseteq> v \<Longrightarrow> k \<inter> u \<subseteq> v \<inter> k`] THEN
  REWRITE_TAC[SET_RULE `u \<inter> k - k \<inter> s = k \<inter> (u - s)`]);;

lemma closedin_kification_finer:
   "\<And>X (s::A=>bool).
        closedin X s \<Longrightarrow> closedin (kification X) s"
oops
  SIMP_TAC[CLOSED_IN_SUBTOPOLOGY_INTER_CLOSED;
           CLOSED_IN_KIFICATION; CLOSED_IN_SUBSET]);;

lemma kification_eq_self:
   "kification X = X \<longleftrightarrow> k_space X"
oops
  REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_KIFICATION; K_SPACE_ALT] THEN
  MESON_TAC[OPEN_IN_SUBSET]);;

lemma compact_in_kification:
   "\<And>X (k::A=>bool).
        compactin (kification X) k \<longleftrightarrow> compactin X k"
oops
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[COMPACT_IN_CONTRACTIVE; OPEN_IN_KIFICATION_FINER;
              TOPSPACE_KIFICATION];
    DISCH_TAC THEN REWRITE_TAC[compactin]] THEN
  ASM_SIMP_TAC[TOPSPACE_KIFICATION; COMPACT_IN_SUBSET_TOPSPACE] THEN
  X_GEN_TAC `U:(A=>bool)->bool` THEN REWRITE_TAC[OPEN_IN_KIFICATION] THEN
  REWRITE_TAC[RIGHT_AND_FORALL_THM; RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `k::A=>bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [COMPACT_IN_SUBSPACE]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[COMPACT_SPACE] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `image (\<lambda>u::A=>bool. k \<inter> u) U`) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_FINITE_SUBSET_IMAGE] THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET] THEN
  REWRITE_TAC[GSYM SIMPLE_IMAGE; GSYM INTER_UNIONS] THEN
  ASM_REWRITE_TAC[SET_RULE `k \<inter> u = k \<longleftrightarrow> k \<subseteq> u`]);;

lemma compact_space_kification:
   "compact_space(kification X) \<longleftrightarrow> compact_space X"
oops
  REWRITE_TAC[compact_space; COMPACT_IN_KIFICATION; TOPSPACE_KIFICATION]);;

lemma kification_kification:
   "kification(kification X) = kification X"
oops
  REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_KIFICATION; TOPSPACE_KIFICATION;
              COMPACT_IN_KIFICATION] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[OPEN_IN_KIFICATION_FINER]] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `k::A=>bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t::A=>bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [OPEN_IN_KIFICATION]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC \<circ> SPEC `k::A=>bool`)) THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

lemma k_space_kification:
   "k_space(kification X)"
oops
  REWRITE_TAC[GSYM KIFICATION_EQ_SELF; KIFICATION_KIFICATION]);;

lemma continuous_map_into_kification:
   "\<And>X X' f.
        k_space X
        \<Longrightarrow> (continuous_map X (kification X') f \<longleftrightarrow>
             continuous_map X X' f)"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[continuous_map; TOPSPACE_KIFICATION] THEN
  EQ_TAC THEN SIMP_TAC[OPEN_IN_KIFICATION_FINER] THEN
  STRIP_TAC THEN X_GEN_TAC `v::B=>bool` THEN
  REWRITE_TAC[OPEN_IN_KIFICATION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
    [GSYM(REWRITE_RULE[GSYM KIFICATION_EQ_SELF] th)]) THEN
  REWRITE_TAC[OPEN_IN_KIFICATION; SUBSET_RESTRICT] THEN
  X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
  REMOVE_THEN "*" (MP_TAC \<circ> SPEC `image f k`) THEN ANTS_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `X::A topology` THEN
    ASM_REWRITE_TAC[continuous_map];
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `u::B=>bool` THEN STRIP_TAC THEN
  EXISTS_TAC `{x \<in> topspace X. f x \<in> u}` THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

lemma continuous_map_from_kification:
   "\<And>X X' f.
        continuous_map X X' f \<Longrightarrow> continuous_map(kification X,X') f"
oops
  REWRITE_TAC[continuous_map; TOPSPACE_KIFICATION] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[OPEN_IN_KIFICATION_FINER]);;

lemma continuous_map_kification:
   "\<And>X X' f.
        continuous_map X X' f
        \<Longrightarrow> continuous_map(kification X,kification X') f"
oops
  SIMP_TAC[CONTINUOUS_MAP_INTO_KIFICATION; K_SPACE_KIFICATION] THEN
  REWRITE_TAC[CONTINUOUS_MAP_FROM_KIFICATION]);;

lemma subtopology_kification_compact:
   "\<And>X (k::A=>bool).
        compactin X k
        \<Longrightarrow> subtopology (kification X) k = subtopology X k"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_SUBTOPOLOGY] THEN
  X_GEN_TAC `u::A=>bool` THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[OPEN_IN_KIFICATION_FINER]] THEN
  REWRITE_TAC[OPEN_IN_KIFICATION] THEN
  DISCH_THEN(X_CHOOSE_THEN `t::A=>bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `k::A=>bool`) THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  MESON_TAC[INTER_COMM]);;

lemma subtopology_kification_finer:
   "\<And>X (s::A=>bool) u.
        openin (subtopology (kification X) s) u
        \<Longrightarrow> openin (kification (subtopology X s)) u"
oops
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_ALT; FORALL_IN_GSPEC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[OPEN_IN_KIFICATION; TOPSPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `k::A=>bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `k::A=>bool`) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  SET_TAC[]);;

lemma proper_map_from_kification:
   "\<And>X X' f.
        k_space X'
        \<Longrightarrow> (proper_map(kification X,X') f \<longleftrightarrow>
             proper_map X X' f)"
oops
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PROPER_MAP_INTO_K_SPACE_EQ] THEN
  REWRITE_TAC[TOPSPACE_KIFICATION; PROPER_MAP_ALT] THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_KIFICATION;
              TOPSPACE_SUBTOPOLOGY; IN_ELIM_THM; IN_INTER;
              TOPSPACE_KIFICATION] THEN
  MATCH_MP_TAC(MESON[]
   `(P \<and> (\<forall>k. Q k \<Longrightarrow> S k) \<Longrightarrow> (\<forall>k. Q k \<Longrightarrow> (R k \<longleftrightarrow> R' k)))
    \<Longrightarrow> (P \<and> (\<forall>k. Q k \<Longrightarrow> R k \<and> S k) \<longleftrightarrow>
         P \<and> (\<forall>k. Q k \<Longrightarrow> R' k \<and> S k))`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC \<circ> MATCH_MP (MESON[]
   `(\<forall>x. P x \<Longrightarrow> (\<forall>y. P y \<and> Q x y \<Longrightarrow> R x y))
    \<Longrightarrow> (\<forall>x. P x \<and> Q x x \<Longrightarrow> R x x)`))) THEN
  REWRITE_TAC[TAUT `(p \<and> p \<and> q) \<and> q \<longleftrightarrow> p \<and> q`; SUBSET_REFL] THEN
  SIMP_TAC[SUBTOPOLOGY_KIFICATION_COMPACT]);;

lemma perfect_map_from_kification:
   "\<And>X X' f.
        k_space X' \<and> perfect_map X X' f
        \<Longrightarrow> perfect_map(kification X,X') f"
oops
  SIMP_TAC[perfect_map; PROPER_MAP_FROM_KIFICATION;
           CONTINUOUS_MAP_FROM_KIFICATION; TOPSPACE_KIFICATION]);;

lemma k_space_perfect_map_image_eq:
   "\<And>X X' f.
     Hausdorff_space X \<and> perfect_map X X' f
     \<Longrightarrow> (k_space X \<longleftrightarrow> k_space X')"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[K_SPACE_PERFECT_MAP_IMAGE]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`kification X::A topology`; `X::A topology`]
        HOMEOMORPHIC_K_SPACE) THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_SPACE; K_SPACE_KIFICATION] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `\<lambda>x::A. x` THEN
  REWRITE_TAC[HOMEOMORPHIC_EQ_INJECTIVE_PERFECT_MAP] THEN
  MP_TAC(ISPECL
   [`kification X::A topology`; `X::A topology`; `X':B topology`;
    `\<lambda>x::A. x`; `f::A=>B`] PERFECT_MAP_FROM_COMPOSITION_RIGHT) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[o_DEF; ETA_AX; IMAGE_ID; TOPSPACE_KIFICATION] THEN
  ASM_SIMP_TAC[PERFECT_MAP_FROM_KIFICATION] THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_KIFICATION; CONTINUOUS_MAP_ID] THEN
  ASM_SIMP_TAC[PERFECT_IMP_CONTINUOUS_MAP]);;


subsection\<open>One-point compactifications and the Alexandroff extension construction\<close>


lemma one_point_compactification_dense:
   "compact_space X \<and> \<not> compactin X (topspace X - {a})
        \<Longrightarrow> X closure_of (topspace X - {a}) = topspace X"
oops
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a::A) \<in> topspace X` THENL
   [STRIP_TAC;
    ASM_MESON_TAC[compact_space; SET_RULE `(a \<notin> s) \<Longrightarrow> s - {a} = s`]] THEN
  MATCH_MP_TAC(SET_RULE
   `u - {a} \<subseteq> s \<and> s \<subseteq> u \<and> (s \<noteq> u - {a}) \<Longrightarrow> s = u`) THEN
  REWRITE_TAC[CLOSURE_OF_EQ; CLOSURE_OF_SUBSET_TOPSPACE] THEN
  ASM_SIMP_TAC[CLOSURE_OF_SUBSET; DELETE_SUBSET] THEN
  ASM_MESON_TAC[CLOSED_IN_COMPACT_SPACE]);;

lemma one_point_compactification_interior:
   "compact_space X \<and> \<not> compactin X (topspace X - {a})
        \<Longrightarrow> X interior_of {a} = {}"
oops
  REWRITE_TAC[INTERIOR_OF_CLOSURE_OF; SET_RULE `s - {a} = s - {a}`] THEN
  SIMP_TAC[ONE_POINT_COMPACTIFICATION_DENSE; DIFF_EQ_EMPTY]);;

lemma kc_space_one_point_compactification_gen:
   "compact_space X
        \<Longrightarrow> (kc_space X \<longleftrightarrow>
             openin X (topspace X - {a}) \<and>
             (\<forall>k. compactin X k \<and> (a \<notin> k) \<Longrightarrow> closedin X k) \<and>
             k_space (subtopology X (topspace X - {a})) \<and>
             kc_space (subtopology X (topspace X - {a})))"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[T1_SPACE_OPEN_IN_DELETE_ALT; KC_IMP_T1_SPACE;
                    OPEN_IN_TOPSPACE];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[kc_space]; ALL_TAC] THEN
    MATCH_MP_TAC K_KC_SPACE_SUBTOPOLOGY THEN
    ASM_SIMP_TAC[COMPACT_IMP_K_SPACE] THEN DISJ1_TAC THEN
    ASM_MESON_TAC[T1_SPACE_OPEN_IN_DELETE_ALT; KC_IMP_T1_SPACE;
                  OPEN_IN_TOPSPACE];
    STRIP_TAC] THEN
  REWRITE_TAC[kc_space] THEN X_GEN_TAC `s::A=>bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(a::A) \<in> s` THEN ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
  ASM_REWRITE_TAC[closedin] THEN
  SUBGOAL_THEN
   `topspace X - s::A=>bool =
    (topspace X - {a}) - (s - {a})`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
  EXISTS_TAC `topspace X DELETE (a::A)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_DIFF THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY; SUBSET_REFL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC \<circ> GEN_REWRITE_RULE id [K_SPACE]) THEN
  REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY;
              TOPSPACE_SUBTOPOLOGY; SUBSET_INTER; SUBSET_DELETE] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `k::A=>bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_IN_SUBSET_TOPSPACE THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_SIMP_TAC[SET_RULE `(a \<notin> k) \<Longrightarrow> k \<inter> s - {a} = k \<inter> s`] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC CLOSED_INTER_COMPACT_IN THEN ASM_SIMP_TAC[]);;

let alexandroff_compactification = new_definition
 `alexandroff_compactification (X::A topology) =
        topology ({ INL ` u | openin X u} \<union>
                  { INR () insert image INL (topspace X - c) | c |
                    compactin X c \<and> closedin X c})`;;

lemma openin_alexandroff_compactification:
   "\<And>(X::A topology) v.
        openin(alexandroff_compactification X) v \<longleftrightarrow>
        (\<exists>u. openin X u \<and> v = INL ` u) \<or>
        (\<exists>c. compactin X c \<and> closedin X c \<and>
             v = INR () insert image INL (topspace X - c))"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[alexandroff_compactification] THEN
  W(MP_TAC \<circ> fst \<circ> EQ_IMP_RULE \<circ>
    PART_MATCH (lhand \<circ> rand) (CONJUNCT2 topology_tybij) \<circ>
    rator \<circ> lhand \<circ> snd) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN SUBST1_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM \<in>] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]] THEN
  REWRITE_TAC[istopology] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ1_TAC THEN
    REWRITE_TAC[SET_RULE `P \<and> {} = f ` s \<longleftrightarrow> s = {} \<and> P`] THEN
    REWRITE_TAC[UNWIND_THM2; OPEN_IN_EMPTY];
    MATCH_MP_TAC(SET_RULE
     `(\<forall>x y. R x y \<Longrightarrow> R y x) \<and>
      (\<forall>x y. x \<in> s \<and> y \<in> s \<Longrightarrow> R x y) \<and>
      (\<forall>x y. x \<in> s \<and> y \<in> t \<Longrightarrow> R x y) \<and>
      (\<forall>x y. x \<in> t \<and> y \<in> t \<Longrightarrow> R x y)
      \<Longrightarrow> \<forall>x y. x \<in> (s \<union> t) \<and> y \<in> (s \<union> t) \<Longrightarrow> R x y`) THEN
    CONJ_TAC THENL [MESON_TAC[INTER_COMM]; ALL_TAC] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `u::A=>bool` THEN DISCH_TAC THEN
      X_GEN_TAC `v::A=>bool` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ1_TAC THEN
      EXISTS_TAC `u \<inter> v::A=>bool` THEN
      ASM_SIMP_TAC[OPEN_IN_INTER] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC IMAGE_INTER_INJ THEN REWRITE_TAC[sum_INJECTIVE];
      X_GEN_TAC `u::A=>bool` THEN DISCH_TAC THEN
      X_GEN_TAC `c::A=>bool` THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ1_TAC THEN
      EXISTS_TAC `u - c::A=>bool` THEN ASM_SIMP_TAC[OPEN_IN_DIFF] THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_INSERT] THEN
      MATCH_MP_TAC sum_INDUCT THEN
      REWRITE_TAC[IN_DIFF; sum_DISTINCT; sum_INJECTIVE; UNWIND_THM1] THEN
      ASM_MESON_TAC[\<subseteq>; OPEN_IN_SUBSET];
      X_GEN_TAC `c::A=>bool` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `d::A=>bool` THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISJ2_TAC THEN
      EXISTS_TAC `c \<union> d::A=>bool` THEN
      ASM_SIMP_TAC[CLOSED_IN_UNION; COMPACT_IN_UNION] THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_INSERT; IN_UNION] THEN
      MATCH_MP_TAC sum_INDUCT THEN
      REWRITE_TAC[IN_DIFF; sum_DISTINCT; sum_INJECTIVE; UNWIND_THM1] THEN
      SET_TAC[]];
    REWRITE_TAC[FORALL_SUBSET_UNION] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_SUBSET_IMAGE] THEN
    REWRITE_TAC[SET_RULE `s \<subseteq> {x. P x} \<longleftrightarrow> \<forall>x. x \<in> s \<Longrightarrow> P x`] THEN
    X_GEN_TAC `uu:(A=>bool)->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `cc:(A=>bool)->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `cc:(A=>bool)->bool = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; UNION_EMPTY] THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE] THEN DISJ1_TAC THEN
      EXISTS_TAC `\<Union> uu::A=>bool` THEN
      ASM_SIMP_TAC[IN_ELIM_THM; OPEN_IN_UNIONS] THEN
      REWRITE_TAC[UNIONS_IMAGE] THEN SET_TAC[];
      REWRITE_TAC[IN_UNION; IN_IMAGE] THEN DISJ2_TAC THEN EXISTS_TAC
       `\<Inter>(cc \<union> image (\<lambda>u. topspace X - u) uu):A=>bool` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[EXTENSION] THEN MATCH_MP_TAC sum_INDUCT THEN
        REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_INTERS; IN_INSERT;
                    IN_UNIONS; IN_UNION; IN_UNIV] THEN
        REWRITE_TAC[sum_DISTINCT; sum_INJECTIVE] THEN
        REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM1] THEN
        REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
        ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
        REWRITE_TAC[IN_IMAGE; IN_UNIV; IN_DIFF; IN_INSERT] THEN
        REWRITE_TAC[sum_DISTINCT; sum_INJECTIVE] THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        REWRITE_TAC[TAUT `p \<or> q \<Longrightarrow> r \<longleftrightarrow> (p \<Longrightarrow> r) \<and> (q \<Longrightarrow> r)`] THEN
        X_GEN_TAC `a::A` THEN REWRITE_TAC[FORALL_AND_THM; UNWIND_THM1] THEN
        ASM_CASES_TAC `(a::A) \<in> topspace X` THEN ASM_REWRITE_TAC[] THENL
         [ALL_TAC; ASM_MESON_TAC[\<subseteq>; OPEN_IN_SUBSET]] THEN
        ONCE_REWRITE_TAC[TAUT `\<not> (p \<and> q) \<longleftrightarrow> \<not> q \<or> \<not> p`] THEN
        BINOP_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
        REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_AND_EXISTS_THM] THEN
        ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
        REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; IN_DIFF] THEN
        ASM_MESON_TAC[\<subseteq>; OPEN_IN_SUBSET];
        FIRST_X_ASSUM(X_CHOOSE_TAC `c::A=>bool` \<circ>
          REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
        SUBGOAL_THEN `cc = (c::A=>bool) insert cc` SUBST1_TAC THENL
         [ASM SET_TAC[];
          REWRITE_TAC[INTERS_INSERT; SET_RULE
           `(insert x s) \<union> t = x insert (s \<union> t)`]] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC
         (MESON[CLOSED_IN_INTER; COMPACT_INTER_CLOSED_IN]
           `closedin X c \<and> compactin X c \<and> closedin X d
            \<Longrightarrow> compactin X (c \<inter> d) \<and> closedin X (c \<inter> d)`) THEN
        ASM_SIMP_TAC[] THEN MATCH_MP_TAC CLOSED_IN_INTERS THEN
        CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[FORALL_IN_UNION]] THEN
        ASM_SIMP_TAC[FORALL_IN_IMAGE; CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE]]]]);;

lemma topspace_alexandroff_compactification:
   "topspace(alexandroff_compactification X) =
        INR () insert image INL (topspace X)"
oops
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [topspace] THEN MATCH_MP_TAC(SET_RULE
   `u \<in> s \<and> (\<forall>c. c \<in> s \<Longrightarrow> c \<subseteq> u) \<Longrightarrow> \<Union> s = u`) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; OPEN_IN_ALEXANDROFF_COMPACTIFICATION] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [MESON_TAC[COMPACT_IN_EMPTY; CLOSED_IN_EMPTY; DIFF_EMPTY]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET)) THEN SET_TAC[]);;

lemma closedin_alexandroff_compactification:
   "\<And>(X::A topology) c.
        closedin (alexandroff_compactification X) c \<longleftrightarrow>
        (\<exists>k. compactin X k \<and> closedin X k \<and> c = INL ` k) \<or>
        (\<exists>u. openin X u \<and>
             c = topspace(alexandroff_compactification X) - INL ` u)"
oops
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [closedin] THEN
  REWRITE_TAC[OPEN_IN_ALEXANDROFF_COMPACTIFICATION] THEN
  MATCH_MP_TAC(TAUT
   `(q' \<Longrightarrow> p) \<and> (r' \<Longrightarrow> p) \<and> (p \<Longrightarrow> (q \<longleftrightarrow> q') \<and> (r \<longleftrightarrow> r'))
    \<Longrightarrow> (p \<and> (q \<or> r) \<longleftrightarrow> r' \<or> q')`) THEN
  REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[closedin] THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
  X_GEN_TAC `s::A=>bool` THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC(TAUT `(p \<Longrightarrow> (q \<longleftrightarrow> r)) \<Longrightarrow> (p \<and> q \<longleftrightarrow> p \<and> r)`) THEN
         DISCH_TAC)
  THENL
   [FIRST_X_ASSUM(ASSUME_TAC \<circ> MATCH_MP OPEN_IN_SUBSET);
    FIRST_X_ASSUM(ASSUME_TAC \<circ> MATCH_MP CLOSED_IN_SUBSET)] THEN
  REWRITE_TAC[EXTENSION; FORALL_SUM_THM; FORALL_ONE_THM] THEN
  REWRITE_TAC[IN_INSERT; IN_DIFF; IN_IMAGE] THEN
  REWRITE_TAC[sum_DISTINCT; sum_INJECTIVE; UNWIND_THM1] THEN
  MP_TAC(INST_TYPE [`:1`,`:B`] sum_DISTINCT) THEN
  MP_TAC(INST_TYPE [`:1`,`:B`] sum_INJECTIVE) THEN
  ASM SET_TAC[]);;

lemma closedin_alexandroff_compactification_image_inl:
   "\<And>(X::A topology) k.
        closedin (alexandroff_compactification X) (INL ` k) \<longleftrightarrow>
        compactin X k \<and> closedin X k"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_ALEXANDROFF_COMPACTIFICATION] THEN
  REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION] THEN
  MATCH_MP_TAC(TAUT `(p' \<longleftrightarrow> p) \<and> \<not> q \<Longrightarrow> (p \<or> q \<longleftrightarrow> p')`) THEN
  SIMP_TAC[MATCH_MP (SET_RULE
   `(\<forall>x y. f x = f y \<longleftrightarrow> x = y) \<Longrightarrow> (f ` s = f ` t \<longleftrightarrow> s = t)`)
   (CONJUNCT1 sum_INJECTIVE)] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:1`,`:B`] sum_DISTINCT) THEN SET_TAC[]);;

lemma open_map_inl:
   "open_map X (alexandroff_compactification X) INL"
oops
  REWRITE_TAC[open_map; OPEN_IN_ALEXANDROFF_COMPACTIFICATION] THEN
  MESON_TAC[]);;

lemma continuous_map_inl:
   "continuous_map X (alexandroff_compactification X) INL"
oops
  REWRITE_TAC[continuous_map; OPEN_IN_ALEXANDROFF_COMPACTIFICATION] THEN
  REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION; IN_INSERT] THEN
  GEN_TAC THEN SIMP_TAC[FUN_IN_IMAGE] THEN X_GEN_TAC `v::A+1=>bool` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN
  REWRITE_TAC[sum_DISTINCT; sum_INJECTIVE; UNWIND_THM1] THEN
  REWRITE_TAC[SET_RULE `x \<in> s \<and> x \<in> s - t \<longleftrightarrow> x \<in> s - t`] THEN
  ASM_SIMP_TAC[SET_RULE `s \<subseteq> t \<Longrightarrow> (x \<in> t \<and> x \<in> s \<longleftrightarrow> x \<in> s)`;
               OPEN_IN_SUBSET; IN_GSPEC; OPEN_IN_DIFF; OPEN_IN_TOPSPACE]);;

lemma embedding_map_inl:
   "embedding_map X (alexandroff_compactification X) INL"
oops
  GEN_TAC THEN MATCH_MP_TAC INJECTIVE_OPEN_IMP_EMBEDDING_MAP THEN
  REWRITE_TAC[CONTINUOUS_MAP_INL; OPEN_MAP_INL; sum_INJECTIVE]);;

lemma compact_space_alexandroff_compactification:
   "compact_space(alexandroff_compactification X)"
oops
  GEN_TAC THEN REWRITE_TAC[COMPACT_SPACE_ALT] THEN
  REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION] THEN
  X_GEN_TAC `uu:(A+1=>bool)->bool` THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [IN_UNIONS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u::A+1=>bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `compactin (alexandroff_compactification(X::A topology))
               (topspace(alexandroff_compactification X) - u)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `\<exists>c. compactin X c \<and> closedin X c \<and>
          topspace(alexandroff_compactification X) - u =
          image INL (c::A=>bool)`
    STRIP_ASSUME_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[IMAGE_COMPACT_IN; CONTINUOUS_MAP_INL]] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `u::A+1=>bool`) THEN
    ASM_REWRITE_TAC[OPEN_IN_ALEXANDROFF_COMPACTIFICATION] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [STRIP_TAC THEN UNDISCH_TAC `INR () \<in> (u::A+1=>bool)` THEN
      ASM_REWRITE_TAC[IN_IMAGE; sum_DISTINCT];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c::A=>bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION] THEN
      MATCH_MP_TAC(SET_RULE
       `c \<subseteq> s \<and> (\<forall>x. (z \<noteq> f x)) \<and> (\<forall>x y. f x = f y \<longleftrightarrow> x = y)
        \<Longrightarrow> (insert z f ` s) - (insert z image f (s - c)) =
            f ` c`) THEN
      ASM_SIMP_TAC[CLOSED_IN_SUBSET; sum_DISTINCT; sum_INJECTIVE]];
    REWRITE_TAC[compactin; SUBSET_DIFF] THEN
    ASM_REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `uu:(A+1=>bool)->bool`) THEN ANTS_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `vv:(A+1=>bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(u::A+1=>bool) insert vv` THEN
    ASM_REWRITE_TAC[FINITE_INSERT] THEN ASM SET_TAC[]]);;

lemma topspace_alexandroff_compactification_delete:
   "topspace(alexandroff_compactification X) DELETE (INR ()) =
        image INL (topspace X)"
oops
  GEN_TAC THEN
  REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION] THEN
  REWRITE_TAC[SET_RULE `(insert a s) - {a} = s \<longleftrightarrow> (a \<notin> s)`] THEN
  REWRITE_TAC[IN_IMAGE; sum_DISTINCT]);;

lemma alexandroff_compactification_dense:
   "\<not> compact_space X
        \<Longrightarrow> (alexandroff_compactification X)
            closure_of (image INL (topspace X)) =
            topspace(alexandroff_compactification X)"
oops
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN
  MATCH_MP_TAC ONE_POINT_COMPACTIFICATION_DENSE THEN
  REWRITE_TAC[COMPACT_SPACE_ALEXANDROFF_COMPACTIFICATION] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN
  REWRITE_TAC[CONTRAPOS_THM; COMPACT_IN_SUBSPACE] THEN
  DISCH_THEN(MP_TAC \<circ> CONJUNCT2) THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPACT_SPACE THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN
  MATCH_MP_TAC EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE THEN
  REWRITE_TAC[EMBEDDING_MAP_INL]);;

lemma t0_space_one_point_compactification:
   "compact_space X \<and>
        openin X (topspace X - {a})
        \<Longrightarrow> (t0_space X \<longleftrightarrow>
             t0_space (subtopology X (topspace X - {a})))"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[T0_SPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[t0_space; TOPSPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[SET_RULE `s \<inter> s - {a} = s - {a}`] THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY; IN_DELETE; SUBSET_DELETE] THEN
  DISCH_TAC THEN MATCH_MP_TAC(MESON[]
   `(\<forall>x y. R x y \<Longrightarrow> R y x) \<and>
    (\<exists>a. (\<forall>x y. (P x \<and> (x \<noteq> a)) \<and> (P y \<and> (y \<noteq> a)) \<and> (x \<noteq> y) \<Longrightarrow> R x y) \<and>
         (\<forall>x. P x \<and> (x \<noteq> a) \<Longrightarrow> R a x))
    \<Longrightarrow> \<forall>x y. P x \<and> P y \<and> (x \<noteq> y) \<Longrightarrow> R x y`) THEN
  CONJ_TAC THENL [MESON_TAC[]; EXISTS_TAC `a::A`] THEN
  CONJ_TAC THENL [ASM_METIS_TAC[]; REPEAT STRIP_TAC] THEN
  EXISTS_TAC `topspace X DELETE (a::A)` THEN
  ASM_REWRITE_TAC[IN_DELETE]);;

lemma t0_space_alexandroff_compactification:
   "t0_space(alexandroff_compactification X) \<longleftrightarrow>
        t0_space X"
oops
  GEN_TAC THEN MP_TAC(ISPECL
   [`alexandroff_compactification(X::A topology)`; `INR ()::A+1`]
   T0_SPACE_ONE_POINT_COMPACTIFICATION) THEN
  REWRITE_TAC[COMPACT_SPACE_ALEXANDROFF_COMPACTIFICATION] THEN ANTS_TAC THENL
   [REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN
    MESON_TAC[open_map; OPEN_IN_TOPSPACE; OPEN_MAP_INL];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN
    MATCH_MP_TAC HOMEOMORPHIC_T0_SPACE THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN
    MATCH_MP_TAC EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE THEN
    REWRITE_TAC[EMBEDDING_MAP_INL]]);;

lemma t1_space_one_point_compactification:
   "openin X (topspace X - {a}) \<and>
        (\<forall>k. compactin (subtopology X (topspace X - {a})) k \<and>
             closedin (subtopology X (topspace X - {a})) k
             \<Longrightarrow> closedin X k)
        \<Longrightarrow> (t1_space X \<longleftrightarrow>
             t1_space (subtopology X (topspace X - {a})))"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[T1_SPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[T1_SPACE_CLOSED_IN_SING] THEN
  DISCH_TAC THEN X_GEN_TAC `x::A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x::A = a` THENL
   [ASM_REWRITE_TAC[closedin; SING_SUBSET] THEN
    ASM_REWRITE_TAC[SET_RULE `s - {a} = s - {a}`];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[COMPACT_IN_SING; TOPSPACE_SUBTOPOLOGY] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DELETE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_DELETE]]);;

lemma t1_space_alexandroff_compactification:
   "t1_space(alexandroff_compactification X) \<longleftrightarrow>
        t1_space X"
oops
  GEN_TAC THEN MP_TAC(ISPECL
   [`alexandroff_compactification(X::A topology)`; `INR ()::A+1`]
   T1_SPACE_ONE_POINT_COMPACTIFICATION) THEN
  REWRITE_TAC[COMPACT_SPACE_ALEXANDROFF_COMPACTIFICATION] THEN ANTS_TAC THENL
   [SIMP_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN CONJ_TAC THENL
     [MESON_TAC[open_map; OPEN_IN_TOPSPACE; OPEN_MAP_INL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MESON[COMPACT_IN_SUBTOPOLOGY]
     `(compactin (subtopology X u) k \<and> P k \<Longrightarrow> Q k) \<longleftrightarrow>
      (k \<subseteq> u \<Longrightarrow> compactin (subtopology X u) k \<and> P k \<Longrightarrow> Q k)`] THEN
    REWRITE_TAC[FORALL_SUBSET_IMAGE] THEN
    X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV
     [CLOSED_IN_ALEXANDROFF_COMPACTIFICATION_IMAGE_INL] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPACTNESS;
      MATCH_MP_TAC HOMEOMORPHIC_MAP_CLOSEDNESS] THEN
    ASM_REWRITE_TAC[GSYM embedding_map; EMBEDDING_MAP_INL];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN
    MATCH_MP_TAC HOMEOMORPHIC_T1_SPACE THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN
    MATCH_MP_TAC EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE THEN
    REWRITE_TAC[EMBEDDING_MAP_INL]]);;

lemma kc_space_one_point_compactification:
   "compact_space X \<and>
        openin X (topspace X - {a}) \<and>
        (\<forall>k. compactin (subtopology X (topspace X - {a})) k \<and>
             closedin (subtopology X (topspace X - {a})) k
             \<Longrightarrow> closedin X k)
        \<Longrightarrow> (kc_space X \<longleftrightarrow>
             k_space (subtopology X (topspace X - {a})) \<and>
             kc_space (subtopology X (topspace X - {a})))"
oops
  SIMP_TAC[KC_SPACE_ONE_POINT_COMPACTIFICATION_GEN] THEN
  REWRITE_TAC[kc_space; COMPACT_IN_SUBTOPOLOGY; SUBSET_DELETE] THEN
  MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE]);;

lemma kc_space_alexandroff_compactification:
   "kc_space(alexandroff_compactification X) \<longleftrightarrow>
        k_space X \<and> kc_space X"
oops
  GEN_TAC THEN MP_TAC(ISPECL
   [`alexandroff_compactification(X::A topology)`; `INR ()::A+1`]
   KC_SPACE_ONE_POINT_COMPACTIFICATION) THEN
  REWRITE_TAC[COMPACT_SPACE_ALEXANDROFF_COMPACTIFICATION] THEN ANTS_TAC THENL
   [SIMP_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN CONJ_TAC THENL
     [MESON_TAC[open_map; OPEN_IN_TOPSPACE; OPEN_MAP_INL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MESON[COMPACT_IN_SUBTOPOLOGY]
     `(compactin (subtopology X u) k \<and> P k \<Longrightarrow> Q k) \<longleftrightarrow>
      (k \<subseteq> u \<Longrightarrow> compactin (subtopology X u) k \<and> P k \<Longrightarrow> Q k)`] THEN
    REWRITE_TAC[FORALL_SUBSET_IMAGE] THEN
    X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV
     [CLOSED_IN_ALEXANDROFF_COMPACTIFICATION_IMAGE_INL] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPACTNESS;
      MATCH_MP_TAC HOMEOMORPHIC_MAP_CLOSEDNESS] THEN
    ASM_REWRITE_TAC[GSYM embedding_map; EMBEDDING_MAP_INL];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN
    BINOP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_K_SPACE;
      MATCH_MP_TAC HOMEOMORPHIC_KC_SPACE] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN
    MATCH_MP_TAC EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE THEN
    REWRITE_TAC[EMBEDDING_MAP_INL]]);;

lemma regular_space_one_point_compactification:
   "compact_space X \<and>
        openin X (topspace X - {a}) \<and>
        (\<forall>k. compactin (subtopology X (topspace X - {a})) k \<and>
             closedin (subtopology X (topspace X - {a})) k
             \<Longrightarrow> closedin X k)
        \<Longrightarrow> (regular_space X \<longleftrightarrow>
             regular_space (subtopology X (topspace X - {a})) \<and>
             locally_compact_space (subtopology X (topspace X - {a})))"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [SIMP_TAC[REGULAR_SPACE_SUBTOPOLOGY] THEN
    ASM_MESON_TAC[LOCALLY_COMPACT_SPACE_OPEN_SUBSET;
                  COMPACT_IMP_LOCALLY_COMPACT_SPACE];
    STRIP_TAC] THEN
  REWRITE_TAC[GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN] THEN
  REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN
  MAP_EVERY X_GEN_TAC [`u::A=>bool`; `x::A`] THEN
  ASM_CASES_TAC `x::A = a` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MP_TAC(ISPEC `subtopology X (topspace X DELETE (a::A))`
        LOCALLY_COMPACT_SPACE_COMPACT_CLOSED_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `topspace X - u::A=>bool`) THEN ANTS_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC CLOSED_IN_COMPACT_SPACE THEN
      ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE];
      ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY; SUBSET_DIFF; SUBSET_DELETE;
                   COMPACT_IN_SUBTOPOLOGY; LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`v::A=>bool`; `k::A=>bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `k::A=>bool`) THEN
    ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY; SUBSET_DELETE] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`topspace X - k::A=>bool`; `topspace X - v::A=>bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_DIFF; CLOSED_IN_DIFF; OPEN_IN_TOPSPACE;
                 CLOSED_IN_TOPSPACE] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET)) THEN ASM SET_TAC[];
    MP_TAC(ISPEC `subtopology X (topspace X DELETE (a::A))`
        LOCALLY_COMPACT_REGULAR_SPACE_NEIGHBOURHOOD_BASE) THEN
    ASM_REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN DISCH_THEN(MP_TAC \<circ> SPECL
     [`(topspace X DELETE (a::A)) \<inter> u`; `x::A`]) THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_SUBTOPOLOGY; SUBSET_DELETE;
                 OPEN_IN_INTER; IN_INTER; IN_DELETE] THEN
    FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]]);;

lemma regular_space_alexandroff_compactification:
   "regular_space(alexandroff_compactification X) \<longleftrightarrow>
        regular_space X \<and> locally_compact_space X"
oops
  GEN_TAC THEN MP_TAC(ISPECL
   [`alexandroff_compactification(X::A topology)`; `INR ()::A+1`]
   REGULAR_SPACE_ONE_POINT_COMPACTIFICATION) THEN
  REWRITE_TAC[COMPACT_SPACE_ALEXANDROFF_COMPACTIFICATION] THEN ANTS_TAC THENL
   [SIMP_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN CONJ_TAC THENL
     [MESON_TAC[open_map; OPEN_IN_TOPSPACE; OPEN_MAP_INL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MESON[COMPACT_IN_SUBTOPOLOGY]
     `(compactin (subtopology X u) k \<and> P k \<Longrightarrow> Q k) \<longleftrightarrow>
      (k \<subseteq> u \<Longrightarrow> compactin (subtopology X u) k \<and> P k \<Longrightarrow> Q k)`] THEN
    REWRITE_TAC[FORALL_SUBSET_IMAGE] THEN
    X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV
     [CLOSED_IN_ALEXANDROFF_COMPACTIFICATION_IMAGE_INL] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPACTNESS;
      MATCH_MP_TAC HOMEOMORPHIC_MAP_CLOSEDNESS] THEN
    ASM_REWRITE_TAC[GSYM embedding_map; EMBEDDING_MAP_INL];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN
    BINOP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_REGULAR_SPACE;
      MATCH_MP_TAC HOMEOMORPHIC_LOCALLY_COMPACT_SPACE] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN
    MATCH_MP_TAC EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE THEN
    REWRITE_TAC[EMBEDDING_MAP_INL]]);;

lemma Hausdorff_space_one_point_compactification:
   "compact_space X \<and>
        openin X (topspace X - {a}) \<and>
        (\<forall>k. compactin (subtopology X (topspace X - {a})) k \<and>
             closedin (subtopology X (topspace X - {a})) k
             \<Longrightarrow> closedin X k)
        \<Longrightarrow> (Hausdorff_space X \<longleftrightarrow>
             Hausdorff_space (subtopology X (topspace X - {a})) \<and>
             locally_compact_space (subtopology X (topspace X - {a})))"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY] THEN
    ASM_MESON_TAC[COMPACT_HAUSDORFF_IMP_REGULAR_SPACE;
                 REGULAR_SPACE_ONE_POINT_COMPACTIFICATION];
    ASM_METIS_TAC[REGULAR_SPACE_ONE_POINT_COMPACTIFICATION;
                  LOCALLY_COMPACT_HAUSDORFF_IMP_REGULAR_SPACE;
                  REGULAR_T1_IMP_HAUSDORFF_SPACE; HAUSDORFF_IMP_T1_SPACE;
                  T1_SPACE_ONE_POINT_COMPACTIFICATION]]);;

lemma Hausdorff_space_alexandroff_compactification:
   "Hausdorff_space(alexandroff_compactification X) \<longleftrightarrow>
        Hausdorff_space X \<and> locally_compact_space X"
oops
  GEN_TAC THEN MP_TAC(ISPECL
   [`alexandroff_compactification(X::A topology)`; `INR ()::A+1`]
   HAUSDORFF_SPACE_ONE_POINT_COMPACTIFICATION) THEN
  REWRITE_TAC[COMPACT_SPACE_ALEXANDROFF_COMPACTIFICATION] THEN ANTS_TAC THENL
   [SIMP_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN CONJ_TAC THENL
     [MESON_TAC[open_map; OPEN_IN_TOPSPACE; OPEN_MAP_INL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[MESON[COMPACT_IN_SUBTOPOLOGY]
     `(compactin (subtopology X u) k \<and> P k \<Longrightarrow> Q k) \<longleftrightarrow>
      (k \<subseteq> u \<Longrightarrow> compactin (subtopology X u) k \<and> P k \<Longrightarrow> Q k)`] THEN
    REWRITE_TAC[FORALL_SUBSET_IMAGE] THEN
    X_GEN_TAC `k::A=>bool` THEN DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV
     [CLOSED_IN_ALEXANDROFF_COMPACTIFICATION_IMAGE_INL] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPACTNESS;
      MATCH_MP_TAC HOMEOMORPHIC_MAP_CLOSEDNESS] THEN
    ASM_REWRITE_TAC[GSYM embedding_map; EMBEDDING_MAP_INL];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN
    BINOP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_HAUSDORFF_SPACE;
      MATCH_MP_TAC HOMEOMORPHIC_LOCALLY_COMPACT_SPACE] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN
    MATCH_MP_TAC EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE THEN
    REWRITE_TAC[EMBEDDING_MAP_INL]]);;

lemma completely_regular_space_alexandroff_compactification:
   "completely_regular_space(alexandroff_compactification X) \<longleftrightarrow>
        completely_regular_space X \<and> locally_compact_space X"
oops
  MESON_TAC[REGULAR_SPACE_ALEXANDROFF_COMPACTIFICATION;
            COMPLETELY_REGULAR_EQ_REGULAR_SPACE;
            COMPACT_IMP_LOCALLY_COMPACT_SPACE;
            COMPACT_SPACE_ALEXANDROFF_COMPACTIFICATION]);;

lemma Hausdorff_space_one_point_compactification_asymmetric_prod:
   "compact_space X
        \<Longrightarrow> (Hausdorff_space X \<longleftrightarrow>
             kc_space
              (prod_topology X (subtopology X (topspace X - {a}))) \<and>
             k_space
              (prod_topology X (subtopology X (topspace X - {a}))))"
oops
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(a::A) \<in> topspace X` THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUBTOPOLOGY_TOPSPACE; KC_SPACE_COMPACT_PROD_TOPOLOGY; SET_RULE
       `(a \<notin> s) \<Longrightarrow> s - {a} = s`] THEN
    SIMP_TAC[COMPACT_IMP_K_SPACE; COMPACT_SPACE_PROD_TOPOLOGY]] THEN
  STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [REWRITE_TAC[PROD_TOPOLOGY_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAUSDORFF_IMP_KC_SPACE THEN
      MATCH_MP_TAC HAUSDORFF_SPACE_SUBTOPOLOGY THEN
      ASM_REWRITE_TAC[HAUSDORFF_SPACE_PROD_TOPOLOGY];

      MATCH_MP_TAC K_SPACE_OPEN_SUBTOPOLOGY THEN
      ASM_REWRITE_TAC[HAUSDORFF_SPACE_PROD_TOPOLOGY] THEN
      ASM_REWRITE_TAC[OPEN_IN_CROSS; OPEN_IN_TOPSPACE] THEN
      ASM_SIMP_TAC[COMPACT_IMP_K_SPACE; COMPACT_SPACE_PROD_TOPOLOGY] THEN
      REPEAT DISJ2_TAC THEN
      ONCE_REWRITE_TAC[SET_RULE `s - {a} = s - {a}`] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN
      ASM_SIMP_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_HAUSDORFF_SING]];
    ALL_TAC] THEN
  ASM_CASES_TAC `topspace X = {a::A}` THENL
   [ASM_REWRITE_TAC[Hausdorff_space] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`prod_topology X (subtopology X (topspace X DELETE (a::A)))`;
    `X::A topology`; `fst::A#A=>A`] KC_SPACE_RETRACTION_MAP_IMAGE) THEN
  ASM_REWRITE_TAC[RETRACTION_MAP_FST; TOPSPACE_SUBTOPOLOGY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[HAUSDORFF_SPACE_CLOSED_IN_DIAGONAL] THEN
  SUBGOAL_THEN
   `closedin (prod_topology X (subtopology X (topspace X - {a})))
              {x::A,x | x \<in> topspace X - {a}}`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC \<circ> GEN_REWRITE_RULE id [K_SPACE]) THEN
    REWRITE_TAC[\<subseteq>; FORALL_IN_GSPEC; TOPSPACE_PROD_TOPOLOGY] THEN
    SIMP_TAC[IN_DELETE; IN_CROSS; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    X_GEN_TAC `k::A#A=>bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC CLOSED_IN_SUBTOPOLOGY_INTER_SUBSET THEN
    EXISTS_TAC `(image fst (k::A#A=>bool)) \<times> (snd ` k)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[\<subseteq>; FORALL_PAIR_THM; IN_CROSS; IN_IMAGE;
                  EXISTS_PAIR_THM; PAIR_EQ] THEN
      SET_TAC[]] THEN
    MATCH_MP_TAC CLOSED_IN_SUBSET_TOPSPACE THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    FIRST_ASSUM(MATCH_MP_TAC \<circ> GEN_REWRITE_RULE id [kc_space]) THEN
    SUBGOAL_THEN
     `(fst ` k \<times> snd ` k) \<inter>
       {x,x | x \<in> topspace X \<and> \<not> (x::A = a)} =
      image (\<lambda>x::A. x,x) (fst ` k \<inter> snd ` k)`
    SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[\<subseteq>; EXTENSION; FORALL_PAIR_THM] THEN
      REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_INTER; IN_IMAGE; IN_DELETE;
                  EXISTS_PAIR_THM; PAIR_EQ; IN_ELIM_THM; IN_CROSS;
                  TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology X (topspace X DELETE (a::A))` THEN
    REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_ID] THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [ALL_TAC;
      FIRST_ASSUM(MP_TAC \<circ> MATCH_MP COMPACT_IN_SUBSET_TOPSPACE) THEN
      REWRITE_TAC[\<subseteq>; EXTENSION; FORALL_PAIR_THM] THEN
      REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_INTER; IN_IMAGE; IN_DELETE;
                  EXISTS_PAIR_THM; PAIR_EQ; IN_ELIM_THM; IN_CROSS;
                  TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      MESON_TAC[]] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED_IN THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN THEN
      EXISTS_TAC
       `prod_topology X (subtopology X (topspace X DELETE (a::A)))` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_FST];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN_GEN THEN
    ASM_REWRITE_TAC[] THEN  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC
     `prod_topology X (subtopology X (topspace X DELETE (a::A)))` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PROD_TOPOLOGY_SUBTOPOLOGY] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[CONTINUOUS_MAP_SND];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_GSPEC; TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
  DISCH_THEN(ASSUME_TAC \<circ> CONJUNCT2) THEN
  REWRITE_TAC[FORALL_PAIR_THM; closure_of; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; PAIR_EQ; TOPSPACE_PROD_TOPOLOGY] THEN
  REWRITE_TAC[MESON[] `(\<exists>x. P x \<and> a = x \<and> b = x) \<longleftrightarrow> a = b \<and> P b`] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM1; IN_CROSS] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `\<not> (x::A = a) \<or> (y \<noteq> a)` THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(y,x):A#A`);
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(x,y):A#A`)] THEN
  ASM_REWRITE_TAC[closure_of; IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS;
                  IN_DELETE; PAIR_EQ; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  (ANTS_TAC THENL [ALL_TAC; MESON_TAC[]]) THEN
  REWRITE_TAC[IMP_CONJ_ALT; PROD_TOPOLOGY_SUBTOPOLOGY] THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_ALT; FORALL_IN_GSPEC] THEN
  ASM_REWRITE_TAC[IN_INTER; IN_CROSS; IN_DELETE; EXISTS_PAIR_THM] THEN
  REWRITE_TAC[PAIR_EQ] THEN
  REWRITE_TAC[MESON[] `(\<exists>x. P x \<and> a = x \<and> b = x) \<longleftrightarrow> a = b \<and> P b`] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM1] THENL
   [ALL_TAC;
    X_GEN_TAC `t::A#A=>bool` THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC
     `t \<inter> (topspace X \<times> (topspace X DELETE (a::A)))`) THEN
    ASM_SIMP_TAC[IN_INTER; IN_CROSS; IN_DELETE] THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[OPEN_IN_CROSS; OPEN_IN_TOPSPACE] THEN
    ASM_MESON_TAC[T1_SPACE_OPEN_IN_DELETE_ALT; OPEN_IN_TOPSPACE;
                  KC_IMP_T1_SPACE]] THEN
  X_GEN_TAC `t::A#A=>bool` THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC
   `{z. z \<in> topspace(prod_topology X X) \<and>
         (snd z::A,fst z) \<in>
         (t \<inter> (topspace X \<times> (topspace X DELETE (a::A))))}`) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER; IN_CROSS; TOPSPACE_PROD_TOPOLOGY;
                      IN_DELETE] THEN
    MESON_TAC[]] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER; IN_CROSS; TOPSPACE_PROD_TOPOLOGY;
                    IN_DELETE];
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `prod_topology (X::A topology) X` THEN
    REWRITE_TAC[CONTINUOUS_MAP_PAIRED] THEN
    REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND] THEN
     MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[OPEN_IN_CROSS; OPEN_IN_TOPSPACE] THEN
    ASM_MESON_TAC[T1_SPACE_OPEN_IN_DELETE_ALT; OPEN_IN_TOPSPACE;
                  KC_IMP_T1_SPACE]]);;

lemma Hausdorff_space_alexandroff_compactification_asymmetric_prod:
   "Hausdorff_space(alexandroff_compactification X) \<longleftrightarrow>
        kc_space(prod_topology (alexandroff_compactification X) X) \<and>
        k_space(prod_topology (alexandroff_compactification X) X)"
oops
  GEN_TAC THEN MP_TAC(ISPECL
   [`alexandroff_compactification(X::A topology)`; `INR ()::A+1`]
   HAUSDORFF_SPACE_ONE_POINT_COMPACTIFICATION_ASYMMETRIC_PROD) THEN
  REWRITE_TAC[COMPACT_SPACE_ALEXANDROFF_COMPACTIFICATION] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC
   (MESON[HOMEOMORPHIC_K_SPACE; HOMEOMORPHIC_KC_SPACE]
    `X homeomorphic_space X'
     \<Longrightarrow> (kc_space X \<and> k_space X \<longleftrightarrow> kc_space X' \<and> k_space X')`) THEN
  MATCH_MP_TAC HOMEOMORPHIC_SPACE_PROD_TOPOLOGY THEN
  REWRITE_TAC[HOMEOMORPHIC_SPACE_REFL] THEN
  REWRITE_TAC[TOPSPACE_ALEXANDROFF_COMPACTIFICATION_DELETE] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN
  MATCH_MP_TAC EMBEDDING_MAP_IMP_HOMEOMORPHIC_SPACE THEN
  REWRITE_TAC[EMBEDDING_MAP_INL]);;

lemma kc_space_as_compactification_unique:
   "kc_space X \<and> compact_space X
        \<Longrightarrow> \<forall>u. openin X u \<longleftrightarrow>
                if a \<in> u
                then u \<subseteq> topspace X \<and>
                     compactin X (topspace X - u)
                else openin (subtopology X (topspace X - {a})) u"
oops
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u::A=>bool` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[OPEN_IN_CLOSED_IN_EQ; CLOSED_IN_COMPACT_SPACE; kc_space];
    FIRST_ASSUM(MP_TAC \<circ> MATCH_MP KC_IMP_T1_SPACE) THEN
    ASM_SIMP_TAC[T1_SPACE_OPEN_IN_DELETE_ALT; OPEN_IN_TOPSPACE;
                 OPEN_IN_OPEN_SUBTOPOLOGY; SUBSET_DELETE] THEN
    MESON_TAC[OPEN_IN_SUBSET]]);;

lemma kc_space_as_compactification_unique_explicit:
   "kc_space X \<and> compact_space X
        \<Longrightarrow> \<forall>u. openin X u \<longleftrightarrow>
                if a \<in> u
                then u \<subseteq> topspace X \<and>
                     compactin (subtopology X (topspace X - {a}))
                                (topspace X - u) \<and>
                     closedin (subtopology X (topspace X - {a}))
                                (topspace X - u)
                else openin (subtopology X (topspace X - {a})) u"
oops
  SIMP_TAC[KC_SPACE_SUBTOPOLOGY; MESON[kc_space]
   `kc_space X
    \<Longrightarrow> (compactin X s \<and> closedin X s \<longleftrightarrow> compactin X s)`] THEN
  SIMP_TAC[COMPACT_IN_SUBTOPOLOGY; SET_RULE
   `a \<in> u \<Longrightarrow> s - u \<subseteq> s - {a}`] THEN
  REWRITE_TAC[KC_SPACE_AS_COMPACTIFICATION_UNIQUE]);;

lemma alexandroff_compactification_unique:
   "kc_space X \<and> compact_space X \<and> a \<in> topspace X
        \<Longrightarrow> alexandroff_compactification
             (subtopology X (topspace X - {a}))
            homeomorphic_space X"
oops
  lemma lemma:
   (`(INL ` s = INL ` t \<longleftrightarrow> s = t) \<and>
     (INR insert x INL ` s = INR insert x INL ` t \<longleftrightarrow> s = t) \<and>
     \<not> (INR insert x INL ` s = INL ` t)"
oops
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INSERT;
                sum_DISTINCT; sum_INJECTIVE] THEN
    MESON_TAC[sum_DISTINCT; sum_INJECTIVE])
in

  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN
  REWRITE_TAC[HOMEOMORPHIC_SPACE; homeomorphic_map] THEN
  EXISTS_TAC `\<lambda>x::A. if x = a then INR () else INL x` THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[sum_INJECTIVE; sum_DISTINCT]] THEN
  REWRITE_TAC[quotient_map; TOPSPACE_ALEXANDROFF_COMPACTIFICATION] THEN
  SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; DELETE_SUBSET] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_SUBSET_INSERT; FORALL_SUBSET_IMAGE] THEN
  X_GEN_TAC `u::A=>bool` THEN REWRITE_TAC[SUBSET_DELETE] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[IN_INSERT; IN_IMAGE; sum_DISTINCT; sum_INJECTIVE] THEN
  REWRITE_TAC[UNWIND_THM1] THEN MP_TAC(ISPECL [`X::A topology`; `a::A`]
        KC_SPACE_AS_COMPACTIFICATION_UNIQUE_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; SUBSET_RESTRICT] THEN
  REWRITE_TAC[OPEN_IN_ALEXANDROFF_COMPACTIFICATION] THEN
  REWRITE_TAC[lemma] THEN
  SUBGOAL_THEN
   `{x::A | x \<in> topspace X \<and> (if x = a then False else x \<in> u)} = u`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[TAUT `(if p then True else q) \<longleftrightarrow> p \<or> q`] THEN
  REWRITE_TAC[SET_RULE
   `u - {x \<in> u. (x = a \<or> x \<in> s)} = u - {a} - s`] THEN
  ONCE_REWRITE_TAC[MESON[CLOSED_IN_SUBSET]
   `closedin X s \<and> P s \<longleftrightarrow>
    \<not> (s \<subseteq> topspace X \<Longrightarrow> closedin X s \<Longrightarrow> \<not> P s)`] THEN
  SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; DELETE_SUBSET] THEN
  ASM_SIMP_TAC[SET_RULE
   `a \<in> t \<and> (a \<notin> u) \<and> u \<subseteq> t \<and> s \<subseteq> t - {a}
    \<Longrightarrow> (u = t - {a} - s \<longleftrightarrow> t - {a} - u = s)`] THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN ONCE_REWRITE_TAC[TAUT
   `p \<and> q \<and> r \<and> s \<longleftrightarrow> s \<and> p \<and> q \<and> r`] THEN
  REWRITE_TAC[UNWIND_THM1] THEN ASM SET_TAC[]);;


subsection\<open>Homotopy of maps p,q : X=>Y with property P of all intermediate maps\<close>
subsection\<open>We often just want to require that it fixes some subset, but to take in   \<close>
text\<open> the case of loop homotopy it's convenient to have a general property P\<close>


let homotopic_with = new_definition
  `homotopic_with P (X,Y) p q \<longleftrightarrow>
   \<exists>h. continuous_map
       (prod_topology (subtopology euclideanreal ({0..1})) X,
        Y) h \<and>
       (\<forall>x. h(0,x) = p x) \<and> (\<forall>x. h(1,x) = q x) \<and>
       (\<forall>t. t \<in> {0..1} \<Longrightarrow> P(\<lambda>x. h(t,x)))`;;

lemma homotopic_with:
   "\<And>P X Y p q::A=>B.
        (\<forall>h k. (\<forall>x. x \<in> topspace X \<Longrightarrow> h x = k x) \<Longrightarrow> (P h \<longleftrightarrow> P k))
        \<Longrightarrow> (homotopic_with P (X,Y) p q \<longleftrightarrow>
             \<exists>h. continuous_map
                  (prod_topology
                   (subtopology euclideanreal (real_interval [0,1])) X,
                   Y) h \<and>
                (\<forall>x. x \<in> topspace X \<Longrightarrow> h (0,x) = p x) \<and>
                (\<forall>x. x \<in> topspace X \<Longrightarrow> h (1,x) = q x) \<and>
                (\<forall>t. t \<in> {0..1} \<Longrightarrow> P (\<lambda>x. h (t,x))))"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_with] THEN EQ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h::real#A=>B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\<lambda>(t,x). if x \<in> topspace X then (h::real#A=>B)(t,x)
                      else if t = 0 then p x else q x` THEN
  ASM_SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[COND_ID] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        CONTINUOUS_MAP_EQ)) THEN
    SIMP_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS];
    X_GEN_TAC `t::real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `t::real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[]]);;

lemma homotopic_with_imp_continuous_maps:
   "\<And>P X Y p q::A=>B.
        homotopic_with P (X,Y) p q
        \<Longrightarrow> continuous_map X Y p \<and> continuous_map X Y q"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homotopic_with; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h::real#A=>B` THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `p = (h::real#A=>B) \<circ> (\<lambda>x. (0,x))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC];
    SUBGOAL_THEN `q = (h::real#A=>B) \<circ> (\<lambda>x. (1,x))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        CONTINUOUS_MAP_COMPOSE)) THEN
  REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX] THEN
  REWRITE_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST] THEN DISJ2_TAC THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

lemma homotopic_with_imp_property:
   "\<And>P X Y f g::A=>B. homotopic_with P (X,Y) f g \<Longrightarrow> P f \<and> P g"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h::real#A=>B` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN DISCH_THEN
   (fun th -> MP_TAC(SPEC `0::real` th) THEN
              MP_TAC(SPEC `1::real` th)) THEN
  ASM_SIMP_TAC[ENDS_IN_UNIT_REAL_INTERVAL; ETA_AX]);;

lemma homotopic_with_equal:
   "\<And>P X X' f g.
        P f \<and> P g \<and>
        continuous_map X X' f \<and>
        (\<forall>x. x \<in> topspace X \<Longrightarrow> f x = g x)
        \<Longrightarrow> homotopic_with P (X,X') f g"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC `(\<lambda>(t,x). if t = 1 then g x else f x):real#A=>B` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `(f \<circ> snd):real#A=>B` THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; o_THM; IN_CROSS] THEN
    ASM_SIMP_TAC[COND_ID] THEN MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `X::A topology` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[PROD_TOPOLOGY_SUBTOPOLOGY; CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
             CONTINUOUS_MAP_SND];
    X_GEN_TAC `t::real` THEN ASM_CASES_TAC `t::real = 1` THEN
    ASM_REWRITE_TAC[ETA_AX]]);;

lemma homotopic_with_refl:
   "\<And>P X X' f::A=>B.
        homotopic_with P (X,X') f f \<longleftrightarrow>
        continuous_map X X' f \<and> P f"
oops
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS; HOMOTOPIC_WITH_IMP_PROPERTY];
    DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
    ASM_REWRITE_TAC[]]);;

lemma homotopic_with_sym:
   "\<And>P X Y f g::A=>B.
     homotopic_with P (X,Y) f g \<longleftrightarrow> homotopic_with P (X,Y) g f"
oops
  REPLICATE_TAC 3 GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(\<forall>x y. P x y \<Longrightarrow> P y x) \<Longrightarrow> (\<forall>x y. P x y \<longleftrightarrow> P y x)`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h::real#A=>B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\<lambda>(t,x). (h::real#A=>B) (1 - t,x)` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_SUB_RZERO] THEN CONJ_TAC THENL
   [REWRITE_TAC[LAMBDA_PAIR] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
      `prod_topology (subtopology euclideanreal (real_interval [0,1]))
                     (X::A topology)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_SND] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; \<subseteq>; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                FORALL_PAIR_THM; IN_CROSS; IN_REAL_INTERVAL] THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
    REWRITE_TAC[CONTINUOUS_MAP_OF_FST] THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID];
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC]);;

lemma homotopic_with_trans:
   "\<And>P X X' f g h.
        homotopic_with P (X,X') f g \<and>
        homotopic_with P (X,X') g h
        \<Longrightarrow> homotopic_with P (X,X') f h"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with; IN_REAL_INTERVAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `h::real#A=>B` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `k::real#A=>B` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\<lambda>z. if fst z \<le> 1 / 2
                  then (h::real#A=>B)(2 * fst z,snd z)
                  else (k::real#A=>B)(2 * fst z - 1,snd z)` THEN
  REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
    SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PROD_TOPOLOGY_SUBTOPOLOGY] THEN
      SIMP_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_FROM_SUBTOPOLOGY];
      CONJ_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
       `prod_topology (subtopology euclideanreal (real_interval [0,1]))
                      (X::A topology)` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX] THEN
      SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_SND] THEN
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY;
                  FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_INTER;
                  IN_ELIM_THM; IN_CROSS; IN_REAL_INTERVAL] THEN
      (CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC]) THEN
      TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB) THEN
      REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[PROD_TOPOLOGY_SUBTOPOLOGY] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[CONTINUOUS_MAP_FST; ETA_AX]];
    X_GEN_TAC `t::real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t \<le> 1 / 2` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

lemma homotopic_with_compose_continuous_map_left:
   "\<And>p q f g (h::B=>C) top1 top2 top3.
        homotopic_with p (top1,top2) f g \<and>
        continuous_map top2 top3 h \<and>
        (\<forall>j. p j \<Longrightarrow> q(h \<circ> j))
        \<Longrightarrow> homotopic_with q (top1,top3) (h \<circ> f) (h \<circ> g)"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN STRIP_TAC THEN
  REWRITE_TAC[homotopic_with; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k::real#A=>B` THEN STRIP_TAC THEN
  EXISTS_TAC `(h::B=>C) \<circ> (k::real#A=>B)` THEN
  ASM_REWRITE_TAC[o_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  ASM_SIMP_TAC[]);;

lemma homotopic_compose_continuous_map_left:
   "\<And>f g (h::B=>C) top1 top2 top3.
        homotopic_with (\<lambda>k. True) (top1,top2) f g \<and>
        continuous_map top2 top3 h
        \<Longrightarrow> homotopic_with (\<lambda>k. True) (top1,top3) (h \<circ> f) (h \<circ> g)"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_LEFT) THEN
  ASM_REWRITE_TAC[]);;

lemma homotopic_with_compose_continuous_map_right:
   "\<And>p q (f::B=>C) g (h::A=>B) top1 top2 top3.
        homotopic_with p (top2,top3) f g \<and>
        continuous_map top1 top2 h \<and>
        (\<forall>j. p j \<Longrightarrow> q(j \<circ> h))
        \<Longrightarrow> homotopic_with q (top1,top3) (f \<circ> h) (g \<circ> h)"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN STRIP_TAC THEN
  REWRITE_TAC[homotopic_with; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k::real#B=>C` THEN STRIP_TAC THEN
  EXISTS_TAC `\<lambda>(t,x). (k::real#B=>C)(t,(h::A=>B) x)` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[LAMBDA_PAIR] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
       CONTINUOUS_MAP_COMPOSE)) THEN
    REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX] THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_OF_SND];
    GEN_TAC THEN REPLICATE_TAC 2 (DISCH_THEN(ANTE_RES_THEN MP_TAC)) THEN
    REWRITE_TAC[o_DEF]]);;

lemma homotopic_compose_continuous_map_right:
   "\<And>(f::B=>C) g (h::A=>B) top1 top2 top3.
        homotopic_with (\<lambda>k. True) (top2,top3) f g \<and>
        continuous_map top1 top2 h
        \<Longrightarrow> homotopic_with (\<lambda>k. True) (top1,top3) (f \<circ> h) (g \<circ> h)"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_RIGHT) THEN
  ASM_REWRITE_TAC[]);;

lemma homotopic_from_subtopology:
   "\<And>P X X' s f (g::A=>B).
        homotopic_with P (X,X') f g
        \<Longrightarrow> homotopic_with P (subtopology X s,X') f g"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopic_with] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONJUNCT2 PROD_TOPOLOGY_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY]);;

lemma homotopic_on_empty:
   "\<And>X X' f g.
        topspace X = {}
        \<Longrightarrow> (homotopic_with P (X,X') f g \<longleftrightarrow> P f \<and> P g)"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC[HOMOTOPIC_WITH_IMP_PROPERTY] THEN STRIP_TAC THEN
  REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC `(\<lambda>(t,x). if t = 0 then f x else g x):real#A=>B` THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; ARITH_EQ; CROSS_EMPTY;
               CONTINUOUS_MAP_ON_EMPTY; TOPSPACE_PROD_TOPOLOGY] THEN
  X_GEN_TAC `t::real` THEN ASM_CASES_TAC `t::real = 0` THEN
  ASM_REWRITE_TAC[ETA_AX]);;

lemma homotopic_constant_maps:
   "\<And>(X::A topology) (X':B topology) a b.
        homotopic_with (\<lambda>x. True) (X,X') (\<lambda>x. a) (\<lambda>x. b) \<longleftrightarrow>
        topspace X = {} \<or> path_component_of X' a b"
oops
  REPEAT GEN_TAC THEN ASM_CASES_TAC `topspace X::A=>bool = {}` THEN
  ASM_SIMP_TAC[HOMOTOPIC_ON_EMPTY] THEN
  REWRITE_TAC[path_component_of; pathin; homotopic_with] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `h::real#A=>B` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `a::A` \<circ>
      GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY]) THEN
    EXISTS_TAC `(h::real#A=>B) \<circ> (\<lambda>t. t,a)` THEN
    ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC
     `prod_topology (subtopology euclideanreal ({0..1}))
                    (X::A topology)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRED; CONTINUOUS_MAP_ID] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST];
    DISCH_THEN(X_CHOOSE_THEN `g::real=>B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(g::real=>B) \<circ> (fst::real#A=>real)` THEN
    ASM_REWRITE_TAC[o_DEF; CONTINUOUS_MAP_OF_FST]]);;

lemma homotopic_with_eq:
   "\<And>P X X' f g f' g':A=>B.
        homotopic_with P (X,X') f g \<and>
        (\<forall>x. x \<in> topspace X \<Longrightarrow> f' x = f x \<and> g' x = g x) \<and>
        (\<forall>h k. (\<forall>x. x \<in> topspace X \<Longrightarrow> h x = k x) \<Longrightarrow> (P h \<longleftrightarrow> P k))
        \<Longrightarrow>  homotopic_with P (X,X') f' g'"
oops
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[homotopic_with] THEN
  DISCH_THEN(X_CHOOSE_THEN `h::real#A=>B`
   (fun th -> EXISTS_TAC
     `\<lambda>y. if snd y \<in> topspace X then (h::real#A=>B) y
          else if fst y = 0 then f'(snd y)
          else g'(snd y)` THEN
   MP_TAC th)) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_MAP_EQ) THEN
    SIMP_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t::real` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[]]);;

lemma homotopic_with_prod_topology:
   "\<And>p q r top1 top1' top2 top2' f (g::C=>D) f' g'.
      homotopic_with p (top1,top1') f f' \<and>
      homotopic_with q (top2,top2') g g' \<and>
      (\<forall>i j. p i \<and> q j \<Longrightarrow> r(\<lambda>(x,y). i x,j y))
      \<Longrightarrow> homotopic_with r (prod_topology top1 top2,prod_topology top1' top2')
                           (\<lambda>z. f(fst z),g(snd z)) (\<lambda>z. f'(fst z),g'(snd z))"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[homotopic_with; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h::real#A=>B` THEN STRIP_TAC THEN
  X_GEN_TAC `k::real#C=>D` THEN
  REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
  EXISTS_TAC `\<lambda>(t,x,y). (h::real#A=>B) (t,x),(k::real#C=>D) (t,y)` THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_SIMP_TAC[LAMBDA_PAIR_THM] THEN
  REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
  REWRITE_TAC[LAMBDA_TRIPLE_THM] THEN REWRITE_TAC[LAMBDA_TRIPLE] THEN
  CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THENL
   [EXISTS_TAC
     `prod_topology (subtopology euclideanreal (real_interval [0,1]))
                    (top1::A topology)`;
    EXISTS_TAC
     `prod_topology (subtopology euclideanreal (real_interval [0,1]))
                    (top2::C topology)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_PAIRED] THEN
  REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND] THEN
  REWRITE_TAC[CONTINUOUS_MAP_OF_FST; CONTINUOUS_MAP_OF_SND] THEN
  REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND]);;

lemma homotopic_with_product_topology:
   "\<And>k (tops::K=>A topology) (tops':K=>B topology) p q f g.
     (\<forall>i. i \<in> k
          \<Longrightarrow> homotopic_with (p i) (tops i,tops' i) (f i) (g i)) \<and>
     (\<forall>h. (\<forall>i. i \<in> k \<Longrightarrow> p i (h i)) \<Longrightarrow> q(\<lambda>x. (\<lambda>i\<in>k. h i (x i))))
     \<Longrightarrow> homotopic_with q (product_topology k tops,product_topology k tops')
                          (\<lambda>z. (\<lambda>i\<in>k. (f i) (z i)))
                          (\<lambda>z. (\<lambda>i\<in>k. (g i) (z i)))"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_TAC THEN
  REWRITE_TAC[homotopic_with] THEN
  GEN_REWRITE_TAC (LAND_CONV \<circ> ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `h::K=>real#A=>B` THEN DISCH_TAC THEN
  EXISTS_TAC `\<lambda>(t,z). (\<lambda>i\<in>k. (h::K=>real#A=>B) i (t,z i))` THEN
  ASM_SIMP_TAC[RESTRICTION_EXTENSION] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE] THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
  REWRITE_TAC[RESTRICTION_IN_EXTENSIONAL] THEN
  X_GEN_TAC `i::K` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [LAMBDA_PAIR_THM] THEN
  ASM_REWRITE_TAC[RESTRICTION] THEN REWRITE_TAC[LAMBDA_PAIR] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
   `prod_topology
     (subtopology euclideanreal (real_interval [0,1]))
     ((tops::K=>A topology) i)` THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_PAIRED] THEN
  REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_OF_SND] THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION]);;


subsection\<open>Homotopy equivalence of topological spaces\<close>


parse_as_infix("homotopy_equivalent_space",(12,"right"));;

let homotopy_equivalent_space = new_definition
 `(X::A topology) homotopy_equivalent_space (X':B topology) \<longleftrightarrow>
        \<exists>f g. continuous_map X X' f \<and>
              continuous_map X' X g \<and>
              homotopic_with (\<lambda>x. True) (X,X) (g \<circ> f) id \<and>
              homotopic_with (\<lambda>x. True) (X',X') (f \<circ> g) id`;;

lemma homeomorphic_imp_homotopy_equivalent_space:
   "\<And>(X::A topology) (X':B topology).
        X homeomorphic_space X'
        \<Longrightarrow> X homotopy_equivalent_space X'"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homeomorphic_space; homotopy_equivalent_space] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  REWRITE_TAC[homeomorphic_maps] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
  ASM_REWRITE_TAC[o_THM; I_THM] THEN
  ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]);;

lemma homotopy_equivalent_space_refl:
   "X homotopy_equivalent_space X"
oops
  SIMP_TAC[HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT_SPACE;
           HOMEOMORPHIC_SPACE_REFL]);;

lemma homotopy_equivalent_space_sym:
   "\<And>(X::A topology) (X':B topology).
        X homotopy_equivalent_space X' \<longleftrightarrow>
        X' homotopy_equivalent_space X"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopy_equivalent_space] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN CONV_TAC TAUT);;

lemma homotopy_equivalent_space_trans:
   "top1 homotopy_equivalent_space top2 \<and>
        top2 homotopy_equivalent_space top3
        \<Longrightarrow> top1 homotopy_equivalent_space top3"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopy_equivalent_space] THEN
  SIMP_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  SIMP_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`f1::A=>B`; `g1::B=>A`;
    `f2::B=>C`; `g2::C=>B`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(f2::B=>C) \<circ> (f1::A=>B)`;
    `(g1::B=>A) \<circ> (g2::C=>B)`] THEN
  REWRITE_TAC[IMAGE_o] THEN REPLICATE_TAC 2
   (CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]; ALL_TAC]) THEN
  CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THENL
   [EXISTS_TAC `(g1::B=>A) \<circ> id \<circ> (f1::A=>B)`;
    EXISTS_TAC `(f2::B=>C) \<circ> id \<circ> (g2::C=>B)`] THEN
  (CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[I_O_ID]]) THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN
  MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_LEFT THEN
  EXISTS_TAC `top2::B topology` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_ASSOC] THEN
  MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_RIGHT THEN
  EXISTS_TAC `top2::B topology` THEN ASM_REWRITE_TAC[]);;

lemma deformation_retraction_imp_homotopy_equivalent_space:
   "\<And>X X' r s.
        homotopic_with (\<lambda>x. True) (X,X) (s \<circ> r) id \<and>
        retraction_maps(X,X') (r,s)
        \<Longrightarrow> X homotopy_equivalent_space X'"
oops
  REWRITE_TAC[LEFT_FORALL_IMP_THM; I_DEF] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[homotopy_equivalent_space] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r::A=>B` THEN
  REWRITE_TAC[retraction_maps] THEN STRIP_TAC THEN
  EXISTS_TAC `s::B=>A` THEN ASM_REWRITE_TAC[I_DEF] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
  ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]);;

lemma deformation_retract_imp_homotopy_equivalent_space:
   "\<And>X X' (r::A=>A).
        homotopic_with (\<lambda>x. True) (X,X) r id \<and>
        retraction_maps(X,X') (r,id)
        \<Longrightarrow> X homotopy_equivalent_space X'"
oops
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DEFORMATION_RETRACTION_IMP_HOMOTOPY_EQUIVALENT_SPACE THEN
  MAP_EVERY EXISTS_TAC [`r::A=>A`; `id::A=>A`] THEN
  ASM_REWRITE_TAC[I_O_ID]);;

lemma deformation_retract_of_space:
   "s \<subseteq> topspace X \<and>
        (\<exists>r. homotopic_with (\<lambda>x. True) (X,X) id r \<and>
             retraction_maps(X,subtopology X s) (r,id)) \<longleftrightarrow>
        s retract_of_space X \<and>
        (\<exists>f. homotopic_with (\<lambda>x. True) (X,X) id f \<and>
             f ` (topspace X) \<subseteq> s)"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[retract_of_space; retraction_maps; I_DEF] THEN
  SIMP_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
  ASM_CASES_TAC `(s::A=>bool) \<subseteq> topspace X` THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `r::A=>A` THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `r::A=>A` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `r::A=>A` STRIP_ASSUME_TAC) MP_TAC) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `f::A=>A` THEN
    STRIP_TAC THEN EXISTS_TAC `r::A=>A` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC HOMOTOPIC_WITH_TRANS `f::A=>A` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC [`(r::A=>A) \<circ> (f::A=>A)`; `(r::A=>A) \<circ> (\<lambda>x. x)`] THEN
    ASM_SIMP_TAC[o_THM] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_LEFT THEN
    EXISTS_TAC `X::A topology` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN ASM_REWRITE_TAC[]]);;


(* Contractible spaces. The definition (which agrees with "contractible" on  *)
(* subsets of Euclidean space) is a little cryptic because we don't in fact  *)
text\<open> assume that the constant "a" is in the space. This forces the convention  \<close>
text\<open> that the empty space / set is contractible, avoiding some special cases.  \<close>


let contractible_space = new_definition
 `contractible_space (X::A topology) \<longleftrightarrow>
        \<exists>a. homotopic_with (\<lambda>x. True) (X,X) (\<lambda>x. x) (\<lambda>x. a)`;;

lemma contractible_space_empty:
   "topspace X = {} \<Longrightarrow> contractible_space X"
oops
  REWRITE_TAC[contractible_space; homotopic_with] THEN
  SIMP_TAC[CONTINUOUS_MAP_ON_EMPTY; TOPSPACE_PROD_TOPOLOGY; CROSS_EMPTY] THEN
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [`undefined::A`; `\<lambda>(t,x):real#A. if t = 0 then x else undefined`] THEN
  REWRITE_TAC[REAL_ARITH `\<not> (1 = 0)`]);;

lemma contractible_space_sing:
   "topspace X = {a} \<Longrightarrow> contractible_space X"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[contractible_space] THEN
  EXISTS_TAC `a::A` THEN REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC `(\<lambda>(t,x). if t = 0 then x else a):real#A=>A` THEN
  REWRITE_TAC[REAL_ARITH `\<not> (1 = 0)`] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `(\<lambda>z. a):real#A=>A` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST; IN_SING] THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
  SET_TAC[]);;

lemma contractible_space_subset_sing:
   "topspace X \<subseteq> {a} \<Longrightarrow> contractible_space X"
oops
  REWRITE_TAC[SET_RULE `s \<subseteq> {a} \<longleftrightarrow> s = {} \<or> s = {a}`] THEN
  MESON_TAC[CONTRACTIBLE_SPACE_EMPTY; CONTRACTIBLE_SPACE_SING]);;

lemma contractible_space_subtopology_sing:
   "contractible_space(subtopology X {a})"
oops
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTRACTIBLE_SPACE_SUBSET_SING THEN
  EXISTS_TAC `a::A` THEN REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; INTER_SUBSET]);;

lemma contractible_space:
   "contractible_space X \<longleftrightarrow>
        topspace X = {} \<or>
        \<exists>a. a \<in> topspace X \<and>
            homotopic_with (\<lambda>x. True) (X,X) (\<lambda>x. x) (\<lambda>x. a)"
oops
  GEN_TAC THEN ASM_CASES_TAC `topspace X::A=>bool = {}` THEN
  ASM_SIMP_TAC[CONTRACTIBLE_SPACE_EMPTY] THEN
  REWRITE_TAC[contractible_space] THEN EQ_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a::A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  REWRITE_TAC[continuous_map] THEN ASM SET_TAC[]);;

lemma contractible_imp_path_connected_space:
   "contractible_space X \<Longrightarrow> path_connected_space X"
oops
  GEN_TAC THEN
  ASM_CASES_TAC `topspace X::A=>bool = {}` THEN
  ASM_SIMP_TAC[PATH_CONNECTED_SPACE_TOPSPACE_EMPTY; CONTRACTIBLE_SPACE] THEN
  REWRITE_TAC[homotopic_with; LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a::A`; `h::real#A=>A`] THEN STRIP_TAC THEN
  REWRITE_TAC[PATH_CONNECTED_SPACE_IFF_PATH_COMPONENT] THEN
  SUBGOAL_THEN
   `\<forall>x::A. x \<in> topspace X \<Longrightarrow> path_component_of X x a`
  MP_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[PATH_COMPONENT_OF_TRANS; PATH_COMPONENT_OF_SYM]] THEN
  X_GEN_TAC `b::A` THEN DISCH_TAC THEN REWRITE_TAC[path_component_of] THEN
  EXISTS_TAC `(h::real#A=>A) \<circ> (\<lambda>x. x,b)` THEN
  ASM_REWRITE_TAC[o_THM] THEN REWRITE_TAC[pathin] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
   `prod_topology (subtopology euclideanreal ({0..1}))
                  (X::A topology)` THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST]);;

lemma contractible_imp_connected_space:
   "contractible_space X \<Longrightarrow> connected_space X"
oops
  MESON_TAC[CONTRACTIBLE_IMP_PATH_CONNECTED_SPACE;
            PATH_CONNECTED_IMP_CONNECTED_SPACE]);;

lemma contractible_space_alt:
   "contractible_space X \<longleftrightarrow>
        \<forall>a. a \<in> topspace X
            \<Longrightarrow> homotopic_with (\<lambda>x. True) (X,X) (\<lambda>x. x) (\<lambda>x. a)"
oops
  GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [CONTRACTIBLE_SPACE]) THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b::A` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
    REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN DISJ2_TAC THEN
    MATCH_MP_TAC PATH_CONNECTED_SPACE_IMP_PATH_COMPONENT_OF THEN
    ASM_SIMP_TAC[CONTRACTIBLE_IMP_PATH_CONNECTED_SPACE];
    DISCH_TAC THEN REWRITE_TAC[CONTRACTIBLE_SPACE] THEN ASM SET_TAC[]]);;

lemma nullhomotopic_through_contractible_space:
   "\<And>f (g::B=>C) top1 top2 top3.
        continuous_map top1 top2 f \<and>
        continuous_map top2 top3 g \<and>
        contractible_space top2
        \<Longrightarrow> \<exists>c. homotopic_with (\<lambda>h. True) (top1,top3) (g \<circ> f) (\<lambda>x. c)"
oops
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [contractible_space]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b::B` MP_TAC) THEN
  DISCH_THEN(MP_TAC \<circ> ISPECL [`g::B=>C`; `top3::C topology`] \<circ> MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_LEFT)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC \<circ> ISPECL [`f::A=>B`; `top1::A topology`] \<circ> MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_RIGHT)) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_TAC THEN
  EXISTS_TAC `(g::B=>C) b` THEN ASM_REWRITE_TAC[]);;

lemma nullhomotopic_into_contractible_space:
   "\<And>f top1 top2.
        continuous_map top1 top2 f \<and> contractible_space top2
        \<Longrightarrow> \<exists>c. homotopic_with (\<lambda>h. True) (top1,top2) f (\<lambda>x. c)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `f = (\<lambda>x. x) \<circ> f` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM; FUN_EQ_THM];
    MATCH_MP_TAC NULLHOMOTOPIC_THROUGH_CONTRACTIBLE_SPACE THEN
    EXISTS_TAC `top2::B topology` THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_ID]]);;

lemma nullhomotopic_from_contractible_space:
   "\<And>f top1 top2.
        continuous_map top1 top2 f \<and> contractible_space top1
        \<Longrightarrow> \<exists>c. homotopic_with (\<lambda>h. True) (top1,top2) f (\<lambda>x. c)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `f = f \<circ> (\<lambda>x. x)` SUBST1_TAC THENL
   [REWRITE_TAC[o_THM; FUN_EQ_THM];
    MATCH_MP_TAC NULLHOMOTOPIC_THROUGH_CONTRACTIBLE_SPACE THEN
    EXISTS_TAC `top1::A topology` THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_ID]]);;

lemma homotopic_through_contractible_space:
   "\<And>f (g::B=>C) f' g' top1 top2 top3.
        continuous_map top1 top2 f \<and>
        continuous_map top1 top2 f' \<and>
        continuous_map top2 top3 g \<and>
        continuous_map top2 top3 g' \<and>
        contractible_space top2 \<and> path_connected_space top3
        \<Longrightarrow> homotopic_with (\<lambda>h. True) (top1,top3) (g \<circ> f) (g' \<circ> f')"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f::A=>B`; `g::B=>C`;
    `top1::A topology`; `top2::B topology`; `top3::C topology`]
   NULLHOMOTOPIC_THROUGH_CONTRACTIBLE_SPACE) THEN
  MP_TAC(ISPECL
   [`f':A=>B`; `g':B=>C`;
    `top1::A topology`; `top2::B topology`; `top3::C topology`]
   NULLHOMOTOPIC_THROUGH_CONTRACTIBLE_SPACE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `c::C` THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  REWRITE_TAC[CONTINUOUS_MAP_CONST] THEN DISCH_TAC THEN
  X_GEN_TAC `d::C` THEN DISCH_THEN(fun th -> MP_TAC th THEN
     MP_TAC(MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS th)) THEN
  REWRITE_TAC[CONTINUOUS_MAP_CONST] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMOTOPIC_WITH_TRANS) THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_TRANS)) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN
  ASM_MESON_TAC[PATH_CONNECTED_SPACE_IFF_PATH_COMPONENT]);;

lemma homotopic_from_contractible_space:
   "\<And>f g X X'.
        continuous_map X X' f \<and> continuous_map X X' g \<and>
        contractible_space X \<and> path_connected_space X'
        \<Longrightarrow> homotopic_with (\<lambda>x. True) (X,X') f g"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\<lambda>x::A. x`; `f::A=>B`; `\<lambda>x::A. x`;
    `g::A=>B`; `X::A topology`; `X::A topology`;
    `X':B topology`] HOMOTOPIC_THROUGH_CONTRACTIBLE_SPACE) THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_ID; o_DEF; ETA_AX]);;

lemma homotopic_into_contractible_space:
   "\<And>f g X X'.
        continuous_map X X' f \<and> continuous_map X X' g \<and>
        contractible_space X'
        \<Longrightarrow> homotopic_with (\<lambda>x. True) (X,X') f g"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f::A=>B`; `\<lambda>x::B. x`;
    `g::A=>B`; `\<lambda>x::B. x`; `X::A topology`; `X':B topology`;
    `X':B topology`] HOMOTOPIC_THROUGH_CONTRACTIBLE_SPACE) THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_ID; o_DEF; ETA_AX] THEN
  ASM_SIMP_TAC[CONTRACTIBLE_IMP_PATH_CONNECTED_SPACE]);;

lemma homotopy_dominated_contractibility:
   "\<And>f g X X'.
        continuous_map X X' f \<and>
        continuous_map X' X g \<and>
        homotopic_with (\<lambda>x. True) (X',X') (f \<circ> g) id \<and>
        contractible_space X
        \<Longrightarrow> contractible_space X'"
oops
  REPEAT GEN_TAC THEN SIMP_TAC[contractible_space; I_DEF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f::A=>B`; `X::A topology`; `X':B topology`]
        NULLHOMOTOPIC_FROM_CONTRACTIBLE_SPACE) THEN
  ASM_REWRITE_TAC[contractible_space; I_DEF] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b::B` THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `f \<circ> (g::B=>A)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\<lambda>x. (b::B)) = (\<lambda>x. b) \<circ> (g::B=>A)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_RIGHT THEN
  EXISTS_TAC `X::A topology` THEN ASM_REWRITE_TAC[]);;

lemma homotopy_equivalent_space_contractibility:
   "\<And>(X::A topology) (X':B topology).
        X homotopy_equivalent_space X'
        \<Longrightarrow> (contractible_space X \<longleftrightarrow> contractible_space X')"
oops
  REWRITE_TAC[homotopy_equivalent_space] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
   (REWRITE_RULE[CONJ_ASSOC] HOMOTOPY_DOMINATED_CONTRACTIBILITY)) THEN
  ASM_MESON_TAC[]);;

lemma homeomorphic_space_contractibility:
   "\<And>(X::A topology) (X':B topology).
        X homeomorphic_space X'
        \<Longrightarrow> (contractible_space X \<longleftrightarrow> contractible_space X')"
oops
  MESON_TAC[HOMOTOPY_EQUIVALENT_SPACE_CONTRACTIBILITY;
            HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT_SPACE]);;

lemma contractible_eq_homotopy_equivalent_singleton_subtopology:
   "contractible_space X \<longleftrightarrow>
        topspace X = {} \<or>
        \<exists>a. a \<in> topspace X \<and>
            X homotopy_equivalent_space (subtopology X {a})"
oops
  GEN_TAC THEN ASM_CASES_TAC `topspace X::A=>bool = {}` THEN
  ASM_SIMP_TAC[CONTRACTIBLE_SPACE_EMPTY] THEN EQ_TAC THENL
   [ASM_REWRITE_TAC[CONTRACTIBLE_SPACE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `a::A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[homotopy_equivalent_space] THEN
    MAP_EVERY EXISTS_TAC [`(\<lambda>x. a):A=>A`; `(\<lambda>x. x):A=>A`] THEN
    ASM_SIMP_TAC[o_DEF; CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID;
      IN_INTER; CONTINUOUS_MAP_CONST; TOPSPACE_SUBTOPOLOGY; IN_SING] THEN
    ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
    ASM_REWRITE_TAC[I_DEF] THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `a::A` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(SUBST1_TAC \<circ>
      MATCH_MP HOMOTOPY_EQUIVALENT_SPACE_CONTRACTIBILITY) THEN
    MATCH_MP_TAC CONTRACTIBLE_SPACE_SING THEN
    EXISTS_TAC `a::A` THEN ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    ASM SET_TAC[]]);;

lemma contractible_space_retraction_map_image:
   "\<And>X X' f.
        retraction_map X X' f \<and> contractible_space X
        \<Longrightarrow> contractible_space X'"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; retraction_map; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g::B=>A` THEN REWRITE_TAC[retraction_maps] THEN STRIP_TAC THEN
  REWRITE_TAC[contractible_space; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a::A` THEN STRIP_TAC THEN EXISTS_TAC `f a` THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  EXISTS_TAC `f \<circ> (\<lambda>x. x) \<circ> (g::B=>A)` THEN
  EXISTS_TAC `f \<circ> (\<lambda>x. a) \<circ> (g::B=>A)` THEN
  ASM_SIMP_TAC[o_THM] THEN
  MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_LEFT THEN
  EXISTS_TAC `X::A topology` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_MAP_RIGHT THEN
  EXISTS_TAC `X::A topology` THEN ASM_REWRITE_TAC[]);;

lemma contractible_space_prod_topology:
   "\<And>(top1::A topology) (top2::B topology).
        contractible_space(prod_topology top1 top2) \<longleftrightarrow>
        topspace top1 = {} \<or> topspace top2 = {} \<or>
        contractible_space top1 \<and> contractible_space top2"
oops
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `topspace top1::A=>bool = {}` THEN
  ASM_SIMP_TAC[CONTRACTIBLE_SPACE_EMPTY; TOPSPACE_PROD_TOPOLOGY;
               CROSS_EQ_EMPTY] THEN
  ASM_CASES_TAC `topspace top2::B=>bool = {}` THEN
  ASM_SIMP_TAC[CONTRACTIBLE_SPACE_EMPTY; TOPSPACE_PROD_TOPOLOGY;
               CROSS_EQ_EMPTY] THEN
  EQ_TAC THENL
   [DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ]
     CONTRACTIBLE_SPACE_RETRACTION_MAP_IMAGE)
    THENL [EXISTS_TAC `fst::A#B=>A`; EXISTS_TAC `snd::A#B=>B`] THEN
    ASM_REWRITE_TAC[RETRACTION_MAP_FST; RETRACTION_MAP_SND];
    ASM_REWRITE_TAC[CONTRACTIBLE_SPACE; TOPSPACE_PROD_TOPOLOGY;
                    CROSS_EQ_EMPTY; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[IN_CROSS; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a::A` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b::B` THEN
    ASM_CASES_TAC `(a::A) \<in> topspace top1` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(b::B) \<in> topspace top2` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP (ONCE_REWRITE_RULE[TAUT
     `p \<and> q \<and> r \<Longrightarrow> s \<longleftrightarrow> p \<and> q \<Longrightarrow> r \<Longrightarrow> s`]
    HOMOTOPIC_WITH_PROD_TOPOLOGY)) THEN SIMP_TAC[]]);;

lemma contractible_space_product_topology:
   "\<And>k (tops::K=>A topology).
        contractible_space(product_topology k tops) \<longleftrightarrow>
        topspace (product_topology k tops) = {} \<or>
        \<forall>i. i \<in> k \<Longrightarrow> contractible_space(tops i)"
oops
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `topspace(product_topology k (tops::K=>A topology)) = {}` THEN
  ASM_SIMP_TAC[CONTRACTIBLE_SPACE_EMPTY] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i::K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
     CONTRACTIBLE_SPACE_RETRACTION_MAP_IMAGE)) THEN
    EXISTS_TAC `\<lambda>x::K=>A. x i` THEN
    ASM_SIMP_TAC[RETRACTION_MAP_PRODUCT_PROJECTION];
    REWRITE_TAC[contractible_space] THEN
    GEN_REWRITE_TAC (LAND_CONV \<circ> BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `a::K=>A` THEN DISCH_TAC THEN
    EXISTS_TAC `RESTRICTION k (a::K=>A)` THEN FIRST_X_ASSUM
     (MP_TAC \<circ> ISPEC `\<lambda>z:(K=>A)->(K=>A). True` \<circ> MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOTOPIC_WITH_PRODUCT_TOPOLOGY)) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        HOMOTOPIC_WITH_EQ) THEN
    REWRITE_TAC[ETA_AX] THEN REWRITE_TAC[FUN_EQ_THM] THEN
    REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; PiE; IN_ELIM_THM] THEN
    REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM; RESTRICTION] THEN MESON_TAC[]]);;

lemma contractible_space_subtopology_euclideanreal:
   "contractible_space(subtopology euclideanreal s) \<longleftrightarrow> is_interval s"
oops
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC \<circ> MATCH_MP CONTRACTIBLE_IMP_PATH_CONNECTED_SPACE) THEN
    REWRITE_TAC[GSYM PATH_CONNECTED_IN_TOPSPACE] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    REWRITE_TAC[PATH_CONNECTED_IN_SUBTOPOLOGY; SUBSET_REFL] THEN
    REWRITE_TAC[PATH_CONNECTED_IN_EUCLIDEANREAL];
    ALL_TAC] THEN
  ASM_CASES_TAC `s::real=>bool = {}` THEN
  ASM_SIMP_TAC[CONTRACTIBLE_SPACE_EMPTY;
               TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `z::real`) THEN REWRITE_TAC[is_interval] THEN
  STRIP_TAC THEN REWRITE_TAC[contractible_space; homotopic_with] THEN
  EXISTS_TAC `z::real` THEN
  EXISTS_TAC `\<lambda>(t::real,x). (1 - t) * x + t * z` THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [REWRITE_TAC[LAMBDA_PAIR; GSYM SUBTOPOLOGY_CROSS] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN
    SIMP_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
             CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND;
             CONTINUOUS_MAP_REAL_SUB];
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`t::real`; `x::real`] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`min x z::real`; `max z x::real`] THEN
    GEN_REWRITE_TAC id [CONJ_ASSOC] THEN CONJ_TAC THENL
     [REWRITE_TAC[real_max; real_min] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_CONVEX_BOUNDS_LE THEN ASM_REAL_ARITH_TAC]);;

lemma contractible_space_euclideanreal:
 (`contractible_space euclideanreal"
oops
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
  REWRITE_TAC[CONTRACTIBLE_SPACE_SUBTOPOLOGY_EUCLIDEANREAL] THEN
  REWRITE_TAC[IS_REALINTERVAL_UNIV]);;


(* Completely metrizable (a.k.a. "topologically complete") spaces.           *)


let completely_metrizable_space = new_definition
 `completely_metrizable_space X \<longleftrightarrow>
  \<exists>m. mcomplete \<and> X = mtopology`;;

lemma completely_metrizable_imp_metrizable_space:
   "completely_metrizable_space X \<Longrightarrow> metrizable_space X"
oops
  REWRITE_TAC[completely_metrizable_space; metrizable_space] THEN
  MESON_TAC[]);;

lemma forall_mcomplete_topology:
   "(\<forall>m::A metric. mcomplete \<Longrightarrow> P mtopology (M)) \<longleftrightarrow>
       \<forall>X. completely_metrizable_space X \<Longrightarrow> P X (topspace X)"
oops
  SIMP_TAC[completely_metrizable_space; LEFT_IMP_EXISTS_THM;
           TOPSPACE_MTOPOLOGY] THEN
  MESON_TAC[]);;

lemma forall_completely_metrizable_space:
 (`(\<forall>X. completely_metrizable_space X \<Longrightarrow> P X (topspace X)) \<longleftrightarrow>
   (\<forall>m::A metric. mcomplete \<Longrightarrow> P mtopology (M))"
oops
  SIMP_TAC[completely_metrizable_space; LEFT_IMP_EXISTS_THM;
           TOPSPACE_MTOPOLOGY] THEN
  MESON_TAC[]);;

lemma exists_completely_metrizable_space:
   "(\<exists>X. completely_metrizable_space X \<and> P X (topspace X)) \<longleftrightarrow>
       (\<exists>m::A metric.mcomplete \<and>  P mtopology (M))"
oops
  REWRITE_TAC[MESON[] `(\<exists>x. P x \<and> Q x) \<longleftrightarrow> \<not> (\<forall>x. P x \<Longrightarrow> \<not> Q x)`] THEN
  REWRITE_TAC[FORALL_MCOMPLETE_TOPOLOGY] THEN MESON_TAC[]);;

lemma completely_metrizable_space_mtopology:
   "mcomplete \<Longrightarrow> completely_metrizable_spacemtopology"
oops
  REWRITE_TAC[FORALL_MCOMPLETE_TOPOLOGY]);;

lemma completely_metrizable_space_discrete_topology:
   "\<And>u::A=>bool. completely_metrizable_space(discrete_topology u)"
oops
  REWRITE_TAC[completely_metrizable_space] THEN
  MESON_TAC[MTOPOLOGY_DISCRETE_METRIC; MCOMPLETE_DISCRETE_METRIC]);;

lemma completely_metrizable_space_euclideanreal:
 (`completely_metrizable_space euclideanreal"
oops
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
  MATCH_MP_TAC COMPLETELY_METRIZABLE_SPACE_MTOPOLOGY THEN
  REWRITE_TAC[MCOMPLETE_REAL_EUCLIDEAN_METRIC]);;

lemma completely_metrizable_space_closedin:
   "completely_metrizable_space X \<and> closedin X s
        \<Longrightarrow> completely_metrizable_space(subtopology X s)"
oops
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[GSYM FORALL_MCOMPLETE_TOPOLOGY] THEN
  REWRITE_TAC[GSYM MTOPOLOGY_SUBMETRIC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLETELY_METRIZABLE_SPACE_MTOPOLOGY THEN
  MATCH_MP_TAC CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE THEN ASM_REWRITE_TAC[]);;

lemma homeomorphic_completely_metrizable_space:
   "\<And>(X::A topology) (X':B topology).
        X homeomorphic_space X'
        \<Longrightarrow> (completely_metrizable_space X \<longleftrightarrow>
             completely_metrizable_space X')"
oops
  lemma lemma:
   "\<And>(X::A topology) (X':B topology).
          X homeomorphic_space X'
          \<Longrightarrow> completely_metrizable_space X
              \<Longrightarrow> completely_metrizable_space X'"
oops
    REPEAT GEN_TAC THEN REWRITE_TAC[completely_metrizable_space] THEN
    REWRITE_TAC[homeomorphic_space; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f::A=>B`; `g::B=>A`] THEN DISCH_TAC THEN
    X_GEN_TAC `m::A metric` THEN DISCH_THEN(STRIP_ASSUME_TAC \<circ> GSYM) THEN
    ABBREV_TAC
     `m' = metric(topspace X',\<lambda>(x,y). d m ((g::B=>A) x,g y))` THEN
    MP_TAC(ISPECL [`g::B=>A`; `m::A metric`; `topspace X':B=>bool`]
          METRIC_INJECTIVE_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [homeomorphic_maps]) THEN
      EXPAND_TAC "X" THEN
      REWRITE_TAC[continuous_map; TOPSPACE_MTOPOLOGY] THEN SET_TAC[];
      STRIP_TAC THEN EXISTS_TAC `m':B metric`] THEN
    MATCH_MP_TAC(TAUT `(q \<Longrightarrow> p) \<and> q \<Longrightarrow> p \<and> q`) THEN CONJ_TAC THENL
     [DISCH_THEN(ASSUME_TAC \<circ> SYM) THEN
      UNDISCH_TAC `mcomplete(m::A metric)` THEN
      ASM_REWRITE_TAC[mcomplete; MCauchy; GSYM TOPSPACE_MTOPOLOGY] THEN
      DISCH_TAC THEN X_GEN_TAC `x::num=>B` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(g::B=>A) \<circ> (x::num=>B)`) THEN
      ASM_REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC \<circ>
        GEN_REWRITE_RULE id [homeomorphic_maps]) THEN
      ANTS_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[continuous_map]) THEN ASM SET_TAC[];
        DISCH_THEN(X_CHOOSE_TAC `y::A`)] THEN
      EXISTS_TAC `f y` THEN
      SUBGOAL_THEN `x = f \<circ> (g::B=>A) \<circ> (x::num=>B)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[continuous_map]) THEN ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_MAP_LIMIT THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_MTOPOLOGY] THEN
    FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [HOMEOMORPHIC_MAPS_SYM]) THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP HOMEOMORPHIC_MAPS_IMP_MAP) THEN
    DISCH_THEN(fun th ->
      REWRITE_TAC[MATCH_MP HOMEOMORPHIC_MAP_OPENNESS_EQ th]) THEN
    X_GEN_TAC `v::B=>bool` THEN
    ASM_CASES_TAC `(v::B=>bool) \<subseteq> topspace X'` THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN
    ASM_REWRITE_TAC[GSYM TOPSPACE_MTOPOLOGY; \<subseteq>; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[IN_MBALL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphic_maps; continuous_map]) THEN
    MATCH_MP_TAC(TAUT `p \<and> (q \<longleftrightarrow> r) \<Longrightarrow> (p \<and> q \<longleftrightarrow> r)`) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; EQ_TAC] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `b::B` THEN
    ASM_CASES_TAC `(b::B) \<in> v` THEN
    ASM_REWRITE_TAC[GSYM TOPSPACE_MTOPOLOGY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r::real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [X_GEN_TAC `y::B` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(g::B=>A) y`) THEN ASM SET_TAC[];
      ASM SET_TAC[]])
in

  REPEAT STRIP_TAC THEN EQ_TAC THEN MATCH_MP_TAC lemma THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SPACE_SYM]);;

lemma completely_metrizable_space_retraction_map_image:
   "\<And>X X' r.
        retraction_map X X' r \<and> completely_metrizable_space X
        \<Longrightarrow> completely_metrizable_space X'"
oops
  MATCH_MP_TAC WEAKLY_HEREDITARY_IMP_RETRACTIVE_PROPERTY THEN
  REWRITE_TAC[HOMEOMORPHIC_COMPLETELY_METRIZABLE_SPACE] THEN
  REWRITE_TAC[COMPLETELY_METRIZABLE_SPACE_CLOSED_IN] THEN
  MESON_TAC[COMPLETELY_METRIZABLE_IMP_METRIZABLE_SPACE;
            METRIZABLE_IMP_HAUSDORFF_SPACE]);;


text\<open> Product metric. For the nicest fit with the main Euclidean theories, we   \<close>
text\<open> make this the Euclidean product, though others would work topologically.  \<close>


let prod_metric = new_definition
 `prod_metric m1 m2 =
  metric((mspace m1 \<times> mspace m2):A#B=>bool,
         \<lambda>((x,y),(x',y')).
            sqrt(d x x' ^ 2 + d y y' ^ 2))`;;

lemma prod_metric:
 (`(!(m1::A metric) (m2::B metric).
      mspace(prod_metric m1 m2) = mspace m1 \<times> mspace m2) \<and>
   (!(m1::A metric) (m2::B metric).
        d(prod_metric m1 m2) =
        \<lambda>((x,y),(x',y')).
            sqrt(d x x' ^ 2 + d y y' ^ 2))"
oops
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV \<circ> LAND_CONV) [mspace] THEN
  GEN_REWRITE_TAC (RAND_CONV \<circ> LAND_CONV) [d] THEN
  REWRITE_TAC[PAIR; GSYM PAIR_EQ] THEN REWRITE_TAC[prod_metric] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 metric_tybij)] THEN
  REWRITE_TAC[is_metric_space; FORALL_PAIR_THM; IN_CROSS] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[SQRT_POS_LE; REAL_LE_ADD; REAL_LE_POW_2];
    REWRITE_TAC[PAIR_EQ; SQRT_EQ_0] THEN SIMP_TAC[REAL_LE_POW_2; REAL_ARITH
     `0 \<le> x \<and> 0 \<le> y \<Longrightarrow> (x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0)`] THEN
    SIMP_TAC[REAL_POW_EQ_0; MDIST_0] THEN CONV_TAC NUM_REDUCE_CONV;
    SIMP_TAC[MDIST_SYM];
    MAP_EVERY X_GEN_TAC [`x1::A`; `y1::B`; `x2::A`; `y2::B`; `x3::A`; `y3::B`] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_LSQRT THEN
    ASM_SIMP_TAC[REAL_LE_ADD; SQRT_POS_LE; REAL_LE_POW_2] THEN
    REWRITE_TAC[REAL_ARITH
     `(a + b::real) ^ 2 = (a ^ 2 + b ^ 2) + 2 * a * b`] THEN
    SIMP_TAC[SQRT_POW_2; REAL_LE_ADD; REAL_LE_POW_2] THEN
    TRANS_TAC REAL_LE_TRANS
     `(d m1 (x1::A,x2) + d x2 x3) ^ 2 +
      (d m2 (y1::B,y2) + d y2 y3) ^ 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_MESON_TAC[MDIST_POS_LE; MDIST_TRIANGLE];
      REWRITE_TAC[REAL_ARITH
       `(x1 + x2) ^ 2 + (y1 + y2) ^ 2 \<le>
        ((x1 ^ 2 + y1 ^ 2) + (x2 ^ 2 + y2 ^ 2)) + 2 * b \<longleftrightarrow>
        x1 * x2 + y1 * y2 \<le> b`] THEN
      REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
      REWRITE_TAC[REAL_LE_POW_2; REAL_ARITH
        `(x1 * x2 + y1 * y2) ^ 2 \<le>
         (x1 ^ 2 + y1 ^ 2) * (x2 ^ 2 + y2 ^ 2) \<longleftrightarrow>
         0 \<le> (x1 * y2 - x2 * y1) ^ 2`]]]);;

lemma component_le_prod_metric:
   "d x1 x2 \<le> d (prod_metric m1 m2) ((x1,y1),(x2,y2)) \<and>
        d y1 y2 \<le> d (prod_metric m1 m2) ((x1,y1),(x2,y2))"
oops
  REPEAT GEN_TAC THEN CONJ_TAC THEN REWRITE_TAC[PROD_METRIC] THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN REWRITE_TAC[REAL_LE_ADDR; REAL_LE_ADDL] THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

lemma prod_metric_le_components:
   "x1 \<in> mspace m1 \<and> x2 \<in> mspace m1 \<and>
        y1 \<in> mspace m2 \<and> y2 \<in> mspace m2
        \<Longrightarrow> d (prod_metric m1 m2) ((x1,y1),(x2,y2))
            \<le> d x1 x2 + d y1 y2"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[PROD_METRIC] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN ASM_SIMP_TAC[REAL_LE_ADD; MDIST_POS_LE;
   REAL_ARITH `x ^ 2 + y ^ 2 \<le> (x + y) ^ 2 \<longleftrightarrow> 0 \<le> x * y`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; MDIST_POS_LE]);;

lemma mball_prod_metric_subset:
   "mball (prod_metric m1 m2) ((x,y),r) \<subseteq>
        mball x r \<times> mball y r"
oops
  REWRITE_TAC[\<subseteq>; FORALL_PAIR_THM; IN_MBALL; IN_CROSS;
              CONJUNCT1 PROD_METRIC] THEN
  MESON_TAC[COMPONENT_LE_PROD_METRIC; REAL_LET_TRANS]);;

lemma mcball_prod_metric_subset:
   "mcball (prod_metric m1 m2) ((x,y),r) \<subseteq>
        mcball m1 (x,r) \<times> mcball m2 (y,r)"
oops
  REWRITE_TAC[\<subseteq>; FORALL_PAIR_THM; IN_MCBALL; IN_CROSS;
              CONJUNCT1 PROD_METRIC] THEN
  MESON_TAC[COMPONENT_LE_PROD_METRIC; REAL_LE_TRANS]);;

lemma mball_subset_prod_metric:
   "\<And>m1 m2 x::A y::B r r'.
        mball x r \<times> mball y r'
        \<subseteq> mball (prod_metric m1 m2) ((x,y),r + r')"
oops
  REWRITE_TAC[\<subseteq>; FORALL_PAIR_THM; IN_MBALL; IN_CROSS;
              CONJUNCT1 PROD_METRIC] THEN
  MESON_TAC[REAL_ARITH `x \<le> y + z \<and> y < a \<and> z < b \<Longrightarrow> x < a + b`;
            PROD_METRIC_LE_COMPONENTS]);;

lemma mcball_subset_prod_metric:
   "\<And>m1 m2 x::A y::B r r'.
        mcball m1 (x,r) \<times> mcball m2 (y,r')
        \<subseteq> mcball (prod_metric m1 m2) ((x,y),r + r')"
oops
  REWRITE_TAC[\<subseteq>; FORALL_PAIR_THM; IN_MCBALL; IN_CROSS;
              CONJUNCT1 PROD_METRIC] THEN
  MESON_TAC[REAL_ARITH `x \<le> y + z \<and> y \<le> a \<and> z \<le> b \<Longrightarrow> x \<le> a + b`;
            PROD_METRIC_LE_COMPONENTS]);;

lemma mtopology_prod_metric:
   "\<And>(m1::A metric) (m2::B metric).
        mtopology(prod_metric m1 m2) =
        prod_topology (mtopology m1) (mtopology m2)"
oops
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[prod_topology] THEN
  MATCH_MP_TAC TOPOLOGY_BASE_UNIQUE THEN
  REWRITE_TAC[SET_RULE `GSPEC a x \<longleftrightarrow> x \<in> GSPEC a`] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC; OPEN_IN_MTOPOLOGY; PROD_METRIC] THEN
    MAP_EVERY X_GEN_TAC [`s::A=>bool`; `t::B=>bool`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_CROSS; FORALL_PAIR_THM; IN_CROSS] THEN
    MAP_EVERY X_GEN_TAC [`x::A`; `y::B`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `y::B`) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `x::A`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r1::real` THEN STRIP_TAC THEN
    X_GEN_TAC `r2::real` THEN STRIP_TAC THEN
    EXISTS_TAC `min r1 r2::real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    W(MP_TAC \<circ> PART_MATCH lhand MBALL_PROD_METRIC_SUBSET \<circ> lhand \<circ> snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
    REWRITE_TAC[SUBSET_CROSS] THEN REPEAT DISJ2_TAC THEN CONJ_TAC;
    REWRITE_TAC[FORALL_PAIR_THM; EXISTS_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`u::A#B=>bool`; `x::A`; `y::B`] THEN
    GEN_REWRITE_TAC (LAND_CONV \<circ> ONCE_DEPTH_CONV) [OPEN_IN_MTOPOLOGY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC \<circ> SPEC `(x,y):A#B`)) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `r::real` THEN STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`mball m1 (x::A,r / 2)`; `mball m2 (y::B,r / 2)`] THEN
    FIRST_ASSUM(MP_TAC \<circ> SPEC `(x,y):A#B` \<circ> REWRITE_RULE[\<subseteq>] \<circ>
     GEN_REWRITE_RULE RAND_CONV [CONJUNCT1 PROD_METRIC]) THEN
    ASM_REWRITE_TAC[IN_CROSS] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[OPEN_IN_MBALL; IN_CROSS; CENTRE_IN_MBALL; REAL_HALF] THEN
    W(MP_TAC \<circ> PART_MATCH lhand MBALL_SUBSET_PROD_METRIC \<circ> lhand \<circ> snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)) THEN
  MATCH_MP_TAC MBALL_SUBSET_CONCENTRIC THEN REAL_ARITH_TAC);;

lemma submetric_prod_metric:
   "\<And>m1 m2 s::A=>bool t::B=>bool.
        submetric (prod_metric m1 m2) (s \<times> t) =
        prod_metric (submetric1 s) (submetric2 t)"
oops
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [prod_metric] THEN
  GEN_REWRITE_TAC LAND_CONV [submetric] THEN
  REWRITE_TAC[SUBMETRIC; PROD_METRIC; INTER_CROSS]);;

lemma metrizable_space_prod_topology:
   "metrizable_space (prod_topology top1 top2) \<longleftrightarrow>
        topspace(prod_topology top1 top2) = {} \<or>
        metrizable_space top1 \<and> metrizable_space top2"
oops
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `topspace(prod_topology top1 top2):A#B=>bool = {}` THENL
   [ASM_MESON_TAC[SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY_EMPTY;
                  METRIZABLE_SPACE_DISCRETE_TOPOLOGY];
    ASM_REWRITE_TAC[]] THEN
  EQ_TAC THENL
   [ALL_TAC; MESON_TAC[MTOPOLOGY_PROD_METRIC; metrizable_space]] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS] THEN
  MAP_EVERY X_GEN_TAC [`a::A`; `b::B`] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP METRIZABLE_SPACE_SUBTOPOLOGY) THENL
   [DISCH_THEN(MP_TAC \<circ> SPEC `(topspace top1 \<times> {b}):A#B=>bool`);
    DISCH_THEN(MP_TAC \<circ> SPEC `({a} \<times> topspace top2):A#B=>bool`)] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HOMEOMORPHIC_METRIZABLE_SPACE THEN
  REWRITE_TAC[SUBTOPOLOGY_CROSS; SUBTOPOLOGY_TOPSPACE] THENL
   [MATCH_MP_TAC PROD_TOPOLOGY_HOMEOMORPHIC_SPACE_LEFT;
    MATCH_MP_TAC PROD_TOPOLOGY_HOMEOMORPHIC_SPACE_RIGHT] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

lemma MCauchy_prod_metric:
   "\<And>m1 m2 x::num=>A#B.
        MCauchy (prod_metric m1 m2) x \<longleftrightarrow>
        MCauchy m1 (fst \<circ> x) \<and> MCauchy m2 (snd \<circ> x)"
oops
  REWRITE_TAC[FORALL_PAIR_FUN_THM] THEN MAP_EVERY X_GEN_TAC
   [`m1::A metric`; `m2::B metric`; `a::num=>A`; `b::num=>B`] THEN
  REWRITE_TAC[MCauchy; CONJUNCT1 PROD_METRIC; IN_CROSS; o_DEF] THEN
  ASM_CASES_TAC `\<forall>n. (a::num=>A) n \<in> mspace m1` THEN
  ASM_REWRITE_TAC[FORALL_AND_THM] THEN
  ASM_CASES_TAC `\<forall>n. (b::num=>B) n \<in> mspace m2` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
   [ASM_MESON_TAC[COMPONENT_LE_PROD_METRIC; REAL_LET_TRANS];
    DISCH_TAC THEN X_GEN_TAC `e::real` THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (MP_TAC \<circ> SPEC `e / 2`)) THEN
  ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `M::num` THEN DISCH_TAC THEN X_GEN_TAC `N::num` THEN DISCH_TAC THEN
  EXISTS_TAC `MAX M N` THEN
  REWRITE_TAC[ARITH_RULE `MAX M N \<le> n \<longleftrightarrow> M \<le> n \<and> N \<le> n`] THEN
  MAP_EVERY X_GEN_TAC [`m::num`; `n::num`] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`m::num`; `n::num`])) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `z \<le> x + y \<Longrightarrow> x < e / 2 \<Longrightarrow> y < e / 2 \<Longrightarrow> z < e`) THEN
  ASM_MESON_TAC[PROD_METRIC_LE_COMPONENTS; REAL_ADD_SYM]);;

lemma mcomplete_prod_metric:
   "\<And>(m1::A metric) (m2::B metric).
        mcomplete (prod_metric m1 m2) \<longleftrightarrow>
        mspace m1 = {} \<or> mspace m2 = {} \<or> mcomplete m1 \<and> mcomplete m2"
oops
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`mspace m1::A=>bool = {}`; `mspace m2::B=>bool = {}`] THEN
  ASM_SIMP_TAC[MCOMPLETE_EMPTY_MSPACE; CONJUNCT1 PROD_METRIC; CROSS_EMPTY] THEN
  REWRITE_TAC[mcomplete; CAUCHY_IN_PROD_METRIC] THEN
  REWRITE_TAC[MTOPOLOGY_PROD_METRIC; LIMIT_PAIRWISE; EXISTS_PAIR_THM] THEN
  EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN DISCH_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `x::num=>A` THEN DISCH_TAC THEN
    UNDISCH_TAC `\<not> (mspace m2::B=>bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y::B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(\<lambda>n. (x n,y)):num=>A#B`);
    X_GEN_TAC `y::num=>B` THEN DISCH_TAC THEN
    UNDISCH_TAC `\<not> (mspace m1::A=>bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x::A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(\<lambda>n. (x,y n)):num=>A#B`)] THEN
  ASM_REWRITE_TAC[o_DEF; ETA_AX; CAUCHY_IN_CONST] THEN MESON_TAC[]);;

lemma completely_metrizable_space_prod_topology:
   "completely_metrizable_space (prod_topology top1 top2) \<longleftrightarrow>
        topspace(prod_topology top1 top2) = {} \<or>
        completely_metrizable_space top1 \<and> completely_metrizable_space top2"
oops
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `topspace(prod_topology top1 top2):A#B=>bool = {}` THENL
   [ASM_MESON_TAC[SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY_EMPTY;
                  COMPLETELY_METRIZABLE_SPACE_DISCRETE_TOPOLOGY];
    ASM_REWRITE_TAC[]] THEN
  EQ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[completely_metrizable_space] THEN
    METIS_TAC[MCOMPLETE_PROD_METRIC; MTOPOLOGY_PROD_METRIC]] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS] THEN
  MAP_EVERY X_GEN_TAC [`a::A`; `b::B`] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> MATCH_MP METRIZABLE_IMP_HAUSDORFF_SPACE \<circ>
     MATCH_MP COMPLETELY_METRIZABLE_IMP_METRIZABLE_SPACE) THEN
  REWRITE_TAC[HAUSDORFF_SPACE_PROD_TOPOLOGY; TOPSPACE_PROD_TOPOLOGY] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_CROSS; FORALL_PAIR_THM] THEN
  (STRIP_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP
   (REWRITE_RULE[IMP_CONJ] COMPLETELY_METRIZABLE_SPACE_CLOSED_IN))
  THENL
   [DISCH_THEN(MP_TAC \<circ> SPEC `(topspace top1 \<times> {b}):A#B=>bool`);
    DISCH_THEN(MP_TAC \<circ> SPEC `({a} \<times> topspace top2):A#B=>bool`)] THEN
  REWRITE_TAC[CLOSED_IN_CROSS; CLOSED_IN_TOPSPACE] THEN
  ASM_SIMP_TAC[CLOSED_IN_HAUSDORFF_SING] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HOMEOMORPHIC_COMPLETELY_METRIZABLE_SPACE THEN
  REWRITE_TAC[SUBTOPOLOGY_CROSS; SUBTOPOLOGY_TOPSPACE] THENL
   [MATCH_MP_TAC PROD_TOPOLOGY_HOMEOMORPHIC_SPACE_LEFT;
    MATCH_MP_TAC PROD_TOPOLOGY_HOMEOMORPHIC_SPACE_RIGHT] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

lemma mbounded_cross:
   "\<And>(m1::A metric) (m2::B metric) s t.
        mbounded (prod_metric m1 m2) (s \<times> t) \<longleftrightarrow>
        s = {} \<or> t = {} \<or> mbounded m1 s \<and> mbounded m2 t"
oops
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`s::A=>bool = {}`; `t::B=>bool = {}`] THEN
  ASM_REWRITE_TAC[MBOUNDED_EMPTY; CROSS_EMPTY] THEN
  REWRITE_TAC[mbounded; EXISTS_PAIR_THM] THEN MATCH_MP_TAC(MESON[]
   `(\<forall>x y. P x y \<longleftrightarrow> Q x \<and> R y)
    \<Longrightarrow> ((\<exists>x y. P x y) \<longleftrightarrow> (\<exists>x. Q x) \<and> (\<exists>y. R y))`) THEN
  MAP_EVERY X_GEN_TAC [`x::A`; `y::B`] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_TAC `r::real`) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
    REPEAT(EXISTS_TAC `r::real`) THEN
    MATCH_MP_TAC(MESON[SUBSET_CROSS]
     `s \<times> t \<subseteq> u \<times> v \<and> (s \<noteq> {}) \<and> (t \<noteq> {})
      \<Longrightarrow> s \<subseteq> u \<and> t \<subseteq> v`) THEN
    ASM_MESON_TAC[SUBSET_TRANS; MCBALL_PROD_METRIC_SUBSET];
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `r1::real`) (X_CHOOSE_TAC `r2::real`)) THEN
    EXISTS_TAC `r1 + r2::real` THEN
    W(MP_TAC \<circ> PART_MATCH rand MCBALL_SUBSET_PROD_METRIC \<circ> rand \<circ> snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
    ASM_REWRITE_TAC[SUBSET_CROSS]]);;

lemma mbounded_prod_metric:
   "\<And>(m1::A metric) (m2::B metric) u.
        mbounded (prod_metric m1 m2) u \<longleftrightarrow>
        mbounded m1 (fst ` u) \<and> mbounded m2 (snd ` u)"
oops
  REPEAT GEN_TAC THEN  EQ_TAC THENL
   [REWRITE_TAC[mbounded; \<subseteq>; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN MATCH_MP_TAC(MESON[]
     `(\<forall>r x y. R x y r \<Longrightarrow> P x r \<and> Q y r)
      \<Longrightarrow> (\<exists>x y r. R x y r) \<Longrightarrow> (\<exists>x r. P x r) \<and> (\<exists>y r. Q y r)`) THEN
    MAP_EVERY X_GEN_TAC [`r::real`; `x::A`; `y::B`] THEN
    MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `x::A`; `y::B`; `r::real`]
        MCBALL_PROD_METRIC_SUBSET) THEN
    REWRITE_TAC[\<subseteq>; FORALL_PAIR_THM; IN_CROSS] THEN MESON_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC MBOUNDED_SUBSET THEN
    EXISTS_TAC `((fst ` u) \<times> (snd ` u)):A#B=>bool` THEN
    ASM_REWRITE_TAC[MBOUNDED_CROSS; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[\<subseteq>; FORALL_PAIR_THM; IN_CROSS] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN MESON_TAC[]]);;

lemma mtotally_bounded_cross:
   "\<And>(m1::A metric) (m2::B metric) s t.
       mtotally_bounded (prod_metric m1 m2) (s \<times> t) \<longleftrightarrow>
       s = {} \<or> t = {} \<or> mtotally_bounded1 s \<and> mtotally_bounded2 t"
oops
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`s::A=>bool = {}`; `t::B=>bool = {}`] THEN
  ASM_REWRITE_TAC[CROSS_EMPTY; TOTALLY_BOUNDED_IN_EMPTY] THEN
  REWRITE_TAC[TOTALLY_BOUNDED_IN_SEQUENTIALLY] THEN
  ASM_REWRITE_TAC[CONJUNCT1 PROD_METRIC; SUBSET_CROSS] THEN
  ASM_CASES_TAC `(s::A=>bool) \<subseteq> mspace m1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(t::B=>bool) \<subseteq> mspace m2` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN STRIP_TAC THEN TRY CONJ_TAC THENL
   [X_GEN_TAC `x::num=>A` THEN DISCH_TAC THEN
    UNDISCH_TAC `\<not> (t::B=>bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `y::B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(\<lambda>n. (x n,y)):num=>A#B`) THEN
    ASM_REWRITE_TAC[IN_CROSS; CAUCHY_IN_PROD_METRIC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[o_DEF];
    X_GEN_TAC `y::num=>B` THEN DISCH_TAC THEN
    UNDISCH_TAC `\<not> (s::A=>bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x::A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(\<lambda>n. (x,y n)):num=>A#B`) THEN
    ASM_REWRITE_TAC[IN_CROSS; CAUCHY_IN_PROD_METRIC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[o_DEF];
    REWRITE_TAC[FORALL_PAIR_FUN_THM; IN_CROSS; FORALL_AND_THM] THEN
    MAP_EVERY X_GEN_TAC [`x::num=>A`; `y::num=>B`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `x::num=>A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1::num=>num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(y::num=>B) \<circ> (r1::num=>num)`) THEN
    ASM_REWRITE_TAC[o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2::num=>num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(r1::num=>num) \<circ> (r2::num=>num)` THEN
    ASM_SIMP_TAC[o_THM; CAUCHY_IN_PROD_METRIC; o_ASSOC] THEN
    ONCE_REWRITE_TAC[o_ASSOC] THEN GEN_REWRITE_TAC
     (BINOP_CONV \<circ> RAND_CONV \<circ> LAND_CONV \<circ> LAND_CONV) [o_DEF] THEN
    ASM_REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[CAUCHY_IN_SUBSEQUENCE]]);;

lemma mtotally_bounded_prod_metric:
   "\<And>(m1::A metric) (m2::B metric) u.
        mtotally_bounded (prod_metric m1 m2) u \<longleftrightarrow>
        mtotally_bounded1 (fst ` u) \<and>
        mtotally_bounded2 (snd ` u)"
oops
  REPEAT GEN_TAC THEN  EQ_TAC THENL
   [REWRITE_TAC[TOTALLY_BOUNDED_IN_SEQUENTIALLY] THEN
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    REWRITE_TAC[CONJUNCT1 PROD_METRIC; IN_CROSS] THEN STRIP_TAC THEN
    CONJ_TAC THEN (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[IN_IMAGE; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN X_GEN_TAC `z::num=>A#B` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `z::num=>A#B`) THEN
    ASM_REWRITE_TAC[CAUCHY_IN_PROD_METRIC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[o_DEF];
    STRIP_TAC THEN MATCH_MP_TAC TOTALLY_BOUNDED_IN_SUBSET THEN
    EXISTS_TAC `((fst ` u) \<times> (snd ` u)):A#B=>bool` THEN
    ASM_REWRITE_TAC[TOTALLY_BOUNDED_IN_CROSS; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[\<subseteq>; FORALL_PAIR_THM; IN_CROSS] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN MESON_TAC[]]);;


text\<open> Three more restrictive notions of continuity for metric spaces.           \<close>


let lipschitz_continuous_map = new_definition
 `lipschitz_continuous_map m1 m2 f \<longleftrightarrow>
        image f (mspace m1) \<subseteq> mspace m2 \<and>
        \<exists>B. \<forall>x y. x \<in> mspace m1 \<and> y \<in> mspace m1
                  \<Longrightarrow> d m2 (f x,f y) \<le> B * d x y`;;

lemma lipschitz_continuous_map_pos:
   "\<And>m1 m2 f::A=>B.
        lipschitz_continuous_map m1 m2 f \<longleftrightarrow>
        image f (mspace m1) \<subseteq> mspace m2 \<and>
        \<exists>B. 0 < B \<and>
            \<forall>x y. x \<in> mspace m1 \<and> y \<in> mspace m1
                  \<Longrightarrow> d m2 (f x,f y) \<le> B * d x y"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[lipschitz_continuous_map] THEN
  AP_TERM_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `B::real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `abs B + 1` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `B * d m1 (x::A,y)` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[MDIST_POS_LE] THEN REAL_ARITH_TAC);;

lemma lipschitz_continuous_map_eq:
   "(\<forall>x. x \<in> mspace m1 \<Longrightarrow> f x = g x) \<and> lipschitz_continuous_map m1 m2 f
      \<Longrightarrow> lipschitz_continuous_map m1 m2 g"
oops
  REWRITE_TAC[lipschitz_continuous_map] THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; IMP_CONJ] THEN SIMP_TAC[]);;

lemma lipschitz_continuous_map_from_submetric:
   "\<And>m1 m2 s f::A=>B.
        lipschitz_continuous_map m1 m2 f
        \<Longrightarrow> lipschitz_continuous_map (submetric1 s,m2) f"
oops
  REWRITE_TAC[lipschitz_continuous_map; SUBMETRIC] THEN SET_TAC[]);;

lemma lipschitz_continuous_map_from_submetric_mono:
   "lipschitz_continuous_map (submetric1 t,m2) f \<and> s \<subseteq> t
           \<Longrightarrow> lipschitz_continuous_map (submetric1 s,m2) f"
oops
  MESON_TAC[LIPSCHITZ_CONTINUOUS_MAP_FROM_SUBMETRIC; SUBMETRIC_SUBMETRIC;
            SET_RULE `s \<subseteq> t \<Longrightarrow> t \<inter> s = s`]);;

lemma lipschitz_continuous_map_into_submetric:
   "\<And>m1 m2 s f::A=>B.
        lipschitz_continuous_map m1 (submetric2 s) f \<longleftrightarrow>
        image f (mspace m1) \<subseteq> s \<and>
        lipschitz_continuous_map m1 m2 f"
oops
  REWRITE_TAC[lipschitz_continuous_map; SUBMETRIC] THEN SET_TAC[]);;

lemma lipschitz_continuous_map_const:
   "lipschitz_continuous_map m1 m2 (\<lambda>x. c) \<longleftrightarrow>
        mspace m1 = {} \<or> c \<in> mspace m2"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[lipschitz_continuous_map] THEN
  ASM_CASES_TAC `mspace m1::A=>bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `(c::B) \<in> mspace m2` THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `1` THEN ASM_SIMP_TAC[MDIST_REFL; MDIST_POS_LE; REAL_MUL_LID]);;

lemma lipschitz_continuous_map_id:
   "lipschitz_continuous_map m1 m1 (\<lambda>x. x)"
oops
  REWRITE_TAC[lipschitz_continuous_map; IMAGE_ID; SUBSET_REFL] THEN
  GEN_TAC THEN EXISTS_TAC `1` THEN REWRITE_TAC[REAL_LE_REFL; REAL_MUL_LID]);;

lemma lipschitz_continuous_map_compose:
   "\<And>m1 m2 m3 f::A=>B g::B=>C.
      lipschitz_continuous_map m1 m2 f \<and> lipschitz_continuous_map m2 m3 g
      \<Longrightarrow> lipschitz_continuous_map m1 m3 (g \<circ> f)"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_POS] THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `B::real` THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `C::real` THEN REPEAT DISCH_TAC THEN ASM_SIMP_TAC[o_THM] THEN
  EXISTS_TAC `C * B::real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN REPEAT DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS `C * d m2 (f x,f y)` THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_LE_LMUL_EQ]);;

let uniformly_continuous_map = new_definition
 `uniformly_continuous_map m1 m2 f \<longleftrightarrow>
        image f (mspace m1) \<subseteq> mspace m2 \<and>
        \<forall>e. 0 < e
            \<Longrightarrow> \<exists>d. 0 < d \<and>
                    !x x'. x \<in> mspace m1 \<and> x' \<in> mspace m1 \<and>
                           d x' x < d
                           \<Longrightarrow> d m2 (f x',f x) < e`;;

let UNIFORMLY_CONTINUOUS_MAP_SEQUENTIALLY,
    UNIFORMLY_CONTINUOUS_MAP_SEQUENTIALLY_ALT = (CONJ_PAIR \<circ> prove)
 (`(\<forall>m1 m2 f::A=>B.
        uniformly_continuous_map m1 m2 f \<longleftrightarrow>
        image f (mspace m1) \<subseteq> mspace m2 \<and>
        \<forall>x y. (\<forall>n. x n \<in> mspace m1) \<and> (\<forall>n. y n \<in> mspace m1) \<and>
              tendsto (\<lambda>n. d m1 (x n,y n)) 0 sequentially
              \<Longrightarrow> tendsto
                    (\<lambda>n. d m2 (f(x n),f(y n))) 0 sequentially) \<and>
   (\<forall>m1 m2 f::A=>B.
        uniformly_continuous_map m1 m2 f \<longleftrightarrow>
        image f (mspace m1) \<subseteq> mspace m2 \<and>
        \<forall>e x y. 0 < e \<and> (\<forall>n. x n \<in> mspace m1) \<and> (\<forall>n. y n \<in> mspace m1) \<and>
                tendsto (\<lambda>n. d m1 (x n,y n)) 0 sequentially
                \<Longrightarrow> \<exists>n. d m2 (f(x n),f(y n)) < e)"
oops
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(p \<Longrightarrow> q) \<and> (q \<Longrightarrow> r) \<and> (r \<Longrightarrow> p)
    \<Longrightarrow> (p \<longleftrightarrow> q) \<and> (p \<longleftrightarrow> r)`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[uniformly_continuous_map; \<subseteq>; FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
    REWRITE_TAC[LIMIT_METRIC; EVENTUALLY_SEQUENTIALLY] THEN
    REWRITE_TAC[REAL_EUCLIDEAN_METRIC; IN_UNIV; IMP_CONJ] THEN
    ASM_SIMP_TAC[MDIST_POS_LE; REAL_ARITH `0 \<le> x \<Longrightarrow> abs(0 - x) = x`] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`e::real`; `x::num=>A`; `y::num=>A`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC \<circ> SPECL [`x::num=>A`; `y::num=>A`]) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC] THEN
    REWRITE_TAC[LIMIT_METRIC] THEN
    DISCH_THEN(MP_TAC \<circ> SPEC `e::real` \<circ> CONJUNCT2) THEN
    ASM_REWRITE_TAC[REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP EVENTUALLY_HAPPENS) THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    ASM_SIMP_TAC[MDIST_POS_LE; REAL_ARITH `0 \<le> x \<Longrightarrow> abs(0 - x) = x`];
    REWRITE_TAC[uniformly_continuous_map; \<subseteq>; FORALL_IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e::real` THEN
    ONCE_REWRITE_TAC[TAUT `p \<Longrightarrow> q \<Longrightarrow> r \<longleftrightarrow> q \<Longrightarrow> \<not> r \<Longrightarrow> \<not> p`] THEN
    DISCH_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC \<circ> GEN `n::num` \<circ> SPEC `inverse(Suc n)`) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `0 < n + 1`] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; SKOLEM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x::num=>A` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y::num=>A` THEN
    REWRITE_TAC[AND_FORALL_THM; REAL_NOT_LT] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[MDIST_SYM; REAL_NOT_LT]] THEN
    MATCH_MP_TAC LIMIT_NULL_REAL_COMPARISON THEN
    EXISTS_TAC `\<lambda>n. inverse(Suc n)` THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; LIMIT_NULL_REAL_HARMONIC_OFFSET] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n::num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `abs(Suc n) = n + 1`;
      METRIC_ARITH `x \<in> M \<and> y \<in> M
                    \<Longrightarrow> abs(d x y) = d y x`] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

lemma uniformly_continuous_map_eq:
   "(\<forall>x. x \<in> mspace m1 \<Longrightarrow> f x = g x) \<and> uniformly_continuous_map m1 m2 f
      \<Longrightarrow> uniformly_continuous_map m1 m2 g"
oops
  REWRITE_TAC[uniformly_continuous_map] THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; IMP_CONJ] THEN SIMP_TAC[]);;

lemma uniformly_continuous_map_from_submetric:
   "\<And>m1 m2 s f::A=>B.
        uniformly_continuous_map m1 m2 f
        \<Longrightarrow> uniformly_continuous_map (submetric1 s,m2) f"
oops
  REWRITE_TAC[uniformly_continuous_map; SUBMETRIC] THEN SET_TAC[]);;

lemma uniformly_continuous_map_from_submetric_mono:
   "uniformly_continuous_map (submetric1 t,m2) f \<and> s \<subseteq> t
           \<Longrightarrow> uniformly_continuous_map (submetric1 s,m2) f"
oops
  MESON_TAC[UNIFORMLY_CONTINUOUS_MAP_FROM_SUBMETRIC; SUBMETRIC_SUBMETRIC;
            SET_RULE `s \<subseteq> t \<Longrightarrow> t \<inter> s = s`]);;

lemma uniformly_continuous_map_into_submetric:
   "\<And>m1 m2 s f::A=>B.
        uniformly_continuous_map m1 (submetric2 s) f \<longleftrightarrow>
        image f (mspace m1) \<subseteq> s \<and>
        uniformly_continuous_map m1 m2 f"
oops
  REWRITE_TAC[uniformly_continuous_map; SUBMETRIC] THEN SET_TAC[]);;

lemma uniformly_continuous_map_const:
   "uniformly_continuous_map m1 m2 (\<lambda>x. c) \<longleftrightarrow>
        mspace m1 = {} \<or> c \<in> mspace m2"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[uniformly_continuous_map] THEN
  ASM_CASES_TAC `mspace m1::A=>bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; NOT_IN_EMPTY] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(c::B) \<in> mspace m2` THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MDIST_REFL] THEN MESON_TAC[]);;

lemma uniformly_continuous_map_real_const:
   "uniformly_continuous_map m real_euclidean_metric (\<lambda>x::A. c)"
oops
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_CONST; REAL_EUCLIDEAN_METRIC; IN_UNIV]);;

lemma uniformly_continuous_map_id:
   "uniformly_continuous_map m1 m1 (\<lambda>x. x)"
oops
  REWRITE_TAC[uniformly_continuous_map; IMAGE_ID; SUBSET_REFL] THEN
  MESON_TAC[]);;

lemma uniformly_continuous_map_compose:
   "\<And>m1 m2 f::A=>B g::B=>C.
    uniformly_continuous_map m1 m2 f \<and> uniformly_continuous_map m2 m3 g
    \<Longrightarrow> uniformly_continuous_map m1 m3 (g \<circ> f)"
oops
  REWRITE_TAC[uniformly_continuous_map; o_DEF; \<subseteq>; FORALL_IN_IMAGE] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e::real` THEN ASM_MESON_TAC[]);;

let cauchy_continuous_map = new_definition
 `cauchy_continuous_map m1 m2 f \<longleftrightarrow>
        \<forall>x. MCauchy m1 x \<Longrightarrow> MCauchy m2 (f \<circ> x)`;;

lemma cauchy_continuous_map_image:
   "\<And>m1 m2 f::A=>B.
        cauchy_continuous_map m1 m2 f
        \<Longrightarrow> image f (mspace m1) \<subseteq> mspace m2"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `a::A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> SPEC `(\<lambda>n. a):num=>A` \<circ>
    REWRITE_RULE[cauchy_continuous_map]) THEN
  ASM_REWRITE_TAC[o_DEF; CAUCHY_IN_CONST]);;

lemma cauchy_continuous_map_eq:
   "(\<forall>x. x \<in> mspace m1 \<Longrightarrow> f x = g x) \<and> cauchy_continuous_map m1 m2 f
      \<Longrightarrow> cauchy_continuous_map m1 m2 g"
oops
  REWRITE_TAC[cauchy_continuous_map; MCauchy; o_DEF; IMP_CONJ] THEN
  SIMP_TAC[]);;

lemma cauchy_continuous_map_from_submetric:
   "\<And>m1 m2 s f::A=>B.
        cauchy_continuous_map m1 m2 f
        \<Longrightarrow> cauchy_continuous_map (submetric1 s,m2) f"
oops
  SIMP_TAC[cauchy_continuous_map; CAUCHY_IN_SUBMETRIC]);;

lemma cauchy_continuous_map_from_submetric_mono:
   "cauchy_continuous_map (submetric1 t,m2) f \<and> s \<subseteq> t
           \<Longrightarrow> cauchy_continuous_map (submetric1 s,m2) f"
oops
  MESON_TAC[CAUCHY_CONTINUOUS_MAP_FROM_SUBMETRIC; SUBMETRIC_SUBMETRIC;
            SET_RULE `s \<subseteq> t \<Longrightarrow> t \<inter> s = s`]);;

lemma cauchy_continuous_map_into_submetric:
   "\<And>m1 m2 s f::A=>B.
        cauchy_continuous_map m1 (submetric2 s) f \<longleftrightarrow>
        image f (mspace m1) \<subseteq> s \<and>
        cauchy_continuous_map m1 m2 f"
oops
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC \<circ> MATCH_MP CAUCHY_CONTINUOUS_MAP_IMAGE) THEN
      REWRITE_TAC[SUBMETRIC] THEN SET_TAC[];
      POP_ASSUM MP_TAC THEN
      SIMP_TAC[cauchy_continuous_map; CAUCHY_IN_SUBMETRIC; o_THM]];
    REPEAT(POP_ASSUM MP_TAC) THEN
    SIMP_TAC[cauchy_continuous_map; CAUCHY_IN_SUBMETRIC; o_THM] THEN
    REWRITE_TAC[MCauchy] THEN SET_TAC[]]);;

lemma cauchy_continuous_map_const:
   "cauchy_continuous_map m1 m2 (\<lambda>x. c) \<longleftrightarrow>
        mspace m1 = {} \<or> c \<in> mspace m2"
oops
  REPEAT GEN_TAC THEN REWRITE_TAC[cauchy_continuous_map] THEN
  REWRITE_TAC[o_DEF; CAUCHY_IN_CONST] THEN
  ASM_CASES_TAC `(c::B) \<in> mspace m2` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL [ALL_TAC; SIMP_TAC[MCauchy; NOT_IN_EMPTY]] THEN
  GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a::A` THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `(\<lambda>n. a):num=>A`) THEN
  ASM_REWRITE_TAC[CAUCHY_IN_CONST]);;

lemma cauchy_continuous_map_real_const:
   "cauchy_continuous_map m real_euclidean_metric (\<lambda>x::A. c)"
oops
  REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_CONST; REAL_EUCLIDEAN_METRIC; IN_UNIV]);;

lemma cauchy_continuous_map_id:
   "cauchy_continuous_map m1 m1 (\<lambda>x. x)"
oops
  REWRITE_TAC[cauchy_continuous_map; o_DEF; ETA_AX]);;

lemma cauchy_continuous_map_compose:
   "\<And>m1 m2 f::A=>B g::B=>C.
    cauchy_continuous_map m1 m2 f \<and> cauchy_continuous_map m2 m3 g
    \<Longrightarrow> cauchy_continuous_map m1 m3 (g \<circ> f)"
oops
  REWRITE_TAC[cauchy_continuous_map; o_DEF; \<subseteq>; FORALL_IN_IMAGE] THEN
  REPEAT GEN_TAC THEN SIMP_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e::real` THEN ASM_MESON_TAC[]);;

lemma lipschitz_imp_uniformly_continuous_map:
   "\<And>m1 m2 f::A=>B.
        lipschitz_continuous_map m1 m2 f
        \<Longrightarrow> uniformly_continuous_map m1 m2 f"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_POS; uniformly_continuous_map] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `B::real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e::real` THEN DISCH_TAC THEN
  EXISTS_TAC `e / B::real` THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_MUL_SYM]);;

lemma uniformly_imp_cauchy_continuous_map:
   "\<And>m1 m2 f::A=>B.
        uniformly_continuous_map m1 m2 f
        \<Longrightarrow> cauchy_continuous_map m1 m2 f"
oops
  REPEAT GEN_TAC THEN
  REWRITE_TAC[uniformly_continuous_map; cauchy_continuous_map] THEN
  STRIP_TAC THEN X_GEN_TAC `x::num=>A` THEN REWRITE_TAC[MCauchy] THEN
  STRIP_TAC THEN REWRITE_TAC[o_THM] THEN ASM SET_TAC[]);;

lemma locally_cauchy_continuous_map:
   "\<And>m1 m2 e f::A=>B.
        0 < e \<and>
        (\<forall>x. x \<in> mspace m1
             \<Longrightarrow> cauchy_continuous_map (submetric1 (mball x e),m2) f)
        \<Longrightarrow> cauchy_continuous_map m1 m2 f"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[cauchy_continuous_map] THEN
  X_GEN_TAC `x::num=>A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [MCauchy]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC \<circ> SPEC `e::real`)) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `M::num` THEN STRIP_TAC THEN
  MATCH_MP_TAC CAUCHY_IN_OFFSET THEN EXISTS_TAC `M::num` THEN CONJ_TAC THENL
   [X_GEN_TAC `n::num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(x::num=>A) n`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP CAUCHY_CONTINUOUS_MAP_IMAGE) THEN
    ASM_SIMP_TAC[\<subseteq>; FORALL_IN_IMAGE; SUBMETRIC; SUBMETRIC; o_THM;
                 IN_INTER; CENTRE_IN_MBALL];
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `(x::num=>A) M`) THEN
    ASM_REWRITE_TAC[cauchy_continuous_map; o_DEF] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CAUCHY_IN_SUBMETRIC; IN_MBALL] THEN
    ASM_SIMP_TAC[LE_ADD; LE_REFL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CAUCHY_IN_SUBSEQUENCE THEN
    ASM_REWRITE_TAC[LT_ADD_LCANCEL]]);;

lemma cauchy_continuous_imp_continuous_map:
   "\<And>m1 m2 f::A=>B.
        cauchy_continuous_map m1 m2 f
        \<Longrightarrow> continuous_map (mtopology m1,mtopology m2) f"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_MAP_ATPOINTOF] THEN
  X_GEN_TAC `a::A` THEN REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN DISCH_TAC THEN
  REWRITE_TAC[LIMIT_ATPOINTOF_SEQUENTIALLY] THEN
  FIRST_ASSUM(ASSUME_TAC \<circ> MATCH_MP CAUCHY_CONTINUOUS_MAP_IMAGE) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x::num=>A` THEN REWRITE_TAC[IN_DELETE; FORALL_AND_THM] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC \<circ> SPEC
   `\<lambda>n. if even n then x(n div 2) else a::A` \<circ>
   REWRITE_RULE[cauchy_continuous_map]) THEN
  ASM_SIMP_TAC[o_DEF; COND_RAND; CAUCHY_IN_INTERLEAVING]);;

lemma uniformly_continuous_imp_continuous_map:
   "\<And>m1 m2 f::A=>B.
        uniformly_continuous_map m1 m2 f
        \<Longrightarrow> continuous_map (mtopology m1,mtopology m2) f"
oops
  MESON_TAC[UNIFORMLY_IMP_CAUCHY_CONTINUOUS_MAP;
            CAUCHY_CONTINUOUS_IMP_CONTINUOUS_MAP]);;

lemma lipschitz_continuous_imp_continuous_map:
   "\<And>m1 m2 f::A=>B.
        lipschitz_continuous_map m1 m2 f
        \<Longrightarrow> continuous_map (mtopology m1,mtopology m2) f"
oops
  SIMP_TAC[UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS_MAP;
           LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP]);;

lemma lipschitz_imp_cauchy_continuous_map:
   "\<And>m1 m2 f::A=>B.
        lipschitz_continuous_map m1 m2 f
        \<Longrightarrow> cauchy_continuous_map m1 m2 f"
oops
  SIMP_TAC[LIPSCHITZ_IMP_UNIFORMLY_CONTINUOUS_MAP;
           UNIFORMLY_IMP_CAUCHY_CONTINUOUS_MAP]);;

lemma continuous_imp_cauchy_continuous_map:
   "\<And>m1 m2 f::A=>B.
        mcomplete m1 \<and>
        continuous_map (mtopology m1,mtopology m2) f
        \<Longrightarrow> cauchy_continuous_map m1 m2 f"
oops
  REPEAT STRIP_TAC THEN REWRITE_TAC[cauchy_continuous_map] THEN
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

lemma cauchy_imp_uniformly_continuous_map:
   "\<And>m1 m2 f::A=>B.
        mtotally_bounded1 (mspace m1) \<and>
        cauchy_continuous_map m1 m2 f
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
   REWRITE_RULE[cauchy_continuous_map]) THEN
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

lemma continuous_eq_cauchy_continuous_map:
   "\<And>m1 m2 f::A=>B.
        mcomplete m1
        \<Longrightarrow> (continuous_map (mtopology m1,mtopology m2) f \<longleftrightarrow>
             cauchy_continuous_map m1 m2 f)"
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

lemma cauchy_eq_uniformly_continuous_map:
   "\<And>m1 m2 f::A=>B.
        mtotally_bounded1 (mspace m1)
        \<Longrightarrow> (cauchy_continuous_map m1 m2 f \<longleftrightarrow>
             uniformly_continuous_map m1 m2 f)"
oops
  MESON_TAC[CAUCHY_IMP_UNIFORMLY_CONTINUOUS_MAP;
            UNIFORMLY_IMP_CAUCHY_CONTINUOUS_MAP]);;

lemma lipschitz_continuous_map_projections:
 (`(\<forall>m1::A metric m2::B metric.
        lipschitz_continuous_map (prod_metric m1 m2,m1) fst) \<and>
   (\<forall>m1::A metric m2::B metric.
        lipschitz_continuous_map (prod_metric m1 m2,m2) snd)"
oops
  CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[lipschitz_continuous_map] THEN
  REWRITE_TAC[\<subseteq>; FORALL_IN_IMAGE; CONJUNCT1 PROD_METRIC] THEN
  SIMP_TAC[FORALL_PAIR_THM; IN_CROSS] THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[REAL_MUL_LID; COMPONENT_LE_PROD_METRIC]);;

lemma lipschitz_continuous_map_pairwise:
   "\<And>m m1 m2 (f::A=>B#C).
        lipschitz_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow>
        lipschitz_continuous_map m m1 (fst \<circ> f) \<and>
        lipschitz_continuous_map m m2 (snd \<circ> f)"
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

lemma cauchy_continuous_map_pairwise:
   "\<And>m m1 m2 (f::A=>B#C).
        cauchy_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow>
        cauchy_continuous_map m m1 (fst \<circ> f) \<and>
        cauchy_continuous_map m m2 (snd \<circ> f)"
oops
  REWRITE_TAC[cauchy_continuous_map; CAUCHY_IN_PROD_METRIC; o_ASSOC] THEN
  MESON_TAC[]);;

lemma lipschitz_continuous_map_paired:
   "\<And>m m1 m2 f (g::A=>C).
        lipschitz_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
        lipschitz_continuous_map m m1 f \<and> lipschitz_continuous_map m m2 g"
oops
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma uniformly_continuous_map_paired:
   "\<And>m m1 m2 f (g::A=>C).
        uniformly_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
        uniformly_continuous_map m m1 f \<and> uniformly_continuous_map m m2 g"
oops
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma cauchy_continuous_map_paired:
   "\<And>m m1 m2 f (g::A=>C).
        cauchy_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
        cauchy_continuous_map m m1 f \<and> cauchy_continuous_map m m2 g"
oops
  REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma mbounded_lipschitz_continuous_image:
   "\<And>m1 m2 f s.
        lipschitz_continuous_map m1 m2 f \<and> mbounded m1 s
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

lemma mtotally_bounded_cauchy_continuous_image:
   "\<And>m1 m2 f s.
        cauchy_continuous_map m1 m2 f \<and> mtotally_bounded1 s
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
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [cauchy_continuous_map]) THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `(x::num=>A) \<circ> (r::num=>num)`) THEN
  ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[o_DEF]);;

lemma lipschitz_coefficient_pos:
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

lemma lipschitz_continuous_map_metric:
   "lipschitz_continuous_map
          (prod_metric m m,real_euclidean_metric)
          (d m)"
oops
  SIMP_TAC[lipschitz_continuous_map; CONJUNCT1 PROD_METRIC;
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

lemma lipschitz_continuous_map_mdist:
   "\<And>m m' f g.
      lipschitz_continuous_map m m' f \<and>
      lipschitz_continuous_map m m' g
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric
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

lemma cauchy_continuous_map_mdist:
   "\<And>m m' f g.
      cauchy_continuous_map m m' f \<and>
      cauchy_continuous_map m m' g
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric
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

lemma lipschitz_continuous_map_real_left_multiplication:
   "lipschitz_continuous_map real_euclidean_metric real_euclidean_metric
         (\<lambda>x. c * x)"
oops
  GEN_TAC THEN REWRITE_TAC[lipschitz_continuous_map] THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC; IN_UNIV; SUBSET_UNIV] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  MESON_TAC[REAL_LE_REFL]);;

lemma lipschitz_continuous_map_real_right_multiplication:
   "lipschitz_continuous_map real_euclidean_metric real_euclidean_metric
         (\<lambda>x. x * c)"
oops
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LEFT_MULTIPLICATION]);;

lemma lipschitz_continuous_map_real_negation:
 (`lipschitz_continuous_map real_euclidean_metric real_euclidean_metric (--)"
oops
  GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LEFT_MULTIPLICATION]);;

lemma lipschitz_continuous_map_real_absolute_value:
 (`lipschitz_continuous_map real_euclidean_metric real_euclidean_metric abs"
oops
  SIMP_TAC[lipschitz_continuous_map; REAL_EUCLIDEAN_METRIC; SUBSET_UNIV] THEN
  EXISTS_TAC `1` THEN REAL_ARITH_TAC);;

lemma lipschitz_continuous_map_real_addition:
 (`lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\<lambda>(x,y). x + y)"
oops
  REWRITE_TAC[lipschitz_continuous_map; CONJUNCT1 PROD_METRIC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV; IN_CROSS] THEN
  EXISTS_TAC `2` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `x \<le> 2 * y \<longleftrightarrow> x / 2 \<le> y`] THEN
  W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand)
        COMPONENT_LE_PROD_METRIC \<circ> rand \<circ> snd) THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN REAL_ARITH_TAC);;

lemma lipschitz_continuous_map_real_subtraction:
 (`lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\<lambda>(x,y). x - y)"
oops
  REWRITE_TAC[lipschitz_continuous_map; CONJUNCT1 PROD_METRIC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV; IN_CROSS] THEN
  EXISTS_TAC `2` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `x \<le> 2 * y \<longleftrightarrow> x / 2 \<le> y`] THEN
  W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand)
        COMPONENT_LE_PROD_METRIC \<circ> rand \<circ> snd) THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN REAL_ARITH_TAC);;

lemma lipschitz_continuous_map_real_maximum:
 (`lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\<lambda>(x,y). max x y)"
oops
  REWRITE_TAC[lipschitz_continuous_map; CONJUNCT1 PROD_METRIC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV; IN_CROSS] THEN
  EXISTS_TAC `1` THEN REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand)
        COMPONENT_LE_PROD_METRIC \<circ> rand \<circ> snd) THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN REAL_ARITH_TAC);;

lemma lipschitz_continuous_map_real_minimum:
 (`lipschitz_continuous_map
    (prod_metric real_euclidean_metric real_euclidean_metric,
     real_euclidean_metric)
    (\<lambda>(x,y). min x y)"
oops
  REWRITE_TAC[lipschitz_continuous_map; CONJUNCT1 PROD_METRIC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; REAL_EUCLIDEAN_METRIC] THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV; IN_CROSS] THEN
  EXISTS_TAC `1` THEN REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MUL_LID] THEN
  W(MP_TAC \<circ> PART_MATCH (rand \<circ> rand)
        COMPONENT_LE_PROD_METRIC \<circ> rand \<circ> snd) THEN
  REWRITE_TAC[REAL_EUCLIDEAN_METRIC] THEN REAL_ARITH_TAC);;

lemma locally_lipschitz_continuous_map_real_multiplication:
   "mbounded (prod_metric real_euclidean_metric real_euclidean_metric) s
       \<Longrightarrow> lipschitz_continuous_map
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
  SIMP_TAC[lipschitz_continuous_map; REAL_EUCLIDEAN_METRIC; SUBSET_UNIV] THEN
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

lemma cauchy_continuous_map_real_multiplication:
 (`cauchy_continuous_map
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

lemma locally_lipschitz_continuous_map_real_inversion:
   "\<not> (0 \<in> euclideanreal closure_of s)
       \<Longrightarrow> lipschitz_continuous_map
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
  REWRITE_TAC[lipschitz_continuous_map; REAL_EUCLIDEAN_METRIC; SUBSET_UNIV;
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

lemma lipschitz_continuous_map_fst:
   "\<And>m m1 m2 f::A=>B#C.
        lipschitz_continuous_map m (prod_metric m1 m2) f
        \<Longrightarrow> lipschitz_continuous_map m m1 (\<lambda>x. fst(f x))"
oops
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF]);;

lemma lipschitz_continuous_map_snd:
   "\<And>m m1 m2 f::A=>B#C.
        lipschitz_continuous_map m (prod_metric m1 m2) f
        \<Longrightarrow> lipschitz_continuous_map m m2 (\<lambda>x. snd(f x))"
oops
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF]);;

lemma lipschitz_continuous_map_real_lmul:
   "\<And>m c f::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. c * f x)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\<lambda>x. c * f x) = (\<lambda>y. c * y) \<circ> f`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `real_euclidean_metric` THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LEFT_MULTIPLICATION]);;

lemma lipschitz_continuous_map_real_rmul:
   "\<And>m c f::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x * c)"
oops
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LMUL]);;

lemma lipschitz_continuous_map_real_neg:
   "\<And>m f::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. --(f x))"
oops
  ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_LMUL]);;

lemma lipschitz_continuous_map_real_abs:
   "\<And>m f::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. abs(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `real_euclidean_metric` THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ABSOLUTE_VALUE]);;

lemma lipschitz_continuous_map_real_inv:
   "\<And>m f::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f \<and>
      \<not> (0 \<in> euclideanreal closure_of (image f (M)))
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. inverse(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
   `submetric real_euclidean_metric (image f (M::A=>bool))` THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_INTO_SUBMETRIC; SUBSET_REFL] THEN
  MATCH_MP_TAC LOCALLY_LIPSCHITZ_CONTINUOUS_MAP_REAL_INVERSION THEN
  ASM_REWRITE_TAC[]);;

lemma lipschitz_continuous_map_real_add:
   "\<And>m f g::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f \<and>
      lipschitz_continuous_map m real_euclidean_metric g
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x + g x)"
oops
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\<lambda>x. f x + g x) = (\<lambda>(x,y). x + y) \<circ> (\<lambda>z. f z,g z)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_DEF; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_metric real_euclidean_metric real_euclidean_metric` THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ADDITION] THEN
  ASM_REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_PAIRWISE; o_DEF; ETA_AX]);;

lemma lipschitz_continuous_map_real_sub:
   "\<And>m f g::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f \<and>
      lipschitz_continuous_map m real_euclidean_metric g
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x - g x)"
oops
  REWRITE_TAC[real_sub] THEN
  SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ADD;
           LIPSCHITZ_CONTINUOUS_MAP_REAL_NEG]);;

lemma lipschitz_continuous_map_real_max:
   "\<And>m f g::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f \<and>
      lipschitz_continuous_map m real_euclidean_metric g
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric
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

lemma lipschitz_continuous_map_real_min:
   "\<And>m f g::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f \<and>
      lipschitz_continuous_map m real_euclidean_metric g
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric
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

lemma lipschitz_continuous_map_real_mul:
   "\<And>m f g::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f \<and>
      lipschitz_continuous_map m real_euclidean_metric g \<and>
      real_bounded (image f (M)) \<and> real_bounded (image g (M))
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x * g x)"
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

lemma lipschitz_continuous_map_real_div:
   "\<And>m f g::A=>real.
      lipschitz_continuous_map m real_euclidean_metric f \<and>
      lipschitz_continuous_map m real_euclidean_metric g \<and>
      real_bounded (image f (M)) \<and>
      \<not> (0 \<in> euclideanreal closure_of (image g (M)))
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x / g x)"
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

lemma lipschitz_continuous_map_sum:
   "\<And>m f::K=>A->real k.
      finite k \<and>
      (\<forall>i. i \<in> k
          \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric (\<lambda>x. f x i))
      \<Longrightarrow> lipschitz_continuous_map m real_euclidean_metric
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

lemma cauchy_continuous_map_fst:
   "\<And>m m1 m2 f::A=>B#C.
        cauchy_continuous_map m (prod_metric m1 m2) f
        \<Longrightarrow> cauchy_continuous_map m m1 (\<lambda>x. fst(f x))"
oops
  SIMP_TAC[CAUCHY_CONTINUOUS_MAP_PAIRWISE; o_DEF]);;

lemma cauchy_continuous_map_snd:
   "\<And>m m1 m2 f::A=>B#C.
        cauchy_continuous_map m (prod_metric m1 m2) f
        \<Longrightarrow> cauchy_continuous_map m m2 (\<lambda>x. snd(f x))"
oops
  SIMP_TAC[CAUCHY_CONTINUOUS_MAP_PAIRWISE; o_DEF]);;

lemma cauchy_continuous_map_real_inv:
   "\<And>m f::A=>real.
      cauchy_continuous_map m real_euclidean_metric f \<and>
      \<not> (0 \<in> euclideanreal closure_of (image f (M)))
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. inverse(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
   `submetric real_euclidean_metric (image f (M::A=>bool))` THEN
  ASM_REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_INTO_SUBMETRIC; SUBSET_REFL] THEN
  MATCH_MP_TAC LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP THEN
  MATCH_MP_TAC LOCALLY_LIPSCHITZ_CONTINUOUS_MAP_REAL_INVERSION THEN
  ASM_REWRITE_TAC[]);;

lemma cauchy_continuous_map_real_add:
   "\<And>m f g::A=>real.
      cauchy_continuous_map m real_euclidean_metric f \<and>
      cauchy_continuous_map m real_euclidean_metric g
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x + g x)"
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

lemma cauchy_continuous_map_real_mul:
   "\<And>m f g::A=>real.
      cauchy_continuous_map m real_euclidean_metric f \<and>
      cauchy_continuous_map m real_euclidean_metric g
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x * g x)"
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

lemma cauchy_continuous_map_real_lmul:
   "\<And>m c f::A=>real.
      cauchy_continuous_map m real_euclidean_metric f
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. c * f x)"
oops
  SIMP_TAC[CAUCHY_CONTINUOUS_MAP_REAL_MUL; CAUCHY_CONTINUOUS_MAP_REAL_CONST]);;

lemma cauchy_continuous_map_real_rmul:
   "\<And>m c f::A=>real.
      cauchy_continuous_map m real_euclidean_metric f
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x * c)"
oops
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_REAL_LMUL]);;

lemma cauchy_continuous_map_real_pow:
   "\<And>m f n.
        cauchy_continuous_map m real_euclidean_metric f
        \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x ^ n)"
oops
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[real_pow; CAUCHY_CONTINUOUS_MAP_REAL_CONST;
               CAUCHY_CONTINUOUS_MAP_REAL_MUL]);;

lemma cauchy_continuous_map_real_neg:
   "\<And>m f::A=>real.
      cauchy_continuous_map m real_euclidean_metric f
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. --(f x))"
oops
  ONCE_REWRITE_TAC[REAL_NEG_MINUS1] THEN
  REWRITE_TAC[CAUCHY_CONTINUOUS_MAP_REAL_LMUL]);;

lemma cauchy_continuous_map_real_abs:
   "\<And>m f::A=>real.
      cauchy_continuous_map m real_euclidean_metric f
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. abs(f x))"
oops
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `real_euclidean_metric` THEN
  ASM_SIMP_TAC[LIPSCHITZ_CONTINUOUS_MAP_REAL_ABSOLUTE_VALUE;
               LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP]);;

lemma cauchy_continuous_map_real_sub:
   "\<And>m f g::A=>real.
      cauchy_continuous_map m real_euclidean_metric f \<and>
      cauchy_continuous_map m real_euclidean_metric g
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x - g x)"
oops
  REWRITE_TAC[real_sub] THEN
  SIMP_TAC[CAUCHY_CONTINUOUS_MAP_REAL_ADD;
           CAUCHY_CONTINUOUS_MAP_REAL_NEG]);;

lemma cauchy_continuous_map_real_max:
   "\<And>m f g::A=>real.
      cauchy_continuous_map m real_euclidean_metric f \<and>
      cauchy_continuous_map m real_euclidean_metric g
    \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric
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

lemma cauchy_continuous_map_real_min:
   "\<And>m f g::A=>real.
      cauchy_continuous_map m real_euclidean_metric f \<and>
      cauchy_continuous_map m real_euclidean_metric g
    \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric
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

lemma cauchy_continuous_map_real_div:
   "\<And>m f g::A=>real.
      cauchy_continuous_map m real_euclidean_metric f \<and>
      cauchy_continuous_map m real_euclidean_metric g \<and>
      \<not> (0 \<in> euclideanreal closure_of (image g (M)))
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x / g x)"
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

lemma cauchy_continuous_map_sum:
   "\<And>m f::K=>A->real k.
      finite k \<and>
      (\<forall>i. i \<in> k
          \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. f x i))
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric
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

lemma cauchy_continuous_map_sqrt:
   "\<And>m f::A=>real.
      cauchy_continuous_map m real_euclidean_metric f
      \<Longrightarrow> cauchy_continuous_map m real_euclidean_metric (\<lambda>x. sqrt(f x))"
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
  ASM_SIMP_TAC[lipschitz_continuous_map; \<subseteq>; FORALL_IN_IMAGE;
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
   "\<And>X X' f::A=>B s t.
       regular_space X' \<and>
       t \<subseteq> X closure_of s \<and>
       (\<forall>x. x \<in> t \<Longrightarrow> limitin X' f (f x) (atin X x within s))
       \<Longrightarrow> continuous_map (subtopology X t,X') f"
oops
  REWRITE_TAC[GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `image f t \<subseteq> topspace X'` ASSUME_TAC THENL
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
  SUBGOAL_THEN `z \<in> topspace X \<and> f z \<in> topspace X'`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC \<circ> MATCH_MP OPEN_IN_SUBSET)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `\<not> (f z \<in> topspace X' - c)` MP_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN STRIP_TAC; ASM SET_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE RAND_CONV [limitin] \<circ> SPEC `z::A`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `topspace X' - c::B=>bool`) THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; IN_DIFF] THEN
  ASM_REWRITE_TAC[EVENTUALLY_ATPOINTOF; EVENTUALLY_WITHIN_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':A=>bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(t::A=>bool) \<subseteq> X closure_of s` THEN
  REWRITE_TAC[closure_of; IN_ELIM_THM; \<subseteq>] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `z::A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `u \<inter> u':A=>bool`) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[]);;

lemma continuous_map_on_intermediate_closure_of_eq:
   "\<And>X X' f::A=>B s t.
        regular_space X' \<and> s \<subseteq> t \<and> t \<subseteq> X closure_of s
        \<Longrightarrow> (continuous_map (subtopology X t,X') f \<longleftrightarrow>
             \<forall>x. x \<in> t \<Longrightarrow> limitin X' f (f x) (atin X x within s))"
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


lemma cauchy_continuous_map_extends_to_continuous_closure_of:
   "\<And>m1 m2 f s.
        mcomplete m2 \<and> cauchy_continuous_map (submetric1 s,m2) f
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
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `mspace m1 \<inter> s::A=>bool`) THEN
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
    SPEC `x::num=>A` \<circ> REWRITE_RULE[cauchy_continuous_map]) THEN
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
   REWRITE_RULE[cauchy_continuous_map]) THEN
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

lemma cauchy_continuous_map_extends_to_continuous_intermediate_closure_of:
   "\<And>m1 m2 f s t.
        mcomplete m2 \<and> cauchy_continuous_map (submetric1 s,m2) f \<and>
        t \<subseteq> mtopology m1 closure_of s
        \<Longrightarrow> \<exists>g. continuous_map(subtopology (mtopology m1) t,mtopology m2) g \<and>
                \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `s::A=>bool`]
        CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO]);;

lemma lipschitz_continuous_map_on_intermediate_closure:
   "\<And>m1 m2 f::A=>B s t.
        s \<subseteq> t \<and> t \<subseteq> (mtopology m1) closure_of s \<and>
        continuous_map (subtopology (mtopology m1) t,mtopology m2) f \<and>
        lipschitz_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> lipschitz_continuous_map (submetric1 t,m2) f"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
  SUBGOAL_THEN `submetric1 (s::A=>bool) = submetric1 (mspace m1 \<inter> s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBMETRIC_SUBMETRIC; SUBMETRIC_MSPACE];
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC \<circ> SPEC `mspace m1::A=>bool` \<circ> MATCH_MP (SET_RULE
       `s \<subseteq> t \<Longrightarrow> \<forall>u. u \<inter> s \<subseteq> u \<and> u \<inter> s \<subseteq> t`))
     MP_TAC) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    SPEC_TAC(`mspace m1 \<inter> (s::A=>bool)`,`s::A=>bool`)] THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(t::A=>bool) \<subseteq> mspace m1` ASSUME_TAC THENL
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

lemma lipschitz_continuous_map_extends_to_closure_of:
   "\<And>m1 m2 f s.
        mcomplete m2 \<and> lipschitz_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> \<exists>g. lipschitz_continuous_map
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
  EXISTS_TAC `mspace m1 \<inter> s::A=>bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_INTER; GSYM TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT; SUBSET_REFL] THEN
  REWRITE_TAC[TOPSPACE_MTOPOLOGY; GSYM SUBMETRIC_RESTRICT] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_EQ THEN EXISTS_TAC `f::A=>B` THEN
  ASM_SIMP_TAC[SUBMETRIC; IN_INTER]);;

lemma lipschitz_continuous_map_extends_to_intermediate_closure_of:
   "\<And>m1 m2 f s t.
        mcomplete m2 \<and>
        lipschitz_continuous_map (submetric1 s,m2) f \<and>
        t \<subseteq> mtopology m1 closure_of s
        \<Longrightarrow> \<exists>g. lipschitz_continuous_map (submetric1 t,m2) g \<and>
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
  SUBGOAL_THEN `submetric1 (s::A=>bool) = submetric1 (mspace m1 \<inter> s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBMETRIC_SUBMETRIC; SUBMETRIC_MSPACE];
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC \<circ> SPEC `mspace m1::A=>bool` \<circ> MATCH_MP (SET_RULE
       `s \<subseteq> t \<Longrightarrow> \<forall>u. u \<inter> s \<subseteq> u \<and> u \<inter> s \<subseteq> t`))
     MP_TAC) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    SPEC_TAC(`mspace m1 \<inter> (s::A=>bool)`,`s::A=>bool`)] THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(t::A=>bool) \<subseteq> mspace m1` ASSUME_TAC THENL
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
  EXISTS_TAC `mspace m1 \<inter> s::A=>bool` THEN ASM_REWRITE_TAC[] THEN
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

lemma cauchy_continuous_map_on_intermediate_closure:
   "\<And>m1 m2 f::A=>B s t.
        s \<subseteq> t \<and> t \<subseteq> (mtopology m1) closure_of s \<and>
        continuous_map (subtopology (mtopology m1) t,mtopology m2) f \<and>
        cauchy_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> cauchy_continuous_map (submetric1 t,m2) f"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
  SUBGOAL_THEN `submetric1 (s::A=>bool) = submetric1 (mspace m1 \<inter> s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBMETRIC_SUBMETRIC; SUBMETRIC_MSPACE];
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC \<circ> SPEC `mspace m1::A=>bool` \<circ> MATCH_MP (SET_RULE
       `s \<subseteq> t \<Longrightarrow> \<forall>u. u \<inter> s \<subseteq> u \<and> u \<inter> s \<subseteq> t`))
     MP_TAC) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    SPEC_TAC(`mspace m1 \<inter> (s::A=>bool)`,`s::A=>bool`)] THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(t::A=>bool) \<subseteq> mspace m1` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[closure_of; TOPSPACE_MTOPOLOGY]) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[cauchy_continuous_map; CAUCHY_IN_SUBMETRIC] THEN
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
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [cauchy_continuous_map]) THEN
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

lemma cauchy_continuous_map_extends_to_closure_of:
   "\<And>m1 m2 f s.
        mcomplete m2 \<and> cauchy_continuous_map (submetric1 s,m2) f
        \<Longrightarrow> \<exists>g. cauchy_continuous_map
                   (submetric1 (mtopology m1 closure_of s),m2) g \<and>
                \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC \<circ> MATCH_MP
    CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g::A=>B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `mspace m1 \<inter> s::A=>bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_INTER; GSYM TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT; SUBSET_REFL] THEN
  REWRITE_TAC[TOPSPACE_MTOPOLOGY; GSYM SUBMETRIC_RESTRICT] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_EQ THEN EXISTS_TAC `f::A=>B` THEN
  ASM_SIMP_TAC[SUBMETRIC; IN_INTER]);;

lemma cauchy_continuous_map_extends_to_intermediate_closure_of:
   "\<And>m1 m2 f s t.
        mcomplete m2 \<and>
        cauchy_continuous_map (submetric1 s,m2) f \<and>
        t \<subseteq> mtopology m1 closure_of s
        \<Longrightarrow> \<exists>g. cauchy_continuous_map (submetric1 t,m2) g \<and>
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
   "\<And>X X' f s.
        completely_metrizable_space X' \<and>
        (continuous_map (subtopology X s,X') f \<or>
         t1_space X \<and> f ` s \<subseteq> topspace X')
        \<Longrightarrow> gdelta_in X
             {x \<in> topspace X.
                  \<exists>l. limitin X' f l (atin X x within s)}"
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
      \<Inter> {\<Union> {u. openin X u \<and>
                          \<forall>x y. x \<in> (s \<inter> u) \<and>
                                y \<in> (s \<inter> u)
                                \<Longrightarrow> d (f x) f y < inverse(Suc n)}
              | n \<in> UNIV}`;
    EXISTS_TAC
     `topspace X \<inter>
      \<Inter> {\<Union> {u. openin X u \<and>
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
   "\<And>X s X' f.
        s \<subseteq> topspace X \<and>
        completely_metrizable_space X' \<and>
        continuous_map(subtopology X s,X') f
        \<Longrightarrow> \<exists>u g. gdelta_in X u \<and>
                  s \<subseteq> u \<and>
                  continuous_map
                     (subtopology X (X closure_of s \<inter> u),X') g \<and>
                  \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `{x \<in> topspace X.
         \<exists>l. limitin X' f l (atin X x within s)}` THEN
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
   "\<And>X s X' f.
        s \<subseteq> topspace X \<and>
        (metrizable_space X \<or> topspace X \<subseteq> X closure_of s) \<and>
        completely_metrizable_space X' \<and>
        continuous_map(subtopology X s,X') f
        \<Longrightarrow> \<exists>u g. gdelta_in X u \<and>
                  s \<subseteq> u \<and>
                  u \<subseteq> X closure_of s \<and>
                  continuous_map(subtopology X u,X') g \<and>
                  \<forall>x. x \<in> s \<Longrightarrow> g x = f x"
oops
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X::A topology`; `s::A=>bool`; `X':B topology`; `f::A=>B`]
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


let capped_metric = new_definition
 `capped_metric d (m::A metric) =
        if d \<le> 0 then m
        else metric(M,(\<lambda>(x,y). min d (d x y)))`;;

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
    EXISTS_TAC `\<Union> {{i. i \<in> l \<and>
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


let euclidean_space = new_definition
 `euclidean_space n = subtopology (product_topology UNIV (\<lambda>i. euclideanreal))
                         {x. \<forall>i. (i \<notin> 1..n) \<Longrightarrow> x i = 0}`;;

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

let nsphere = new_definition
 `nsphere n = subtopology (euclidean_space (Suc n))
                          { x | sum(1..n+1) (\<lambda>i. x i ^ 2) = 1 }`;;

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
     `(a = b \<Longrightarrow> t = 1 / 2) \<and> (t = 1 / 2 \<Longrightarrow> (a \<noteq> b))
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
       `1 / 2 * x = 1 / 2 * y \<longleftrightarrow> x = y`] THEN
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
   ASM_REWRITE_TAC[lipschitz_continuous_map; \<subseteq>; FORALL_IN_IMAGE] THEN
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


let funspace = new_definition
  `funspace s m =
   metric ({f::A=>B | (\<forall>x. x \<in> s \<Longrightarrow> f x \<in> M) \<and>
                     f \<in> EXTENSIONAL s \<and>
                     mbounded (f ` s)},
           (\<lambda>(f,g). if s = {} then 0 else
                    sup {d (f x) g x | x | x \<in> s}))`;;

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


let cfunspace = new_definition
  `cfunspace X m =
   submetric (funspace (topspace X) m)
     {f::A=>B | continuous_map X mtopology f}`;;

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
  REPEAT GEN_TAC THEN ASM_CASES_TAC `topspace (X::A topology) = {}` THEN
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
                completely_metrizable_space X' \<and>
                embedding_map X X' f \<and>
                X' closure_of (f ` (topspace X)) = topspace X'"
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
   INTRO_TAC "@r. rpos ball" THEN EXISTS_TAC `min r 1 / 2` THEN
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
         \<Longrightarrow> mtopology interior_of (\<Union> g) = {}"
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
   "\<And>X g:(A=>bool)->bool.
        (completely_metrizable_space X \<or>
         locally_compact_space X \<and>
         (Hausdorff_space X \<or> regular_space X)) \<and>
        countable g \<and>
        (\<forall>t. t \<in> g \<Longrightarrow> closedin X t \<and> X interior_of t = {})
        \<Longrightarrow> X interior_of (\<Union> g) = {}"
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
        \<Union> u = topspace X
         \<Longrightarrow> u = {topspace X}"
oops
  lemma lemma:
   (`\<Union> (f ` s \<union> g ` s) =
     \<Union> (image (\<lambda>x. f x \<union> g x) s)"
oops
    REWRITE_TAC[UNIONS_UNION; UNIONS_IMAGE] THEN SET_TAC[])
in

  REWRITE_TAC[REAL_CLOSED_IN] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `v = image (\<lambda>c::A=>bool. X frontier_of c) u` THEN
  ABBREV_TAC `b::A=>bool = \<Union> v` THEN
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
     `(\<forall>s. s \<in> u \<and> s \<subseteq> \<Union> u \<and> f s = {} \<Longrightarrow> s = {}) \<and>
      \<not> (\<Union> u = {})
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
          \<Union> (image (\<lambda>c::A=>bool. X interior_of c) u)`
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
         `disjnt (\<Union> s) (\<Union> t) \<longleftrightarrow>
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
        \<Union> u = {a..b}
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
   `subtopology (X::A topology)
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
    `{{x \<in> topspace X. (g::A=>A->real) a x \<in> {t. t < 1 / 2}} |
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
   `\<lambda>x. 2 * max 0 (inf {(g::A=>A->real) a x | a \<in> k} - 1 / 2)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; \<subseteq>; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[REAL_ARITH `2 * max 0 (x - 1 / 2) = 0 \<longleftrightarrow> x \<le> 1 / 2`;
              REAL_ARITH `2 * max 0 (x - 1 / 2) = 1 \<longleftrightarrow> x = 1`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REWRITE_TAC[REAL_ARITH `0 \<le> 2 * max 0 a`;
              REAL_ARITH  `2 * max 0 (x - 1 / 2) \<le> 1 \<longleftrightarrow> x \<le> 1`] THEN
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
    REWRITE_TAC[lipschitz_continuous_map; REAL_EUCLIDEAN_METRIC] THEN
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
   `prod_topology (X::A topology) (product_topology {()} (\<lambda>i. euclideanreal))
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
            \<Longrightarrow> (X::A topology) dimension_le (n::int)`;;

lemma dimension_le_neighbourhood_base:
   "\<And>(X::A topology) n.
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
   "\<And>(X::A topology) (X':B topology) n.
        X homeomorphic_space X'
        \<Longrightarrow> (X dimension_le n \<longleftrightarrow> X' dimension_le n)"
oops
  lemma lemma:
   "\<And>n (X::A topology) (X':B topology).
        X homeomorphic_space X' \<and> X dimension_le (n - 1)
        \<Longrightarrow> X' dimension_le (n - 1)"
oops
    INDUCT_TAC THENL
     [CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[DIMENSION_LE_EQ_EMPTY] THEN
      MESON_TAC[HOMEOMORPHIC_EMPTY_SPACE];
      REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ARITH `(x + y) - y::int = x`]] THEN
    MAP_EVERY X_GEN_TAC [`X::A topology`; `X':B topology`] THEN
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
   "\<And>X X' n r.
        retraction_map X X' r \<and> X dimension_le n
        \<Longrightarrow> X' dimension_le n"
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
   "\<And>(X::A topology) s n.
        hereditarily normal_space X \<and>
        (\<exists>u. u HAS_SIZE n \<and>
             pairwise (separatedin X) u \<and>
             (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
             \<Union> u = topspace X - s)
        \<Longrightarrow>  \<exists>c. closedin X c \<and> c \<subseteq> s \<and>
                 \<forall>d. closedin X d \<and> c \<subseteq> d \<and> d \<subseteq> s
                     \<Longrightarrow> \<exists>u. u HAS_SIZE n \<and>
                             pairwise (separatedin X) u \<and>
                             (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
                             \<Union> u = topspace X - d"
oops
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `u:(A=>bool)->bool` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `u:(A=>bool)->bool` \<circ>
    GEN_REWRITE_RULE id [HEREDITARILY_NORMAL_SEPARATION_PAIRWISE]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[HAS_SIZE]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `f:(A=>bool)->(A=>bool)` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC
   `topspace X - \<Union> (image (f:(A=>bool)->(A=>bool)) u)` THEN
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
   "\<And>(X::A topology) s.
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
   "\<And>(X::A topology) s n.
        locally_connected_space X \<and> hereditarily normal_space X
        \<Longrightarrow> ((\<exists>u. u HAS_SIZE n \<and>
                  pairwise (separatedin X) u \<and>
                  (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
                  \<Union> u = topspace X - s) \<longleftrightarrow>
             (\<exists>c. closedin X c \<and> c \<subseteq> s \<and>
                  \<forall>d. closedin X d \<and> c \<subseteq> d \<and> d \<subseteq> s
                      \<Longrightarrow> \<exists>u. u HAS_SIZE n \<and>
                              pairwise (separatedin X) u \<and>
                              (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
                              \<Union> u = topspace X - d))"
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
     `(topspace X - s - \<Union> (v - {t})) insert
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
  REMOVE_THEN "*" (MP_TAC \<circ> SPEC `topspace X - \<Union> u::A=>bool`) THEN
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
   "\<And>(X::A topology) s.
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
     \<Union> u = topspace(subtopology X (topspace X - s)) \<longleftrightarrow>
     pairwise (separatedin X) u \<and>
     (\<forall>t. t \<in> u \<Longrightarrow> (t \<noteq> {})) \<and>
     \<Union> u = topspace X - s"
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
