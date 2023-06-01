section \<open>Abstract Metric Spaces\<close>

theory AMS
  imports
    "HOL-Analysis.Analysis" "HOL-Library.Equipollence"
    "HOL-ex.Sketch_and_Explore"
begin

(*MAYBE FOR Analysis/Elementary_Topology*)
thm continuous_closed_imp_Cauchy_continuous uniformly_continuous_imp_Cauchy_continuous
    definition Cauchy_continuous_on where
      "Cauchy_continuous_on \<equiv> \<lambda>S f. \<forall>\<sigma>. Cauchy \<sigma> \<longrightarrow> range \<sigma> \<subseteq> S \<longrightarrow> Cauchy (f \<circ> \<sigma>)"
    
    lemma continuous_closed_imp_Cauchy_continuous:
      fixes S :: "('a::complete_space) set"
      shows "\<lbrakk>continuous_on S f; closed S\<rbrakk> \<Longrightarrow> Cauchy_continuous_on S f"
      unfolding Cauchy_continuous_on_def
      by (metis LIMSEQ_imp_Cauchy completeE complete_eq_closed continuous_on_sequentially range_subsetD)
    
    lemma uniformly_continuous_imp_Cauchy_continuous:
      fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
      shows "uniformly_continuous_on S f \<Longrightarrow> Cauchy_continuous_on S f"
      by (simp add: uniformly_continuous_on_def Cauchy_continuous_on_def Cauchy_def image_subset_iff) metis
    
    lemma Cauchy_continuous_on_imp_continuous:
      fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
      assumes "Cauchy_continuous_on S f"
      shows "continuous_on S f"
    proof -
      have False if x: "\<forall>n. \<exists>x'\<in>S. dist x' x < inverse(Suc n) \<and> \<not> dist (f x') (f x) < \<epsilon>" "\<epsilon>>0" "x \<in> S" for x and \<epsilon>::real
      proof -
        obtain \<rho> where \<rho>: "\<forall>n. \<rho> n \<in> S" and dx: "\<forall>n. dist (\<rho> n) x < inverse(Suc n)" and dfx: "\<forall>n. \<not> dist (f (\<rho> n)) (f x) < \<epsilon>"
          using x by metis
        define \<sigma> where "\<sigma> \<equiv> \<lambda>n. if even n then \<rho> n else x"
        with \<rho> \<open>x \<in> S\<close> have "range \<sigma> \<subseteq> S"
          by auto
        have "\<sigma> \<longlonglongrightarrow> x"
          unfolding tendsto_iff
        proof (intro strip)
          fix e :: real
          assume "e>0"
          then obtain N where "inverse (Suc N) < e"
            using reals_Archimedean by blast
          then have "\<forall>n. N \<le> n \<longrightarrow> dist (\<rho> n) x < e"
            by (smt (verit, ccfv_SIG) dx inverse_Suc inverse_less_iff_less inverse_positive_iff_positive of_nat_Suc of_nat_mono)
          with \<open>e>0\<close> show "\<forall>\<^sub>F n in sequentially. dist (\<sigma> n) x < e"
            by (auto simp add: eventually_sequentially \<sigma>_def)
        qed
        then have "Cauchy \<sigma>"
          by (intro LIMSEQ_imp_Cauchy)
        then have Cf: "Cauchy (f \<circ> \<sigma>)"
          by (meson Cauchy_continuous_on_def \<open>range \<sigma> \<subseteq> S\<close> assms)
        have "(f \<circ> \<sigma>) \<longlonglongrightarrow> f x"
          unfolding tendsto_iff 
        proof (intro strip)
          fix e :: real
          assume "e>0"
          then obtain N where N: "\<forall>m\<ge>N. \<forall>n\<ge>N. dist ((f \<circ> \<sigma>) m) ((f \<circ> \<sigma>) n) < e"
            using Cf unfolding Cauchy_def by presburger
          moreover have "(f \<circ> \<sigma>) (Suc(N+N)) = f x"
            by (simp add: \<sigma>_def)
          ultimately have "\<forall>n\<ge>N. dist ((f \<circ> \<sigma>) n) (f x) < e"
            by (metis add_Suc le_add2)
          then show "\<forall>\<^sub>F n in sequentially. dist ((f \<circ> \<sigma>) n) (f x) < e"
            using eventually_sequentially by blast
        qed
        moreover have "\<And>n. \<not> dist (f (\<sigma> (2*n))) (f x) < \<epsilon>"
          using dfx by (simp add: \<sigma>_def)
        ultimately show False
          using \<open>\<epsilon>>0\<close> by (fastforce simp: mult_2 nat_le_iff_add tendsto_iff eventually_sequentially)
      qed
      then show ?thesis
        unfolding continuous_on_iff by (meson inverse_Suc)
    qed
    

    lemma mtopology_of_euclidean [simp]: "mtopology_of euclidean_metric = euclidean"
      by (simp add: Met_TC.mtopology_def mtopology_of_def)
    
    lemma prod_dist_dist [simp]: "prod_dist dist dist = dist"
      by (simp add: prod_dist_def dist_prod_def fun_eq_iff)
    
    lemma prod_metric_euclidean [simp]:
      "prod_metric euclidean_metric euclidean_metric = euclidean_metric"
      by (simp add: prod_metric_def euclidean_metric_def)
    
    lemma mtopology_of_submetric: "mtopology_of (submetric m A) = subtopology (mtopology_of m) A"
    proof -
      interpret Submetric "mspace m" "mdist m" "A \<inter> mspace m"
        using Metric_space_mspace_mdist Submetric.intro Submetric_axioms.intro inf_le2 by blast
      have "sub.mtopology = subtopology (mtopology_of m) A"
        by (metis inf_commute mtopology_of_def mtopology_submetric subtopology_mspace subtopology_subtopology)
      then show ?thesis
        by (simp add: submetric_def)
    qed
    

(*NEEDS LEPOLL (Used nowhere in Analysis) *)
lemma card_lepoll_quasi_components_of_topspace:
  "quasi_components_of X \<lesssim> topspace X"
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
    
    context Metric_space12
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
        

    subsection \<open>Three strong notions of continuity for metric spaces\<close>
    
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
      shows "Lipschitz_continuous_map m1 m3 (g \<circ> f)"
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
    
    text \<open>Equivalence between "abstract" and "type class" Lipschitz notions, 
    for all types in the metric space class\<close>
    lemma Lipschitz_map_euclidean [simp]:
      "Lipschitz_continuous_map euclidean_metric euclidean_metric f
         \<longleftrightarrow> (\<exists>B. lipschitz_on B UNIV f)"  (is "?lhs \<longleftrightarrow> ?rhs")
    proof
      show "?lhs \<Longrightarrow> ?rhs"
        by (force simp add: Lipschitz_continuous_map_pos lipschitz_on_def less_le_not_le)
      show "?rhs \<Longrightarrow> ?lhs"
      by (metis Lipschitz_continuous_map_def lipschitz_onD mdist_euclidean_metric mspace_euclidean_metric top_greatest)
    qed
    
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
    
    lemma uniformly_continuous_map_id [simp]:
       "uniformly_continuous_map m1 m1 (\<lambda>x. x)"
      by (metis image_ident order_refl uniformly_continuous_map_def)
    
    lemma uniformly_continuous_map_compose:
      assumes f: "uniformly_continuous_map m1 m2 f" and g: "uniformly_continuous_map m2 m3 g"
      shows "uniformly_continuous_map m1 m3 (g \<circ> f)"
      by (smt (verit, ccfv_threshold) comp_apply f g image_subset_iff uniformly_continuous_map_def)
    
    lemma uniformly_continuous_map_real_const [simp]:
       "uniformly_continuous_map m euclidean_metric (\<lambda>x. c)"
      by (simp add: euclidean_metric_def uniformly_continuous_map_const)
    
    text \<open>Equivalence between "abstract" and "type class" notions\<close>
    lemma uniformly_continuous_map_euclidean [simp]:
      "uniformly_continuous_map (submetric euclidean_metric S) euclidean_metric f
         = uniformly_continuous_on S f"
      by (auto simp add: uniformly_continuous_map_def uniformly_continuous_on_def)
    
    subsubsection \<open>Cauchy continuity\<close>
    
    definition Cauchy_continuous_map where
     "Cauchy_continuous_map \<equiv>
      \<lambda>m1 m2 f. \<forall>\<sigma>. Metric_space.MCauchy (mspace m1) (mdist m1) \<sigma> 
                \<longrightarrow> Metric_space.MCauchy (mspace m2) (mdist m2) (f \<circ> \<sigma>)"
    
    lemma Cauchy_continuous_map_euclidean [simp]:
      "Cauchy_continuous_map (submetric euclidean_metric S) euclidean_metric f
         = Cauchy_continuous_on S f"
      by (auto simp add: Cauchy_continuous_map_def Cauchy_continuous_on_def Cauchy_def Met_TC.subspace Metric_space.MCauchy_def)
    
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
      shows "Cauchy_continuous_map m1 m3 (g \<circ> f)"
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
    
    context Metric_space12
    begin
    
    lemma Cauchy_continuous_imp_continuous_map:
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
        then have "M2.MCauchy (f \<circ> (\<lambda>n. if even n then \<sigma> (n div 2) else x))"
          using assms by (simp add: Cauchy_continuous_map_def)
        then show "limitin M2.mtopology (f \<circ> \<sigma>) (f x) sequentially"
          using M2.MCauchy_interleaving [of "f \<circ> \<sigma>" "f x"]
          by (simp add: o_def if_distrib cong: if_cong)
      qed
    qed
    
    lemma continuous_imp_Cauchy_continuous_map:
      assumes "M1.mcomplete"
        and f: "continuous_map M1.mtopology M2.mtopology f"
      shows "Cauchy_continuous_map (metric (M1,d1)) (metric (M2,d2)) f"
      unfolding Cauchy_continuous_map_def
    proof clarsimp
      fix \<sigma>
      assume \<sigma>: "M1.MCauchy \<sigma>"
      then obtain y where y: "limitin M1.mtopology \<sigma> y sequentially"
        using M1.mcomplete_def assms by blast
      have "range (f \<circ> \<sigma>) \<subseteq> M2"
        using \<sigma> f by (simp add: M2.subspace M1.MCauchy_def M1.metric_continuous_map image_subset_iff)
      then show "M2.MCauchy (f \<circ> \<sigma>)"
        using continuous_map_limit [OF f y] M2.convergent_imp_MCauchy
        by blast
    qed
    
    end
    
    text \<open>The same outside the locale\<close>
    lemma Cauchy_continuous_imp_continuous_map:
      assumes "Cauchy_continuous_map m1 m2 f"
      shows "continuous_map (mtopology_of m1) (mtopology_of m2) f"
      using assms Metric_space12.Cauchy_continuous_imp_continuous_map [OF Metric_space12_mspace_mdist]
      by (auto simp add: mtopology_of_def)
    
    lemma continuous_imp_Cauchy_continuous_map:
      assumes "Metric_space.mcomplete (mspace m1) (mdist m1)"
        and "continuous_map (mtopology_of m1) (mtopology_of m2) f"
      shows "Cauchy_continuous_map m1 m2 f"
      using assms Metric_space12.continuous_imp_Cauchy_continuous_map [OF Metric_space12_mspace_mdist]
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
    
    lemma Cauchy_imp_uniformly_continuous_map:
      assumes f: "Cauchy_continuous_map m1 m2 f"
        and tbo: "Metric_space.mtotally_bounded (mspace m1) (mdist m1) (mspace m1)"
      shows "uniformly_continuous_map m1 m2 f"
      unfolding uniformly_continuous_map_sequentially_alt imp_conjL
    proof (intro conjI strip)
      show "f ` mspace m1 \<subseteq> mspace m2"
        by (simp add: Cauchy_continuous_map_image f)
      interpret M1: Metric_space "mspace m1" "mdist m1"
        by (simp add: Metric_space_mspace_mdist)
      interpret M2: Metric_space "mspace m2" "mdist m2"
        by (simp add: Metric_space_mspace_mdist)
      fix \<epsilon> :: real and \<rho> \<sigma> 
      assume "\<epsilon> > 0"
        and \<rho>: "range \<rho> \<subseteq> mspace m1"
        and \<sigma>: "range \<sigma> \<subseteq> mspace m1"
        and 0: "(\<lambda>n. mdist m1 (\<rho> n) (\<sigma> n)) \<longlonglongrightarrow> 0"
      then obtain r1 where "strict_mono r1" and r1: "M1.MCauchy (\<rho> \<circ> r1)"
        using M1.mtotally_bounded_sequentially tbo by meson
      then obtain r2 where "strict_mono r2" and r2: "M1.MCauchy (\<sigma> \<circ> r1 \<circ> r2)"
        by (metis M1.mtotally_bounded_sequentially tbo \<sigma> image_comp image_subset_iff range_subsetD)
      define r where "r \<equiv> r1 \<circ> r2"
      have r: "strict_mono r"
        by (simp add: r_def \<open>strict_mono r1\<close> \<open>strict_mono r2\<close> strict_mono_o)
      define \<eta> where "\<eta> \<equiv> \<lambda>n. if even n then (\<rho> \<circ> r) (n div 2) else (\<sigma> \<circ> r) (n div 2)"
      have "M1.MCauchy \<eta>"
        unfolding \<eta>_def M1.MCauchy_interleaving_gen
      proof (intro conjI)
        show "M1.MCauchy (\<rho> \<circ> r)"
          by (simp add: M1.MCauchy_subsequence \<open>strict_mono r2\<close> fun.map_comp r1 r_def)
        show "M1.MCauchy (\<sigma> \<circ> r)"
          by (simp add: fun.map_comp r2 r_def)
        show "(\<lambda>n. mdist m1 ((\<rho> \<circ> r) n) ((\<sigma> \<circ> r) n)) \<longlonglongrightarrow> 0"
          using LIMSEQ_subseq_LIMSEQ [OF 0 r] by (simp add: o_def)
      qed
      then have "Metric_space.MCauchy (mspace m2) (mdist m2) (f \<circ> \<eta>)"
        by (meson Cauchy_continuous_map_def f)
      then have "(\<lambda>n. mdist m2 (f (\<rho> (r n))) (f (\<sigma> (r n)))) \<longlonglongrightarrow> 0"
        using M2.MCauchy_interleaving_gen [of "f \<circ> \<rho> \<circ> r" "f \<circ> \<sigma> \<circ> r"]
        by (simp add: \<eta>_def o_def if_distrib cong: if_cong)
      then show "\<exists>n. mdist m2 (f (\<rho> n)) (f (\<sigma> n)) < \<epsilon>"
        by (meson LIMSEQ_le_const \<open>0 < \<epsilon>\<close> linorder_not_le)
    qed
    
    lemma continuous_imp_uniformly_continuous_map:
       "compact_space (mtopology_of m1) \<and>
            continuous_map (mtopology_of m1) (mtopology_of m2) f
            \<Longrightarrow> uniformly_continuous_map m1 m2 f"
      by (simp add: Cauchy_imp_uniformly_continuous_map continuous_imp_Cauchy_continuous_map
                    Metric_space.compact_space_eq_mcomplete_mtotally_bounded
                    Metric_space_mspace_mdist mtopology_of_def)
    
    lemma continuous_eq_Cauchy_continuous_map:
       "Metric_space.mcomplete (mspace m1) (mdist m1) \<Longrightarrow> 
        continuous_map (mtopology_of m1) (mtopology_of m2) f \<longleftrightarrow> Cauchy_continuous_map m1 m2 f"
      using Cauchy_continuous_imp_continuous_map continuous_imp_Cauchy_continuous_map by blast
    
    lemma continuous_eq_uniformly_continuous_map:
       "compact_space (mtopology_of m1) 
        \<Longrightarrow> continuous_map (mtopology_of m1) (mtopology_of m2) f \<longleftrightarrow>
            uniformly_continuous_map m1 m2 f"
      using continuous_imp_uniformly_continuous_map uniformly_continuous_imp_continuous_map by blast
    
    lemma Cauchy_eq_uniformly_continuous_map:
       "Metric_space.mtotally_bounded (mspace m1) (mdist m1) (mspace m1)
        \<Longrightarrow> Cauchy_continuous_map m1 m2 f \<longleftrightarrow> uniformly_continuous_map m1 m2 f"
      using Cauchy_imp_uniformly_continuous_map uniformly_imp_Cauchy_continuous_map by blast
    
    lemma Lipschitz_continuous_map_projections:
      "Lipschitz_continuous_map (prod_metric m1 m2) m1 fst"
      "Lipschitz_continuous_map (prod_metric m1 m2) m2 snd"
      by (simp add: Lipschitz_continuous_map_def prod_dist_def; 
          metis mult_numeral_1 real_sqrt_sum_squares_ge1 real_sqrt_sum_squares_ge2)+
    
    lemma Lipschitz_continuous_map_pairwise:
       "Lipschitz_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow>
        Lipschitz_continuous_map m m1 (fst \<circ> f) \<and> Lipschitz_continuous_map m m2 (snd \<circ> f)"
       (is "?lhs \<longleftrightarrow> ?rhs")
    proof 
      show "?lhs \<Longrightarrow> ?rhs"
        by (simp add: Lipschitz_continuous_map_compose Lipschitz_continuous_map_projections)
      have "Lipschitz_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f1 x, f2 x))"
        if f1: "Lipschitz_continuous_map m m1 f1" and f2: "Lipschitz_continuous_map m m2 f2" for f1 f2
      proof -
        obtain B1 where "B1 > 0" 
          and B1: "\<And>x y. \<lbrakk>x \<in> mspace m; y \<in> mspace m\<rbrakk> \<Longrightarrow> mdist m1 (f1 x) (f1 y) \<le> B1 * mdist m x y"
          by (meson Lipschitz_continuous_map_pos f1)
        obtain B2 where "B2 > 0" 
          and B2: "\<And>x y. \<lbrakk>x \<in> mspace m; y \<in> mspace m\<rbrakk> \<Longrightarrow> mdist m2 (f2 x) (f2 y) \<le> B2 * mdist m x y"
          by (meson Lipschitz_continuous_map_pos f2)
        show ?thesis
          unfolding Lipschitz_continuous_map_pos
        proof (intro exI conjI strip)
          have f1im: "f1 ` mspace m \<subseteq> mspace m1"
            by (simp add: Lipschitz_continuous_map_image f1)
          moreover have f2im: "f2 ` mspace m \<subseteq> mspace m2"
            by (simp add: Lipschitz_continuous_map_image f2)
          ultimately show "(\<lambda>x. (f1 x, f2 x)) ` mspace m \<subseteq> mspace (prod_metric m1 m2)"
            by auto
          show "B1+B2 > 0"
            using \<open>0 < B1\<close> \<open>0 < B2\<close> by linarith
          fix x y
          assume xy: "x \<in> mspace m" "y \<in> mspace m"
          with f1im f2im have "mdist (prod_metric m1 m2) (f1 x, f2 x) (f1 y, f2 y) \<le> mdist m1 (f1 x) (f1 y) + mdist m2 (f2 x) (f2 y)"
            unfolding mdist_prod_metric
            by (intro Metric_space12.prod_metric_le_components [OF Metric_space12_mspace_mdist]) auto
          also have "... \<le> (B1+B2) * mdist m x y"
            using B1 [OF xy] B2 [OF xy] by (simp add: vector_space_over_itself.scale_left_distrib) 
          finally show "mdist (prod_metric m1 m2) (f1 x, f2 x) (f1 y, f2 y) \<le> (B1+B2) * mdist m x y" .
        qed
      qed
      then show "?rhs \<Longrightarrow> ?lhs"
        by force
    qed
    
    lemma uniformly_continuous_map_pairwise:
       "uniformly_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow> 
        uniformly_continuous_map m m1 (fst \<circ> f) \<and> uniformly_continuous_map m m2 (snd \<circ> f)"
       (is "?lhs \<longleftrightarrow> ?rhs")
    proof 
      show "?lhs \<Longrightarrow> ?rhs"
        by (simp add: Lipschitz_continuous_map_projections Lipschitz_imp_uniformly_continuous_map uniformly_continuous_map_compose)
      have "uniformly_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f1 x, f2 x))"
        if f1: "uniformly_continuous_map m m1 f1" and f2: "uniformly_continuous_map m m2 f2" for f1 f2
      proof -
        show ?thesis
          unfolding uniformly_continuous_map_def
        proof (intro conjI strip)
          have f1im: "f1 ` mspace m \<subseteq> mspace m1"
            by (simp add: uniformly_continuous_map_image f1)
          moreover have f2im: "f2 ` mspace m \<subseteq> mspace m2"
            by (simp add: uniformly_continuous_map_image f2)
          ultimately show "(\<lambda>x. (f1 x, f2 x)) ` mspace m \<subseteq> mspace (prod_metric m1 m2)"
            by auto
          fix \<epsilon>:: real
          assume "\<epsilon> > 0"
          obtain \<delta>1 where "\<delta>1>0" 
            and \<delta>1: "\<And>x y. \<lbrakk>x \<in> mspace m; y \<in> mspace m; mdist m y x < \<delta>1\<rbrakk> \<Longrightarrow> mdist m1 (f1 y) (f1 x) < \<epsilon>/2"
            by (metis \<open>0 < \<epsilon>\<close> f1 half_gt_zero uniformly_continuous_map_def)
          obtain \<delta>2 where "\<delta>2>0" 
            and \<delta>2: "\<And>x y. \<lbrakk>x \<in> mspace m; y \<in> mspace m; mdist m y x < \<delta>2\<rbrakk> \<Longrightarrow> mdist m2 (f2 y) (f2 x) < \<epsilon>/2"
            by (metis \<open>0 < \<epsilon>\<close> f2 half_gt_zero uniformly_continuous_map_def)
          show "\<exists>\<delta>>0. \<forall>x\<in>mspace m. \<forall>y\<in>mspace m. mdist m y x < \<delta> \<longrightarrow> mdist (prod_metric m1 m2) (f1 y, f2 y) (f1 x, f2 x) < \<epsilon>"
          proof (intro exI conjI strip)
            show "min \<delta>1 \<delta>2>0"
              using \<open>0 < \<delta>1\<close> \<open>0 < \<delta>2\<close> by auto
            fix x y
            assume xy: "x \<in> mspace m" "y \<in> mspace m" and d: "mdist m y x < min \<delta>1 \<delta>2"
            have *: "mdist m1 (f1 y) (f1 x) < \<epsilon>/2" "mdist m2 (f2 y) (f2 x) < \<epsilon>/2"
              using \<delta>1 \<delta>2 d xy by auto
            have "mdist (prod_metric m1 m2) (f1 y, f2 y) (f1 x, f2 x) \<le> mdist m1 (f1 y) (f1 x) + mdist m2 (f2 y) (f2 x)"
              unfolding mdist_prod_metric using f1im f2im xy
              by (intro Metric_space12.prod_metric_le_components [OF Metric_space12_mspace_mdist]) auto
            also have "... < \<epsilon>/2 + \<epsilon>/2"
              using * by simp
            finally show "mdist (prod_metric m1 m2) (f1 y, f2 y) (f1 x, f2 x) < \<epsilon>"
              by simp
          qed
        qed
      qed
      then show "?rhs \<Longrightarrow> ?lhs"
        by force
    qed
    
    lemma Cauchy_continuous_map_pairwise:
       "Cauchy_continuous_map m (prod_metric m1 m2) f \<longleftrightarrow> Cauchy_continuous_map m m1 (fst \<circ> f) \<and> Cauchy_continuous_map m m2 (snd \<circ> f)"
      by (auto simp: Cauchy_continuous_map_def Metric_space12.MCauchy_prod_metric[OF Metric_space12_mspace_mdist] comp_assoc)
    
    lemma Lipschitz_continuous_map_paired:
       "Lipschitz_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
            Lipschitz_continuous_map m m1 f \<and> Lipschitz_continuous_map m m2 g"
      by (simp add: Lipschitz_continuous_map_pairwise o_def)
    
    lemma uniformly_continuous_map_paired:
       "uniformly_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
            uniformly_continuous_map m m1 f \<and> uniformly_continuous_map m m2 g"
      by (simp add: uniformly_continuous_map_pairwise o_def)
    
    lemma Cauchy_continuous_map_paired:
       "Cauchy_continuous_map m (prod_metric m1 m2) (\<lambda>x. (f x, g x)) \<longleftrightarrow>
            Cauchy_continuous_map m m1 f \<and> Cauchy_continuous_map m m2 g"
      by (simp add: Cauchy_continuous_map_pairwise o_def)
    
    lemma mbounded_Lipschitz_continuous_image:
      assumes f: "Lipschitz_continuous_map m1 m2 f" and S: "Metric_space.mbounded (mspace m1) (mdist m1) S"
      shows "Metric_space.mbounded (mspace m2) (mdist m2) (f`S)"
    proof -
      obtain B where fim: "f ` mspace m1 \<subseteq> mspace m2"
        and "B>0" and B: "\<And>x y. \<lbrakk>x \<in> mspace m1; y \<in> mspace m1\<rbrakk> \<Longrightarrow> mdist m2 (f x) (f y) \<le> B * mdist m1 x y"
        by (meson Lipschitz_continuous_map_pos f)
      show ?thesis
        unfolding Metric_space.mbounded_alt_pos [OF Metric_space_mspace_mdist]
      proof
        obtain C where "S \<subseteq> mspace m1" and "C>0" and C: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> mdist m1 x y \<le> C"
          using S by (auto simp: Metric_space.mbounded_alt_pos [OF Metric_space_mspace_mdist])
        show "f ` S \<subseteq> mspace m2"
          using fim \<open>S \<subseteq> mspace m1\<close> by blast
        have "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> mdist m2 (f x) (f y) \<le> B * C"
          by (smt (verit) B C \<open>0 < B\<close> \<open>S \<subseteq> mspace m1\<close> mdist_nonneg mult_mono subsetD)
        moreover have "B*C > 0"
          by (simp add: \<open>0 < B\<close> \<open>0 < C\<close>)
        ultimately show "\<exists>B>0. \<forall>x\<in>f ` S. \<forall>y\<in>f ` S. mdist m2 x y \<le> B"
          by auto
      qed
    qed
    
    lemma mtotally_bounded_Cauchy_continuous_image:
      assumes f: "Cauchy_continuous_map m1 m2 f" and S: "Metric_space.mtotally_bounded (mspace m1) (mdist m1) S"
      shows "Metric_space.mtotally_bounded (mspace m2) (mdist m2) (f ` S)"
      unfolding Metric_space.mtotally_bounded_sequentially[OF Metric_space_mspace_mdist]
    proof (intro conjI strip)
      have "S \<subseteq> mspace m1"
        using S by (simp add: Metric_space.mtotally_bounded_sequentially[OF Metric_space_mspace_mdist])
      then show "f ` S \<subseteq> mspace m2"
        using Cauchy_continuous_map_image f by blast
      fix \<sigma> :: "nat \<Rightarrow> 'b"
      assume "range \<sigma> \<subseteq> f ` S"
      then have "\<forall>n. \<exists>x. \<sigma> n = f x \<and> x \<in> S"
        by (meson imageE range_subsetD)
      then obtain \<rho> where \<rho>: "\<And>n. \<sigma> n = f (\<rho> n)" "range \<rho> \<subseteq> S"
        by (metis image_subset_iff)
      then have "\<sigma> = f \<circ> \<rho>"
        by fastforce
      obtain r where "strict_mono r" "Metric_space.MCauchy (mspace m1) (mdist m1) (\<rho> \<circ> r)"
        by (meson \<rho> S Metric_space.mtotally_bounded_sequentially[OF Metric_space_mspace_mdist])
      then have "Metric_space.MCauchy (mspace m2) (mdist m2) (f \<circ> \<rho> \<circ> r)"
        using f unfolding Cauchy_continuous_map_def by (metis fun.map_comp)
      then show "\<exists>r. strict_mono r \<and> Metric_space.MCauchy (mspace m2) (mdist m2) (\<sigma> \<circ> r)"
        using \<open>\<sigma> = f \<circ> \<rho>\<close> \<open>strict_mono r\<close> by blast
    qed
    
    lemma Lipschitz_coefficient_pos:
      assumes "x \<in> mspace m" "y \<in> mspace m" "f x \<noteq> f y" 
        and "f ` mspace m \<subseteq> mspace m2" 
        and "\<And>x y. \<lbrakk>x \<in> mspace m; y \<in> mspace m\<rbrakk>
                \<Longrightarrow> mdist m2 (f x) (f y) \<le> k * mdist m x y"
      shows  "0 < k"
      using assms by (smt (verit, best) image_subset_iff mdist_nonneg mdist_zero mult_nonpos_nonneg)
    
    lemma Lipschitz_continuous_map_metric:
       "Lipschitz_continuous_map (prod_metric m m) euclidean_metric (\<lambda>(x,y). mdist m x y)"
    proof -
      have "\<And>x y x' y'. \<lbrakk>x \<in> mspace m; y \<in> mspace m; x' \<in> mspace m; y' \<in> mspace m\<rbrakk>
           \<Longrightarrow> \<bar>mdist m x y - mdist m x' y'\<bar> \<le> 2 * sqrt ((mdist m x x')\<^sup>2 + (mdist m y y')\<^sup>2)"
        by (smt (verit, del_insts) mdist_commute mdist_triangle real_sqrt_sum_squares_ge2)
      then show ?thesis
        by (fastforce simp add: Lipschitz_continuous_map_def prod_dist_def dist_real_def)
    qed
    
    lemma Lipschitz_continuous_map_mdist:
      assumes f: "Lipschitz_continuous_map m m' f" 
        and g: "Lipschitz_continuous_map m m' g"
      shows "Lipschitz_continuous_map m euclidean_metric (\<lambda>x. mdist m' (f x) (g x))"
        (is "Lipschitz_continuous_map m _ ?h")
    proof -
      have eq: "?h = ((\<lambda>(x,y). mdist m' x y) \<circ> (\<lambda>x. (f x,g x)))"
        by force
      show ?thesis
        unfolding eq
      proof (rule Lipschitz_continuous_map_compose)
        show "Lipschitz_continuous_map m (prod_metric m' m') (\<lambda>x. (f x, g x))"
          by (simp add: Lipschitz_continuous_map_paired f g)
        show "Lipschitz_continuous_map (prod_metric m' m') euclidean_metric (\<lambda>(x,y). mdist m' x y)"
          by (simp add: Lipschitz_continuous_map_metric)
      qed
    qed
    
    lemma uniformly_continuous_map_mdist:
      assumes f: "uniformly_continuous_map m m' f" 
        and g: "uniformly_continuous_map m m' g"
      shows "uniformly_continuous_map m euclidean_metric (\<lambda>x. mdist m' (f x) (g x))"
        (is "uniformly_continuous_map m _ ?h")
    proof -
      have eq: "?h = ((\<lambda>(x,y). mdist m' x y) \<circ> (\<lambda>x. (f x,g x)))"
        by force
      show ?thesis
        unfolding eq
      proof (rule uniformly_continuous_map_compose)
        show "uniformly_continuous_map m (prod_metric m' m') (\<lambda>x. (f x, g x))"
          by (simp add: uniformly_continuous_map_paired f g)
        show "uniformly_continuous_map (prod_metric m' m') euclidean_metric (\<lambda>(x,y). mdist m' x y)"
          by (simp add: Lipschitz_continuous_map_metric Lipschitz_imp_uniformly_continuous_map)
      qed
    qed
    
    lemma Cauchy_continuous_map_mdist:
      assumes f: "Cauchy_continuous_map m m' f" 
        and g: "Cauchy_continuous_map m m' g"
      shows "Cauchy_continuous_map m euclidean_metric (\<lambda>x. mdist m' (f x) (g x))"
        (is "Cauchy_continuous_map m _ ?h")
    proof -
      have eq: "?h = ((\<lambda>(x,y). mdist m' x y) \<circ> (\<lambda>x. (f x,g x)))"
        by force
      show ?thesis
        unfolding eq
      proof (rule Cauchy_continuous_map_compose)
        show "Cauchy_continuous_map m (prod_metric m' m') (\<lambda>x. (f x, g x))"
          by (simp add: Cauchy_continuous_map_paired f g)
        show "Cauchy_continuous_map (prod_metric m' m') euclidean_metric (\<lambda>(x,y). mdist m' x y)"
          by (simp add: Lipschitz_continuous_map_metric Lipschitz_imp_Cauchy_continuous_map)
      qed
    qed
    
    lemma mtopology_of_prod_metric [simp]:
        "mtopology_of (prod_metric m1 m2) = prod_topology (mtopology_of m1) (mtopology_of m2)"
      by (simp add: mtopology_of_def Metric_space12.mtopology_prod_metric[OF Metric_space12_mspace_mdist])
    
    lemma continuous_map_metric:
       "continuous_map (prod_topology (mtopology_of m) (mtopology_of m)) euclidean
          (\<lambda>(x,y). mdist m x y)"
      using Lipschitz_continuous_imp_continuous_map [OF Lipschitz_continuous_map_metric]
      by auto
    
    lemma continuous_map_mdist_alt:
      assumes "continuous_map X (prod_topology (mtopology_of m) (mtopology_of m)) f"
      shows "continuous_map X euclidean (\<lambda>x. case_prod (mdist m) (f x))"
        (is "continuous_map _ _ ?h")
    proof -
      have eq: "?h = case_prod (mdist m) \<circ> f"
        by force
      show ?thesis
        unfolding eq
        using assms continuous_map_compose continuous_map_metric by blast
    qed
    
    lemma continuous_map_mdist:
      assumes f: "continuous_map X (mtopology_of m) f" 
          and g: "continuous_map X (mtopology_of m) g"
      shows "continuous_map X euclidean (\<lambda>x. mdist m (f x) (g x))"
        (is "continuous_map X _ ?h")
    proof -
      have eq: "?h = ((\<lambda>(x,y). mdist m x y) \<circ> (\<lambda>x. (f x,g x)))"
        by force
      show ?thesis
        unfolding eq
      proof (rule continuous_map_compose)
        show "continuous_map X (prod_topology (mtopology_of m) (mtopology_of m)) (\<lambda>x. (f x, g x))"
          by (simp add: continuous_map_paired f g)
      qed (simp add: continuous_map_metric)
    qed
    
    lemma continuous_on_mdist:
       "a \<in> mspace m \<Longrightarrow> continuous_map (mtopology_of m) euclidean (mdist m a)"
      by (simp add: continuous_map_mdist)
    

subsection \<open>WTF\<close>
    
    lemma (in Metric_space12) isometry_imp_embedding_map:
      assumes fim: "f ` M1 \<subseteq> M2" and d: "\<And>x y. \<lbrakk>x \<in> M1; y \<in> M1\<rbrakk> \<Longrightarrow> d2 (f x) (f y) = d1 x y"
      shows "embedding_map M1.mtopology M2.mtopology f"
    proof -
      have "inj_on f M1"
        by (metis M1.zero d inj_onI)
      then obtain g where g: "\<And>x. x \<in> M1 \<Longrightarrow> g (f x) = x"
        by (metis inv_into_f_f)
      have "homeomorphic_maps M1.mtopology (subtopology M2.mtopology (f ` topspace M1.mtopology)) f g"
        unfolding homeomorphic_maps_def
      proof (intro conjI; clarsimp)
        show "continuous_map M1.mtopology (subtopology M2.mtopology (f ` M1)) f"
          by (metis M1.metric_continuous_map M1.topspace_mtopology M2.Metric_space_axioms continuous_map_into_subtopology d fim order_refl)
        have "Lipschitz_continuous_map (submetric (metric(M2,d2)) (f ` M1)) (metric(M1,d1)) g"
          unfolding Lipschitz_continuous_map_def
        proof (intro conjI exI strip; simp)
          show "d1 (g x) (g y) \<le> 1 * d2 x y" if "x \<in> f ` M1 \<and> x \<in> M2" and "y \<in> f ` M1 \<and> y \<in> M2" for x y
            using that d g by force
        qed (use g in auto)
        then have "continuous_map (mtopology_of (submetric (metric(M2,d2)) (f ` M1))) M1.mtopology g"
          using Lipschitz_continuous_imp_continuous_map by force
        moreover have "mtopology_of (submetric (metric(M2,d2)) (f ` M1)) = subtopology M2.mtopology (f ` M1)"
          by (simp add: mtopology_of_submetric)
        ultimately show "continuous_map (subtopology M2.mtopology (f ` M1)) M1.mtopology g"
           by simp
      qed (use g in auto)
      then show ?thesis
        by (auto simp: embedding_map_def homeomorphic_map_maps)
    qed
    
    lemma (in Metric_space12) isometry_imp_homeomorphic_map:
      assumes fim: "f ` M1 = M2" and d: "\<And>x y. \<lbrakk>x \<in> M1; y \<in> M1\<rbrakk> \<Longrightarrow> d2 (f x) (f y) = d1 x y"
      shows "homeomorphic_map M1.mtopology M2.mtopology f"
      by (metis M1.topspace_mtopology M2.subtopology_mspace d embedding_map_def fim isometry_imp_embedding_map subsetI)



subsection\<open>"Capped" equivalent bounded metrics and general product metrics\<close>

definition (in Metric_space) capped_dist where
  "capped_dist \<equiv> \<lambda>\<delta> x y. if \<delta> > 0 then min \<delta> (d x y) else d x y"

lemma (in Metric_space) capped_dist: "Metric_space M (capped_dist \<delta>)"
proof
  fix x y
  assume "x \<in> M" "y \<in> M"
  then show "(capped_dist \<delta> x y = 0) = (x = y)"
    by (smt (verit, best) capped_dist_def zero)
  fix z 
  assume "z \<in> M"
  show "capped_dist \<delta> x z \<le> capped_dist \<delta> x y + capped_dist \<delta> y z"
    unfolding capped_dist_def using \<open>x \<in> M\<close> \<open>y \<in> M\<close> \<open>z \<in> M\<close> 
    by (smt (verit, del_insts) Metric_space.mdist_pos_eq Metric_space_axioms mdist_reverse_triangle)
qed (use capped_dist_def commute in auto)


definition capped_metric where
  "capped_metric \<delta> m \<equiv> metric(mspace m, Metric_space.capped_dist (mdist m) \<delta>)"

lemma capped_metric:
  "capped_metric \<delta> m = (if \<delta> \<le> 0 then m else metric(mspace m, \<lambda>x y. min \<delta> (mdist m x y)))"
proof -
  interpret Metric_space "mspace m" "mdist m"
    by (simp add: Metric_space_mspace_mdist)
  show ?thesis
    by (auto simp add: capped_metric_def capped_dist_def)
qed

lemma capped_metric_mspace [simp]:
  "mspace (capped_metric \<delta> m) = mspace m"
  apply (simp add: capped_metric not_le)
  by (smt (verit, ccfv_threshold) Metric_space.mspace_metric Metric_space_def Metric_space_mspace_mdist)

lemma capped_metric_mdist:
  "mdist (capped_metric \<delta> m) = (\<lambda>x y. if \<delta> \<le> 0 then mdist m x y else min \<delta> (mdist m x y))"
  apply (simp add: capped_metric not_le)
  by (smt (verit, del_insts) Metric_space.mdist_metric Metric_space_def Metric_space_mspace_mdist)

lemma mdist_capped_le: "mdist (capped_metric \<delta> m) x y \<le> mdist m x y"
  by (simp add: capped_metric_mdist)

lemma mdist_capped: "\<delta> > 0 \<Longrightarrow> mdist (capped_metric \<delta> m) x y \<le> \<delta>"
  by (simp add: capped_metric_mdist)

text \<open>The following two declarations are experimental. Is it really worth a locale just to save a couple of lines?\<close>
locale Capped = Metric_space +
  fixes \<delta>::real

sublocale Capped \<subseteq> capped: Metric_space M "capped_dist \<delta>"
  by (simp add: capped_dist)

lemma mtopology_capped_metric:
  "mtopology_of(capped_metric \<delta> m) = mtopology_of m"
proof (cases "\<delta> > 0")
  case True
  interpret Metric_space "mspace m" "mdist m"
    by (simp add: Metric_space_mspace_mdist)
  interpret Cap: Metric_space "mspace m" "mdist (capped_metric \<delta> m)"
    by (metis Metric_space_mspace_mdist capped_metric_mspace)
  show ?thesis
    unfolding topology_eq
  proof
    fix S
    show "openin (mtopology_of (capped_metric \<delta> m)) S = openin (mtopology_of m) S"
    proof (cases "S \<subseteq> mspace m")
      case True
      have "mball x r \<subseteq> Cap.mball x r" for x r
        by (smt (verit, ccfv_SIG) Cap.in_mball in_mball mdist_capped_le subsetI)
      moreover have "\<exists>r>0. Cap.mball x r \<subseteq> S" if "r>0" "x \<in> S" and r: "mball x r \<subseteq> S" for r x
      proof (intro exI conjI)
        show "min (\<delta>/2) r > 0"
          using \<open>r>0\<close> \<open>\<delta>>0\<close> by force
        show "Cap.mball x (min (\<delta>/2) r) \<subseteq> S"
          using that
          by clarsimp (smt (verit) capped_metric_mdist field_sum_of_halves in_mball subsetD)
      qed
      ultimately have "(\<exists>r>0. Cap.mball x r \<subseteq> S) = (\<exists>r>0. mball x r \<subseteq> S)" if "x \<in> S" for x
        by (meson subset_trans that)
      then show ?thesis
        by (simp add: mtopology_of_def openin_mtopology Cap.openin_mtopology)
    qed (simp add: openin_closedin_eq)
  qed
qed (simp add: capped_metric)

text \<open>Might have been easier to prove this within the locale to start with\<close>
lemma (in Metric_space) mtopology_capped_metric:
  "Metric_space.mtopology M (capped_dist \<delta>) = mtopology"
  using mtopology_capped_metric [of \<delta> "metric(M,d)"]
  by (simp add: Metric_space.mtopology_of capped_dist capped_metric_def)

lemma (in Metric_space) MCauchy_capped_metric:
  "Metric_space.MCauchy M (capped_dist \<delta>) \<sigma> \<longleftrightarrow> MCauchy \<sigma>"
proof (cases "\<delta> > 0")
  case True
  interpret Cap: Metric_space "M" "capped_dist \<delta>"
    by (simp add: capped_dist)
  show ?thesis
  proof
    assume \<sigma>: "Cap.MCauchy \<sigma>"
    show "MCauchy \<sigma>"
      unfolding MCauchy_def
    proof (intro conjI strip)
      show "range \<sigma> \<subseteq> M"
        using Cap.MCauchy_def \<sigma> by presburger
      fix \<epsilon> :: real
      assume "\<epsilon> > 0"
      with True \<sigma>
      obtain N where "\<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> capped_dist \<delta> (\<sigma> n) (\<sigma> n') < min \<delta> \<epsilon>"
        unfolding Cap.MCauchy_def by (metis min_less_iff_conj)
      with True show "\<exists>N. \<forall>n n'. N \<le> n \<longrightarrow> N \<le> n' \<longrightarrow> d (\<sigma> n) (\<sigma> n') < \<epsilon>"
        by (force simp add: capped_dist_def)
    qed
  next
    assume "MCauchy \<sigma>"
    then
    show "Cap.MCauchy \<sigma>"
      unfolding MCauchy_def Cap.MCauchy_def by (force simp add: capped_dist_def)
  qed
qed (simp add: capped_dist_def)


lemma (in Metric_space) mcomplete_capped_metric:
   "Metric_space.mcomplete M (capped_dist \<delta>) \<longleftrightarrow> mcomplete"
  by (simp add: MCauchy_capped_metric Metric_space.mcomplete_def capped_dist local.mtopology_capped_metric mcomplete_def)

lemma bounded_equivalent_metric:
  assumes "\<delta> > 0"
  obtains m' where "mspace m' = mspace m" "mtopology_of m' = mtopology_of m" "\<And>x y. mdist m' x y < \<delta>"
proof
  let ?m = "capped_metric (\<delta>/2) m"
  fix x y
  show "mdist ?m x y < \<delta>"
    by (smt (verit, best) assms field_sum_of_halves mdist_capped)    
qed (auto simp: mtopology_capped_metric)


lemma Sup_metric_cartesian_product:
  assumes m': "metric(PiE I (mspace \<circ> m), \<lambda>x y. SUP i\<in>I. mdist (m i) (x i) (y i)) = m'"
    and "I \<noteq> {}"
    and c: "\<And>i x y. \<lbrakk>i \<in> I; x \<in> mspace(m i); y \<in> mspace(m i)\<rbrakk> \<Longrightarrow> mdist (m i) x y \<le> c"
  shows "mspace m' = PiE I (mspace \<circ> m) \<and>
         mdist m' = (\<lambda>x y. SUP i\<in>I. mdist (m i) (x i) (y i)) \<and>
         (\<forall>x \<in> PiE I (mspace \<circ> m). \<forall>y \<in> PiE I (mspace \<circ> m). \<forall>b. 
               (mdist m' x y \<le> b \<longleftrightarrow> (\<forall>i \<in> I. mdist (m i) (x i) (y i) \<le> b)))"
proof -
  define M where "M \<equiv> \<lambda>x y. SUP i\<in>I. mdist (m i) (x i) (y i)"
  have bdd: "bdd_above ((\<lambda>i. mdist (m i) (x i) (y i)) ` I)"
    if "x \<in> PiE I (mspace \<circ> m)" "y \<in> PiE I (mspace \<circ> m)" for x y 
    using c that by (force simp add: bdd_above_def)
  have "M x y \<le> b \<longleftrightarrow> (\<forall>i \<in> I. mdist (m i) (x i) (y i) \<le> b)"
    if "x \<in> PiE I (mspace \<circ> m)" "y \<in> PiE I (mspace \<circ> m)" for x y b
    using that \<open>I \<noteq> {}\<close>
    by (simp add: M_def PiE_iff cSup_le_iff bdd)

oops
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `M = \<lambda>(x,y). sup {d(m i) (x i::A,y i) | (i::K) \<in> I}` THEN
  SUBGOAL_THEN
   `!x (y::K=>A) b.
        x \<in> PiE I (mspace \<circ> m) \<and>
        y \<in> PiE I (mspace \<circ> m)
        \<Longrightarrow> (M(x,y) \<le> b \<longleftrightarrow> \<forall>i. i \<in> I \<Longrightarrow> mdist (m i) (x i) (y i) \<le> b)`
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
 (`(!(tops::K=>A topology) I.
        metrizable_space (product_topology I tops) \<longleftrightarrow>
        topspace (product_topology I tops) = {} \<or>
        countable {i. i \<in> I \<and> \<not> (\<exists>a. topspace(tops i) \<subseteq> {a})} \<and>
        \<forall>i. i \<in> I \<Longrightarrow> metrizable_space (tops i)) \<and>
   (!(tops::K=>A topology) I.
        completely_metrizable_space (product_topology I tops) \<longleftrightarrow>
        topspace (product_topology I tops) = {} \<or>
        countable {i. i \<in> I \<and> \<not> (\<exists>a. topspace(tops i) \<subseteq> {a})} \<and>
        \<forall>i. i \<in> I \<Longrightarrow> completely_metrizable_space (tops i))"
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
     `l = {i::K | i \<in> I \<and> \<not> (\<exists>a::A. topspace(tops i) \<subseteq> {a})}` THEN
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
     `p \<in> topspace(product_topology I (tops::K=>A topology)) \<and>
      (\<forall>i::K. i \<in> l
             \<Longrightarrow> q i \<in> topspace(product_topology I (tops::K=>A topology)))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z::K=>A) \<in> PiE I (\<lambda>x. topspace(tops x))` THEN
      MAP_EVERY EXPAND_TAC ["q"; "p"] THEN
      REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; PiE; o_THM] THEN
      REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `\<forall>u:(K=>A)->bool.
        openin (product_topology I tops) u \<and> p \<in> u
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
       `(l \<Longrightarrow> I) \<and> (I \<and> l \<Longrightarrow> p \<Longrightarrow> q) \<Longrightarrow> l \<and> \<not> q \<Longrightarrow> I \<and> \<not> p`) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; REPEAT STRIP_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC \<circ> GEN_REWRITE_RULE id [\<subseteq>]) THEN
      EXPAND_TAC "q" THEN UNDISCH_TAC `(p::K=>A) \<in> PiE I v` THEN
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
  ASM_CASES_TAC `I::K=>bool = {}` THENL
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
  ASM_CASES_TAC `\<forall>i. i \<in> I \<Longrightarrow> mtopology(m i) = (tops::K=>A topology) i` THEN
  ASM_SIMP_TAC[] THENL [ALL_TAC; ASM_MESON_TAC[]] THEN MATCH_MP_TAC(MESON[]
   `\<forall>m. P m \<and> (Q \<Longrightarrow> C m) \<Longrightarrow> (\<exists>m. P m) \<and> (Q \<Longrightarrow> \<exists>m. C m \<and> P m)`) THEN
  FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id
   [COUNTABLE_AS_INJECTIVE_IMAGE_SUBSET]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; INJECTIVE_ON_LEFT_INVERSE] THEN
  MAP_EVERY X_GEN_TAC [`nk::num=>K`; `c::num=>bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `kn::K=>num`)) THEN
  MP_TAC(ISPECL
   [`I::K=>bool`; `\<lambda>i. capped_metric (inverse((kn i) + 1)) ((m::K=>A metric) i)`]
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
   `PiE I (\<lambda>i. mspace (m i)) =
    topspace(product_topology I (tops::K=>A topology))`
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
       `(\<forall>i. i \<in> I \<Longrightarrow> (z::K=>A) i \<in> topspace(tops i)) \<and>
        (\<forall>i. i \<in> I \<Longrightarrow> (x::K=>A) i \<in> topspace(tops i))`
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
         `{i. i \<in> I \<and> P i} = nk ` c
          \<Longrightarrow> (\<forall>i. i \<in> I \<and> Q i \<Longrightarrow> P i) \<and>
              (\<forall>n. n \<in> c \<Longrightarrow> Q(nk n) \<Longrightarrow> n \<in> s)
              \<Longrightarrow> \<forall>i. i \<in> I \<and> Q i \<Longrightarrow> i \<in> image nk (c \<inter> s)`)) THEN
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
        SUBGOAL_THEN `(x::K=>A) \<in> PiE I (topspace \<circ> tops)`
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
          ASM_CASES_TAC `(i::K) \<in> I` THEN ASM_REWRITE_TAC[] THEN
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
       [UNDISCH_TAC `(z::K=>A) \<in> PiE I u` THEN
        ASM_REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; PiE] THEN
        REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
        ASM_MESON_TAC[OPEN_IN_SUBSET; \<subseteq>];
        EXISTS_TAC `z::K=>A` THEN ASM_SIMP_TAC[MDIST_REFL; CONJ_ASSOC]] THEN
      SUBGOAL_THEN
       `\<forall>i. \<exists>r. i \<in> I \<Longrightarrow> 0 < r \<and> mball (m i) ((z::K=>A) i,r) \<subseteq> u i`
      MP_TAC THENL
       [X_GEN_TAC `i::K` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `openin(mtopology(m i)) ((u::K=>A->bool) i)` MP_TAC THENL
         [ASM_MESON_TAC[]; REWRITE_TAC[OPEN_IN_MTOPOLOGY]] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC) THEN
        UNDISCH_TAC `(z::K=>A) \<in> PiE I u` THEN
        ASM_SIMP_TAC[PiE; IN_ELIM_THM];
        REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
      X_GEN_TAC `r::K=>real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `\<exists>a::K. a \<in> I` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC
        `inf (image (\<lambda>i. min (r i) (inverse((kn i) + 1)))
                 (a insert {i. i \<in> I \<and>
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
      SUBGOAL_THEN `(x::K=>A) \<in> topspace(product_topology I tops)` MP_TAC THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY]] THEN
      REWRITE_TAC[PiE; o_THM; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i::K` THEN
      ASM_CASES_TAC `(i::K) \<in> I` THEN ASM_REWRITE_TAC[] THEN
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
     `\<forall>i. \<exists>y. i \<in> I \<Longrightarrow> limitin (tops i) (\<lambda>n. (x::num=>K->A) n i) y sequentially`
    MP_TAC THENL
     [X_GEN_TAC `i::K` THEN ASM_CASES_TAC `(i::K) \<in> I` THEN
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
    EXISTS_TAC `RESTRICTION I (y::K=>A)` THEN
    ASM_REWRITE_TAC[REWRITE_RULE[\<in>] RESTRICTION_IN_EXTENSIONAL] THEN
    SIMP_TAC[RESTRICTION; EVENTUALLY_TRUE] THEN ASM_REWRITE_TAC[]]);;



lemma completely_metrizable_Euclidean_space:
   "completely_metrizable_space(Euclidean_space n)"
  unfolding Euclidean_space_def
  apply (rule completely_metrizable_space_closedin)
apply (rule completely_metrizable_space_product_topology)
  defer
apply (simp add: closedin_Euclidean_space flip: topspace_Euclidean_space)
apply (auto simp: )

oops
  GEN_TAC THEN REWRITE_TAC[Euclidean_space] THEN
  MATCH_MP_TAC COMPLETELY_METRIZABLE_SPACE_CLOSED_IN THEN
  REWRITE_TAC[GSYM TOPSPACE_EUCLIDEAN_SPACE; CLOSED_IN_EUCLIDEAN_SPACE] THEN
  REWRITE_TAC[COMPLETELY_METRIZABLE_SPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[COMPLETELY_METRIZABLE_SPACE_EUCLIDEANREAL] THEN
  REWRITE_TAC[COUNTABLE_SUBSET_NUM]);;

lemma metrizable_Euclidean_space:
   "metrizable_space(Euclidean_space n)"
oops
  SIMP_TAC[COMPLETELY_METRIZABLE_IMP_METRIZABLE_SPACE;
           COMPLETELY_METRIZABLE_EUCLIDEAN_SPACE]);;
  oops

lemma locally_compact_Euclidean_space:
   "locally_compact_space(Euclidean_space n)"
oops
  X_GEN_TAC `n::num` THEN
  MP_TAC(SPEC `n::num` HOMEOMORPHIC_EUCLIDEAN_SPACE_PRODUCT_TOPOLOGY) THEN
  DISCH_THEN(SUBST1_TAC \<circ> MATCH_MP HOMEOMORPHIC_LOCALLY_COMPACT_SPACE) THEN
  REWRITE_TAC[LOCALLY_COMPACT_SPACE_PRODUCT_TOPOLOGY] THEN
  DISJ2_TAC THEN REWRITE_TAC[LOCALLY_COMPACT_SPACE_EUCLIDEANREAL] THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_RESTRICT]);;

lemma locally_connected_Euclidean_space:
   "locally_connected_space(Euclidean_space n)"
oops
  SIMP_TAC[LOCALLY_PATH_CONNECTED_EUCLIDEAN_SPACE;
           LOCALLY_PATH_CONNECTED_IMP_LOCALLY_CONNECTED_SPACE]);;


subsection\<open>Extending continuous maps "pointwise" in a regular space\<close>


lemma continuous_map_on_intermediate_closure_of:
  assumes "regular_space Y" "T \<subseteq> X closure_of S" "\<And>x. x \<in> T \<Longrightarrow> limitin Y f (f x) (atin_within X x  S)"
  shows "continuous_map (subtopology X T) Y f"
oops
  REWRITE_TAC[GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `image f T \<subseteq> topspace Y` ASSUME_TAC THENL
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
  UNDISCH_TAC `(T::A=>bool) \<subseteq> X closure_of S` THEN
  REWRITE_TAC[closure_of; IN_ELIM_THM; \<subseteq>] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `z::A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC \<circ> SPEC `u \<inter> u':A=>bool`) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER] THEN ASM SET_TAC[]);;

lemma continuous_map_on_intermediate_closure_of_eq:
  assumes "regular_space Y" "S \<subseteq> T" "T \<subseteq> X closure_of S"
   shows "continuous_map (subtopology X T) Y f \<longleftrightarrow> (\<forall>x \<in> T. limitin Y f (f x) (atin_within X x S))"
oops
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_ATPOINTOF; TOPSPACE_SUBTOPOLOGY] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x::A` THEN
    ASM_CASES_TAC `(x::A) \<in> T` THEN ASM_SIMP_TAC[ATPOINTOF_SUBTOPOLOGY] THEN
    ASSUME_TAC(ISPECL [`X::A topology`; `S::A=>bool`]
      CLOSURE_OF_SUBSET_TOPSPACE) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[LIMIT_WITHIN_SUBSET]];
    ASM_MESON_TAC[CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE_OF]]);;

lemma continuous_map_extension_pointwise_alt:
   "\<And>top1 top2 f::A=>B S T.
        regular_space top2" "S \<subseteq> T" "T \<subseteq> top1 closure_of S \<and>
        continuous_map (subtopology top1 S,top2) f \<and>
        (\<forall>x. x \<in> T - S \<Longrightarrow> \<exists>l. limitin top2 f l (atin top1 x within S))
        \<Longrightarrow> \<exists>g. continuous_map (subtopology top1 T,top2) g \<and>
                (\<forall>x. x \<in> S \<Longrightarrow> g x = f x)"
oops
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC \<circ> GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; IN_DIFF] THEN
  X_GEN_TAC `g::A=>B` THEN DISCH_TAC THEN
  EXISTS_TAC `\<lambda>x. if x \<in> S then f x else g x` THEN
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
   "\<And>top1 top2 f::A=>B S T.
        regular_space top2" "S \<subseteq> T" "T \<subseteq> top1 closure_of S \<and>
        (\<forall>x. x \<in> T
             \<Longrightarrow> \<exists>g. continuous_map (subtopology top1 (insert x S),top2) g \<and>
                     \<forall>x. x \<in> S \<Longrightarrow> g x = f x)
        \<Longrightarrow> \<exists>g. continuous_map (subtopology top1 T,top2) g \<and>
                (\<forall>x. x \<in> S \<Longrightarrow> g x = f x)"
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
  EXISTS_TAC `(x::A) insert S` THEN
  ASM_REWRITE_TAC[SET_RULE `S \<subseteq> insert x S`]);;


subsection\<open>Extending Cauchy continuous functions to the closure\<close>


lemma Cauchy_continuous_map_extends_to_continuous_closure_of:
   "\<And>m1 m2 f S.
        mcomplete m2 \<and> Cauchy_continuous_map (submetric1 S,m2) f
        \<Longrightarrow> \<exists>g. continuous_map
                 (subtopology (mtopology m1) (mtopology m1 closure_of S),
                  mtopology m2) g \<and>
                \<forall>x. x \<in> S \<Longrightarrow> g x = f x"
oops
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC(MESON[]
   `\<forall>m. ((\<forall>S. S \<subseteq> M \<Longrightarrow> P S) \<Longrightarrow> (\<forall>S. P S)) \<and>
        (\<forall>S. S \<subseteq> M \<Longrightarrow> P S)
        \<Longrightarrow> \<forall>S. P S`) THEN
  EXISTS_TAC `m1::A metric` THEN CONJ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `S::A=>bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC \<circ> SPEC `M1 \<inter> S::A=>bool`) THEN
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
   "\<And>m1 m2 f S T.
        mcomplete m2 \<and> Cauchy_continuous_map (submetric1 S,m2) f \<and>
        T \<subseteq> mtopology m1 closure_of S
        \<Longrightarrow> \<exists>g. continuous_map(subtopology (mtopology m1) T,mtopology m2) g \<and>
                \<forall>x. x \<in> S \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `S::A=>bool`]
        CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO]);;

lemma Lipschitz_continuous_map_on_intermediate_closure:
   "\<And>m1 m2 f::A=>B S T.
        S \<subseteq> T \<and> T \<subseteq> (mtopology m1) closure_of S \<and>
        continuous_map (subtopology (mtopology m1) T,mtopology m2) f \<and>
        Lipschitz_continuous_map (submetric1 S,m2) f
        \<Longrightarrow> Lipschitz_continuous_map (submetric1 T,m2) f"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
  SUBGOAL_THEN `submetric1 (S::A=>bool) = submetric1 (M1 \<inter> S)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBMETRIC_SUBMETRIC; SUBMETRIC_MSPACE];
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC \<circ> SPEC `M1::A=>bool` \<circ> MATCH_MP (SET_RULE
       `S \<subseteq> T \<Longrightarrow> \<forall>u. u \<inter> S \<subseteq> u \<and> u \<inter> S \<subseteq> T`))
     MP_TAC) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    SPEC_TAC(`M1 \<inter> (S::A=>bool)`,`S::A=>bool`)] THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(T::A=>bool) \<subseteq> M1` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[closure_of; TOPSPACE_MTOPOLOGY]) THEN
    ASM SET_TAC[];
    FIRST_ASSUM(MP_TAC \<circ> CONJUNCT1 \<circ> REWRITE_RULE[CONTINUOUS_MAP])] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[LIPSCHITZ_CONTINUOUS_MAP_POS] THEN
  ASM_SIMP_TAC[SUBMETRIC; SET_RULE `S \<subseteq> u \<Longrightarrow> S \<inter> u = S`;
               SET_RULE `S \<subseteq> u \<Longrightarrow> u \<inter> S = S`] THEN
  DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B::real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology (mtopology m1) (T::A=>bool))
                   (subtopology (mtopology m1) (T::A=>bool))`;
    `\<lambda>z. d m2 (f (fst z),f(snd z)) \<le> B * d m1 (fst z,snd z)`;
    `S \<times> (S::A=>bool)`] FORALL_IN_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[CLOSURE_OF_CROSS; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN ASM_SIMP_TAC[SET_RULE
   `S \<subseteq> T \<Longrightarrow> T \<inter> S = S \<and> S \<inter> T = S`] THEN
  ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN REWRITE_TAC[SET_RULE
   `{x \<in> S. 0 \<le> f x} = {x \<in> S. f x \<in> {y. 0 \<le> y}}`] THEN
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
    EXISTS_TAC `subtopology (mtopology m1) (T::A=>bool)`] THEN
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
   "\<And>m1 m2 f S.
        mcomplete m2 \<and> Lipschitz_continuous_map (submetric1 S,m2) f
        \<Longrightarrow> \<exists>g. Lipschitz_continuous_map
                   (submetric1 (mtopology m1 closure_of S),m2) g \<and>
                \<forall>x. x \<in> S \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `S::A=>bool`]
         CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
  ASM_SIMP_TAC[LIPSCHITZ_IMP_CAUCHY_CONTINUOUS_MAP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g::A=>B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `M1 \<inter> S::A=>bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_INTER; GSYM TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT; SUBSET_REFL] THEN
  REWRITE_TAC[TOPSPACE_MTOPOLOGY; GSYM SUBMETRIC_RESTRICT] THEN
  MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_MAP_EQ THEN EXISTS_TAC `f::A=>B` THEN
  ASM_SIMP_TAC[SUBMETRIC; IN_INTER]);;

lemma Lipschitz_continuous_map_extends_to_intermediate_closure_of:
   "\<And>m1 m2 f S T.
        mcomplete m2 \<and>
        Lipschitz_continuous_map (submetric1 S,m2) f \<and>
        T \<subseteq> mtopology m1 closure_of S
        \<Longrightarrow> \<exists>g. Lipschitz_continuous_map (submetric1 T,m2) g \<and>
                \<forall>x. x \<in> S \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `S::A=>bool`]
        LIPSCHITZ_CONTINUOUS_MAP_EXTENDS_TO_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[LIPSCHITZ_CONTINUOUS_MAP_FROM_SUBMETRIC_MONO]);;

lemma uniformly_continuous_map_on_intermediate_closure:
   "\<And>m1 m2 f::A=>B S T.
        S \<subseteq> T \<and> T \<subseteq> (mtopology m1) closure_of S \<and>
        continuous_map (subtopology (mtopology m1) T,mtopology m2) f \<and>
        uniformly_continuous_map (submetric1 S,m2) f
        \<Longrightarrow> uniformly_continuous_map (submetric1 T,m2) f"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
  SUBGOAL_THEN `submetric1 (S::A=>bool) = submetric1 (M1 \<inter> S)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBMETRIC_SUBMETRIC; SUBMETRIC_MSPACE];
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC \<circ> SPEC `M1::A=>bool` \<circ> MATCH_MP (SET_RULE
       `S \<subseteq> T \<Longrightarrow> \<forall>u. u \<inter> S \<subseteq> u \<and> u \<inter> S \<subseteq> T`))
     MP_TAC) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    SPEC_TAC(`M1 \<inter> (S::A=>bool)`,`S::A=>bool`)] THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(T::A=>bool) \<subseteq> M1` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[closure_of; TOPSPACE_MTOPOLOGY]) THEN
    ASM SET_TAC[];
    FIRST_ASSUM(MP_TAC \<circ> CONJUNCT1 \<circ> REWRITE_RULE[CONTINUOUS_MAP])] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[uniformly_continuous_map] THEN
  ASM_SIMP_TAC[SUBMETRIC; SET_RULE `S \<subseteq> u \<Longrightarrow> S \<inter> u = S`;
               SET_RULE `S \<subseteq> u \<Longrightarrow> u \<inter> S = S`] THEN
  DISCH_TAC THEN STRIP_TAC THEN X_GEN_TAC `e::real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC \<circ> SPEC `e / 2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d::real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`prod_topology (subtopology (mtopology m1) (T::A=>bool))
                   (subtopology (mtopology m1) (T::A=>bool))`;
    `\<lambda>z. d m1 (fst z,snd z) < d
         \<Longrightarrow> d m2 (f (fst z),f(snd z)) \<le> e / 2`;
    `S \<times> (S::A=>bool)`] FORALL_IN_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[CLOSURE_OF_CROSS; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN ASM_SIMP_TAC[SET_RULE
   `S \<subseteq> T \<Longrightarrow> T \<inter> S = S \<and> S \<inter> T = S`] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_MESON_TAC[REAL_ARITH `0 < e \<and> x \<le> e / 2 \<Longrightarrow> x < e`]] THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  REWRITE_TAC[SET_RULE
   `{x \<in> S. (\<not> (0 \<le> f x) \<Longrightarrow> 0 \<le> g x)} =
    {x \<in> S. g x \<in> {y. 0 \<le> y}} \<union>
    {x \<in> S. f x \<in> {y. 0 \<le> y}}`] THEN
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
  EXISTS_TAC `subtopology (mtopology m1) (T::A=>bool)` THEN
  ASM_SIMP_TAC[SUBTOPOLOGY_CROSS; CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND]);;

lemma uniformly_continuous_map_extends_to_closure_of:
   "\<And>m1 m2 f S.
        mcomplete m2 \<and> uniformly_continuous_map (submetric1 S,m2) f
        \<Longrightarrow> \<exists>g. uniformly_continuous_map
                   (submetric1 (mtopology m1 closure_of S),m2) g \<and>
                \<forall>x. x \<in> S \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `S::A=>bool`]
         CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
  ASM_SIMP_TAC[UNIFORMLY_IMP_CAUCHY_CONTINUOUS_MAP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g::A=>B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `M1 \<inter> S::A=>bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_INTER; GSYM TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT; SUBSET_REFL] THEN
  REWRITE_TAC[TOPSPACE_MTOPOLOGY; GSYM SUBMETRIC_RESTRICT] THEN
  MATCH_MP_TAC UNIFORMLY_CONTINUOUS_MAP_EQ THEN EXISTS_TAC `f::A=>B` THEN
  ASM_SIMP_TAC[SUBMETRIC; IN_INTER]);;

lemma uniformly_continuous_map_extends_to_intermediate_closure_of:
   "\<And>m1 m2 f S T.
        mcomplete m2 \<and>
        uniformly_continuous_map (submetric1 S,m2) f \<and>
        T \<subseteq> mtopology m1 closure_of S
        \<Longrightarrow> \<exists>g. uniformly_continuous_map (submetric1 T,m2) g \<and>
                \<forall>x. x \<in> S \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `S::A=>bool`]
        UNIFORMLY_CONTINUOUS_MAP_EXTENDS_TO_CLOSURE_OF) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[UNIFORMLY_CONTINUOUS_MAP_FROM_SUBMETRIC_MONO]);;

lemma Cauchy_continuous_map_on_intermediate_closure:
   "\<And>m1 m2 f::A=>B S T.
        S \<subseteq> T \<and> T \<subseteq> (mtopology m1) closure_of S \<and>
        continuous_map (subtopology (mtopology m1) T,mtopology m2) f \<and>
        Cauchy_continuous_map (submetric1 S,m2) f
        \<Longrightarrow> Cauchy_continuous_map (submetric1 T,m2) f"
oops
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
  SUBGOAL_THEN `submetric1 (S::A=>bool) = submetric1 (M1 \<inter> S)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBMETRIC_SUBMETRIC; SUBMETRIC_MSPACE];
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC \<circ> SPEC `M1::A=>bool` \<circ> MATCH_MP (SET_RULE
       `S \<subseteq> T \<Longrightarrow> \<forall>u. u \<inter> S \<subseteq> u \<and> u \<inter> S \<subseteq> T`))
     MP_TAC) THEN
    REWRITE_TAC[TOPSPACE_MTOPOLOGY] THEN
    SPEC_TAC(`M1 \<inter> (S::A=>bool)`,`S::A=>bool`)] THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(T::A=>bool) \<subseteq> M1` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[closure_of; TOPSPACE_MTOPOLOGY]) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  REWRITE_TAC[Cauchy_continuous_map; CAUCHY_IN_SUBMETRIC] THEN
  X_GEN_TAC `x::num=>A` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `\<forall>n. \<exists>y. y \<in> S \<and>
            d m1 (x n,y) < inverse(Suc n) \<and>
            d m2 (f(x n),f y) < inverse(Suc n)`
  MP_TAC THENL
   [X_GEN_TAC `n::num` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM MTOPOLOGY_SUBMETRIC]) THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [METRIC_CONTINUOUS_MAP]) THEN
    ASM_SIMP_TAC[SUBMETRIC; SET_RULE `S \<subseteq> u \<Longrightarrow> S \<inter> u = S`] THEN
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
   `S \<subseteq> u \<Longrightarrow> S \<inter> u = S`] THEN
  ANTS_TAC THENL [UNDISCH_TAC `MCauchy m1 (x::num=>A)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[MCauchy; o_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> CONJUNCT1 \<circ> GEN_REWRITE_RULE id [continuous_map]) THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_MTOPOLOGY;
               SET_RULE `S \<subseteq> T \<Longrightarrow> T \<inter> S = S`] THEN
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
   "\<And>m1 m2 f S.
        mcomplete m2 \<and> Cauchy_continuous_map (submetric1 S,m2) f
        \<Longrightarrow> \<exists>g. Cauchy_continuous_map
                   (submetric1 (mtopology m1 closure_of S),m2) g \<and>
                \<forall>x. x \<in> S \<Longrightarrow> g x = f x"
oops
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC \<circ> MATCH_MP
    CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g::A=>B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_ON_INTERMEDIATE_CLOSURE THEN
  EXISTS_TAC `M1 \<inter> S::A=>bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_INTER; GSYM TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT; SUBSET_REFL] THEN
  REWRITE_TAC[TOPSPACE_MTOPOLOGY; GSYM SUBMETRIC_RESTRICT] THEN
  MATCH_MP_TAC CAUCHY_CONTINUOUS_MAP_EQ THEN EXISTS_TAC `f::A=>B` THEN
  ASM_SIMP_TAC[SUBMETRIC; IN_INTER]);;

lemma Cauchy_continuous_map_extends_to_intermediate_closure_of:
   "\<And>m1 m2 f S T.
        mcomplete m2 \<and>
        Cauchy_continuous_map (submetric1 S,m2) f \<and>
        T \<subseteq> mtopology m1 closure_of S
        \<Longrightarrow> \<exists>g. Cauchy_continuous_map (submetric1 T,m2) g \<and>
                \<forall>x. x \<in> S \<Longrightarrow> g x = f x"
oops
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m1::A metric`; `m2::B metric`; `f::A=>B`; `S::A=>bool`]
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


subsection\<open> The Baire Category Theorem                                                \<close>


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

subsection \<open>Urysohn and Tietze analogs for completely regular spaces\<close>

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
