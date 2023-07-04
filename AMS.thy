section \<open>Abstract Metric Spaces\<close>

theory AMS
  imports
    "HOL-Analysis.Analysis" "HOL-Library.Equipollence"
    "HOL-ex.Sketch_and_Explore"
begin
    
    lemma power_of_nat_log_ge: "b > 1 \<Longrightarrow> b ^ nat \<lceil>log b x\<rceil> \<ge> x"
      by (smt (verit) less_log_of_power of_nat_ceiling)


lemma power_of_nat_log_le: "b > 1 \<Longrightarrow> b ^ nat (floor(log b x)) \<le> x"
  oops

lemma reals01_lepoll_nat_sets: "{0..<1::real} \<lesssim> (UNIV::nat set set)"
proof -
  define nxt where "nxt \<equiv> \<lambda>x::real. if x < 1/2 then (True, 2*x) else (False, 2*x - 1)"
  have nxt_fun: "nxt \<in> {0..<1} \<rightarrow> UNIV \<times> {0..<1}"
    by (simp add: nxt_def Pi_iff)
  define \<sigma> where "\<sigma> \<equiv> \<lambda>x. rec_nat (True, x) (\<lambda>n (b,y). nxt y)"
  have \<sigma>Suc [simp]: "\<sigma> x (Suc k) = nxt (snd (\<sigma> x k))" for k x
    by (simp add: \<sigma>_def case_prod_beta')
  have \<sigma>01: "x \<in> {0..<1} \<Longrightarrow> \<sigma> x n \<in> UNIV \<times> {0..<1}" for x n
  proof (induction n)
    case 0
    then show ?case                                           
      by (simp add: \<sigma>_def)
   next
    case (Suc n)
    with nxt_fun show ?case
      by (force simp add: Pi_iff split: prod.split)
  qed
  define f where "f \<equiv> \<lambda>x. {n. fst (\<sigma> x (Suc n))}"
  have snd_nxt: "snd (nxt y) - snd (nxt x) = 2 * (y-x)" 
    if "fst (nxt x) = fst (nxt y)" for x y
    using that by (simp add: nxt_def split: if_split_asm)
  have False if "f x = f y" "x < y" "0 \<le> x" "x < 1" "0 \<le> y" "y < 1" for x y :: real
  proof -
    have "\<And>k. fst (\<sigma> x (Suc k)) = fst (\<sigma> y (Suc k))"
      using that by (force simp add: f_def)
    then have eq: "\<And>k. fst (nxt (snd (\<sigma> x k))) = fst (nxt (snd (\<sigma> y k)))"
      by (metis \<sigma>_def case_prod_beta' rec_nat_Suc_imp)
    have *: "snd (\<sigma> y k) - snd (\<sigma> x k) = 2 ^ k * (y-x)" for k
    proof (induction k)
      case 0
      then show ?case
        by (simp add: \<sigma>_def)
    next
      case (Suc k)
      then show ?case
        by (simp add: eq snd_nxt)
    qed
    define n where "n \<equiv> nat (\<lceil>log 2 (1 / (y - x))\<rceil>)"
    have "2^n \<ge> 1 / (y - x)"
      by (simp add: n_def power_of_nat_log_ge)
    then have "2^n * (y-x) \<ge> 1"
      using \<open>x < y\<close> by (simp add: n_def field_simps)
    with * have "snd (\<sigma> y n) - snd (\<sigma> x n) \<ge> 1"
      by presburger
    moreover have "snd (\<sigma> x n) \<in> {0..<1}" "snd (\<sigma> y n) \<in> {0..<1}"
      using that by (meson \<sigma>01 atLeastLessThan_iff mem_Times_iff)+
    ultimately show False by simp
  qed
  then have "inj_on f {0..<1}"
    by (meson atLeastLessThan_iff linorder_inj_onI')
  then show ?thesis
    unfolding lepoll_def by blast
qed


thm geometric_sum
lemma geometric_sum_less:
  assumes "0 < x" "x < 1" "finite S"
  shows "(\<Sum>i\<in>S. x ^ i) < 1 / (1 - x::'a::linordered_field)"
proof -
  define n where "n \<equiv> Suc (Max S)" 
  have "(\<Sum>i\<in>S. x ^ i) \<le> (\<Sum>i<n. x ^ i)"
    unfolding n_def using assms  by (fastforce intro!: sum_mono2 le_imp_less_Suc)
  also have "\<dots> = (1 - x ^ n) / (1 - x)"
    using assms by (simp add: geometric_sum field_simps)
  also have "\<dots> < 1 / (1-x)"
    using assms by (simp add: field_simps)
  finally show ?thesis .
qed

lemma Jayne:
  "(\<Sum>i\<in>S \<inter> {m..n}. (inverse 3::real) ^ i) < 3 / 2 / 3 ^ m"
proof -
  have "(\<Sum>i\<in>S \<inter> {m..n}. (inverse(3::real)) ^ i) \<le> (\<Sum>i = m..n. inverse 3 ^ i)"
    by (force intro!: sum_mono2)
  also have "\<dots> < 3 / 2 / 3 ^ m"
  proof (cases "m \<le> n")
    case True
    have eq: "(\<Sum>i = m..n. (inverse 3::real) ^ i) = (3/2) * (inverse 3 ^ m - inverse 3 ^ Suc n)"
      using sum_gp_multiplied [OF True, of "inverse (3::real)"] by auto
    show ?thesis
      unfolding eq by (simp add: field_simps)
  qed auto
  finally show ?thesis .
qed



lemma nat_sets_lepoll_reals01: "(UNIV::nat set set) \<lesssim> {0..<1::real}"
proof -
  define F where "F \<equiv> \<lambda>S i. if i\<in>S then (inverse 3::real) ^ i else 0"
  have Fge0: "F S i \<ge> 0" for S i
    by (simp add: F_def)
  have F: "summable (F S)" for S
    unfolding F_def by (force intro: summable_comparison_test_ev [where g = "power (inverse 3)"])
  have J: "sum (F S) {..<n} \<le> 3/2" for n S
  proof (cases n)
    case (Suc n')
    have "sum (F S) {..<n} \<le> (\<Sum>i<n. inverse 3 ^ i)"
      by (simp add: F_def sum_mono)
    also have "\<dots> = (\<Sum>i=0..n'. inverse 3 ^ i)"
      using Suc atLeast0AtMost lessThan_Suc_atMost by presburger
    also have "\<dots> = (3/2) * (1 - inverse 3 ^ n)"
      using sum_gp_multiplied [of 0 n' "inverse (3::real)"] by (simp add: Suc field_simps)
    also have "\<dots> \<le> 3/2"
      by (simp add: field_simps)
    finally show ?thesis .
  qed auto
  define f where "f \<equiv> \<lambda>S. suminf (F S) / 2"
  have "F S n \<le> F T n" if "S \<subseteq> T" for S T n
    using F_def that by auto
  then have monof: "f S \<le> f T" if "S \<subseteq> T" for S T
    using that F by (simp add: f_def suminf_le)

  have "f S \<in> {0..<1::real}" for S
  proof -
    have "0 \<le> suminf (F S)"
      using F by (simp add: F_def suminf_nonneg)
    moreover have "suminf (F S) \<le> 3/2"
      by (rule suminf_le_const [OF F J])
    ultimately show ?thesis
      by (auto simp: f_def)
  qed
  moreover have "inj f"
  proof
    fix S T
    assume "f S = f T" 
    show "S = T"
    proof (rule ccontr)
      assume "S \<noteq> T"
      then have ST_ne: "sym_diff S T \<noteq> {}"
        by blast
      define n where "n \<equiv> LEAST n. n \<in> sym_diff S T"

      have eq: "S \<inter> {..<n} = T \<inter> {..<n}"
        using not_less_Least by (fastforce simp add: n_def)
      have D: "sum (F S) {..<n} = sum (F T) {..<n}"
        by (metis (no_types, lifting) F_def Int_iff eq sum.cong)

      have yes: "f U \<ge> (sum (F U) {..<n} + (inverse 3::real) ^ n) / 2" 
        if "n \<in> U" for U
      proof -
        have FUn: "F U n = (1/3) ^ n"
          by (simp add: F_def that)
        have "0 \<le> (\<Sum>k. F U (k + Suc n))"
          by (metis F Fge0 suminf_nonneg summable_iff_shift)
        then have "F U n + (\<Sum>i<n. F U i) \<le> (\<Sum>k. F U (k + Suc n)) + F U n + (\<Sum>i<n. F U i)"
          by simp
        also have "\<dots> = (\<Sum>k. F U (k + n)) + (\<Sum>i<n. F U i)"
          by (metis (no_types) F add.commute add.left_commute sum.lessThan_Suc suminf_split_initial_segment)
        also have "\<dots> = suminf (F U)"
          by (metis F suminf_split_initial_segment)
        finally show ?thesis
          by (simp add: f_def add.commute FUn)
      qed
      have no: "f U < (sum (F U) {..<n} + (inverse 3::real) ^ n) / 2" 
        if "n \<notin> U" for U
        sorry
      consider "n \<in> S-T" | "n \<in> T-S"
        by (metis LeastI_ex ST_ne UnE ex_in_conv n_def)
      with yes no D show False
        by (smt (verit, best) Diff_iff \<open>f S = f T\<close>)
    qed
  qed
  ultimately show ?thesis
    by (meson image_subsetI lepoll_def)
qed

lemma "(UNIV::nat set set) \<approx> (UNIV::real set)"

  oops


    (*delete*)
      thm relative_to_subset relative_to_subset_trans

(*REPLACE*)
lemma relative_to_subset_trans:
       "\<lbrakk>(P relative_to U) S; S \<subseteq> T; T \<subseteq> U\<rbrakk> \<Longrightarrow> (P relative_to T) S"
      unfolding relative_to_def by auto
    
    (*The HOL Light CARD_LE_RELATIONAL_FULL*)
    lemma lepoll_relational_full:
      assumes "\<And>y. y \<in> B \<Longrightarrow> \<exists>x. x \<in> A \<and> R x y"
        and "\<And>x y y'. \<lbrakk>x \<in> A; y \<in> B; y' \<in> B; R x y; R x y'\<rbrakk> \<Longrightarrow> y = y'"
      shows "B \<lesssim> A"
    proof -
      obtain f where f: "\<And>y. y \<in> B \<Longrightarrow> f y \<in> A \<and> R (f y) y"
        using assms by metis
      with assms have "inj_on f B"
        by (metis inj_onI)
      with f show ?thesis
        unfolding lepoll_def by blast
    qed
    
    lemma lepoll_iff_card_le: "\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow> A \<lesssim> B \<longleftrightarrow> card A \<le> card B"
      by (simp add: inj_on_iff_card_le lepoll_def)
    
    lemma lepoll_iff_finite_card: "A \<lesssim> {..<n::nat} \<longleftrightarrow> finite A \<and> card A \<le> n"
      by (metis card_lessThan finite_lessThan finite_surj lepoll_iff lepoll_iff_card_le)
    
    lemma eqpoll_iff_finite_card: "A \<approx> {..<n::nat} \<longleftrightarrow> finite A \<and> card A = n"
      by (metis card_lessThan eqpoll_finite_iff eqpoll_iff_card finite_lessThan)
    
    lemma lesspoll_iff_finite_card: "A \<prec> {..<n::nat} \<longleftrightarrow> finite A \<and> card A < n"
      by (metis eqpoll_iff_finite_card lepoll_iff_finite_card lesspoll_def order_less_le)


  
  (*HOL Light's FORALL_POS_MONO_1_EQ*)
  lemma Inter_eq_Inter_inverse_Suc:
    assumes "\<And>r' r. r' < r \<Longrightarrow> A r' \<subseteq> A r"
    shows "\<Inter> (A ` {0<..}) = (\<Inter>n. A(inverse(Suc n)))"
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
    lemma quasi_components_lepoll_topspace: "quasi_components_of X \<lesssim> topspace X"
      unfolding lepoll_def
      by (metis bot.extremum image_empty inj_on_empty inj_on_iff_surj quasi_components_of_def)

(*NEEDS first_countable
lemma first_countable_mtopology:
   "first_countable mtopology"
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
  REWRITE_TAC[FORALL_METRIZABLE_SPACE; FIRST_COUNTABLE_MTOPOLOGY]);;
*)

      
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
            and fim: "f \<in> (topspace X) \<rightarrow> {0..1::real}"
            and f0: "f a = 0" and f1: "f ` S \<subseteq> {1}"
            using \<open>completely_regular_space X\<close>
            unfolding completely_regular_space_def
            by (metis Diff_iff \<open>a \<in> topspace X\<close> \<open>a \<notin> S\<close> \<open>closedin X S\<close> continuous_map_in_subtopology image_subset_iff_funcset)
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
             and fim: "f \<in> (topspace X) \<rightarrow> {0..1::real}"
             and f0: "f ` S \<subseteq> {0}" and f1: "f ` T \<subseteq> {1}"
            using assms by (metis continuous_map_in_subtopology normal_space_iff_Urysohn image_subset_iff_funcset)
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
          by (meson \<gamma> path_image_subset_topspace subset_imp_lepoll image_subset_iff_funcset)
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
          by (meson path_image_subset_topspace subset_imp_lepoll image_subset_iff_funcset)
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
        assumes "mcomplete" and fim: "f \<in> (topspace X \<inter> S) \<rightarrow> M"
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
                  using b \<open>openin X U\<close> by (metis image_subset_iff_funcset Int_iff fim image_eqI openin_subset subsetD)
                moreover
                have "mtopology closure_of f ` ((S \<inter> U) - {a}) \<subseteq> mcball (f b) \<epsilon>"
                proof (rule closure_of_minimal)
                  have "f y \<in> M" if "y \<in> S" and "y \<in> U" for y
                    using \<open>U \<subseteq> topspace X\<close> fim that by (auto simp: Pi_iff)
                  moreover
                  have "d (f b) (f y) \<le> \<epsilon>" if "y \<in> S" "y \<in> U" "y \<noteq> a" for y
                    using that Uless b by force
                  ultimately show "f ` (S \<inter> U - {a}) \<subseteq> mcball (f b) \<epsilon>"
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
                  using fim U
                  apply (simp add: eventually_atin eventually_within_imp del: divide_const_simps flip: image_subset_iff_funcset)
                  by (smt (verit, del_insts) Diff_iff Int_iff imageI insertI1 openin_subset subsetD)
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
      
      text \<open>The HOL Light proof uses some ugly tricks to share common parts of what are two separate proofs for the two cases\<close>
      lemma (in Metric_space) gdelta_in_points_of_convergence_within:
        assumes "mcomplete"
          and f: "continuous_map (subtopology X S) mtopology f \<or> t1_space X \<and> f \<in> S \<rightarrow> M"
        shows "gdelta_in X {x \<in> topspace X. \<exists>l. limitin mtopology f l (atin_within X x S)}"
      proof -
        have fim: "f \<in> (topspace X \<inter> S) \<rightarrow> M"
          using continuous_map_image_subset_topspace f by force
        show ?thesis
        proof (cases "M={}")
          case True
          then show ?thesis
            by (smt (verit) Collect_cong empty_def empty_iff gdelta_in_empty limitin_mspace)
        next
          case False
          define A where "A \<equiv> {a \<in> topspace X. \<forall>\<epsilon>>0. \<exists>U. openin X U \<and> a \<in> U \<and> (\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>)}"
          have "gdelta_in X A"
            using f 
          proof (elim disjE conjE)
            assume cm: "continuous_map (subtopology X S) mtopology f"
            define C where "C \<equiv> \<lambda>r. \<Union>{U. openin X U \<and> (\<forall>x \<in> S\<inter>U. \<forall>y \<in> S\<inter>U. d (f x) (f y) < r)}"
            define B where "B \<equiv> (\<Inter>n. C(inverse(Suc n)))"
            define D where "D \<equiv> (\<Inter> (C ` {0<..}))"
            have "D=B"
              unfolding B_def C_def D_def
              apply (intro Inter_eq_Inter_inverse_Suc Sup_subset_mono)
              by (smt (verit, ccfv_threshold) Collect_mono_iff)
            have "B \<subseteq> topspace X"
              using openin_subset by (force simp add: B_def C_def)
            have "(countable intersection_of openin X) B"
              unfolding B_def C_def 
              by (intro relative_to_inc countable_intersection_of_Inter countable_intersection_of_inc) auto
            then have "gdelta_in X B"
              unfolding gdelta_in_def by (intro relative_to_subset_inc \<open>B \<subseteq> topspace X\<close>)
            moreover have "A=D"
            proof (intro equalityI subsetI)
              fix a
              assume x: "a \<in> A"
              then have "a \<in> topspace X"
                using A_def by blast
              show "a \<in> D"
              proof (clarsimp simp: D_def C_def \<open>a \<in> topspace X\<close>)
                fix \<epsilon>::real assume "\<epsilon> > 0"
                then obtain U where "openin X U" "a \<in> U" and U: "(\<forall>x\<in>S \<inter> U - {a}. \<forall>y\<in>S \<inter> U - {a}. d (f x) (f y) < \<epsilon>)"
                  using x by (force simp: A_def)
                show "\<exists>T. openin X T \<and> (\<forall>x\<in>S \<inter> T. \<forall>y\<in>S \<inter> T. d (f x) (f y) < \<epsilon>) \<and> a \<in> T"
                proof (cases "a \<in> S")
                  case True
                  then obtain V where "openin X V" "a \<in> V" and V: "\<forall>x. x \<in> S \<and> x \<in> V \<longrightarrow> f a \<in> M \<and> f x \<in> M \<and> d (f a) (f x) < \<epsilon>"
                    using \<open>a \<in> topspace X\<close> \<open>\<epsilon> > 0\<close> cm
                    by (force simp add: continuous_map_to_metric openin_subtopology_alt Ball_def)
                  show ?thesis
                  proof (intro exI conjI strip)
                    show "openin X (U \<inter> V)"
                      using \<open>openin X U\<close> \<open>openin X V\<close> by blast 
                    show "a \<in> U \<inter> V"
                      using \<open>a \<in> U\<close> \<open>a \<in> V\<close> by blast
                    show "\<And>x y. \<lbrakk>x \<in> S \<inter> (U \<inter> V); y \<in> S \<inter> (U \<inter> V)\<rbrakk> \<Longrightarrow> d (f x) (f y) < \<epsilon>"
                      by (metis DiffI Int_iff U V commute singletonD)
                  qed
                next
                  case False then show ?thesis
                    using U \<open>a \<in> U\<close> \<open>openin X U\<close> by auto
                qed
              qed
            next
              fix x
              assume x: "x \<in> D"
              then have "x \<in> topspace X"
                using \<open>B \<subseteq> topspace X\<close> \<open>D=B\<close> by blast
              with x show "x \<in> A"
                apply (clarsimp simp: D_def C_def A_def)
                by (meson DiffD1 greaterThan_iff)
            qed
            ultimately show ?thesis
              by (simp add: \<open>D=B\<close>)
          next
            assume "t1_space X" "f \<in> S \<rightarrow> M"
            define C where "C \<equiv> \<lambda>r. \<Union>{U. openin X U \<and> 
                                 (\<exists>b \<in> topspace X. \<forall>x \<in> S\<inter>U - {b}. \<forall>y \<in> S\<inter>U - {b}. d (f x) (f y) < r)}"
            define B where "B \<equiv> (\<Inter>n. C(inverse(Suc n)))"
            define D where "D \<equiv> (\<Inter> (C ` {0<..}))"
            have "D=B"
              unfolding B_def C_def D_def
              apply (intro Inter_eq_Inter_inverse_Suc Sup_subset_mono)
              by (smt (verit, ccfv_threshold) Collect_mono_iff)
            have "B \<subseteq> topspace X"
              using openin_subset by (force simp add: B_def C_def)
            have "(countable intersection_of openin X) B"
              unfolding B_def C_def 
              by (intro relative_to_inc countable_intersection_of_Inter countable_intersection_of_inc) auto
            then have "gdelta_in X B"
              unfolding gdelta_in_def by (intro relative_to_subset_inc \<open>B \<subseteq> topspace X\<close>)
            moreover have "A=D"
            proof (intro equalityI subsetI)
              fix x
              assume x: "x \<in> D"
              then have "x \<in> topspace X"
                using \<open>B \<subseteq> topspace X\<close> \<open>D=B\<close> by blast
              show "x \<in> A"
              proof (clarsimp simp: A_def \<open>x \<in> topspace X\<close>)
                fix \<epsilon> :: real
                assume "\<epsilon>>0"
                then obtain U b where "openin X U" "b \<in> topspace X"
                        and U: "\<forall>x\<in>S \<inter> U - {b}. \<forall>y\<in>S \<inter> U - {b}. d (f x) (f y) < \<epsilon>" and "x \<in> U"
                  using x by (auto simp: D_def C_def A_def Ball_def)
                then have "openin X (U-{b})"
                  by (meson \<open>t1_space X\<close> t1_space_openin_delete_alt)
                then show "\<exists>U. openin X U \<and> x \<in> U \<and> (\<forall>xa\<in>S \<inter> U - {x}. \<forall>y\<in>S \<inter> U - {x}. d (f xa) (f y) < \<epsilon>)"
                  using U \<open>openin X U\<close> \<open>x \<in> U\<close> by auto
              qed
            next
              show "\<And>x. x \<in> A \<Longrightarrow> x \<in> D"
                unfolding A_def D_def C_def
                by clarsimp meson
            qed
            ultimately show ?thesis
              by (simp add: \<open>D=B\<close>)
          qed
          then show ?thesis
            by (simp add: A_def convergent_eq_zero_oscillation_gen False fim \<open>mcomplete\<close> cong: conj_cong)
        qed
      qed
      
      
      lemma gdelta_in_points_of_convergence_within:
        assumes Y: "completely_metrizable_space Y"
          and f: "continuous_map (subtopology X S) Y f \<or> t1_space X \<and> f \<in> S \<rightarrow> topspace Y"
        shows "gdelta_in X {x \<in> topspace X. \<exists>l. limitin Y f l (atin_within X x S)}"
        using assms
        unfolding completely_metrizable_space_def
        using Metric_space.gdelta_in_points_of_convergence_within Metric_space.topspace_mtopology by fastforce
      
      
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
          "mcomplete_of m'" and fim: "f \<in> M \<rightarrow> mspace m'"
          and clo: "mtopology_of m' closure_of f ` M = mspace m'"
          and d: "\<And>x y. \<lbrakk>x \<in> M; y \<in> M\<rbrakk> \<Longrightarrow> mdist m' (f x) (f y) = d x y"
          by (metis metric_completion)
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
          by (simp add: clo dense_locally_compact_openin_Hausdorff_space fim image_subset_iff_funcset)
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
      
    
    subsection \<open>Dimension of a topological space\<close>
    
    text\<open>Basic definition of the small inductive dimension relation. Works in any topological space.\<close>
    
    inductive dimension_le :: "['a topology, int] \<Rightarrow> bool" (infix "dim'_le" 50) 
      where "\<lbrakk>-1 \<le> n;
            \<And>V a. \<lbrakk>openin X V; a \<in> V\<rbrakk> \<Longrightarrow> \<exists>U. a \<in> U \<and> U \<subseteq> V \<and> openin X U \<and> (subtopology X (X frontier_of U)) dim_le (n-1)\<rbrakk>
                  \<Longrightarrow> X dim_le (n::int)"
    
    lemma dimension_le_neighbourhood_base:
       "X dim_le n \<longleftrightarrow>
       -1 \<le> n \<and> neighbourhood_base_of (\<lambda>U. openin X U \<and> (subtopology X (X frontier_of U)) dim_le (n-1)) X"
      by (smt (verit, best) dimension_le.simps open_neighbourhood_base_of)
    
    lemma dimension_le_bound: "X dim_le n \<Longrightarrow>-1 \<le> n"
      using dimension_le.simps by blast
      
    lemma dimension_le_mono [rule_format]:
      assumes "X dim_le m"
      shows "m \<le> n \<longrightarrow> X dim_le n"
      using assms
    proof (induction arbitrary: n rule: dimension_le.induct)
      case (1 m X)
      show ?case
      proof (intro strip dimension_le.intros)
        show "-1 \<le> n" if "m \<le> n" for n :: int using that using "1.hyps" by fastforce    
        show "\<exists>U. a \<in> U \<and> U \<subseteq> V \<and> openin X U \<and> subtopology X (X frontier_of U) dim_le n-1"
          if "m \<le> n" and "openin X V" and "a \<in> V" for n V a
          using that by (meson "1.IH" diff_right_mono)
      qed
    qed
    
    lemma dimension_le_eq_empty:
       "X dim_le -1 \<longleftrightarrow> topspace X = {}"
    proof
      assume "X dim_le (-1)"
      then show "topspace X = {}"
        by (smt (verit, ccfv_threshold) Diff_empty Diff_eq_empty_iff dimension_le.cases openin_topspace subset_eq)
    next
      assume "topspace X = {}"
      then show "X dim_le (-1)"
        using dimension_le.simps openin_subset by fastforce
    qed
    
    lemma dimension_le_0_neighbourhood_base_of_clopen:
      "X dim_le 0 \<longleftrightarrow> neighbourhood_base_of (\<lambda>U. closedin X U \<and> openin X U) X"
    proof -
      have "(subtopology X (X frontier_of U) dim_le -1) =
            closedin X U" if "openin X U" for U
        by (metis dimension_le_eq_empty frontier_of_eq_empty frontier_of_subset_topspace openin_subset that topspace_subtopology_subset)
      then show ?thesis
        by (smt (verit, del_insts) dimension_le.simps open_neighbourhood_base_of)
    qed
    
    lemma dimension_le_subtopology:
      "X dim_le n \<Longrightarrow> subtopology X S dim_le n"
    proof (induction arbitrary: S rule: dimension_le.induct)
      case (1 n X)
      show ?case 
      proof (intro dimension_le.intros)
        show "- 1 \<le> n"
          by (simp add: "1.hyps")
        fix U' a
        assume U': "openin (subtopology X S) U'" and "a \<in> U'"
        then obtain U where U: "openin X U" "U' = U \<inter> S"
          by (meson openin_subtopology)
        then obtain V where "a \<in> V" "V \<subseteq> U" "openin X V" 
          and subV: "subtopology X (X frontier_of V) dim_le n-1" 
          and dimV: "\<And>T. subtopology X (X frontier_of V \<inter> T) dim_le n-1"
          by (metis "1.IH" Int_iff \<open>a \<in> U'\<close> subtopology_subtopology)
        show "\<exists>W. a \<in> W \<and> W \<subseteq> U' \<and> openin (subtopology X S) W \<and> subtopology (subtopology X S) (subtopology X S frontier_of W) dim_le n-1"
        proof (intro exI conjI)
          show "a \<in> S \<inter> V" "S \<inter> V \<subseteq> U'"
            using \<open>U' = U \<inter> S\<close> \<open>a \<in> U'\<close> \<open>a \<in> V\<close> \<open>V \<subseteq> U\<close> by blast+
          show "openin (subtopology X S) (S \<inter> V)"
            by (simp add: \<open>openin X V\<close> openin_subtopology_Int2)
          have "S \<inter> subtopology X S frontier_of V \<subseteq> X frontier_of V"
            by (simp add: frontier_of_subtopology_subset)
          then show "subtopology (subtopology X S) (subtopology X S frontier_of (S \<inter> V)) dim_le n-1"
            by (metis dimV frontier_of_restrict inf.absorb_iff2 inf_left_idem subtopology_subtopology topspace_subtopology)
        qed
      qed
    qed
    
    lemma dimension_le_subtopologies:
       "\<lbrakk>subtopology X T dim_le n; S \<subseteq> T\<rbrakk> \<Longrightarrow> (subtopology X S) dim_le n"
      by (metis dimension_le_subtopology inf.absorb_iff2 subtopology_subtopology)
    
    lemma dimension_le_eq_subtopology:
       "(subtopology X S) dim_le n \<longleftrightarrow>
        -1 \<le> n \<and>
        (\<forall>V a. openin X V \<and> a \<in> V \<and> a \<in> S
               \<longrightarrow> (\<exists>U. a \<in> U \<and> U \<subseteq> V \<and> openin X U \<and>
                        subtopology X (subtopology X S frontier_of (S \<inter> U)) dim_le (n-1)))"
    proof -
      have *: "(\<exists>T. a \<in> T \<and> T \<inter> S \<subseteq> V \<inter> S \<and> openin X T \<and> subtopology X (S \<inter> (subtopology X S frontier_of (T \<inter> S))) dim_le n-1)
           \<longleftrightarrow> (\<exists>U. a \<in> U \<and> U \<subseteq> V \<and> openin X U \<and> subtopology X (subtopology X S frontier_of (S \<inter> U)) dim_le n-1)"
        if "a \<in> V" "a \<in> S" "openin X V" for a V
      proof -
        have "\<exists>U. a \<in> U \<and> U \<subseteq> V \<and> openin X U \<and> subtopology X (subtopology X S frontier_of (S \<inter> U)) dim_le n-1"
          if "a \<in> T" and sub: "T \<inter> S \<subseteq> V \<inter> S" and "openin X T"
            and dim: "subtopology X (S \<inter> subtopology X S frontier_of (T \<inter> S)) dim_le n-1"
          for T 
        proof (intro exI conjI)
          show "openin X (T \<inter> V)"
            using \<open>openin X V\<close> \<open>openin X T\<close> by blast
          show "subtopology X (subtopology X S frontier_of (S \<inter> (T \<inter> V))) dim_le n-1"
            by (metis dim frontier_of_subset_subtopology inf.boundedE inf_absorb2 inf_assoc inf_commute sub)
        qed (use \<open>a \<in> V\<close> \<open>a \<in> T\<close> in auto)
        moreover have "\<exists>T. a \<in> T \<and> T \<inter> S \<subseteq> V \<inter> S \<and> openin X T \<and> subtopology X (S \<inter> subtopology X S frontier_of (T \<inter> S)) dim_le n-1"
          if "a \<in> U" and "U \<subseteq> V" and "openin X U"
            and dim: "subtopology X (subtopology X S frontier_of (S \<inter> U)) dim_le n-1"
          for U
          by (metis that frontier_of_subset_subtopology inf_absorb2 inf_commute inf_le1 le_inf_iff)
        ultimately show ?thesis
          by safe
      qed
      show ?thesis
        apply (simp add: dimension_le.simps [of _ n] subtopology_subtopology openin_subtopology flip: *)
        by (safe; metis Int_iff inf_le2 le_inf_iff)
    qed
    
    
    lemma homeomorphic_space_dimension_le_aux:
      assumes "X homeomorphic_space Y" "X dim_le of_nat n - 1"
      shows "Y dim_le of_nat n - 1"
      using assms
    proof (induction n arbitrary: X Y)
      case 0
      then show ?case
        by (simp add: dimension_le_eq_empty homeomorphic_empty_space)
    next
      case (Suc n)
      then have X_dim_n: "X dim_le n"
        by simp
      show ?case 
      proof (clarsimp simp add: dimension_le.simps [of Y n])
        fix V b
        assume "openin Y V" and "b \<in> V"
        obtain f g where fg: "homeomorphic_maps X Y f g"
          using \<open>X homeomorphic_space Y\<close> homeomorphic_space_def by blast
        then have "openin X (g ` V)"
          using \<open>openin Y V\<close> homeomorphic_map_openness_eq homeomorphic_maps_map by blast
        then obtain U where "g b \<in> U" "openin X U" and gim: "U \<subseteq> g ` V" and sub: "subtopology X (X frontier_of U) dim_le int n - int 1"
          using X_dim_n unfolding dimension_le.simps [of X n] by (metis \<open>b \<in> V\<close> imageI of_nat_eq_1_iff)
        show "\<exists>U. b \<in> U \<and> U \<subseteq> V \<and> openin Y U \<and> subtopology Y (Y frontier_of U) dim_le int n - 1"
        proof (intro conjI exI)
          show "b \<in> f ` U"
            by (metis (no_types, lifting) \<open>b \<in> V\<close> \<open>g b \<in> U\<close> \<open>openin Y V\<close> fg homeomorphic_maps_map image_iff openin_subset subsetD)
          show "f ` U \<subseteq> V"
            by (smt (verit, ccfv_threshold) \<open>openin Y V\<close> fg gim homeomorphic_maps_map image_iff openin_subset subset_iff)
          show "openin Y (f ` U)"
            using \<open>openin X U\<close> fg homeomorphic_map_openness_eq homeomorphic_maps_map by blast
          show "subtopology Y (Y frontier_of f ` U) dim_le int n-1"
          proof (rule Suc.IH)
            have "homeomorphic_maps (subtopology X (X frontier_of U)) (subtopology Y (Y frontier_of f ` U)) f g"
              using \<open>openin X U\<close> fg
              by (metis frontier_of_subset_topspace homeomorphic_map_frontier_of homeomorphic_maps_map homeomorphic_maps_subtopologies openin_subset topspace_subtopology topspace_subtopology_subset)
            then show "subtopology X (X frontier_of U) homeomorphic_space subtopology Y (Y frontier_of f ` U)"
              using homeomorphic_space_def by blast
            show "subtopology X (X frontier_of U) dim_le int n-1"
              using sub by fastforce
          qed
        qed
      qed
    qed
    
    lemma homeomorphic_space_dimension_le:
      assumes "X homeomorphic_space Y"
      shows "X dim_le n \<longleftrightarrow> Y dim_le n"
    proof (cases "n \<ge> -1")
      case True
      then show ?thesis
        using homeomorphic_space_dimension_le_aux [of _ _ "nat(n+1)"] by (smt (verit) assms homeomorphic_space_sym nat_eq_iff)
    next
      case False
      then show ?thesis
        by (metis dimension_le_bound)
    qed
    
    lemma dimension_le_retraction_map_image:
       "\<lbrakk>retraction_map X Y r; X dim_le n\<rbrakk> \<Longrightarrow> Y dim_le n"
      by (meson dimension_le_subtopology homeomorphic_space_dimension_le retraction_map_def retraction_maps_section_image2)
    
    lemma dimension_le_discrete_topology [simp]: "(discrete_topology U) dim_le 0"
      using dimension_le.simps dimension_le_eq_empty by fastforce
    
    lemma zero_dimensional_imp_completely_regular_space:
      assumes "X dim_le 0" 
      shows "completely_regular_space X"
    proof (clarsimp simp: completely_regular_space_def)
      fix C a
      assume "closedin X C" and "a \<in> topspace X" and "a \<notin> C"
      then obtain U where "closedin X U" "openin X U" "a \<in> U" and U: "U \<subseteq> topspace X - C"
        using assms by (force simp add: closedin_def dimension_le_0_neighbourhood_base_of_clopen open_neighbourhood_base_of)
      show "\<exists>f. continuous_map X (top_of_set {0::real..1}) f \<and> f a = 0 \<and> f ` C \<subseteq> {1}"
      proof (intro exI conjI)
        have "continuous_map X euclideanreal (\<lambda>x. if x \<in> U then 0 else 1)"
          using \<open>closedin X U\<close> \<open>openin X U\<close> apply (clarsimp simp: continuous_map_def closedin_def)
          by (smt (verit) Diff_iff mem_Collect_eq openin_subopen subset_eq)
        then show "continuous_map X (top_of_set {0::real..1}) (\<lambda>x. if x \<in> U then 0 else 1)"
          by (auto simp: continuous_map_in_subtopology)
      qed (use U \<open>a \<in> U\<close> in auto)
    qed
    
    lemma zero_dimensional_imp_regular_space: "X dim_le 0 \<Longrightarrow> regular_space X"
      by (simp add: completely_regular_imp_regular_space zero_dimensional_imp_completely_regular_space)
    

subsection\<open> Theorems from Kuratowski\<close>

text\<open>Kuratowski, Remark on an Invariance Theorem, \emph{Fundamenta Mathematicae} \textbf{37} (1950), pp. 251-252. 
 The idea is that in suitable spaces, to show "number of components of the complement" (without 
 distinguishing orders of infinity) is a homeomorphic invariant, it 
 suffices to show it for closed subsets. Kuratowski states the main result 
 for a "locally connected continuum", and seems clearly to be implicitly   
 assuming that means metrizable. We call out the general topological       
 hypotheses more explicitly, which do not however include connectedness.   \<close>


lemma separation_by_closed_intermediates_count:
  assumes X: "hereditarily normal_space X"
    and "finite \<U>"
    and pwU: "pairwise (separatedin X) \<U>"
    and nonempty: "{} \<notin> \<U>"
    and UU: "\<Union>\<U> = topspace X - S"
  obtains C where "closedin X C" "C \<subseteq> S"
                  "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                     \<Longrightarrow> \<exists>\<V>. finite \<V> \<and> card \<V> = card \<U> \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - D"
proof -
  obtain F where F: "\<And>S. S \<in> \<U> \<Longrightarrow> openin X (F S) \<and> S \<subseteq> F S"
    and pwF: "pairwise (\<lambda>S T. disjnt (F S) (F T)) \<U>"
    using assms by (smt (verit, best) Diff_subset Sup_le_iff hereditarily_normal_separation_pairwise)
  show thesis
  proof
    show "closedin X (topspace X - \<Union>(F ` \<U>))"
      using F by blast
    show "topspace X - \<Union>(F ` \<U>) \<subseteq> S"
      using UU F by auto
    show "\<exists>\<V>. finite \<V> \<and> card \<V> = card \<U> \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - C"
      if "closedin X C" "C \<subseteq> S" and C: "topspace X - \<Union>(F ` \<U>) \<subseteq> C" for C
    proof (intro exI conjI strip)
      show "finite ((\<lambda>S. F S - C) ` \<U>)"
        by (simp add: assms(2))
      have "inj_on (\<lambda>S. F S - C) \<U>"
        using pwF F
        unfolding inj_on_def pairwise_def disjnt_iff
        by (metis Diff_iff UU UnionI nonempty subset_empty subset_eq \<open>C \<subseteq> S\<close>)
      then show "card ((\<lambda>S. F S - C) ` \<U>) = card \<U>"
        using card_image by blast
      show "pairwise (separatedin X) ((\<lambda>S. F S - C) ` \<U>)"
        using \<open>closedin X C\<close> F pwF by (force simp: pairwise_def openin_diff separatedin_open_sets disjnt_iff)
      show "{} \<notin> (\<lambda>S. F S - C) ` \<U>"
        using nonempty UU \<open>C \<subseteq> S\<close> F
        by clarify (metis DiffD2 Diff_eq_empty_iff F UnionI subset_empty subset_eq)
      show "(\<Union>S\<in>\<U>. F S - C) = topspace X - C"
        using UU F C openin_subset by fastforce
    qed
  qed
qed

lemma separation_by_closed_intermediates_gen:
  assumes X: "hereditarily normal_space X"
    and discon: "\<not> connectedin X (topspace X - S)"
  obtains C where "closedin X C" "C \<subseteq> S"
                  "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk> \<Longrightarrow> \<not> connectedin X (topspace X - D)"
proof -
  obtain C1 C2 where Ueq: "C1 \<union> C2 = topspace X - S" and "C1 \<noteq> {}" "C2 \<noteq> {}" 
    and sep: "separatedin X C1 C2" and "C1 \<noteq> C2"
    by (metis Diff_subset connectedin_eq_not_separated discon separatedin_refl)
  then obtain C where "closedin X C" "C \<subseteq> S"
    and C: "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                     \<Longrightarrow> \<exists>\<V>. finite \<V> \<and> card \<V> = Suc (Suc 0) \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - D"
    using separation_by_closed_intermediates_count [of X "{C1,C2}" S] X
    apply (simp add: pairwise_insert separatedin_sym)
    by metis
  have "\<not> connectedin X (topspace X - D)"
    if D: "closedin X D" "C \<subseteq> D" "D \<subseteq> S" for D 
  proof -
    obtain V1 V2 where *: "pairwise (separatedin X) {V1,V2}" "{} \<notin> {V1,V2}" 
                          "\<Union>{V1,V2} = topspace X - D" "V1\<noteq>V2"
      by (smt (verit, ccfv_SIG) C [OF D] pairwise_insert card_Suc_eq_finite card_0_eq insert_iff)
    then have "disjnt V1 V2"
      by (metis pairwise_insert separatedin_imp_disjoint singleton_iff)
      with * show ?thesis
        by (auto simp add: connectedin_eq_not_separated pairwise_insert)
    qed
  then show thesis
    using \<open>C \<subseteq> S\<close> \<open>closedin X C\<close> that by auto
qed


lemma separation_by_closed_intermediates_eq_count:
  assumes lcX: "locally_connected_space X" and hnX: "hereditarily normal_space X"
  shows "(\<exists>\<U>. finite \<U> \<and> card \<U> = n \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S
                   \<longrightarrow> (\<exists>\<U>. finite \<U> \<and> card \<U> = n \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D)))"
         (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis hnX separation_by_closed_intermediates_count)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "n=0")
    case True
    with R show ?thesis
      by (metis Diff_mono card_0_eq ccSup_empty empty_iff subsetI subset_antisym)
  next
    case False
    obtain C where "closedin X C" "C \<subseteq> S"
             and C: "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                      \<Longrightarrow> \<exists>\<U>. finite \<U> \<and> card \<U> = n \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D"
      using R by force
    then have "C \<subseteq> topspace X"
      by (simp add: closedin_subset)
    define \<U> where "\<U> \<equiv> {D \<in> connected_components_of (subtopology X (topspace X - C)). D-S \<noteq> {}}"
    have ope\<U>: "openin X U" if "U \<in> \<U>" for U
      using that  \<open>closedin X C\<close> lcX locally_connected_space_open_connected_components 
      by (fastforce simp add: closedin_def \<U>_def)
    have "{} \<notin> \<U>"
      by (auto simp: \<U>_def)
    have "pairwise disjnt \<U>"
      using connected_components_of_disjoint by (fastforce simp add: pairwise_def \<U>_def)
    show ?lhs
    proof (rule ccontr)
      assume con: "\<nexists>\<U>. finite \<U> \<and> card \<U> = n \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S"
      have card\<U>: "finite \<U> \<and> card \<U> < n"
      proof (rule ccontr)
        assume "\<not> (finite \<U> \<and> card \<U> < n)"
        then obtain \<V> where "\<V> \<subseteq> \<U>" "finite \<V>" "card \<V> = n"
          by (metis infinite_arbitrarily_large linorder_not_less obtain_subset_with_card_n)
        then obtain T where "T \<in> \<V>"
          using False by force
        define \<W> where "\<W> \<equiv> insert (topspace X - S - \<Union>(\<V> - {T})) ((\<lambda>D. D - S) ` (\<V> - {T}))"
        have "\<Union>\<W> = topspace X - S"
          using \<open>\<And>U. U \<in> \<U> \<Longrightarrow> openin X U\<close> \<open>\<V> \<subseteq> \<U>\<close> topspace_def by (fastforce simp: \<W>_def)
        moreover have "{} \<notin> \<W>"
        proof -
          obtain a where "a \<in> T" "a \<notin> S"
            using \<U>_def \<open>T \<in> \<V>\<close> \<open>\<V> \<subseteq> \<U>\<close> by blast
          then have "a \<in> topspace X"
            using \<open>T \<in> \<V>\<close> ope\<U> \<open>\<V> \<subseteq> \<U>\<close> openin_subset by blast
          moreover have "a \<notin> \<Union> (\<V> - {T})"
            using diff_Union_pairwise_disjoint [of \<V> "{T}"] \<open>disjoint \<U>\<close> pairwise_subset \<open>T \<in> \<V>\<close> \<open>\<V> \<subseteq> \<U>\<close> \<open>a \<in> T\<close> 
            by auto
          ultimately have "topspace X - S - \<Union> (\<V> - {T}) \<noteq> {}"
            using \<open>a \<notin> S\<close> by blast
          moreover have "\<And>V. V \<in> \<V> - {T} \<Longrightarrow> V - S \<noteq> {}"
            using \<U>_def \<open>\<V> \<subseteq> \<U>\<close> by blast
          ultimately show ?thesis
            by (metis (no_types, lifting) \<W>_def image_iff insert_iff)
        qed
        moreover have "disjoint \<V>"
          using \<open>\<V> \<subseteq> \<U>\<close> \<open>disjoint \<U>\<close> pairwise_subset by blast
        then have inj: "inj_on (\<lambda>D. D - S) (\<V> - {T})"
          unfolding inj_on_def using \<open>\<V> \<subseteq> \<U>\<close> disjointD \<U>_def inf_commute by blast
        have "finite \<W>" "card \<W> = n"
          using \<open>{} \<notin> \<W>\<close> \<open>n \<noteq> 0\<close> \<open>T \<in> \<V>\<close>
          by (auto simp add: \<W>_def \<open>finite \<V>\<close> card_insert_if card_image inj \<open>card \<V> = n\<close>)
        moreover have "pairwise (separatedin X) \<W>"
        proof -
          have "disjoint \<W>"
            using \<open>disjoint \<V>\<close> by (auto simp: \<W>_def pairwise_def disjnt_iff)
          have "pairwise (separatedin (subtopology X (topspace X - S))) \<W>"
          proof (intro pairwiseI)
            fix A B
            assume \<section>: "A \<in> \<W>" "B \<in> \<W>" "A \<noteq> B"
            then have "disjnt A B"
              by (meson \<open>disjoint \<W>\<close> pairwiseD)
            have "closedin (subtopology X (topspace X - C)) (\<Union>(\<V> - {T}))"
              using \<U>_def \<open>\<V> \<subseteq> \<U>\<close> closedin_connected_components_of \<open>finite \<V>\<close>
              by (force simp add: intro!: closedin_Union)
            with \<open>C \<subseteq> S\<close> have "openin (subtopology X (topspace X - S)) (topspace X - S - \<Union>(\<V> - {T}))"
              by (fastforce simp add: openin_closedin_eq closedin_subtopology Int_absorb1)
            moreover have "\<And>V. V \<in> \<V> \<and> V\<noteq>T \<Longrightarrow> openin (subtopology X (topspace X - S)) (V - S)"
              using \<open>\<V> \<subseteq> \<U>\<close> ope\<U>
              by (metis IntD2 Int_Diff inf.orderE openin_subset openin_subtopology) 
            ultimately have "openin (subtopology X (topspace X - S)) A" "openin (subtopology X (topspace X - S)) B"
              using \<section> \<W>_def by blast+
            with \<open>disjnt A B\<close> show "separatedin (subtopology X (topspace X - S)) A B"
              using separatedin_open_sets by blast
          qed
          then show ?thesis
            by (simp add: pairwise_def separatedin_subtopology)
        qed
        ultimately show False
          using con by blast
      qed
      obtain \<V> where "finite \<V>" "card \<V> = n" "{} \<notin> \<V>"
                and pw\<V>: "pairwise (separatedin X) \<V>" and UV: "\<Union>\<V> = topspace X - (topspace X - \<Union>\<U>)"
      proof -
        have "closedin X (topspace X - \<Union>\<U>)"
          using ope\<U> by blast
        moreover 
        have "C \<subseteq> topspace X - \<Union>\<U>"
          using \<open>C \<subseteq> topspace X\<close> connected_components_of_subset by (fastforce simp: \<U>_def)
        moreover have "topspace X - \<Union>\<U> \<subseteq> S"
          using Union_connected_components_of [of "subtopology X (topspace X - C)"] \<open>C \<subseteq> S\<close>
          by (auto simp: \<U>_def)
        ultimately show thesis
          by (metis C that)
      qed
      have "\<V> \<lesssim> \<U>"
      proof (rule lepoll_relational_full)
        have "\<Union>\<V> = \<Union>\<U>"
          by (simp add: Sup_le_iff UV double_diff ope\<U> openin_subset)
        then show "\<exists>U. U \<in> \<U> \<and> \<not> disjnt U V" if "V \<in> \<V>" for V
          using that
          by (metis \<open>{} \<notin> \<V>\<close> disjnt_Union1 disjnt_self_iff_empty)
        show "C1 = C2"
          if "T \<in> \<U>" and "C1 \<in> \<V>" and "C2 \<in> \<V>" and "\<not> disjnt T C1" and "\<not> disjnt T C2" for T C1 C2
        proof (cases "C1=C2")
          case False
          then have "connectedin X T"
            using \<U>_def connectedin_connected_components_of connectedin_subtopology \<open>T \<in> \<U>\<close> by blast
          have "T \<subseteq> C1 \<union> \<Union>(\<V> - {C1})"
            using \<open>\<Union> \<V> = \<Union> \<U>\<close> \<open>T \<in> \<U>\<close> by auto
          with \<open>connectedin X T\<close>
          have "\<not> separatedin X C1 (\<Union>(\<V> - {C1}))"
            unfolding connectedin_eq_not_separated_subset
            by (smt (verit) that False disjnt_def UnionI disjnt_iff insertE insert_Diff)
          with that show ?thesis
            by (metis (no_types, lifting) \<open>finite \<V>\<close> finite_Diff pairwiseD pairwise_alt pw\<V> separatedin_Union(1) separatedin_def)
        qed auto
      qed
      then show False
        using \<open>card \<V> = n\<close> card\<U>
        by (simp add: \<open>finite \<V>\<close> lepoll_iff_card_le)
    qed
  qed
qed

lemma separation_by_closed_intermediates_eq_gen:
  assumes "locally_connected_space X" "hereditarily normal_space X"
  shows "\<not> connectedin X (topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S \<longrightarrow> \<not> connectedin X (topspace X - D)))"
    (is "?lhs = ?rhs")
proof -
  have *: "(\<exists>C1 C2. separatedin X C1 C2 \<and> C1\<noteq>C2 \<and> C1\<noteq>{} \<and> C2\<noteq>{} \<and> C1 \<union> C2 = topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S
                   \<longrightarrow> (\<exists>C1 C2. separatedin X C1 C2 \<and> C1\<noteq>C2 \<and> C1\<noteq>{} \<and> C2\<noteq>{} \<and> C1 \<union> C2 = topspace X - D)))"
    using separation_by_closed_intermediates_eq_count [OF assms, of "Suc(Suc 0)" S]
    apply (simp add: card_Suc_eq pairwise_insert separatedin_sym flip: ex_simps cong: conj_cong)
    apply (simp add: eq_sym_conv conj_ac)
    done
  with separatedin_refl
  show ?thesis
    apply (simp add: connectedin_eq_not_separated)
    by (smt (verit, best) separatedin_refl)
qed



lemma lepoll_connnected_components_connectedin:
  assumes "\<And>C. C \<in> \<U> \<Longrightarrow> connectedin X C"  "\<Union>\<U> = topspace X"
  shows "connected_components_of X \<lesssim> \<U>"
proof -
  have "connected_components_of X \<lesssim> \<U> - {{}}"
  proof (rule lepoll_relational_full)
    show "\<exists>U. U \<in> \<U> - {{}} \<and> U \<subseteq> V"
      if "V \<in> connected_components_of X" for V 
      using that unfolding connected_components_of_def image_iff
      by (metis Union_iff assms connected_component_of_maximal empty_iff insert_Diff_single insert_iff)
    show "V = V'"
      if "U \<in> \<U> - {{}}" "V \<in> connected_components_of X" "V' \<in> connected_components_of X" "U \<subseteq> V" "U \<subseteq> V'"
      for U V V'
      by (metis DiffD2 disjointD insertCI le_inf_iff pairwise_disjoint_connected_components_of subset_empty that)
  qed
  also have "\<dots> \<lesssim> \<U>"
    by (simp add: subset_imp_lepoll)
  finally show ?thesis .
qed

lemma lepoll_connected_components_alt:
  "{..<n::nat} \<lesssim> connected_components_of X \<longleftrightarrow>
    n = 0 \<or> (\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "n=0")
next
  case False
  show ?thesis 
  proof
    assume L: ?lhs 
    with False show ?rhs
    proof (induction n rule: less_induct)
      case (less n)
      show ?case
      proof (cases "n\<le>1")
        case True
        with less.prems connected_components_of_empty_space show ?thesis
          by (force simp add: le_Suc_eq eqpoll_iff_finite_card card_Suc_eq simp flip: ex_simps)
      next
        case False
        then have "n-1 \<noteq> 0"
          by linarith
        have n1_lesspoll: "{..<n-1} \<prec> {..<n}"
          using False lesspoll_iff_finite_card by fastforce
        also have "\<dots> \<lesssim> connected_components_of X"
          using less by blast
        finally have "{..<n-1} \<lesssim> connected_components_of X"
          using lesspoll_imp_lepoll by blast 
        then obtain \<U> where Ueq: "\<U> \<approx> {..<n-1}" and "{} \<notin> \<U>" 
          and pwU: "pairwise (separatedin X) \<U>" and UU: "\<Union>\<U> = topspace X"
          by (meson \<open>n - 1 \<noteq> 0\<close> diff_less gr0I less zero_less_one)
        show ?thesis
        proof (cases "\<forall>C \<in> \<U>. connectedin X C")
          case True
          then show ?thesis
            using lepoll_connnected_components_connectedin [of \<U> X] less.prems
            by (metis UU Ueq lepoll_antisym lepoll_trans lepoll_trans2 lesspoll_def n1_lesspoll)
          next
            case False
            with UU obtain C A B where ABC: "C \<in> \<U>" "A \<union> B = C" "A \<noteq> {}" "B \<noteq> {}" and sep: "separatedin X A B"
              by (fastforce simp add: connectedin_eq_not_separated)
            define \<V> where "\<V> \<equiv> insert A (insert B (\<U> - {C}))"
            have "\<V> \<approx> {..<n}"
            proof -
              have "A \<noteq> B"
                using \<open>B \<noteq> {}\<close> sep by auto
              moreover obtain "A \<notin> \<U>" "B \<notin> \<U>"
                using pwU unfolding pairwise_def
                by (metis ABC sep separatedin_Un(1) separatedin_refl separatedin_sym)
              moreover have "card \<U> = n-1" "finite \<U>"
                using Ueq eqpoll_iff_finite_card by blast+
              ultimately
              have "card (insert A (insert B (\<U> - {C}))) = n"
                using \<open>C \<in> \<U>\<close> by (auto simp add: card_insert_if)
              then show ?thesis
                using \<V>_def \<open>finite \<U>\<close> eqpoll_iff_finite_card by blast
            qed
            moreover have "{} \<notin> \<V>"
              using ABC \<V>_def \<open>{} \<notin> \<U>\<close> by blast
            moreover have "\<Union>\<V> = topspace X"
              using ABC UU \<V>_def by auto
            moreover have "pairwise (separatedin X) \<V>"
              using pwU sep ABC unfolding  \<V>_def
              apply (simp add: separatedin_sym pairwise_def)
              by (metis member_remove remove_def separatedin_Un(1))
            ultimately show ?thesis
              by blast
          qed
      qed
    qed
  next
    assume ?rhs
    then obtain \<U> where "\<U> \<approx> {..<n}" "{} \<notin> \<U>" and pwU: "pairwise (separatedin X) \<U>" and UU: "\<Union>\<U> = topspace X"
      using False by force
    have "card (connected_components_of X) \<ge> n" if "finite (connected_components_of X)"
    proof -
      have "\<U> \<lesssim> connected_components_of X"
      proof (rule lepoll_relational_full)
        show "\<exists>T. T \<in> connected_components_of X \<and> \<not> disjnt T C" if "C \<in> \<U>" for C 
          by (metis that UU Union_connected_components_of Union_iff \<open>{} \<notin> \<U>\<close> disjnt_iff equals0I)
        show "(C1::'a set) = C2"
          if "T \<in> connected_components_of X" and "C1 \<in> \<U>" "C2 \<in> \<U>" "\<not> disjnt T C1" "\<not> disjnt T C2" for T C1 C2
        proof (rule ccontr)
          assume "C1 \<noteq> C2"
          then have "connectedin X T"
            by (simp add: connectedin_connected_components_of that(1))
          moreover have "\<not> separatedin X C1 (\<Union>(\<U> - {C1}))"
            using \<open>connectedin X T\<close> pwU unfolding pairwise_def
            by (smt (verit) Sup_upper UU Union_connected_components_of \<open>C1 \<noteq> C2\<close> complete_lattice_class.Sup_insert connectedin_subset_separated_union disjnt_subset2 disjnt_sym insert_Diff separatedin_imp_disjoint that)
          ultimately show False
            using \<open>\<U> \<approx> {..<n}\<close>
            apply (simp add: connectedin_eq_not_separated_subset eqpoll_iff_finite_card)
            by (metis Sup_upper UU finite_Diff pairwise_alt pwU separatedin_Union(1) that(2))
        qed
      qed
      then show ?thesis
        by (metis \<open>\<U> \<approx> {..<n}\<close> eqpoll_iff_finite_card lepoll_iff_card_le that)
    qed
    then show ?lhs
      by (metis card_lessThan finite_lepoll_infinite finite_lessThan lepoll_iff_card_le)
  qed
qed auto


lemma lemmaX:
  assumes "\<And>S T. R S T \<Longrightarrow> R T S"
  shows "(\<forall>S T n. R S T \<longrightarrow> (f S \<approx> {..<n::nat} \<longleftrightarrow> f T \<approx> {..<n::nat})) \<longleftrightarrow>
         (\<forall>n S T. R S T \<longrightarrow> {..<n::nat} \<lesssim> f S \<longrightarrow> {..<n::nat} \<lesssim> f T)"
  apply (rule )
   apply (meson eqpoll_iff_finite_card eqpoll_sym finite_lepoll_infinite finite_lessThan lepoll_trans2)
  by (smt (verit, best) assms card_lessThan eqpoll_iff_card eqpoll_imp_lepoll finite_lepoll_infinite finite_lessThan lepoll_antisym lepoll_iff_finite_card lessI linorder_not_le nle_le)



lemma lemur: (*NEEDED?*)
   "pairwise (separatedin (subtopology X (topspace X - S))) \<U> \<and> {} \<notin> \<U> \<and>
     \<Union>\<U> = topspace(subtopology X (topspace X - S)) \<longleftrightarrow>
     pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S"
  by (auto simp: pairwise_def separatedin_subtopology)


lemma Kuratowski_component_number_invariance:
  assumes "compact_space X" "Hausdorff_space X" "locally_connected_space X" "hereditarily normal_space X"
  shows "((\<forall>S T n.
              closedin X S \<and> closedin X T \<and>
              (subtopology X S) homeomorphic_space (subtopology X T)
              \<longrightarrow> (connected_components_of
                    (subtopology X (topspace X - S)) \<approx> {..<n::nat} \<longleftrightarrow>
                   connected_components_of
                    (subtopology X (topspace X - T)) \<approx> {..<n::nat})) \<longleftrightarrow>
           (\<forall>S T n.
              (subtopology X S) homeomorphic_space (subtopology X T)
              \<longrightarrow> (connected_components_of
                    (subtopology X (topspace X - S)) \<approx> {..<n::nat} \<longleftrightarrow>
                   connected_components_of
                    (subtopology X (topspace X - T)) \<approx> {..<n::nat})))"
         (is "?lhs = ?rhs")
proof
  assume L: ?lhs 
  then
  show ?rhs
    apply (subst (asm)lemmaX)
    using homeomorphic_space_sym apply blast
    apply (subst lemmaX)
    using homeomorphic_space_sym apply blast
    apply (erule all_forward)
    apply (simp add: lepoll_connected_components_alt)
    apply (case_tac "n=0")
     apply (simp add: )
    apply (simp add: Int_absorb1)



    by (metis hnX separation_by_closed_intermediates_count)
qed blast

oops

  MAP_EVERY X_GEN_TAC [`S::A=>bool`; `t::A=>bool`] THEN
  ONCE_REWRITE_TAC[SUBTOPOLOGY_RESTRICT] THEN
  ONCE_REWRITE_TAC[SET_RULE `S - t = S - S \<inter> t`] THEN
  MP_TAC(SET_RULE
   `topspace X \<inter> (S::A=>bool) \<subseteq> topspace X \<and>
    topspace X \<inter> (t::A=>bool) \<subseteq> topspace X`) THEN
  SPEC_TAC(`topspace X \<inter> (t::A=>bool)`,`t::A=>bool`) THEN
  SPEC_TAC(`topspace X \<inter> (S::A=>bool)`,`S::A=>bool`) THEN
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
  X_GEN_TAC `C::A=>bool` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(LABEL_TAC "*") THEN EXISTS_TAC `image (f::A=>A) C` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology X (S::A=>bool)` THEN
    ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY; CLOSED_IN_COMPACT_SPACE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY]) THEN
    ASM SET_TAC[];
    X_GEN_TAC `d':A=>bool` THEN STRIP_TAC] THEN
  ABBREV_TAC `D = image (g::A=>A) d'` THEN
  SUBGOAL_THEN `closedin X (D::A=>bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "D" THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology X (t::A=>bool)` THEN
    ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY; CLOSED_IN_COMPACT_SPACE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C::A=>bool) \<subseteq> D \<and> D \<subseteq> S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC \<circ> SPEC `D::A=>bool`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[homeomorphic_space] THEN
  MAP_EVERY EXISTS_TAC [`f::A=>A`; `g::A=>A`] THEN
  SUBGOAL_THEN
   `subtopology X D::A topology = subtopology (subtopology X S) D \<and>
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

(** WE NEED A PROOF THAT the reals and sets of naturals are equipollent **)

lemma (in Metric_space) card_ge_perfect_set:
  assumes "mcomplete"
    and "mtopology derived_set_of S = S" "S \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> S"
proof -
  have "S \<subseteq> M"
    using assms(2) derived_set_of_infinite_mball by blast
  have "(UNIV::real set) \<lesssim> (UNIV::num set set)"
    sorry
  also have "\<dots> \<lesssim> S"
    thm uncountable_closed_interval
    sorry


lemma card_ge_perfect_set:
  assumes X: "completely_metrizable_space X \<or> locally_compact_space X \<and> Hausdorff_space X"
    and "X derived_set_of S = S" "S \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> S"
  using assms
  apply-
  apply (erule disjE)

oops
  REWRITE_TAC[TAUT `(p \<or> q) \<and> r \<Longrightarrow> S \<longleftrightarrow>
                    (p \<Longrightarrow> r \<Longrightarrow> S) \<and> (q \<and> r \<Longrightarrow> S)`] THEN
  REWRITE_TAC[FORALL_AND_THM; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[GSYM FORALL_MCOMPLETE_TOPOLOGY] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS `(:num=>bool)` THEN
    SIMP_TAC[CARD_EQ_REAL; CARD_EQ_IMP_LE] THEN
    SUBGOAL_THEN `(S::A=>bool) \<subseteq> M` ASSUME_TAC THENL
     [ASM_MESON_TAC[DERIVED_SET_OF_SUBSET_TOPSPACE; TOPSPACE_MTOPOLOGY];
      ALL_TAC] THEN

    SUBGOAL_THEN
     `\<forall>x e. x \<in> S \<and> 0 < e
            \<Longrightarrow> \<exists>y z d. y \<in> S \<and> z \<in> S \<and> 0 < d \<and> d < e/2 \<and>
                        mcball y d \<subseteq> mcball x e \<and>
                        mcball z d \<subseteq> mcball x e \<and>
                        disjnt (mcball m (y::A,d)) (mcball z d)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`m::A metric`; `S::A=>bool`]
          DERIVED_SET_OF_INFINITE_MBALL) THEN
      ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `x::A`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC \<circ> SPEC `e / 4`)) THEN
      ASM_REWRITE_TAC[infinite; REAL_ARITH `0 < e / 4 \<longleftrightarrow> 0 < e`] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `x::A` \<circ> MATCH_MP
       (MESON[FINITE_RULES; FINITE_SUBSET]
         `\<not> finite S \<Longrightarrow> \<forall>a b c. \<not> (S \<subseteq> {a,b,c})`)) THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP (SET_RULE
       `(\<forall>b c. \<not> (S \<subseteq> {a,b,c}))
        \<Longrightarrow> \<exists>b c. b \<in> S \<and> c \<in> S \<and> (c \<noteq> a) \<and> (b \<noteq> a) \<and> (b \<noteq> c)`)) THEN
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
    SUBGOAL_THEN `mcomplete (submetric S::A metric)` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE THEN
      ASM_REWRITE_TAC[CLOSED_IN_CONTAINS_DERIVED_SET; TOPSPACE_MTOPOLOGY] THEN
      ASM SET_TAC[];
      REWRITE_TAC[MCOMPLETE_NEST_SING]] THEN
    DISCH_THEN(MP_TAC \<circ> MATCH_MP MONO_FORALL \<circ> GEN `b::num=>bool` \<circ>
      SPEC `\<lambda>n. mcball (submetric S)
                       ((x:(num=>bool)->num=>A) b n,r b n)`) THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    SUBGOAL_THEN `(\<forall>b n. (x:(num=>bool)->num=>A) b n \<in> S) \<and>
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
       `S = {a} \<and> t = {a} \<Longrightarrow> a \<in> S \<inter> t`)) THEN
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
      MAP_EVERY X_GEN_TAC [`X::A topology`; `S::A=>bool`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> SPEC `subtopology X (S::A=>bool)`) THEN
      SUBGOAL_THEN `(S::A=>bool) \<subseteq> topspace X` ASSUME_TAC THENL
       [ASM_MESON_TAC[DERIVED_SET_OF_SUBSET_TOPSPACE]; ALL_TAC] THEN
      ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_SUBTOPOLOGY;
                   DERIVED_SET_OF_SUBTOPOLOGY; SET_RULE `S \<inter> S = S`;
                   SET_RULE `S \<subseteq> u \<Longrightarrow> u \<inter> S = S`] THEN
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
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC \<circ> AP_TERM `\<lambda>s. (z::A) \<in> S`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `X interior_of c::A=>bool`) THEN
      ASM_SIMP_TAC[OPEN_IN_INTERIOR_OF; INTERIOR_OF_SUBSET_TOPSPACE;
                   SET_RULE `S \<subseteq> u \<Longrightarrow> u \<inter> S = S`] THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP (MESON[infinite; FINITE_SING; FINITE_SUBSET]
        `infinite S \<Longrightarrow> \<forall>a. \<not> (S \<subseteq> {a})`)) THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP (SET_RULE
       `(\<forall>a. \<not> (S \<subseteq> {a})) \<Longrightarrow> \<exists>a b. a \<in> S \<and> b \<in> S \<and> (a \<noteq> b)`)) THEN
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
       `p \<and> q \<and> r \<and> S \<and> t \<longleftrightarrow> (q \<and> S) \<and> p \<and> r \<and> t`] THEN
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


