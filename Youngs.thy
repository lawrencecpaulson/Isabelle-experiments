theory Youngs imports 
  "HOL-Library.Sum_of_Squares" "HOL-Analysis.Analysis"
  "HOL-ex.Sketch_and_Explore"
   
begin

text \<open>Kevin Buzzard's example\<close>
lemma
  fixes x::real
  shows "(x+y)*(x+2*y)*(x+3*y) = x^3 + 6*x^2*y + 11*x*y^2 + 6*y^3"
  by (simp add: algebra_simps eval_nat_numeral)


thm strict_mono_inv_on_range
lemma strict_mono_on_inv_into:
  fixes f :: "'a::linorder \<Rightarrow> 'b::order"
  assumes "strict_mono_on f S"
  shows "strict_mono_on (inv_into S f) (f ` S)"
  using assms
  unfolding strict_mono_on_def
  by (metis f_inv_into_f inv_into_into less_asym' neqE)

lemma strict_mono_image_endpoints:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes "strict_mono_on f {a..b}" and f: "continuous_on {a..b} f" and "a \<le> b"
  shows "f ` {a..b} = {f a..f b}"
proof
  show "f ` {a..b} \<subseteq> {f a..f b}"
    using assms(1) strict_mono_on_leD by fastforce
  show "{f a..f b} \<subseteq> f ` {a..b}"
    using assms IVT'[OF _ _ _ f] by (force simp add: Bex_def)
qed

lemma strict_mono_continuous_inv:
  fixes f :: "real \<Rightarrow> real"
  assumes "strict_mono_on f {a..b}" and "continuous_on {a..b} f" and "a \<le> b"
  shows "continuous_on {f a..f b} (inv_into {a..b} f)"
  by (metis strict_mono_image_endpoints assms compact_interval continuous_on_inv inv_into_f_eq strict_mono_on_imp_inj_on)

lemma strict_mono_continuous_inv':
  fixes f :: "real \<Rightarrow> real"
  assumes "strict_mono_on f {a..b}" "continuous_on {a..b} f" "a \<le> b"
     and "\<forall>x\<in>{a..b}. g (f x) = x"
   shows "continuous_on {f a..f b} g"
  by (metis assms compact_Icc continuous_on_inv strict_mono_image_endpoints)

lemma integrable_mono_on:
  fixes f :: "real \<Rightarrow> real"
  assumes "mono_on f {a..b}" and 0: "\<And>x. 0 \<le> f x"
  shows "integrable (lebesgue_on {a..b}) f" 
proof -
  have fborel: "f \<in> borel_measurable (lebesgue_on {a..b})"
    by (smt (verit, best) assms atLeastAtMost_borel borel_measurable_mono_on_fnc borel_measurable_subalgebra mono_restrict_space sets_completionI_sets sets_lborel space_restrict_space2 subset_eq)
  then obtain g where g: "incseq g" and simple: "\<And>i. simple_function (lebesgue_on {a..b}) (g i)" 
    and bdd: " (\<forall>x. bdd_above (range (\<lambda>i. g i x)))" and nonneg: "\<forall>i x. 0 \<le> g i x"
    and fsup: "f = (SUP i. g i)"
    using borel_measurable_implies_simple_function_sequence_real 0
    by metis
  have "f ` {a..b} \<subseteq> {f a..f b}" 
    using assms by (auto simp: mono_on_def)
  have "g i x \<le> f x" for i x
  proof -
    have "bdd_above ((\<lambda>xa. xa x) ` range g)"
      using bdd cSUP_lessD linorder_not_less by fastforce
    then show ?thesis
      by (metis SUP_apply UNIV_I bdd cSUP_upper fsup)
  qed
  then have gf: "g i x \<le> f b" if "x \<in> {a..b}" for i x
    by (smt (verit, best) assms(1) atLeastAtMost_iff mono_on_def that)
  have g_le: "g i x \<le> g j x" if "i\<le>j"  for i j x
    using g by (simp add: incseq_def le_funD that)
  show "integrable (lebesgue_on {a..b}) ( f)"
    apply (rule integrable_dominated_convergence [where s=g and w = "\<lambda>x. f b"])
    using fborel apply blast
    using g
    using borel_measurable_simple_function simple apply blast
      apply blast
     apply (simp add: fsup)
     apply (rule eventuallyI)
     apply (rule order_tendstoI)
      apply (subst (asm)less_cSUP_iff)
        apply (force simp add: )
       apply (smt (verit, best) bdd image_cong range_composition)
      apply clarify
    using g
      apply (smt (verit, del_insts) g_le eventually_sequentially)
     apply (metis (mono_tags) SUP_apply Sup_apply UNIV_I bdd cSUP_lessD eventuallyI)
    apply (rule Measure_Space.AE_I' [of "{}"])
     apply (auto simp: )
    by (simp add: gf nonneg)
qed




definition "segment \<equiv> \<lambda>n k. {real k / real n..(1 + k) / real n}"

lemma segment_nonempty: "segment n k \<noteq> {}"
  by (auto simp: segment_def divide_simps)

lemma segment_Suc: "segment n ` {..<Suc k} = insert {k/n..(1 + real k) / n} (segment n ` {..<k})"
  by (simp add: segment_def lessThan_Suc)

lemma Union_segment_image: "\<Union> (segment n ` {..<k}) = (if k=0 then {} else {0..real k/real n})"
proof (induction k)
  case 0
  then show ?case
    by (auto simp: segment_def)
next
  case (Suc k)
  then show ?case
    by (simp add: divide_simps segment_Suc Un_commute ivl_disj_un_two_touch split: if_split_asm)
qed

definition "segments \<equiv> \<lambda>n. segment n ` {..<n}"

lemma segments_0 [simp]: "segments 0 = {}"
  by (simp add: segments_def)

lemma Union_segments: "\<Union> (segments n) = (if n=0 then {} else {0..1})"
  by (simp add: segments_def Union_segment_image)

definition "regular_division \<equiv> \<lambda>a b n. image (image ((+) a o (*) (b-a))) (segments n)"

lemma translate_scale_01:
  assumes "a \<le> b" 
  shows "(\<lambda>x. a + (b - a) * x) ` {0..1} = {a..b::real}"
proof
  show "{a..b} \<subseteq> (\<lambda>x. a + (b - a) * x) ` {0..1}"
  proof -
    have "u \<in> (\<lambda>x. a + (b - a) * x) ` {0..1}"
      if "a \<le> u" and "u \<le> b" for u
      using that by (rule_tac x="(u-a)/(b-a)" in image_eqI) (auto simp: divide_simps)
    then show ?thesis
      by auto
  qed
  show "(\<lambda>x. a + (b - a) * x) ` {0..1} \<subseteq> {a..b}"
    using assms 
    by (smt (verit, best) atLeastAtMost_iff image_subset_iff mult_left_le mult_nonneg_nonneg)
qed

lemma Union_regular_division:
  assumes "a \<le> b" 
  shows "\<Union>(regular_division a b n) = (if n=0 then {} else {a..b})"
  using assms
  by (auto simp add: regular_division_def Union_segments translate_scale_01 simp flip: image_Union)


lemma regular_divisionE:
  assumes "K \<in> regular_division a b n" "a<b"
  obtains k where "K = {a + (b-a)*(real k / real n) .. a + (b-a)*((1 + real k) / real n)}"
proof -
  have eq: "(\<lambda>x. a + (b - a) * x) = (\<lambda>x. a + x) o (\<lambda>x. (b - a) * x)"
    by (simp add: o_def)
  obtain k where "K = ((\<lambda>x. a + x) o (\<lambda>x. (b - a) * x)) ` {real k / real n .. (1 + real k) / real n}"
    using assms by (auto simp: regular_division_def segments_def segment_def)
  with that \<open>a<b\<close> show ?thesis
    unfolding image_comp [symmetric]  by auto
qed

lemma regular_division_division_of:
  assumes "a < b" "n>0"
  shows "(regular_division a b n) division_of {a..b}"
proof (rule division_ofI)
  show "finite (regular_division a b n)"
    by (simp add: regular_division_def segments_def)
  show \<section>: "\<Union> (regular_division a b n) = {a..b}"
    using Union_regular_division assms by simp
  fix K
  assume K: "K \<in> regular_division a b n"
  then obtain k where Keq: "K = {a + (b-a)*(real k / real n) .. a + (b-a)*((1 + real k) / real n)}" 
    using \<open>a<b\<close> regular_divisionE by blast
  show "K \<subseteq> {a..b}"
    using K Union_regular_division \<open>n>0\<close> by (metis Union_upper \<section>)
  show "(K::real set) \<noteq> {}"
    using K by (auto simp: regular_division_def segment_nonempty segments_def)
  show "\<exists>a b. K = cbox (a::real) b"
    by (metis K \<open>a<b\<close> box_real(2) regular_divisionE)
  fix K'
  assume K': "K' \<in> regular_division a b n" and "K \<noteq> K'"
  then obtain k' where Keq': "K' = {a + (b-a)*(real k' / real n) .. a + (b-a)*((1 + real k') / real n)}" 
    using K \<open>a<b\<close> regular_divisionE by blast
  consider "1 + real k \<le> k'" | "1 + real k' \<le> k"
    using Keq Keq' \<open>K \<noteq> K'\<close> by force
  then show "interior K \<inter> interior K' = {}"
  proof cases
    case 1
    then show ?thesis
      by (simp add: Keq Keq' min_def max_def divide_right_mono assms)
  next
    case 2
    then have "interior K' \<inter> interior K = {}"
      by (simp add: Keq Keq' min_def max_def divide_right_mono assms)
    then show ?thesis
      by (simp add: inf_commute)
  qed
qed



lemma D:
  fixes f :: "real \<Rightarrow> real"
  assumes *: "strict_mono_on f {0..a}"  "continuous_on {0..a} f"  "0 \<le> a"
  obtains f1 f2 where "\<And>x. x \<in> {0..a} \<Longrightarrow> f1 x \<le> f x \<and> f x \<le> f2 x"
  by (metis strict_mono_image_endpoints assms(1) assms(2) assms(3) compact_Icc continuous_on_inv g)


lemma B:
  fixes f :: "'a::linorder \<Rightarrow> 'b::linorder"
  assumes "strict_mono_on f S"  
  shows "bij_betw (inv_into S f) (f ` S) S"
  by (meson assms bij_betw_imageI strict_mono_on_imp_inj_on assms bij_betw_inv_into)



lemma C:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes "strict_mono_on f {a..b}"  "continuous_on {a..b} f"  "a \<le> b"
   shows "strict_mono_on (inv_into {a..b} f) {f a..f b}"
    by (metis assms strict_mono_image_endpoints strict_mono_on_inv_into)

  thm has_integral
proof -
  have "((\<lambda>x. f a) has_integral a * f a) {0..a}"
    using has_integral_const_real [of "f a" 0 a] \<open>a \<ge> 0\<close>
    by simp
  then show ?thesis
    using has_integral_le [OF f]
qed



lemma X:
  fixes a::real
  assumes "strict_mono_on f {0..a}" and f: "(f has_integral I) {0..a}" 
    and "a \<ge> 0"
  shows "I \<le> a * f a"
proof -
  have "((\<lambda>x. f a) has_integral a * f a) {0..a}"
    using has_integral_const_real [of "f a" 0 a] \<open>a \<ge> 0\<close>
    by simp
  then show ?thesis
    using has_integral_le [OF f]
    by (metis assms(1) assms(3) atLeastAtMost_iff order_refl strict_mono_on_leD)
qed


lemma Y:
  fixes a::real
  assumes f_mono: "strict_mono_on f {0..a}" and f_int: "(f has_integral I) {0..a}" 
    and f_cont: "continuous_on {0..a} f"
    and g: "\<forall>x\<in>{0..a}. g (f x) = x"
    and g_int: "(g has_integral J) {f 0..f a}"
    and "a \<ge> 0"
  shows "I \<le> a * f a"
proof -
  have feq: "(f ` {0..a}) = {f 0..f a}"
    using IVT' f_mono
    by (smt (z3) f_cont \<open>a \<ge> 0\<close> atLeastAtMost_iff atLeastatMost_subset_iff continuous_image_closed_interval image_subset_iff strict_mono_on_leD)
  have "continuous_on {f 0..f a} g"
    using continuous_on_inv [where f=f, OF _ _ g]
    by (metis feq f_cont compact_Icc) 
  then have g_int: "g integrable_on {f 0..f a}"
    using integrable_continuous_real by blast 
  have "((\<lambda>x. f a) has_integral a * f a) {0..a}"
    using has_integral_const_real [of "f a" 0 a] \<open>a \<ge> 0\<close>
    by simp
  then show ?thesis
    using has_integral_le [OF f]
qed
  oops

declare [[show_consts=true]]


lemma poly_dvd_tendsto_0_at_top_pos_coeff: 
  fixes p q :: "real poly"
  assumes "degree p > degree q" "coeff p (degree p) > 0"
  shows "((\<lambda>x. poly q x / poly p x) ---> 0 ) at_top" using assms
proof (induct "degree q" arbitrary: q p)
  case 0 
  then obtain c where "\<forall>x. poly q x=c" 
    by (metis smult_eq_0_iff synthetic_div_correct synthetic_div_eq_0_iff synthetic_div_unique)
  hence "eventually (\<lambda>x. poly q x = c) at_top" 
    using Topological_Spaces.always_eventually[of "\<lambda>x. poly q x=c" at_top]
    by simp
  hence "(poly q ---> c) at_top" by (metis `\<forall>x. poly q x = c` ext tendsto_const)
  moreover have "filterlim (poly p) at_infinity at_top" 
    using poly_inf_at_top[of p] `0 = degree q` `degree q < degree p` by auto
  ultimately show ?case using Limits.tendsto_divide_0[of "poly q" _ at_top "poly p" ] by auto 
next
  case (Suc n) print_facts
  have "filterlim (poly p) at_top at_top" 
    using poly_at_top_at_top[of p] Suc by auto
  moreover have "eventually (\<lambda>x. poly (pderiv p) x \<noteq> 0) at_top" 
    apply (rule filter_leD,rule Limits.at_top_le_at_infinity, rule poly_neq_0_at_infinity)
    by (metis Suc.prems(1) less_nat_zero_code pderiv_eq_0_iff)
  moreover have "eventually (\<lambda>x. DERIV (poly q) x :> poly (pderiv q) x) at_top" 
    by (metis (mono_tags) always_eventually poly_DERIV)
  moreover have " eventually (\<lambda>x. DERIV (poly p) x :> poly (pderiv p) x) at_top" 
    by (metis (lifting) always_eventually poly_DERIV)
  moreover have "((\<lambda>x. poly (pderiv q) x / poly (pderiv p) x) ---> 0) at_top" 
    proof -
      have "n = degree (pderiv q)" 
        using degree_pderiv[of q] `Suc n = degree q` by auto
      moreover have "0 < coeff (pderiv p) (degree (pderiv p))"  
        proof -
          have "degree p>0" using Suc by auto
          hence "Suc (degree (pderiv p))=degree p" using degree_pderiv[of p] by auto
          thus ?thesis 
            using Poly_Deriv.coeff_pderiv[of p "degree (pderiv p)"] ` 0 < coeff p (degree p)`
            by (metis `0 < degree p` mult_pos_pos of_nat_0_less_iff)
        qed
      moreover  have "degree (pderiv q) < degree (pderiv p)" 
        using Suc 
        by (metis (hide_lams, no_types) Nat.add_0_right One_nat_def add_Suc_right calculation 
          degree_pderiv less_diff_conv)
      ultimately show ?thesis using Suc(1)[of "pderiv q" "pderiv p"] by auto
    qed
  ultimately show ?case
    using lhospital_at_top_at_top[of "poly p" "poly (pderiv p)" "poly q" "poly (pderiv q)" 0] 
    by auto
qed

lemma poly_dvd_tendsto_0_at_top_neg_coeff: 
  fixes p q :: "real poly"
  assumes "degree p > degree q" "coeff p (degree p) < 0"
  shows "((\<lambda>x. poly q x / poly p x) ---> 0 ) at_top" using assms
proof -
  have "((\<lambda>x. poly q x / poly (- p) x) ---> 0 ) at_top"
    using poly_dvd_tendsto_0_at_top_pos_coeff[of q "-p"] 
    by (metis assms(1) assms(2) coeff_minus degree_minus neg_0_less_iff_less)  
  moreover have "(\<lambda>x. poly q x / poly (- p) x)=   (\<lambda>x. - poly q x / poly ( p) x)" by auto
  ultimately have "((\<lambda>x.- poly q x / poly ( p) x) ---> 0 ) at_top" 
    using Polynomial.poly_minus[of p] by auto
  thus ?thesis 
    using Limits.tendsto_minus_cancel_left[of "(\<lambda>x. poly q x / poly p x)" 0 at_top] by auto
qed

lemma poly_dvd_tendsto_0_at_top: 
  fixes p q :: "real poly"
  assumes "degree p > degree q"
  shows "((\<lambda>x. poly q x / poly p x) ---> 0 ) at_top" 
proof -
  have "coeff p (degree p) > 0 \<Longrightarrow> ?thesis" 
    by (metis (full_types) assms poly_dvd_tendsto_0_at_top_pos_coeff)
  moreover have "coeff p (degree p) = 0 \<Longrightarrow> ?thesis" 
    by (metis assms degree_0 leading_coeff_0_iff less_nat_zero_code)
  moreover have "coeff p (degree p) < 0 \<Longrightarrow> ?thesis" 
    by (metis (full_types) assms poly_dvd_tendsto_0_at_top_neg_coeff)
  ultimately show ?thesis by (metis linorder_neqE_linordered_idom)
qed

end
