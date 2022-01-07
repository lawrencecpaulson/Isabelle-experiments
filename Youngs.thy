section \<open>Misc experiments\<close>

theory Youngs imports
  "HOL-Library.Sum_of_Squares" "HOL-Analysis.Analysis" "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
  "HOL-ex.Sketch_and_Explore"
   
begin


lemma
  fixes f :: "real \<Rightarrow> real"
  assumes contf: "continuous_on {0..1} f" and intf: "(f has_integral 0) {0..1}"
    and f_ge0: "\<And>x. x \<in> {0..1} \<Longrightarrow> f x \<ge> 0"
  shows "\<forall>x \<in> {0..1}. f x = 0"
proof (rule ccontr)
  assume "\<not> (\<forall>x\<in>{0..1}. f x = 0)"
  then obtain a where a: "a \<in> {0..1}" "f a > 0"
    using assms by force
  then obtain \<delta> where "\<delta> > 0" and \<delta>: "\<And>x. x \<in> {0..1} \<Longrightarrow> abs (a - x) < \<delta> \<Longrightarrow> abs (f a - f x) < f a / 2"
    using contf unfolding continuous_on_real_range
    by (metis abs_minus_commute half_gt_zero_iff real_norm_def)
  define l where "l \<equiv> max 0 (a-\<delta>)"
  define u where "u \<equiv> min 1 (a+\<delta>)"
  have [simp]: "max 0 l = l" "min 1 u = u" "min l u = l" "max u l = u" 
               "{0..l} \<union> {u..1} \<union> {l..u} = {0..1}"
    using a \<open>\<delta> > 0\<close> by (auto simp add: l_def u_def)
  have "l < u"
    using \<open>0 < \<delta>\<close> a(1) l_def u_def by auto
  define I where "I \<equiv> (u-l) * f a / 2"
  have "I > 0"
    by (simp add: I_def \<open>l < u\<close> a(2))
  define g where "g \<equiv> \<lambda>x. if x \<in> {0..l} \<union> {u..1} then 0 else f a / 2"
  have g_le_f: "g x \<le> f x" if "x \<in> {0..1}" for x
    using that \<delta>  by (simp add: l_def u_def g_def f_ge0) (smt (verit, best))
  have "(g has_integral 0) ({0..l} \<union> {u..1})"
    by (meson g_def has_integral_is_0)
  moreover  have "((\<lambda>x. f a / 2) has_integral I) {l..u}"
    unfolding I_def g_def
    using has_integral_const_real [of "f a / 2" l u] using \<open>l < u\<close> by force
  then have "(g has_integral I) {l..u}"
    using has_integral_spike_interior_eq [of l u "\<lambda>x. f a / 2" g I]
    by (simp add: g_def)
  ultimately have "(g has_integral I) {0..1}"
    using has_integral_Un [of g 0 "{0..l} \<union> {u..1}" _ "{l..u}"]
    by (simp add: Int_Un_distrib2)
  with g_le_f has_integral_le intf have "I \<le> 0"
    by blast
  with \<open>0 < I\<close> show False by fastforce
qed

subsection \<open>Possible library additions\<close>

lemma mono_on_compose: "mono_on f (g ` S) \<Longrightarrow> mono_on g S \<Longrightarrow> mono_on (f \<circ> g) S"
  by (simp add: mono_on_def)



thm of_int_less_iff
context linordered_idom
begin

lemma of_nat_nat_eq_iff: "of_nat (nat i) = of_int i \<longleftrightarrow> 0 \<le> i"
  using local.of_int_le_iff by fastforce

end



  lemma fact_eq_fact_times:
    assumes "m \<ge> n"
    shows "fact m = fact n * \<Prod>{Suc n..m}"
    unfolding fact_prod
    by (metis add.commute assms le_add1 le_add_diff_inverse of_nat_id plus_1_eq_Suc prod.ub_add_nat)
  
  (*REPLACE THE UGLY ORIGINAL*)
  lemma fact_div_fact:
    assumes "m \<ge> n"
    shows "fact m div fact n = \<Prod>{n + 1..m}"
    by (simp add: fact_eq_fact_times [OF assms])

  lemma deriv_sum [simp]:
    "\<lbrakk>\<And>i. f i field_differentiable at z\<rbrakk>
     \<Longrightarrow> deriv (\<lambda>w. sum (\<lambda>i. f i w) S) z = sum (\<lambda>i. deriv (f i) z) S"
    unfolding DERIV_deriv_iff_field_differentiable[symmetric]
    by (auto intro!: DERIV_imp_deriv derivative_intros)
  
  lemma deriv_pow: "\<lbrakk>f field_differentiable at z\<rbrakk>
     \<Longrightarrow> deriv (\<lambda>w. f w ^ n) z = (if n=0 then 0 else n * deriv f z * f z ^ (n - Suc 0))"
    unfolding DERIV_deriv_iff_field_differentiable[symmetric]
    by (auto intro!: DERIV_imp_deriv derivative_eq_intros)
  
  lemma deriv_minus [simp]:
    "f field_differentiable at z \<Longrightarrow> deriv (\<lambda>w. - f w) z = - deriv f z"
    by (simp add: DERIV_deriv_iff_field_differentiable DERIV_imp_deriv Deriv.field_differentiable_minus)

text \<open>Kevin Buzzard's example\<close>
lemma
  fixes x::real
  shows "(x+y)*(x+2*y)*(x+3*y) = x^3 + 6*x^2*y + 11*x*y^2 + 6*y^3"
  by (simp add: algebra_simps eval_nat_numeral)

subsection \<open>Experiments involving Young's Inequality\<close>
  
  lemma integrable_mono_on_nonneg:
    fixes f :: "real \<Rightarrow> real"
    assumes mon: "mono_on f {a..b}" and 0: "\<And>x. 0 \<le> f x"
    shows "integrable (lebesgue_on {a..b}) f" 
  proof -
    have "space lborel = space lebesgue" "sets borel \<subseteq> sets lebesgue"
      by force+
    then have fborel: "f \<in> borel_measurable (lebesgue_on {a..b})"
      by (metis mon borel_measurable_mono_on_fnc borel_measurable_subalgebra mono_restrict_space space_lborel space_restrict_space)
    then obtain g where g: "incseq g" and simple: "\<And>i. simple_function (lebesgue_on {a..b}) (g i)" 
                  and bdd: " (\<forall>x. bdd_above (range (\<lambda>i. g i x)))" and nonneg: "\<forall>i x. 0 \<le> g i x"
                  and fsup: "f = (SUP i. g i)"
      by (metis borel_measurable_implies_simple_function_sequence_real 0)
    have "f ` {a..b} \<subseteq> {f a..f b}" 
      using assms by (auto simp: mono_on_def)
    have g_le_f: "g i x \<le> f x" for i x
    proof -
      have "bdd_above ((\<lambda>h. h x) ` range g)"
        using bdd cSUP_lessD linorder_not_less by fastforce
      then show ?thesis
        by (metis SUP_apply UNIV_I bdd cSUP_upper fsup)
    qed
    then have gfb: "g i x \<le> f b" if "x \<in> {a..b}" for i x
      by (smt (verit, best) mon atLeastAtMost_iff mono_on_def that)
    have g_le: "g i x \<le> g j x" if "i\<le>j"  for i j x
      using g by (simp add: incseq_def le_funD that)
    show "integrable (lebesgue_on {a..b}) ( f)"
    proof (rule integrable_dominated_convergence)
      show "f \<in> borel_measurable (lebesgue_on {a..b})"
        using fborel by blast
      have "\<And>x. (\<lambda>i. g i x) \<longlonglongrightarrow> (SUP h \<in> range g. h  x)"
      proof (rule order_tendstoI)
        show "\<forall>\<^sub>F i in sequentially. y < g i x"
          if "y < (SUP h\<in>range g. h x)" for x y
        proof -
          from that obtain h where h: "h \<in> range g" "y < h x"
            using g_le_f by (subst (asm)less_cSUP_iff) fastforce+
          then show ?thesis
            by (smt (verit, ccfv_SIG) eventually_sequentially g_le imageE)
        qed
        show "\<forall>\<^sub>F i in sequentially. g i x < y"
          if "(SUP h\<in>range g. h x) < y" for x y
          by (smt (verit, best) that Sup_apply g_le_f always_eventually fsup image_cong)
      qed
      then show "AE x in lebesgue_on {a..b}. (\<lambda>i. g i x) \<longlonglongrightarrow> f x"
        by (simp add: fsup)
      fix i
      show "g i \<in> borel_measurable (lebesgue_on {a..b})"
        using borel_measurable_simple_function simple by blast
      show "AE x in lebesgue_on {a..b}. norm (g i x) \<le> f b"
        by (simp add: gfb nonneg Measure_Space.AE_I' [of "{}"])
    qed auto
  qed
  
  lemma integrable_mono_on:
    fixes f :: "real \<Rightarrow> real"
    assumes "mono_on f {a..b}" 
    shows "integrable (lebesgue_on {a..b}) f" 
  proof -
    define f' where "f' \<equiv> \<lambda>x. if x \<in> {a..b} then f x - f a else 0"
    have "mono_on f' {a..b}"
      by (smt (verit, best) assms f'_def mono_on_def)
    moreover have 0: "\<And>x. 0 \<le> f' x"
      by (smt (verit, best) assms atLeastAtMost_iff f'_def mono_on_def)
    ultimately have "integrable (lebesgue_on {a..b}) f'"
      using integrable_mono_on_nonneg by presburger
    then have "integrable (lebesgue_on {a..b}) (\<lambda>x. f' x + f a)"
      by force
    moreover have "space lborel = space lebesgue" "sets borel \<subseteq> sets lebesgue"
      by force+
    then have fborel: "f \<in> borel_measurable (lebesgue_on {a..b})"
      by (metis assms borel_measurable_mono_on_fnc borel_measurable_subalgebra mono_restrict_space space_lborel space_restrict_space)
    ultimately show ?thesis
      by (rule integrable_cong_AE_imp) (auto simp add: f'_def)
  qed
  
  lemma integrable_on_mono_on:
    fixes f :: "real \<Rightarrow> real"
    assumes "mono_on f {a..b}" 
    shows "f integrable_on {a..b}"
    by (simp add: assms integrable_mono_on integrable_on_lebesgue_on) 

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

subsection \<open>Regular divisions\<close>

definition "segment \<equiv> \<lambda>n k. {real k / real n..(1 + k) / real n}"

lemma segment_nonempty: "segment n k \<noteq> {}"
  by (auto simp: segment_def divide_simps)

lemma segment_Suc: "segment n ` {..<Suc k} = insert {k/n..(1 + real k) / n} (segment n ` {..<k})"
  by (simp add: segment_def lessThan_Suc)

lemma Union_segment_image: "\<Union> (segment n ` {..<k}) = (if k=0 then {} else {0..real k/real n})"
proof (induction k)
  case (Suc k)
  then show ?case
    by (simp add: divide_simps segment_Suc Un_commute ivl_disj_un_two_touch split: if_split_asm)
qed (auto simp: segment_def)

definition "segments \<equiv> \<lambda>n. segment n ` {..<n}"

lemma segments_0 [simp]: "segments 0 = {}"
  by (simp add: segments_def)

lemma Union_segments: "\<Union> (segments n) = (if n=0 then {} else {0..1})"
  by (simp add: segments_def Union_segment_image)

definition "regular_division \<equiv> \<lambda>a b n. image (image ((+) a \<circ> (*) (b-a))) (segments n)"

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
  have eq: "(\<lambda>x. a + (b - a) * x) = (\<lambda>x. a + x) \<circ> (\<lambda>x. (b - a) * x)"
    by (simp add: o_def)
  obtain k where "K = ((\<lambda>x. a + x) \<circ> (\<lambda>x. (b - a) * x)) ` {real k / real n .. (1 + real k) / real n}"
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
    using K \<open>a<b\<close> regular_divisionE by meson
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
  assumes sm: "strict_mono_on f {0..}" and cont: "continuous_on {0..} f" and "0 \<le> a" "0 \<le> b" "f 0 = 0" "f a = b"
  shows "a*b = integral {0..a} f + integral {0..b} (inv_into {0..a} f)"
proof (cases "a=0")
  case False
  then have "a > 0"
    using assms(3) by linarith
  have cont_0a: "continuous_on {0..a} f"
    using cont continuous_on_subset by fastforce
  with sm have "continuous_on {0..b} (inv_into {0..a} f)"
    apply (simp add: strict_mono_on_def)
    by (metis \<open>0 \<le> a\<close> \<open>f 0 = 0\<close> \<open>f a = b\<close> atLeastAtMost_iff strict_mono_continuous_inv strict_mono_onI)
  have "uniformly_continuous_on {0..a} f"
    using compact_uniformly_continuous cont_0a by blast
  then
  obtain del where del_gt0: "\<And>e. e>0 \<Longrightarrow> del e > 0" 
                   and del:  "\<And>e x x'. \<lbrakk>dist x' x < del e; e>0; x \<in> {0..a}; x' \<in> {0..a}\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
    unfolding uniformly_continuous_on_def by metis

  obtain S where S: "(f has_integral S) {0..a}"
    using \<open>continuous_on {0..a} f\<close> integrable_continuous_real by blast
  { fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    with \<open>a > 0\<close> have gt0: "\<epsilon>/(2*a) > 0"
      by simp
    define \<delta> where "\<delta> = min a (del (\<epsilon>/(2*a)))"
    define n where "n \<equiv> ceiling (a/\<delta>)"
    have "\<delta> \<le> a"
      by (simp add: \<delta>_def)
    then have "real_of_int \<lceil>a/\<delta>\<rceil> \<le> 2 * a / \<delta>"
      using of_int_ceiling_le_add_one [of "a/\<delta>"]
      by (smt (verit, best) False \<delta>_def add_divide_distrib del_gt0 divide_le_eq_1_pos divide_self_if gt0)
    moreover have "2 * a * (\<epsilon> / (2 * a)) \<le> \<epsilon>"
      using \<open>0 < a\<close> by auto
    ultimately have "n * \<delta> * (\<epsilon>/(2*a)) \<le> \<epsilon>"
      unfolding n_def
      by (smt (verit) \<delta>_def \<open>0 < a\<close> del_gt0 gt0 pos_le_divide_eq) 

    define f_lwr where "f_lwr \<equiv> \<lambda>x. f (floor (n*x/a) * a/n)"

    define n where "n \<equiv> ceiling (a / del (\<epsilon>/a))"
    define \<delta> where "\<delta> = a/n"
    have "n > 0"
      by (simp add: \<open>0 < a\<close> \<open>0 < \<epsilon>\<close> del_gt0 n_def)
    have "n * \<delta> * (\<epsilon>/a) \<le> \<epsilon>"
      using \<delta>_def \<open>0 < \<epsilon>\<close> n_def by force
 

    define lower where "lower \<equiv> \<lambda>x. \<lfloor>(of_int n * x) / a\<rfloor> * a/n"
    define f1 where "f1 \<equiv> f o lower"
    have mo_lower: "mono_on lower {0..a}"
      using \<open>0 < n\<close> unfolding lower_def mono_on_def
      by (auto simp: divide_right_mono floor_mono mult.commute mult_left_mono order_less_imp_le)
    have lower_im: "lower ` {0..a} \<subseteq> {0..}"
      using \<open>0 < n\<close> by (auto simp: lower_def)
    have f1_lower: "f1 x \<le> f x" if "0 \<le> x" "x \<le> a" for x
    proof -
      have "lower x \<le> x"
        unfolding lower_def using \<open>n > 0\<close> \<open>a > 0\<close> 
        by (metis floor_divide_lower divide_le_eq mult_of_int_commute of_int_0_less_iff)
      moreover have "lower x \<ge> 0"
        unfolding lower_def using \<open>0 < n\<close> \<open>0 \<le> a\<close> \<open>0 \<le> x\<close> by force
      ultimately show ?thesis
        using sm strict_mono_on_leD by (fastforce simp add: f1_def)
    qed
    define upper where "upper \<equiv> \<lambda>x. ceiling((of_int n * x) / a)* a/n"
    define f2 where "f2 \<equiv> f o upper"

    have mo_upper: "mono_on upper {0..a}"
      using \<open>0 < n\<close> unfolding upper_def mono_on_def
      by (simp add: ceiling_mono divide_right_mono mult_right_mono)
    have upper_im: "upper ` {0..a} \<subseteq> {0..}"
      using \<open>0 < n\<close>
      apply (clarsimp simp: upper_def field_split_simps)
      by (smt (verit, best) mult_nonneg_nonneg of_int_pos)

    have f2_upper: "f2 x \<ge> f x" if "0 \<le> x" "x \<le> a" for x
    proof -
      have "x \<le> upper x"
        using \<open>n > 0\<close> ceiling_divide_upper [OF \<open>a > 0\<close>] by (simp add: upper_def field_simps)
      then show ?thesis
        using sm strict_mono_on_leD \<open>0 \<le> x\<close> by (force simp add: f2_def)
    qed
    let ?\<D> = "regular_division 0 a (nat n)"
    have div: "?\<D> division_of {0..a}"
      using \<open>0 < a\<close> \<open>0 < n\<close> regular_division_division_of zero_less_nat_eq by presburger

    have f1: "(f1 has_integral (\<Sum>i\<in>?\<D>. integral i f1)) {0..a}"
    proof (rule has_integral_combine_division_topdown)
      have "mono_on f (lower ` {0..a})"
        by (meson lower_im mono_on_subset sm strict_mono_on_imp_mono_on)
      then show "f1 integrable_on {0..a}"
        unfolding f1_def by (intro integrable_on_mono_on mono_on_compose mo_lower)
    qed (use div in auto)

    have f2: "(f2 has_integral (\<Sum>i\<in>?\<D>. integral i f2)) {0..a}"
    proof (rule has_integral_combine_division_topdown)
      have "mono_on f (upper ` {0..a})"
        by (meson upper_im mono_on_subset sm strict_mono_on_imp_mono_on)
      then show "f2 integrable_on {0..a}"
        unfolding f2_def by (intro integrable_on_mono_on mono_on_compose mo_upper)
    qed (use div in auto)


    have "integral i f1 = f i * (\<epsilon>/(2*a))" if "i\<in>?\<D>" for i
    sorry
  }
  show ?thesis
    sorry
qed (use assms in force)


lemma D:
  fixes f :: "real \<Rightarrow> real"
  assumes *: "strict_mono_on f {0..a}"  "continuous_on {0..a} f"  "0 \<le> a" "0 \<le> b"
  shows "a*b \<le> integral {0..a} f + integral {0..b} (inv_into {0..a} f)"
  sorry

  obtains f1 f2 where "\<And>x. x \<in> {0..a} \<Longrightarrow> f1 x \<le> f x \<and> f x \<le> f2 x"
  using strict_mono_image_endpoints assms(1) assms(2) assms(3) compact_Icc continuous_on_inv 


lemma D:
  fixes f :: "real \<Rightarrow> real"
  assumes *: "strict_mono_on f {0..a}"  "continuous_on {0..a} f"  "0 \<le> a"
  obtains f1 f2 where "\<And>x. x \<in> {0..a} \<Longrightarrow> f1 x \<le> f x \<and> f x \<le> f2 x"
  using strict_mono_image_endpoints assms(1) assms(2) assms(3) compact_Icc continuous_on_inv 





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
