section \<open>Misc experiments\<close>

theory Youngs imports
  "HOL-Analysis.Analysis" 
  "HOL-ex.Sketch_and_Explore"
   
begin

text \<open>Kevin Buzzard's examples\<close>
lemma
  fixes x::real
  shows "(x+y)*(x+2*y)*(x+3*y) = x^3 + 6*x^2*y + 11*x*y^2 + 6*y^3"
  by (simp add: algebra_simps eval_nat_numeral)

lemma "sqrt 2 + sqrt 3 < sqrt 10"
proof -
  have "(sqrt 2 + sqrt 3)^2 < (sqrt 10)^2"
  proof (simp add: algebra_simps eval_nat_numeral)
    have "(2 * (sqrt 2 * sqrt 3))^2 < 5 ^ 2"
      by (simp add: algebra_simps eval_nat_numeral)
    then show "2 * (sqrt 2 * sqrt 3) < 5"
      by (smt (verit, best) power_mono)
  qed
  then show ?thesis
    by (simp add: real_less_rsqrt)
qed

  
  thm has_integral_Union
  lemma has_integral_UN:
    fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
    assumes "finite I"
      and int: "\<And>i. i \<in> I \<Longrightarrow> (f has_integral (g i)) (\<T> i)"
      and neg: "pairwise (\<lambda>i i'. negligible (\<T> i \<inter> \<T> i')) I"
    shows "(f has_integral (sum g I)) (\<Union>i\<in>I. \<T> i)"
  proof -
    let ?\<U> = "((\<lambda>(a,b). \<T> a \<inter> \<T> b) ` {(a,b). a \<in> I \<and> b \<in> I-{a}})"
    have "((\<lambda>x. if x \<in> (\<Union>i\<in>I. \<T> i) then f x else 0) has_integral sum g I) UNIV"
    proof (rule has_integral_spike)
      show "negligible (\<Union>?\<U>)"
      proof (rule negligible_Union)
        have "finite (I \<times> I)"
          by (simp add: \<open>finite I\<close>)
        moreover have "{(a,b). a \<in> I \<and> b \<in> I-{a}} \<subseteq> I \<times> I"
          by auto
        ultimately show "finite ?\<U>"
          by (simp add: finite_subset)
        show "\<And>t. t \<in> ?\<U> \<Longrightarrow> negligible t"
          using neg unfolding pairwise_def by auto
      qed
    next
      show "(if x \<in> (\<Union>i\<in>I. \<T> i) then f x else 0) = (\<Sum>i\<in>I. if x \<in> \<T> i then f x else 0)"
        if "x \<in> UNIV - (\<Union>?\<U>)" for x
      proof clarsimp
        fix i assume i: "i \<in> I" "x \<in> \<T> i"
        then have "\<forall>j\<in>I. x \<in> \<T> j \<longleftrightarrow> j = i"
          using that by blast
        with i show "f x = (\<Sum>i\<in>I. if x \<in> \<T> i then f x else 0)"
          by (simp add: sum.delta[OF \<open>finite I\<close>])
      qed
    next
      show "((\<lambda>x. (\<Sum>i\<in>I. if x \<in> \<T> i then f x else 0)) has_integral sum g I) UNIV"
        using int by (simp add: has_integral_restrict_UNIV has_integral_sum [OF \<open>finite I\<close>])
    qed
    then show ?thesis
      using has_integral_restrict_UNIV by blast
  qed
  
  lemma has_integral_Union:
    fixes f :: "'n::euclidean_space \<Rightarrow> 'a::banach"
    assumes "finite \<T>"
      and "\<And>S. S \<in> \<T> \<Longrightarrow> (f has_integral (i S)) S"
      and "pairwise (\<lambda>S S'. negligible (S \<inter> S')) \<T>"
    shows "(f has_integral (sum i \<T>)) (\<Union>\<T>)"
  proof -
    have "(f has_integral (sum i \<T>)) (\<Union>S\<in>\<T>. S)"
      by (intro has_integral_UN assms)
    then show ?thesis
      by force
  qed

  corollary integral_cbox_eq_0_iff:
    fixes f :: "'a::euclidean_space \<Rightarrow> real"
    assumes "continuous_on (cbox a b) f" and "box a b \<noteq> {}"
      and "\<And>x. x \<in> (cbox a b) \<Longrightarrow> f x \<ge> 0"
    shows "integral (cbox a b) f = 0 \<longleftrightarrow> (\<forall>x \<in> (cbox a b). f x = 0)" (is "?lhs = ?rhs")
  proof
    assume int0: ?lhs
    show ?rhs
      using has_integral_0_cbox_imp_0 [of a b f] assms
      by (metis box_subset_cbox eq_integralD int0 integrable_continuous subsetD) 
  next
    assume ?rhs then show ?lhs
      by (meson has_integral_is_0_cbox integral_unique)
  qed
  
  lemma integral_eq_0_iff:
    fixes f :: "real \<Rightarrow> real"
    assumes contf: "continuous_on {a..b} f" and "a < b"
      and f_ge0: "\<And>x. x \<in> {a..b} \<Longrightarrow> f x \<ge> 0"
    shows "integral {a..b} f = 0 \<longleftrightarrow> (\<forall>x \<in> {a..b}. f x = 0)"
    using integral_cbox_eq_0_iff [of a b f] assms by simp
  
  lemma integralL_eq_0_iff:
    fixes f :: "real \<Rightarrow> real"
    assumes contf: "continuous_on {a..b} f" and "a < b"
      and "\<And>x. x \<in> {a..b} \<Longrightarrow> f x \<ge> 0"
    shows "integral\<^sup>L (lebesgue_on {a..b}) f = 0 \<longleftrightarrow> (\<forall>x \<in> {a..b}. f x = 0)" 
    using integral_eq_0_iff [OF assms]
    by (simp add: contf continuous_imp_integrable_real lebesgue_integral_eq_integral)

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

lemma card_segments [simp]: "card (segments n) = n"
  by (simp add: segments_def segment_def card_image divide_right_mono inj_on_def)

lemma segments_0 [simp]: "segments 0 = {}"
  by (simp add: segments_def)

lemma Union_segments: "\<Union> (segments n) = (if n=0 then {} else {0..1})"
  by (simp add: segments_def Union_segment_image)

definition "regular_division \<equiv> \<lambda>a b n. image (image ((+) a \<circ> (*) (b-a))) (segments n)"

lemma translate_scale_01:
  assumes "a \<le> b" 
  shows "(\<lambda>x. a + (b - a) * x) ` {0..1} = {a..b::real}"
  using closed_segment_real_eq [of a b] assms closed_segment_eq_real_ivl by auto

lemma finite_regular_division [simp]: "finite (regular_division a b n)"
  by (simp add: regular_division_def segments_def)

lemma card_regular_division [simp]: 
  assumes "a<b"
  shows "card (regular_division a b n) = n"
proof -
  have "inj_on ((`) ((+) a \<circ> (*) (b - a))) (segments n)"
  proof
    fix x y
    assume "((+) a \<circ> (*) (b - a)) ` x = ((+) a \<circ> (*) (b - a)) ` y"
    then have "(+) (-a) ` ((+) a \<circ> (*) (b - a)) ` x = (+) (-a) ` ((+) a \<circ> (*) (b - a)) ` y"
      by simp
    then have "((*) (b - a)) ` x = ((*) (b - a)) ` y"
      by (simp add: image_comp)
    then have "(*) (inverse(b - a)) ` (*) (b - a) ` x = (*) (inverse(b - a)) ` (*) (b - a) ` y"
      by simp
    then show "x = y"
      using assms by (simp add: image_comp mult_ac)
  qed
  then show ?thesis
    by (metis card_image card_segments regular_division_def)
qed

lemma Union_regular_division:
  assumes "a \<le> b" 
  shows "\<Union>(regular_division a b n) = (if n=0 then {} else {a..b})"
  using assms
  by (auto simp add: regular_division_def Union_segments translate_scale_01 simp flip: image_Union)


lemma regular_division_eqI:
  assumes K: "K = {a + (b-a)*(real k / n) .. a + (b-a)*((1 + real k) / n)}"
    and "a<b" "k < n"
  shows "K \<in> regular_division a b n" 
  unfolding regular_division_def segments_def image_comp
proof
  have "K = (\<lambda>x. (b-a) * x + a) ` {real k / real n..(1 + real k) / real n}"
    using K \<open>a<b\<close> by (simp add: image_affinity_atLeastAtMost divide_simps)
  then show "K = ((`) ((+) a \<circ> (*) (b - a)) \<circ> segment n) k" 
    by (simp add: segment_def add.commute)
qed (use assms in auto)

lemma regular_divisionE:
  assumes "K \<in> regular_division a b n" "a<b"
  obtains k where "k<n" "K = {a + (b-a)*(real k / n) .. a + (b-a)*((1 + real k) / n)}"
proof -
  have eq: "(\<lambda>x. a + (b - a) * x) = (\<lambda>x. a + x) \<circ> (\<lambda>x. (b - a) * x)"
    by (simp add: o_def)
  obtain k where "k<n" "K = ((\<lambda>x. a + x) \<circ> (\<lambda>x. (b - a) * x)) ` {real k / real n .. (1 + real k) / real n}"
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
    using \<open>a<b\<close> regular_divisionE by meson
  show "K \<subseteq> {a..b}"
    using K Union_regular_division \<open>n>0\<close> by (metis Union_upper \<section>)
  show "K \<noteq> {}"
    using K by (auto simp: regular_division_def segment_nonempty segments_def)
  show "\<exists>a b. K = cbox a b"
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

lemma weighted_nesting_sum:
  fixes g :: "nat \<Rightarrow> 'a::comm_ring_1"
  shows "(\<Sum>k<n. (1 + of_nat k) * (g (Suc k) - g k)) = of_nat n * g n - (\<Sum>i<n. g i)"
  by (induction n) (auto simp: algebra_simps)

theorem Young:
  fixes f :: "real \<Rightarrow> real"
  assumes sm: "strict_mono_on f {0..}" and cont: "continuous_on {0..} f" and a: "0 \<le> a" "0 \<le> b" 
    and f[simp]: "f 0 = 0" "f a = b"
  shows "a*b = integral {0..a} f + integral {0..b} (inv_into {0..a} f)" (is "_ = _ + integral {0..b} ?g")
proof (cases "a=0")
  case False
  with \<open>0 \<le> a\<close> have "a > 0" by linarith
  have cont_0a: "continuous_on {0..a} f"
    using cont continuous_on_subset by fastforce
  with sm have "continuous_on {0..b} ?g"
    apply (simp add: strict_mono_on_def)
    by (metis \<open>0 \<le> a\<close> \<open>f 0 = 0\<close> \<open>f a = b\<close> atLeastAtMost_iff strict_mono_continuous_inv strict_mono_onI)
  then have intgb_g: "?g integrable_on {0..b}"
    using integrable_continuous_interval by blast
  have intgb_f: "f integrable_on {0..a}"
    using cont_0a integrable_continuous_real by blast

  have f_iff [simp]: "f x < f y \<longleftrightarrow> x < y" "f x \<le> f y \<longleftrightarrow> x \<le> y"
    if "x \<ge> 0" "y \<ge> 0" for x y
    using that by (smt (verit, best) atLeast_iff sm strict_mono_onD)+
  have fim: "f ` {0..a} = {0..b}"
    by (simp add: \<open>0 \<le> a\<close> cont_0a strict_mono_image_endpoints strict_mono_on_def)
  have "uniformly_continuous_on {0..a} f"
    using compact_uniformly_continuous cont_0a by blast
  then obtain del where del_gt0: "\<And>e. e>0 \<Longrightarrow> del e > 0" 
                   and del:  "\<And>e x x'. \<lbrakk>\<bar>x' - x\<bar> < del e; e>0; x \<in> {0..a}; x' \<in> {0..a}\<rbrakk> \<Longrightarrow> \<bar>f x' - f x\<bar> < e"
    unfolding uniformly_continuous_on_def dist_real_def by metis

  have *: "\<bar>a * b - integral {0..a} f - integral {0..b} (inv_into {0..a} f)\<bar> < 2*\<epsilon>" if "\<epsilon> > 0" for \<epsilon>
  proof -
    define \<delta> where "\<delta> = min a (del (\<epsilon>/a)) / 2"
    have "\<delta> > 0" "\<delta> \<le> a"
      using \<open>a > 0\<close> \<open>\<epsilon> > 0\<close> del_gt0 by (auto simp add: \<delta>_def)

    define n where "n \<equiv> nat\<lfloor>a / \<delta>\<rfloor>"
    define a_seg where "a_seg \<equiv> \<lambda>u::real. u * a/n"
    have "n > 0"
      using  \<open>a > 0\<close> \<open>\<delta> > 0\<close> \<open>\<delta> \<le> a\<close> by (simp add: n_def)
    have a_seg_ge_0 [simp]: "a_seg x \<ge> 0 \<longleftrightarrow> x \<ge> 0" and a_seg_le_a [simp]: "a_seg x \<le> a \<longleftrightarrow> x \<le> n" for x
      using \<open>n > 0\<close> \<open>a > 0\<close> by (auto simp: a_seg_def zero_le_mult_iff divide_simps)
    have a_seg_le_iff [simp]: "a_seg x \<le> a_seg y \<longleftrightarrow> x \<le> y" 
      and a_seg_less_iff [simp]: "a_seg x < a_seg y \<longleftrightarrow> x < y" for x y
      using \<open>n > 0\<close> \<open>a > 0\<close> by (auto simp: a_seg_def zero_le_mult_iff divide_simps)
    have "strict_mono a_seg"
      by (simp add: strict_mono_def)
    have a_seg_eq_a_iff: "a_seg x = a \<longleftrightarrow> x=n" for x
      using \<open>0 < n\<close> \<open>a > 0\<close> by (simp add: a_seg_def nonzero_divide_eq_eq)
    have fa_eq_b: "f (a_seg n) = b"
      using a_seg_eq_a_iff f by fastforce

    have "a/d < real_of_int \<lfloor>a * 2 / min a d\<rfloor>" if "d>0" for d
      by (smt (verit, best) \<open>0 < \<delta>\<close> \<open>\<delta> \<le> a\<close> add_divide_distrib divide_less_eq_1_pos floor_eq_iff that)
    then have an_less_del: "a/n < del (\<epsilon>/a)"
      using \<open>a > 0\<close> \<open>\<epsilon> > 0\<close> del_gt0  by (simp add: n_def \<delta>_def field_simps)

    define lower where "lower \<equiv> \<lambda>x. a_seg\<lfloor>(real n * x) / a\<rfloor>"
    define f1 where "f1 \<equiv> f \<circ> lower"
    have f1_lower: "f1 x \<le> f x" if "0 \<le> x" "x \<le> a" for x
    proof -
      have "lower x \<le> x"
        using \<open>n > 0\<close> floor_divide_lower [OF \<open>a > 0\<close>] by (auto simp add: lower_def a_seg_def field_simps)
      moreover have "lower x \<ge> 0"
        unfolding lower_def using \<open>n > 0\<close> \<open>0 \<le> a\<close> \<open>0 \<le> x\<close> by force
      ultimately show ?thesis
        using sm strict_mono_on_leD by (fastforce simp add: f1_def)
    qed
    define upper where "upper \<equiv> \<lambda>x. a_seg\<lceil>real n * x / a\<rceil>"
    define f2 where "f2 \<equiv> f \<circ> upper"
    have f2_upper: "f2 x \<ge> f x" if "0 \<le> x" "x \<le> a" for x
    proof -
      have "x \<le> upper x"
        using \<open>n > 0\<close> ceiling_divide_upper [OF \<open>a > 0\<close>] by (simp add: upper_def a_seg_def field_simps)
      then show ?thesis
        using sm strict_mono_on_leD \<open>0 \<le> x\<close> by (force simp add: f2_def)
    qed
    let ?\<D> = "regular_division 0 a n"
    have div: "?\<D> division_of {0..a}"
      using \<open>a > 0\<close> \<open>n > 0\<close> regular_division_division_of zero_less_nat_eq by presburger

    have int_f1_D: "(f1 has_integral f(Inf K) * (a/n)) K" and int_f2_D: "(f2 has_integral f(Sup K) * (a/n)) K" 
            and less: "\<bar>f(Sup K) - f(Inf K)\<bar> < \<epsilon>/a"
      if "K\<in>?\<D>" for K
    proof -
      from regular_divisionE [OF that] \<open>a > 0\<close>
      obtain k where "k<n" and k: "K = {a_seg(real k)..a_seg(Suc k)}"
        by (auto simp add: a_seg_def mult.commute)
      define u where "u \<equiv> a_seg k"
      define v where "v \<equiv> a_seg (Suc k)"
      have "u < v" "0 \<le> u" "0 \<le> v" "u \<le> a" "v \<le> a" and Kuv: "K = {u..v}"
        using \<open>n > 0\<close> \<open>k < n\<close> \<open>a > 0\<close> by (auto simp: k u_def v_def divide_simps)
      have InfK: "Inf K = u" and SupK: "Sup K = v"
        using Kuv \<open>u < v\<close> apply force
        using \<open>n > 0\<close> \<open>a > 0\<close> by (auto simp: divide_right_mono k u_def v_def)
      have f1: "f1 x = f (Inf K)" if "x \<in> K - {v}" for x
      proof -
        have "x \<in> {u..<v}"
          using that Kuv atLeastLessThan_eq_atLeastAtMost_diff by blast
        then have "\<lfloor>real_of_int n * x / a\<rfloor> = int k"
          using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: field_simps u_def v_def a_seg_def floor_eq_iff)
        then show ?thesis
          by (simp add: InfK f1_def lower_def a_seg_def mult.commute u_def) 
      qed
      have "((\<lambda>x. f (Inf K)) has_integral (f (Inf K) * (a/n))) K"
        using has_integral_const_real [of "f (Inf K)" u v] 
              \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: Kuv field_simps a_seg_def u_def v_def)
      then show "(f1 has_integral (f (Inf K) * (a/n))) K"
        using has_integral_spike_finite_eq [of "{v}" K "\<lambda>x. f (Inf K)" f1] f1 by simp
      have f2: "f2 x = f (Sup K)" if "x \<in> K - {u}" for x
      proof -
        have "x \<in> {u<..v}"
          using that Kuv greaterThanAtMost_eq_atLeastAtMost_diff by blast 
        then have "\<lceil>x * real_of_int n / a\<rceil>  = 1 + int k"
          using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: field_simps u_def v_def a_seg_def ceiling_eq_iff)
        then show ?thesis 
          by (simp add: mult.commute f2_def upper_def a_seg_def SupK v_def)
      qed
      have "((\<lambda>x. f (Sup K)) has_integral (f (Sup K) * (a/n))) K"
        using  \<open>n > 0\<close> \<open>a > 0\<close> has_integral_const_real [of "f (Sup K)" u v]
        by (simp add: Kuv field_simps u_def v_def a_seg_def)
      then show "(f2 has_integral (f (Sup K) * (a/n))) K"
        using has_integral_spike_finite_eq [of "{u}" K "\<lambda>x. f (Sup K)" f2] f2 by simp
      have "\<bar>v - u\<bar> < del (\<epsilon>/a)"
        using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: v_def u_def a_seg_def field_simps an_less_del)
      then have "\<bar>f v - f u\<bar> < \<epsilon>/a"
        using \<open>\<epsilon> > 0\<close> \<open>a > 0\<close> \<open>0 \<le> u\<close> \<open>u \<le> a\<close> \<open>0 \<le> v\<close> \<open>v \<le> a\<close>
        by (intro del) auto
      then show "\<bar>f(Sup K) - f(Inf K)\<bar> < \<epsilon>/a"
        using InfK SupK by blast
    qed

    have int_21_D: "((\<lambda>x. f2 x - f1 x) has_integral (f(Sup K) - f(Inf K)) * (a/n)) K" if "K\<in>?\<D>" for K
      using that has_integral_diff [OF int_f2_D int_f1_D] by (simp add: algebra_simps)

    have D_ne: "?\<D> \<noteq> {}"
      by (metis \<open>0 < a\<close> \<open>n > 0\<close> card_gt_0_iff card_regular_division)
    have f12: "((\<lambda>x. f2 x - f1 x) has_integral (\<Sum>K\<in>?\<D>. (f(Sup K) - f(Inf K)) * (a/n))) {0..a}"
      by (intro div int_21_D has_integral_combine_division)
    moreover have "(\<Sum>K\<in>?\<D>. (f(Sup K) - f(Inf K)) * (a/n)) < \<epsilon>"
    proof -
      have "(\<Sum>K\<in>?\<D>. (f(Sup K) - f(Inf K)) * (a/n)) \<le> (\<Sum>K\<in>?\<D>. \<bar>f(Sup K) - f(Inf K)\<bar> * (a/n))"
        using \<open>n > 0\<close> \<open>a > 0\<close>
        by (smt (verit) divide_pos_pos of_nat_0_less_iff sum_mono zero_le_mult_iff)
      also have "... < (\<Sum>K\<in>?\<D>. \<epsilon>/n)"
        using \<open>n > 0\<close> \<open>a > 0\<close> less
        by (intro sum_strict_mono finite_regular_division D_ne) (simp add: field_simps)
      also have "... = \<epsilon>"
        using \<open>n > 0\<close> \<open>a > 0\<close> by simp
      finally show ?thesis .
    qed
    ultimately have f2_near_f1: "integral {0..a} (\<lambda>x. f2 x - f1 x) < \<epsilon>"
      by (simp add: integral_unique)

    define yidx where "yidx \<equiv> \<lambda>y. LEAST k. y < f (a_seg (Suc k))"
    have yidx_le: "f (a_seg (yidx y)) \<le> y" and yidx_gt: "y < f (a_seg (Suc (yidx y)))" 
      if "y \<in> {0..b}" for y
    proof -
      obtain x where x: "f x = y" "x \<in> {0..a}"
        using Topological_Spaces.IVT' [OF _ _ _ cont_0a] assms
        by (metis \<open>y \<in> {0..b}\<close> atLeastAtMost_iff)
      define k where "k \<equiv> nat \<lfloor>x/a * n\<rfloor>"
      have x_lims: "a_seg k \<le> x" "x < a_seg (Suc k)"
        using \<open>n > 0\<close> \<open>0 < a\<close> floor_divide_lower floor_divide_upper [of a "x*n"] x
        by (auto simp add: k_def a_seg_def field_simps)
      with that x obtain f_lims: "f (a_seg k) \<le> y" "y < f (a_seg (Suc k))"
        using strict_mono_onD [OF sm] by force
      then have "a_seg (yidx y) \<le> a_seg k"
        by (simp add: Least_le \<open>strict_mono a_seg\<close> strict_mono_less_eq yidx_def)
      then have "f (a_seg (yidx y)) \<le> f (a_seg k)"
        using strict_mono_onD [OF sm] by simp
      then show "f (a_seg (yidx y)) \<le> y"
        using f_lims by linarith
      show "y < f (a_seg (Suc (yidx y)))"
        by (metis LeastI f_lims(2) yidx_def) 
    qed

    have yidx_equality: "yidx y = k" if "y \<in> {0..b}" "y \<in> {f (a_seg k)..<f (a_seg (Suc k))}" for y k
    proof (rule antisym)
      show "yidx y \<le> k"
        unfolding yidx_def by (metis atLeastLessThan_iff that(2) Least_le)
      have "(a_seg (real k)) < a_seg (1 + real (yidx y))"
        using yidx_gt [OF that(1)] that(2) strict_mono_onD [OF sm] order_le_less_trans by fastforce
      then have "real k < 1 + real (yidx y)"
        by (simp add: \<open>strict_mono a_seg\<close> strict_mono_less)
      then show "k \<le> yidx y"
        by simp 
    qed
    have "yidx b = n"
    proof -
      have "a < (1 + real n) * a / real n"
        using \<open>0 < n\<close> \<open>0 < a\<close> by (simp add: divide_simps)
      then have "b < f (a_seg (1 + real n))"
        using \<open>0 \<le> a\<close> a_seg_def sm strict_mono_onD by fastforce
      then show ?thesis
        using \<open>0 \<le> b\<close> by (auto simp: a_seg_def yidx_equality)
    qed
    moreover have yidx_less_n: "yidx y < n" if "y < b" for y
      by (metis \<open>0 < n\<close> fa_eq_b gr0_conv_Suc less_Suc_eq_le that Least_le yidx_def)
    ultimately have yidx_le_n: "yidx y \<le> n" if "y \<le> b" for y
      by (metis dual_order.order_iff_strict that)

    have zero_to_b_eq: "{0..b} = (\<Union>k<n. {f(a_seg k)..f(a_seg (Suc k))})" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof
        fix y assume y: "y \<in> {0..b}"
        have fn: "f (a_seg n) = b"
          using a_seg_eq_a_iff assms(6) by fastforce
        show "y \<in> ?rhs"
        proof (cases "y=b")
          case True
          with fn \<open>n>0\<close> show ?thesis
            by (rule_tac a="n-1" in UN_I) auto
        next
          case False
          with y show ?thesis 
            apply (simp add: subset_iff Bex_def)
            by (metis atLeastAtMost_iff of_nat_Suc order_le_less yidx_gt yidx_le yidx_less_n)
        qed
      qed
      show "?rhs \<subseteq> ?lhs"
        apply clarsimp
        by (smt (verit, best) a_seg_ge_0 a_seg_le_a f f_iff(2) nat_less_real_le of_nat_0_le_iff)
    qed

    define g1 where "g1 \<equiv> \<lambda>y. if y=b then a else a_seg (Suc (yidx y))"
    define g2 where "g2 \<equiv> \<lambda>y. if y=0 then 0 else a_seg (yidx y)"
    have g1: "g1 y \<in> {0..a}" if "y \<in> {0..b}" for y
      using that \<open>a > 0\<close> yidx_less_n [of y] by (auto simp: g1_def a_seg_def divide_simps)
    have g2: "g2 y \<in> {0..a}" if "y \<in> {0..b}" for y
      using that \<open>a > 0\<close> yidx_le_n [of y] by (simp add: g2_def a_seg_def divide_simps)

    have g2_le_g: "g2 y \<le> ?g y" if "y \<in> {0..b}" for y
    proof -
      have "f (g2 y) \<le> y"
        using \<open>f 0 = 0\<close> g2_def that yidx_le by presburger
      then have "f (g2 y) \<le> f (?g y)"
        using that by (simp add: fim f_inv_into_f [where f=f])
      then show ?thesis
        by (metis atLeastAtMost_iff f_iff(2) fim g2 inv_into_into that)
    qed
    have g_le_g1: "?g y \<le> g1 y" if "y \<in> {0..b}" for y
    proof -
      have "y \<le> f (g1 y)"
        by (smt (verit, best) \<open>f a = b\<close> g1_def that yidx_gt)
      then have "f (?g y) \<le> f (g1 y)"
        using that by (simp add: fim f_inv_into_f [where f=f])
      then show ?thesis
        by (metis atLeastAtMost_iff f_iff(2) fim g1 inv_into_into that)
    qed

    define DN where "DN \<equiv> \<lambda>K. nat \<lfloor>Inf K * real n / a\<rfloor>"
    have [simp]: "DN {a * real k / n..a * (1 + real k) / n} = k" for k
      using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: DN_def divide_simps)
    have DN: "bij_betw DN ?\<D> {..<n}"
    proof (intro bij_betw_imageI)
      show "inj_on DN (regular_division 0 a n)"
      proof
        fix K K'
        assume "K \<in> regular_division 0 a n"
        with \<open>a > 0\<close> obtain k where k: "K = {a * (real k / n) .. a * (1 + real k) / n}"
          by (force elim: regular_divisionE)
        assume "K' \<in> regular_division 0 a n"
        with \<open>a > 0\<close> obtain k' where k': "K' = {a * (real k' / n) .. a * (1 + real k') / n}"
          by (force elim: regular_divisionE)
        assume "DN K = DN K'"
        then show "K = K'" by (simp add: k k')
      qed
      have "\<exists>K\<in>regular_division 0 a n. k = nat \<lfloor>Inf K * real n / a\<rfloor>" if "k < n" for k
        using \<open>n > 0\<close> \<open>a > 0\<close> that
        by (force simp add: divide_simps intro: regular_division_eqI [OF refl])
      then show "DN ` regular_division 0 a n = {..<n}"
        using \<open>0 < a\<close> by (auto simp: DN_def bij_betw_def image_iff frac_le elim!: regular_divisionE)
    qed
 
    have int_f1: "(f1 has_integral (\<Sum>k<n. f(a_seg k)) * (a/n)) {0..a}"
    proof -
      have "a_seg (real (DN K)) = Inf K" if "K \<in> ?\<D>" for K
        using that \<open>0 < a\<close> by (auto simp: DN_def field_simps a_seg_def elim: regular_divisionE)
      then have "(\<Sum>K\<in>?\<D>. f(Inf K) * (a/n)) = (\<Sum>k<n. (f(a_seg k)) * (a/n))"
        by (simp flip: sum.reindex_bij_betw [OF DN])
      moreover have "(f1 has_integral (\<Sum>K\<in>?\<D>. f(Inf K) * (a/n))) {0..a}"
        by (intro div int_f1_D has_integral_combine_division)
      ultimately show ?thesis
        by (metis sum_distrib_right)
    qed
    text \<open>{term "(f2 has_integral (\<Sum>k<n. f(a_seg(Suc k))) * (a/n)) {0..a}"} can similarly be proved\<close>

    have int_g1_D: "(g1 has_integral a_seg (Suc k) * (f (a_seg (Suc k)) - f (a_seg k))) {f(a_seg k)..f(a_seg (Suc k))}" 
      and int_g2_D: "(g2 has_integral a_seg k * (f (a_seg (Suc k)) - f (a_seg k))) {f(a_seg k)..f(a_seg (Suc k))}" 
      if "k < n" for k
    proof -
      define u where "u \<equiv> f (a_seg k)"
      define v where "v \<equiv> f (a_seg (Suc k))"
      obtain "u < v" "0 \<le> u" "0 \<le> v"
        unfolding u_def v_def 
        by (smt (verit, best) a_seg_ge_0 a_seg_less_iff assms(5) atLeast_iff lessI of_nat_0_le_iff of_nat_less_iff sm strict_mono_onD) 
      obtain "u \<le> b" "v \<le> b"
        apply (simp add: u_def v_def flip: \<open>f a = b\<close>)
        by (smt (verit, best) \<open>k < n\<close> \<open>yidx b = n\<close> a_seg_ge_0 a_seg_le_a assms(4) assms(6) atLeastAtMost_iff atLeastLessThan_iff atLeast_iff of_nat_0_le_iff of_nat_1 of_nat_add of_nat_less_iff plus_1_eq_Suc sm strict_mono_onD yidx_equality)

      have yidx_eq: "yidx x = k" if "x \<in> {u..<v}" for x
        using \<open>0 \<le> u\<close> \<open>v \<le> b\<close> that u_def v_def yidx_equality by auto

      have "g1 x = a_seg (Suc k)" if "x \<in> {u..<v}" for x
        using that \<open>v \<le> b\<close> by (simp add: g1_def yidx_eq)
      moreover have "((\<lambda>x. a_seg (Suc k)) has_integral (a_seg (Suc k) * (v-u))) {u..v}"
        using has_integral_const_real \<open>u < v\<close>
        by (metis content_real_if less_eq_real_def mult.commute real_scaleR_def)
      ultimately show "(g1 has_integral (a_seg (Suc k) * (v-u))) {u..v}"
        using has_integral_spike_finite_eq [of "{v}" "{u..v}" "\<lambda>x. a_seg (Suc k)" g1] by simp

      have g2: "g2 x = a_seg k" if "x \<in> {u<..<v}" for x
        using that \<open>0 \<le> u\<close> by (simp add: g2_def yidx_eq)
      moreover have "((\<lambda>x. a_seg k) has_integral (a_seg k * (v-u))) {u..v}"
        using has_integral_const_real \<open>u < v\<close>
        by (metis content_real_if less_eq_real_def mult.commute real_scaleR_def)
      ultimately show "(g2 has_integral (a_seg k * (v-u))) {u..v}"
        using has_integral_spike_finite_eq [of "{u,v}" "{u..v}" "\<lambda>x. a_seg k" g2] by simp
    qed

    have int_g1: "(g1 has_integral (\<Sum>k<n. a_seg (Suc k) * (f (a_seg (Suc k)) - f (a_seg k)))) {0..b}"
    and int_g2: "(g2 has_integral (\<Sum>k<n. a_seg k * (f (a_seg (Suc k)) - f (a_seg k)))) {0..b}"
      unfolding zero_to_b_eq using int_g1_D int_g2_D
      by (auto simp add: min_def pairwise_def intro!: has_integral_UN negligible_atLeastAtMostI)

    have "(\<Sum>k<n. a_seg (Suc k) * (f (a_seg (Suc k)) - f (a_seg k)))
        = (\<Sum>k<n. (Suc k) * (f (a_seg (Suc k)) - f (a_seg k))) * (a/n)"
      unfolding a_seg_def sum_distrib_right sum_divide_distrib by (simp add: mult_ac)
    also have "... = (n * f (a_seg n) - (\<Sum>k<n. f (a_seg k))) * a / n"
      using weighted_nesting_sum [where g = "f o a_seg"] by simp
    also have "... = a * b - (\<Sum>k<n. f (a_seg k)) * a / n"
      using \<open>n > 0\<close> by (simp add: fa_eq_b field_simps)
    finally have int_g1': "(g1 has_integral a * b - (\<Sum>k<n. f (a_seg k)) * a / n) {0..b}"
      using int_g1 by simp

    text \<open>@{term "(g2 has_integral a * b - (\<Sum>k<n. f (a_seg (Suc k))) * a / n) {0..b}"} can similarly be proved.\<close> 

    have a_seg_diff: "a_seg (1 + real k) - a_seg k = a/n" for k
      by (simp add: a_seg_def field_split_simps)

    have f_a_seg_diff: "abs (f (a_seg (1 + real k)) - f (a_seg k)) < \<epsilon>/a" if "k<n" for k
      using that \<open>a > 0\<close> a_seg_diff an_less_del \<open>\<epsilon> > 0\<close>
      by (intro del) auto

    have "((\<lambda>x. g1 x - g2 x) has_integral (\<Sum>k<n. (f (a_seg (Suc k)) - f (a_seg k)) * (a/n))) {0..b}"
      using has_integral_diff [OF int_g1 int_g2]
      apply (simp add: a_seg_diff flip: sum_subtractf left_diff_distrib)
      apply (simp add: field_simps)
      done
    moreover have "(\<Sum>k<n. (f (a_seg (Suc k)) - f (a_seg k)) * (a/n)) < \<epsilon>"
    proof -
      have "(\<Sum>k<n. (f (a_seg (Suc k)) - f (a_seg k)) * (a/n)) 
         \<le> (\<Sum>k<n. \<bar>f (a_seg (Suc k)) - f (a_seg k)\<bar> * (a/n))"
        by simp
      also have "... < (\<Sum>k<n. (\<epsilon>/a) * (a/n))"
      proof (rule sum_strict_mono)
        fix k assume "k \<in> {..<n}"
        with \<open>n > 0\<close> \<open>a > 0\<close> divide_strict_right_mono f_a_seg_diff pos_less_divide_eq
        show "\<bar>f (a_seg (Suc k)) - f (a_seg k)\<bar> * (a/n) < \<epsilon>/a * (a/n)" by fastforce
      qed (use \<open>n > 0\<close> in auto)
      also have "... = \<epsilon>"
        using \<open>n > 0\<close> \<open>a > 0\<close> by simp
      finally show ?thesis .
    qed
    ultimately have g2_near_g1: "integral {0..b} (\<lambda>x. g1 x - g2 x) < \<epsilon>"
      by (simp add: integral_unique)

    have ab1: "integral {0..a} f1 + integral {0..b} g1 = a*b"
      using int_f1 int_g1' by (simp add: integral_unique)

    have "integral {0..a} (\<lambda>x. f x - f1 x) \<le> integral {0..a} (\<lambda>x. f2 x - f1 x)"
    proof (rule integral_le)
      show "(\<lambda>x. f x - f1 x) integrable_on {0..a}" "(\<lambda>x. f2 x - f1 x) integrable_on {0..a}"
        using Henstock_Kurzweil_Integration.integrable_diff int_f1 intgb_f f12 by blast+
    qed (auto simp add: f2_upper)
    with f2_near_f1 have "integral {0..a} (\<lambda>x. f x - f1 x) < \<epsilon>"
      by simp
    moreover have "integral {0..a} f1 \<le> integral {0..a} f"
      by (intro integral_le has_integral_integral intgb_f has_integral_integrable [OF int_f1]) (simp add: f1_lower)
    ultimately have f_error: "\<bar>integral {0..a} f - integral {0..a} f1\<bar> < \<epsilon>"
      using Henstock_Kurzweil_Integration.integral_diff int_f1 intgb_f by fastforce

    have "integral {0..b} (\<lambda>x. g1 x - ?g x) \<le> integral {0..b} (\<lambda>x. g1 x - g2 x)"
    proof (rule integral_le)
      show "(\<lambda>x. g1 x - ?g x) integrable_on {0..b}" "(\<lambda>x. g1 x - g2 x) integrable_on {0..b}"
        using Henstock_Kurzweil_Integration.integrable_diff int_g1 int_g2 intgb_g by blast+
    qed (auto simp add: g2_le_g)
    with g2_near_g1 have "integral {0..b} (\<lambda>x. g1 x - ?g x) < \<epsilon>"
      by simp
    moreover have "integral {0..b} ?g \<le> integral {0..b} g1"
      by (intro integral_le has_integral_integral intgb_g has_integral_integrable [OF int_g1]) (simp add: g_le_g1)
    ultimately have g_error: "\<bar>integral {0..b} g1 - integral {0..b} ?g\<bar> < \<epsilon>"
      using integral_diff int_g1 intgb_g by fastforce
    show ?thesis
      using f_error g_error ab1 by linarith
  qed
  show ?thesis
    using * [of "\<bar>a * b - integral {0..a} f - integral {0..b} ?g\<bar> / 2"] by fastforce
qed (use assms in force)






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



end
