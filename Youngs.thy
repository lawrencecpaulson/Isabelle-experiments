section \<open>Misc experiments\<close>

theory Youngs imports
  "HOL-Analysis.Analysis" 
  "HOL-ex.Sketch_and_Explore"
   
begin
  
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
  assumes sm: "strict_mono_on f {0..}" and cont: "continuous_on {0..} f" and a: "0 \<le> a" "0 \<le> b" 
      and [simp]: "f 0 = 0" "f a = b"
  shows "a*b = integral {0..a} f + integral {0..b} (inv_into {0..a} f)"
proof (cases "a=0")
  case False
  then have "a > 0"
    using assms(3) by linarith
  let ?g = "inv_into {0..a} f"
  have cont_0a: "continuous_on {0..a} f"
    using cont continuous_on_subset by fastforce
  with sm have "continuous_on {0..b} ?g"
    apply (simp add: strict_mono_on_def)
    by (metis \<open>0 \<le> a\<close> \<open>f 0 = 0\<close> \<open>f a = b\<close> atLeastAtMost_iff strict_mono_continuous_inv strict_mono_onI)
  have fim: "f ` {0..a} = {0..b}"
    by (metis \<open>0 \<le> a\<close> \<open>f 0 = 0\<close> \<open>f a = b\<close> atLeastAtMost_iff atLeast_iff cont_0a sm strict_mono_image_endpoints strict_mono_on_def)
  have "uniformly_continuous_on {0..a} f"
    using compact_uniformly_continuous cont_0a by blast
  then obtain del where del_gt0: "\<And>e. e>0 \<Longrightarrow> del e > 0" 
                   and del:  "\<And>e x x'. \<lbrakk>dist x' x < del e; e>0; x \<in> {0..a}; x' \<in> {0..a}\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
    unfolding uniformly_continuous_on_def by metis

  obtain S where S: "(f has_integral S) {0..a}"
    using cont_0a integrable_continuous_real by blast
  { fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    with \<open>a > 0\<close> have gt0: "\<epsilon>/a > 0"
      by simp
    define \<delta> where "\<delta> = min a (del (\<epsilon>/a)) / 2"
    have "\<delta> > 0" "\<delta> \<le> a"
      using \<open>a > 0\<close> \<open>\<epsilon> > 0\<close> del_gt0 by (auto simp add: \<delta>_def)

    have \<delta>:  "\<And>x x'. \<lbrakk>abs (x'-x) \<le> \<delta>; x \<in> {0..a}; x' \<in> {0..a}\<rbrakk> \<Longrightarrow> abs (f x' - f x) < \<epsilon>/a"
      apply (rule del [unfolded dist_real_def])
         apply (simp add: \<delta>_def)
      using del_gt0 gt0 apply fastforce
        apply (auto simp: )
      using gt0 by blast

    define n where "n \<equiv> nat\<lfloor>a / \<delta>\<rfloor>"
    have "n > 0"
      using  \<open>a > 0\<close> \<open>\<delta> > 0\<close> \<open>\<delta> \<le> a\<close> by (simp add: n_def)
    have "n * \<delta> * (\<epsilon>/a) \<le> \<epsilon>"
      unfolding n_def
      by (smt (z3) False \<open>0 < \<delta>\<close> \<open>n > 0\<close> gt0 less_imp_of_nat_less mult_imp_div_pos_less n_def nat_eq_iff2 nonzero_eq_divide_eq nonzero_mult_div_cancel_left of_nat_floor zero_le_floor) 

    have "a/d < real_of_int \<lfloor>a * 2 / min a d\<rfloor>" if "d>0" for d
      by (smt (verit, best) \<open>0 < \<delta>\<close> \<open>\<delta> \<le> a\<close> add_divide_distrib divide_less_eq_1_pos floor_eq_iff that)
    then have an_less_del: "a/n < del (\<epsilon>/a)"
      using \<open>a > 0\<close> \<open>\<epsilon> > 0\<close> del_gt0  by (simp add: n_def \<delta>_def field_simps)

    define lower where "lower \<equiv> \<lambda>x. \<lfloor>(real n * x) / a\<rfloor> * a/n"
    define f1 where "f1 \<equiv> f \<circ> lower"
    have mo_lower: "mono_on lower {0..a}"
      using \<open>n > 0\<close> unfolding lower_def mono_on_def
      by (auto simp: divide_right_mono floor_mono mult.commute mult_left_mono order_less_imp_le)
    have lower_im: "lower ` {0..a} \<subseteq> {0..}"
      using \<open>n > 0\<close> by (auto simp: lower_def)
    have f1_lower: "f1 x \<le> f x" if "0 \<le> x" "x \<le> a" for x
    proof -
      have "lower x \<le> x"
        using \<open>n > 0\<close> floor_divide_lower [OF \<open>a > 0\<close>] by (auto simp add: lower_def field_simps)
      moreover have "lower x \<ge> 0"
        unfolding lower_def using \<open>n > 0\<close> \<open>0 \<le> a\<close> \<open>0 \<le> x\<close> by force
      ultimately show ?thesis
        using sm strict_mono_on_leD by (fastforce simp add: f1_def)
    qed
    define upper where "upper \<equiv> \<lambda>x. \<lceil>real n * x / a\<rceil> * a/n"
    define f2 where "f2 \<equiv> f \<circ> upper"

    have mo_upper: "mono_on upper {0..a}"
      using \<open>n > 0\<close> unfolding upper_def mono_on_def
      by (simp add: ceiling_mono divide_right_mono mult_right_mono)
    have upper_im: "upper ` {0..a} \<subseteq> {0..}"
      using \<open>n > 0\<close>
      apply (clarsimp simp: upper_def field_split_simps)
      by (smt (verit) mult_nonneg_nonneg of_nat_0_le_iff)

    have f2_upper: "f2 x \<ge> f x" if "0 \<le> x" "x \<le> a" for x
    proof -
      have "x \<le> upper x"
        using \<open>n > 0\<close> ceiling_divide_upper [OF \<open>a > 0\<close>] by (simp add: upper_def field_simps)
      then show ?thesis
        using sm strict_mono_on_leD \<open>0 \<le> x\<close> by (force simp add: f2_def)
    qed
    let ?\<D> = "regular_division 0 a n"
    have div: "?\<D> division_of {0..a}"
      using \<open>a > 0\<close> \<open>n > 0\<close> regular_division_division_of zero_less_nat_eq by presburger

    have int21: "((\<lambda>x. f2 x - f1 x) has_integral (f(Sup K) - f(Inf K)) * (a/n)) K" 
            and less: "\<bar>f(Sup K) - f(Inf K)\<bar> < \<epsilon>/a"
      if "K\<in>?\<D>" for K
    proof -
      from regular_divisionE [OF that] \<open>a > 0\<close>
      obtain k where "k<n" and k: "K = {a * (real k / n) .. a * (1 + real k) / n}"
        by (auto simp add: zless_nat_eq_int_zless)
      define u where "u \<equiv> a * (real k / n)"
      define v where "v \<equiv> a * (1 + real k) / n"
      have "u < v" "0 \<le> u" "0 \<le> v" and Kuv: "K = {u..v}"
        using \<open>n > 0\<close> \<open>a > 0\<close> by (auto simp: k u_def v_def divide_simps)
      have "u \<le> a" "v \<le> a"
        using \<open>k < n\<close> \<open>a > 0\<close> by (auto simp: u_def v_def divide_simps)
      have InfK: "Inf K = u" and SupK: "Sup K = v"
        using \<open>n > 0\<close> \<open>a > 0\<close> by (auto simp: divide_right_mono k u_def v_def)
      have f1: "f (Inf K) = f1 x" if "x \<in> K - {v}" for x
      proof -
        have "x \<in> {u..<v}"
          using that Kuv atLeastLessThan_eq_atLeastAtMost_diff by blast
        then have "\<lfloor>real_of_int n * x / a\<rfloor> = int k"
          using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: field_simps u_def v_def floor_eq_iff)
        then show ?thesis
          by (simp add: InfK f1_def lower_def mult.commute u_def) 
      qed
      have "((\<lambda>x. f (Inf K)) has_integral (f (Inf K) * (a/n))) K"
        using has_integral_const_real [of "f (Inf K)" u v] 
              \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: Kuv field_simps u_def v_def)
      then have intf1: "(f1 has_integral (f (Inf K) * (a/n))) K"
        using has_integral_spike_finite_eq [of "{v}" K "\<lambda>x. f (Inf K)" f1] f1 by simp
      have f2: "f (Sup K) = f2 x" if "x \<in> K - {u}" for x
      proof -
        have "x \<in> {u<..v}"
          using that Kuv greaterThanAtMost_eq_atLeastAtMost_diff by blast 
        then have "\<lceil>x * real_of_int n / a\<rceil>  = 1 + int k"
          using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: field_simps u_def v_def ceiling_eq_iff)
        then show ?thesis 
          by (simp add: mult.commute f2_def upper_def SupK v_def)
      qed
      have "((\<lambda>x. f (Sup K)) has_integral (f (Sup K) * (a/n))) K"
        using  \<open>n > 0\<close> \<open>a > 0\<close> has_integral_const_real [of "f (Sup K)" u v]
        by (simp add: Kuv field_simps u_def v_def)
      then have intf2: "(f2 has_integral (f (Sup K) * (a/n))) K"
        using has_integral_spike_finite_eq [of "{u}" K "\<lambda>x. f (Sup K)" f2] f2 by simp
      show "((\<lambda>x. f2 x - f1 x) has_integral (f(Sup K) - f(Inf K)) * (a/n)) K"
        using has_integral_diff [OF intf2 intf1] by (simp add: algebra_simps)

      have "\<bar>v - u\<bar> < del (\<epsilon>/a)"
        using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: v_def u_def field_simps an_less_del)
      then have "\<bar>f v - f u\<bar> < \<epsilon>/a"
        using \<open>\<epsilon> > 0\<close> \<open>a > 0\<close> \<open>0 \<le> u\<close> \<open>u \<le> a\<close> \<open>0 \<le> v\<close> \<open>v \<le> a\<close>
        by (intro del [unfolded dist_real_def]) auto
      then show "\<bar>f(Sup K) - f(Inf K)\<bar> < \<epsilon>/a"
        using InfK SupK by blast
    qed

    have D_ne: "?\<D> \<noteq> {}"
      by (metis \<open>0 < a\<close> \<open>n > 0\<close> card_gt_0_iff card_regular_division)
    have f12: "((\<lambda>x. f2 x - f1 x) has_integral (\<Sum>K\<in>?\<D>. (f(Sup K) - f(Inf K)) * (a/n))) {0..a}"
      by (intro div int21 has_integral_combine_division)
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
    ultimately have "integral {0..a} (\<lambda>x. f2 x - f1 x) < \<epsilon>"
      by (simp add: integral_unique)

(*So f1 x = 0*)
    have "real_of_int \<lfloor>real n * x / a\<rfloor> * a / real n = 0" if "x \<in> {0..< a/n}" for x
      using that \<open>n > 0\<close> \<open>a > 0\<close> floor_le_iff [of _ 0]
      apply (simp add: f1_def lower_def field_simps)
      by (smt (verit, best) divide_nonneg_nonneg floor_le_zero le_divide_eq_1_pos mult_nonneg_nonneg of_nat_0_le_iff zero_le_floor)

    define invf where "invf \<equiv> \<lambda>k. k * a/n"
    define yidx where "yidx \<equiv> \<lambda>y. LEAST k. y < f (invf (Suc k))"
    have "strict_mono invf"
      using \<open>n > 0\<close> \<open>a > 0\<close> by (simp add: invf_def strict_mono_def divide_simps)

    have yidx_le: "f (invf (yidx y)) \<le> y" and yidx_gt: "y < f (invf (Suc (yidx y)))" 
      if "y \<in> {0..b}" for y
    proof -
      obtain x where x: "f x = y" "x \<in> {0..a}"
        using Topological_Spaces.IVT' [OF _ _ _ cont_0a] assms
        by (metis \<open>y \<in> {0..b}\<close> atLeastAtMost_iff)
      define k where "k \<equiv> nat \<lfloor>x/a * n\<rfloor>"
      have x_lims: "invf k \<le> x" "x < invf (Suc k)"
        using \<open>n > 0\<close> \<open>0 < a\<close> floor_divide_lower floor_divide_upper [of a "x*n"] x
        by (auto simp add: k_def invf_def field_simps)
      with that x obtain f_lims: "f (invf k) \<le> y" "y < f (invf (Suc k))"
        using strict_mono_onD [OF sm] 
        by (smt (verit, best) \<open>0 \<le> a\<close> atLeast_iff divide_nonneg_nonneg invf_def of_nat_0_le_iff zero_le_mult_iff)
      then have "invf (yidx y) \<le> invf k"
        by (simp add: Least_le \<open>strict_mono invf\<close> strict_mono_less_eq yidx_def)
      then have "f (invf (yidx y)) \<le> f (invf k)"
        using strict_mono_onD [OF sm] 
        by (metis \<open>0 \<le> a\<close> atLeast_iff divide_nonneg_nonneg invf_def less_eq_real_def of_nat_0_le_iff zero_le_mult_iff)
      then show "f (invf (yidx y)) \<le> y"
        using f_lims by force 
      show "y < f (invf (Suc (yidx y)))"
        by (metis LeastI f_lims(2) yidx_def) 
    qed

    have yidx_equality: "yidx y = k" if "y \<in> {0..b}" "y \<in> {f (invf k)..<f (invf (Suc k))}" for y k
    proof (rule antisym)
      show "yidx y \<le> k"
        unfolding yidx_def by (metis atLeastLessThan_iff that(2) Least_le)
      have "(invf (real k)) < invf (1 + real (yidx y))"
        using yidx_gt [OF that(1)] that(2) using strict_mono_onD [OF sm]
        apply (simp add: )
        by (smt (verit, ccfv_SIG) \<open>0 \<le> a\<close> divide_nonneg_nonneg invf_def mult_nonneg_nonneg of_nat_0_le_iff)
      then have "real k < 1 + real (yidx y)"
        by (simp add: \<open>strict_mono invf\<close> strict_mono_less)
      then show "k \<le> yidx y"
        by simp 
    qed

    have [simp]: "yidx 0 = 0"
      using \<open>0 < a\<close> \<open>0 \<le> b\<close> \<open>0 < n\<close> strict_mono_onD [OF sm] by (fastforce simp: invf_def yidx_equality)

    have [simp]: "yidx b = n"
    proof -
      have "a < (1 + real n) * a / real n"
        using \<open>0 < n\<close> \<open>0 < a\<close> by (simp add: divide_simps)
      then have "b < f (invf (1 + real n))"
        using \<open>0 \<le> a\<close> invf_def sm strict_mono_onD by fastforce
      then show ?thesis
        using \<open>0 \<le> b\<close> by (auto simp: invf_def yidx_equality)
    qed

    have E: "yidx y < n" if "0 \<le> y" "y < b" for y
      using yidx_gt [of y] \<open>f a = b\<close>
      by (smt (verit, del_insts) \<open>0 < n\<close> yidx_def gr0_conv_Suc invf_def less_Suc_eq_le less_imp_of_nat_less nonzero_mult_div_cancel_left of_nat_0 that(2) Least_le)

    have F: "yidx y \<le> n" if "0 \<le> y" "y \<le> b" for y
      by (metis E \<open>yidx b = n\<close> linorder_not_le not_less_iff_gr_or_eq that)

    define g1 where "g1 \<equiv> \<lambda>y. if y=b then a else invf (Suc (yidx y))"
    define g2 where "g2 \<equiv> \<lambda>y. if y=0 then 0 else invf (yidx y)"

    have g1: "g1 y \<in> {0..a}" if "y \<in> {0..b}" for y
      using that \<open>a > 0\<close> E [of y] by (auto simp: g1_def invf_def divide_simps)

    have g2: "g2 y \<in> {0..a}" if "y \<in> {0..b}" for y
      using that \<open>a > 0\<close> F [of y] by (simp add: g2_def invf_def divide_simps)

    have g0 [simp]: "?g 0 = 0"
      using \<open>f 0 = 0\<close> \<open>0 \<le> a\<close>
      by (smt (verit, best) Icc_subset_Ici_iff atLeastAtMost_iff f_inv_into_f image_iff in_mono inv_into_into sm strict_mono_on_eqD)

    have g2_le_g: "g2 y \<le> ?g y" if "y \<in> {0..b}" for y
    proof -
      have "f (g2 y) \<le> y"
        using that
      apply (simp add: g2_def)
        using that yidx_le by blast
      then have "f (g2 y) \<le> f (?g y)"
        using that by (simp add: fim f_inv_into_f [where f=f])
      then show ?thesis
      using that \<open>0 \<le> a\<close>
      apply (simp add: g2_def)
      apply (auto simp: )
      apply (auto simp: invf_def)

      apply (auto simp: yidx_def)

      sorry
    have g_le_g1: "?g y \<le> g1 y" if "y \<in> {0..b}" for y
      using that \<open>0 \<le> a\<close>
      by (simp add: g1_def g2_def invf_def \<open>yidx b = n\<close> divide_right_mono mult_right_mono)

    have g2_le_g1: "g2 y \<le> g1 y" if "y \<in> {0..b}" for y
      using that \<open>0 \<le> a\<close>
      by (simp add: g1_def g2_def invf_def divide_right_mono mult_right_mono)



    have "f2 (invf k) = f1 (invf ( k))" for k
      by (simp add: f1_def f2_def upper_def lower_def invf_def)
  }
  show ?thesis
    sorry
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
