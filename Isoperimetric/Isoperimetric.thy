theory Isoperimetric
  imports Arc_Length_Reparametrization "Fourier.Square_Integrable"
    "HOL-ex.Sketch_and_Explore" 
begin

hide_const (open) Polynomial.content

section \<open>Start of the actual isoperimetric inequality\<close>

text \<open>
  Formalisation of the isoperimetric inequality, following John Harrison's
  HOL Light proof in @{text "100/isoperimetric.ml"}.

  The proof has five parts:
  \<^enum> Convex curve lemmas (switching between views of a convex simple closed curve)
  \<^enum> The Wirtinger inequality
  \<^enum> A special case of Green's theorem for convex area
  \<^enum> The isoperimetric theorem for convex curves
  \<^enum> Convexification of an arbitrary rectifiable simple closed curve
  \<^enum> The full isoperimetric theorem

  Infrastructure is provided by the prerequisite theories:
  \<^item> @{text Bounded_Variation}: bounded variation and vector variation
  \<^item> @{text Absolute_Continuity}: absolute continuity and FTC
  \<^item> @{text Rectifiable_Path}: rectifiable paths and path length
  \<^item> @{text Arc_Length_Reparametrization}: arc length reparametrization

  AFP dependencies:
  \<^item> @{text Fourier}: trigonometric orthonormal system, Bessel inequality,
    L2 Fourier convergence (useful for Wirtinger inequality)
  \<^item> @{text Lp} (via Fourier): Hölder inequality, Minkowski inequality
\<close>

subsection \<open>Convex curve lemmas\<close>

text \<open>Switching between views of a convex simple closed curve.\<close>

lemma convex_hull_eq_closure_inside:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "simple_path g" "pathfinish g = pathstart g"
    and conv: "convex (inside (path_image g))"
  shows "convex hull (path_image g) = closure (inside (path_image g))"
proof (rule equalityI)
  have bounded_inside: "bounded (inside (path_image g))"
    using Jordan_inside_outside g by blast
  have frontier_inside: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast
  show "convex hull (path_image g) \<subseteq> closure (inside (path_image g))"
    by (metis Diff_subset conv convex_closure convex_hull_subset frontier_def
        frontier_inside hull_same)
  moreover
  have "compact (closure (inside (path_image g)))"
    using compact_closure local.bounded_inside by blast
  ultimately show "closure (inside (path_image g)) \<subseteq> convex hull (path_image g)"
    by (metis (no_types) Krein_Milman_frontier conv closure_closure convex_closure 
        convex_interior_closure frontier_def frontier_inside)
qed


lemma frontier_convex_hull_eq_path_image:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "simple_path g" "pathfinish g = pathstart g"
    and conv: "convex (inside (path_image g))"
  shows "frontier (convex hull (path_image g)) = path_image g"
proof -
  have eq: "convex hull (path_image g) = closure (inside (path_image g))"
    by (rule convex_hull_eq_closure_inside[OF assms])
  have open_inside: "open (inside (path_image g))"
    and frontier_inside: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast+
  have "frontier (convex hull (path_image g)) = 
        closure (inside (path_image g)) - inside (path_image g)"
    by (simp add: conv convex_interior_closure eq frontier_def interior_open open_inside)
  also have "\<dots> = frontier (inside (path_image g))"
    using interior_open[OF open_inside] by (simp add: frontier_def)
  also have "\<dots> = path_image g"
    by (rule frontier_inside)
  finally show ?thesis .
qed

lemma frontier_convex_hull_subset_path_image:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
    "path_image g \<subseteq> frontier (convex hull (path_image g))"
  shows "frontier (convex hull path_image g) \<subseteq> path_image g"
proof -
  have bounded_hull: "bounded (convex hull (path_image g))"
    by (simp add: assms(1) bounded_convex_hull bounded_simple_path_image)
      \<comment> \<open>The interior of the convex hull is connected, bounded, and disjoint from @{term "path_image g"}\<close>
  have int_sub: "interior (convex hull (path_image g)) \<inter> path_image g = {}"
    using assms(3) frontier_def by auto
  have "connected (interior (convex hull (path_image g)))"
    by (simp add: convex_connected)
  moreover have "bounded (interior (convex hull (path_image g)))"
    using bounded_hull bounded_interior by blast
  moreover have "interior (convex hull (path_image g)) \<subseteq> - path_image g"
    using int_sub by blast
  moreover have "inside (path_image g) \<subseteq> convex hull path_image g"
    by (metis Un_subset_iff compl_le_swap2 convex_convex_hull hull_subset
        outside_subset_convex union_with_inside)
  ultimately have int_inside: "interior (convex hull (path_image g)) \<subseteq> inside (path_image g)"
    using Jordan_inside_outside[OF \<open>simple_path g\<close>] assms
    by (smt (verit) connected_Int_frontier diff_shunt inf.commute int_sub interior_Int
        interior_eq le_iff_inf)
  have "- (convex hull (path_image g)) \<subseteq> outside (path_image g)"
    by (simp add: hull_subset outside_subset_convex)
  hence inside_sub: "inside (path_image g) \<subseteq> convex hull (path_image g)"
    by (metis Un_subset_iff compl_le_swap2 union_with_inside)
      \<comment> \<open>Since @{term "inside (path_image g)"} is open and contained in the convex hull, it lies in the interior of the hull\<close>
  have "inside (path_image g) \<subseteq> interior (convex hull (path_image g))"
    by (simp add: Jordan_inside_outside assms inside_sub interior_maximal)
  with assms show ?thesis
    using frontier_convex_hull_eq_path_image int_inside by auto
qed

section \<open>Part 1: The Wirtinger inequality\<close>

text \<open>The Hölder bound for @{text "p = q = 2"} follows from @{thm Holder_inequality} in the
  AFP @{text Lp} entry.\<close>

lemma real_hoelder_bound_2:
  fixes f :: "real \<Rightarrow> real" and S :: "real set"
  assumes S: "S \<in> sets lebesgue" "S \<in> lmeasurable" 
    and f: "f \<in> borel_measurable lebesgue" "integrable lebesgue (\<lambda>x. indicator S x * (f x)\<^sup>2)"
  shows "(LINT x|lebesgue. indicator S x * f x)\<^sup>2 \<le>
    measure lebesgue S * (LINT x|lebesgue. indicator S x * (f x)\<^sup>2)"
proof -
  have to_lebesgue_on: "\<And>g::real\<Rightarrow>real. (LINT x|lebesgue. indicator S x * g x) = integral\<^sup>L (lebesgue_on S) g"
    and f_sq_integ: "integrable (lebesgue_on S) (\<lambda>x. (f x)\<^sup>2)"
    by (simp_all add: assms integral_restrict_space integrable_restrict_space)
  then obtain f_meas_on: "f \<in> borel_measurable (lebesgue_on S)" 
    and f_sq_int: "f square_integrable S"
    using assms measurable_restrict_space1 square_integrable_def by blast
  have one_sq_int: "(\<lambda>x. 1::real) square_integrable S"
    unfolding square_integrable_def 
    using finite_measure_lebesgue_on assms finite_measure.integrable_const by blast

  have schwartz: "\<bar>l2product S f (\<lambda>x. 1)\<bar> \<le> l2norm S f * l2norm S (\<lambda>x. 1)"
    by (rule Schwartz_inequality_abs[OF f_sq_int one_sq_int])

  have "(l2norm S (\<lambda>x. 1))\<^sup>2 = l2product S (\<lambda>x. 1) (\<lambda>x. 1)"
    by (rule l2norm_pow_2[OF one_sq_int])
  also have "\<dots> = measure lebesgue S"
    using finite_measure_lebesgue_on[OF assms(2)]
    by (simp add: l2product_def assms(1) measure_restrict_space)
  finally have "(l2norm S (\<lambda>x. 1))\<^sup>2 = measure lebesgue S" .
  moreover have "(l2product S f (\<lambda>x. 1))\<^sup>2 \<le> (l2norm S f)\<^sup>2 * (l2norm S (\<lambda>x. 1))\<^sup>2"
    by (metis power_mult_distrib real_sqrt_abs schwartz sqrt_le_D)
  moreover
  have "LINT x|lebesgue. indicator S x * f x = l2product S f (\<lambda>x. 1)" 
       "LINT x|lebesgue. indicator S x * (f x)\<^sup>2 = l2product S f f"
    by (simp_all add: to_lebesgue_on l2product_def power2_eq_square)
  ultimately show ?thesis
    by (metis f_sq_int l2norm_pow_2 mult.commute)
qed

locale W =
  fixes f f' :: "real \<Rightarrow> real" and a::real
  assumes f'hsd: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and feq: "f (2*pi) = f 0"
    and f0: "(f has_integral 0) {0..2*pi}"
    and f'2: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..2*pi}"
    and a: "0 \<le> a" "a < pi" "f (a + pi) = f a"

begin

definition g where "g \<equiv> \<lambda>x. (f x - f a)\<^sup>2 / tan (x - a)"
definition g' where "g' \<equiv> \<lambda>x. (f' x)\<^sup>2 - (f x - f a)\<^sup>2 - (f' x - (f x - f a) / tan (x - a))\<^sup>2"

lemma f': \<open>f' integrable_on {0..2*pi}\<close>
  using f'hsd [of \<open>2*pi\<close>] by fastforce

lemma f'abs: \<open>f' absolutely_integrable_on {0..2*pi}\<close>
proof (rule absolutely_integrable_integrable_bound)
  show \<open>norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close> for x
  proof -
    have \<open>0 \<le> (1 - f' x)\<^sup>2\<close> and \<open>0 \<le> (1 + f' x)\<^sup>2\<close>
      by (auto simp: power2_eq_square)
    then show \<open>norm (f' x) \<le> 1 + (f' x)\<^sup>2\<close>
      by (auto simp: power2_eq_square abs_le_iff algebra_simps)
  qed
  show \<open>f' integrable_on {0..2*pi}\<close> by (rule f')
  show \<open>(\<lambda>x. 1 + (f' x)\<^sup>2) integrable_on {0..2*pi}\<close>
    using integrable_add [OF integrable_const_ivl f'2] by simp
qed

lemma contf: \<open>continuous_on {0..2*pi} f\<close>
proof (rule continuous_on_eq)
  show \<open>continuous_on {0..2*pi} (\<lambda>x. integral {0..x} f' + f 0)\<close>
    by (intro continuous_on_add indefinite_integral_continuous_1 [OF f'] continuous_on_const)
  show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> integral {0..x} f' + f 0 = f x\<close>
    using f'hsd by (auto simp: has_integral_integrable_integral)
qed

text \<open>The integral over completely trouble-free intervals.\<close>
lemma trouble_free: 
  assumes cd: "c \<le> d"
    and sub_cd: "{c..d} \<subseteq> {0..2*pi}"
    and sin_nz: "\<And>x. x \<in> {c..d} \<Longrightarrow> sin (x - a) \<noteq> 0"
  shows "(g' has_integral g d - g c) {c..d}"
proof -
  have f'_int: "((\<lambda>t. 2 * (f t - f a) * f' t) has_integral
                   ((f x - f a)\<^sup>2 - (f c - f a)\<^sup>2)) {c..x}"
    if xcd: "x \<in> {c..d}" for x
  proof -
    have cx: "c \<le> x" and xd: "x \<le> d" using xcd cd by auto
    have sub_cx: "{c..x} \<subseteq> {0..2*pi}" using sub_cd xd by auto
    have ac_f: "absolutely_continuous_on {0..2*pi} f"
      using absolute_integral_absolutely_continuous_derivative_eq f'abs f'hsd by blast
    have ac_sq: "absolutely_continuous_on {c..x} (\<lambda>t. (f t - f a)\<^sup>2)"
      unfolding power2_eq_square using absolutely_continuous_on_subset ac_f sub_cx 
      by(intro continuous_intros) fastforce+
    obtain k where negk: "negligible k"
      and derivf: "\<And>t. t \<in> {0..2*pi} - k \<Longrightarrow>
          ((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
      using f' has_vector_derivative_indefinite_integral by blast
    have deriv_sq: "((\<lambda>t. (f t - f a)\<^sup>2) has_vector_derivative 2 * (f t - f a) * f' t) (at t within {c..x})"
      if "t \<in> {c..x} - k" for t
    proof -
      have hvd_int: "((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
        using derivf that sub_cx by auto
      have "((\<lambda>u. f u - f 0) has_vector_derivative f' t) (at t within {0..2*pi})"
      proof (rule has_vector_derivative_transform_within[OF hvd_int])
        fix u assume "u \<in> {0..2*pi}" "dist u t < 1"
        then show "integral {0..u} f' = f u - f 0"
          using f'hsd by blast
      qed (use that sub_cx in auto)
      then have fderiv: "(f has_vector_derivative f' t) (at t within {c..x})"
        using has_vector_derivative_diff_const has_vector_derivative_within_subset sub_cx by blast
      then show ?thesis
        unfolding power2_eq_square has_vector_derivative_def
        by - (rule derivative_eq_intros | simp add: algebra_simps)+
    qed
    show ?thesis
      using fundamental_theorem_of_calculus_absolutely_continuous [OF negk cx ac_sq deriv_sq] by simp
  qed
  text \<open>Apply integration by parts with
      \<^item> \<open>\<lambda>x. (f x - f a)²\<close> and its derivative \<open>\<lambda>x. 2 * (f x - f a) * f' x\<close>
      \<^item> \<open>\<lambda>x. inverse (tan (x - a))\<close> and its derivative \<open>\<lambda>x. - inverse (sin (x - a))²\<close>\<close>
  have ibp_int: "((\<lambda>x. (f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)))
      has_integral ((f y - f a)\<^sup>2 * inverse (tan (y - a)) -
                    (f c - f a)\<^sup>2 * inverse (tan (c - a)))) {c..y}"
    if "y \<in> {c..d}" for y
  proof (rule absolute_real_integration_by_parts_sum(2))
    show "c \<le> d" using cd .
    have f'_abs_cd: "f' absolutely_integrable_on {c..d}"
      using absolutely_integrable_on_subinterval[OF f'abs sub_cd] .
    have cont_ffa: "continuous_on {c..d} (\<lambda>x. 2 * (f x - f a))"
      using sub_cd by (intro continuous_intros continuous_on_subset [OF contf]) auto
    have meas: "(\<lambda>x. 2 * (f x - f a)) \<in> borel_measurable (lebesgue_on {c..d})"
      using cont_ffa by (intro continuous_imp_measurable_on_sets_lebesgue) auto
    have bdd: "bounded ((\<lambda>x. 2 * (f x - f a)) ` {c..d})"
      using cont_ffa compact_Icc compact_continuous_image compact_imp_bounded by blast
    show "(\<lambda>x. 2 * (f x - f a) * f' x) absolutely_integrable_on {c..d}"
      using absolutely_integrable_bounded_measurable_product_real [OF meas _ bdd f'_abs_cd] by auto
    show "(\<lambda>x. - inverse ((sin (x - a))\<^sup>2)) absolutely_integrable_on {c..d}"
      by (intro absolutely_integrable_continuous_real continuous_intros) (use sin_nz in auto)
    show "((\<lambda>t. - inverse ((sin (t-a))\<^sup>2)) has_integral (inverse (tan (x - a)) - inverse (tan (c - a)))) {c..x}"
      if "x \<in> {c..d}" for x 
    proof -
      have cx: "c \<le> x" and sub_cx: "{c..x} \<subseteq> {c..d}"
        using that by auto
      have inv_tan_eq: "inverse (tan (t-a)) = cos (t-a) / sin (t-a)"
        if "t \<in> {c..x}" for t
        by (simp add: Multiseries_Expansion.tan_conv_sin_cos)
      have deriv: "((\<lambda>t. cos (t-a) / sin (t-a)) has_vector_derivative
                    - inverse ((sin (t-a))\<^sup>2)) (at t within {c..x})"
        if "t \<in> {c..x}" for t
      proof -
        have sin_nz_t: "sin (t-a) \<noteq> 0" using sin_nz that sub_cx by auto
        have "((\<lambda>t. cos (t-a) / sin (t-a)) has_real_derivative - inverse ((sin (t-a))\<^sup>2))
              (at t within {c..x})"
          using sin_cos_squared_add3 [of "t-a"]
          by (intro derivative_eq_intros | simp (no_asm_simp) add: sin_nz_t divide_simps power2_eq_square)+
        then show ?thesis
          by (simp add: has_real_derivative_iff_has_vector_derivative)
      qed
      show ?thesis
        using fundamental_theorem_of_calculus[OF cx deriv] inv_tan_eq inv_tan_eq cx
        by simp
    qed
  qed (use f'_int that in auto)
  have integrand_eq: "(f x - f a)\<^sup>2 * (- inverse ((sin (x - a))\<^sup>2)) +
      2 * (f x - f a) * f' x * inverse (tan (x - a)) = g' x"
    if "x \<in> {c..d}" for x
  proof -
    have snz: "sin (x - a) \<noteq> 0" using sin_nz[OF that] .
    have snz2: "(sin (x - a))\<^sup>2 \<noteq> 0" using snz by auto
    let ?F = "f x - f a"
    let ?s = "sin (x - a)"
    let ?c = "cos (x - a)"
    have sc1: "?s\<^sup>2 + ?c\<^sup>2 = 1"
      using sin_cos_squared_add[of "x - a"] by simp
    have "((f x - f a)\<^sup>2 * (- inverse (?s\<^sup>2)) + 2 * (f x - f a) * f' x * inverse (tan (x - a))) * ?s\<^sup>2
          = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
      using snz snz2 by (simp add: tan_def field_simps power2_eq_square)
    moreover have "g' x * ?s\<^sup>2 = ((f' x)\<^sup>2 - ?F\<^sup>2) * ?s\<^sup>2 - (f' x * ?s - ?F * ?c)\<^sup>2"
      using snz by (simp add: g'_def tan_def field_simps)
    moreover have "\<dots>  = - ?F\<^sup>2 + 2 * ?F * f' x * ?c * ?s"
      using sc1 by algebra 
    ultimately show ?thesis using snz2
      by (metis mult_right_cancel)
  qed
    \<comment> \<open>Combine using has_integral_eq\<close>
  show ?thesis
    using has_integral_eq ibp_int integrand_eq unfolding g_def divide_inverse
    by (metis (no_types, lifting) atLeastAtMost_iff order.refl cd)
qed

text \<open>Continuity of @{term g}.\<close>
lemma g_cont: "continuous_on {0..2*pi} g"
  unfolding continuous_on_eq_continuous_within
proof
  fix c assume c_in: "c \<in> {0..2*pi}"
  show "continuous (at c within {0..2*pi}) g"
  proof (cases "sin (c - a) = 0")
    case False
    have g_eq: "g x = (f x - f a)\<^sup>2 * cos (x - a) / sin (x - a)" for x
      unfolding g_def tan_def by (simp add: field_simps)
    have "continuous (at c within {0..2*pi}) f"
      using contf c_in continuous_on_eq_continuous_within by blast
    then show ?thesis unfolding g_eq
      using False by (auto simp: continuous_intros)
  next
    case True
      \<comment> \<open>When $\sin(c - a) = 0$, we have $g(c) = 0$ and need to show $g(x) \to 0$.\<close>
    then obtain n :: int where npi: "c - a = of_int n * pi"
      using sin_zero_iff_int2 by auto
    have "of_int n \<ge> -a / pi" "of_int n \<le> (2 * pi - a) / pi"
      using a npi c_in pi_gt_zero by (simp_all add: field_simps)
    moreover have "-a / pi > -1" using a pi_gt_zero by (simp add: field_simps)
    moreover have "(2 * pi - a) / pi < 3"
      using a pi_gt_zero by (auto simp: divide_simps)
    ultimately have "of_int n > (-1 :: real)" "of_int n < (3 :: real)" by linarith+
    then have "n = 0 \<or> n = 1 \<or> n = 2"
      by auto
    then have fca: "f c = f a"
    proof (elim disjE)
      assume "n = 2"
      then have "c = a + 2 * pi" using npi by (simp add: algebra_simps)
      with c_in a pi_gt_zero have "a = 0" by auto
      thus "f c = f a" using \<open>c = a + 2 * pi\<close> feq by simp
    qed (use npi a in \<open>auto simp: algebra_simps\<close>)
    have gc0: "g c = 0"
      unfolding g_def using fca by simp
    have tan_eq: "tan (x - a) = tan (x - c)" for x
      by (metis npi diff_add_cancel diff_diff_eq2 tan_periodic_int)
    have g_eq2: "g x = (f x - f c)\<^sup>2 * cos (x - c) / sin (x - c)" for x
      unfolding g_def by (metis fca divide_divide_eq_right local.tan_eq tan_def)
    show ?thesis 
      unfolding continuous_within gc0
    proof -
      \<comment> \<open>Cauchy--Schwarz bound: $(f(x) - f(c))^2 \le |x - c| \cdot \int_c^x (f')^2$.\<close>
      have cs_bound: "(f x - f c)\<^sup>2 \<le> \<bar>x - c\<bar> * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
        if xin: "x \<in> {0..2*pi}" for x
      proof -
        have f'_int_sub: "f' integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
          using integrable_subinterval_real[OF set_lebesgue_integral_eq_integral(1)[OF f'abs] that] .
        have f'2_int_sub: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" if "{a..b} \<subseteq> {0..2*pi}" for a b
          using integrable_subinterval_real[OF f'2 that] .
            \<comment> \<open>Helper: the FTC gives $f(b) - f(a) = \int_a^b f'$ for $a, b \in \{0..2\pi\}$\<close>
        have ftc_sub: "f b - f a = integral {a..b} f'"
          if "a \<in> {0..2*pi}" "b \<in> {0..2*pi}" "a \<le> b" for a b
        proof -
          have "integral {0..a} f' + integral {a..b} f' = integral {0..b} f'"
            by (meson Henstock_Kurzweil_Integration.integral_combine atLeastAtMost_iff f'hsd
                has_integral_integrable that)
          moreover have "integral {0..a} f' = f a - f 0" and "integral {0..b} f' = f b - f 0"
            using f'hsd that by (auto simp: has_integral_integrable_integral)
          ultimately show ?thesis by linarith
        qed
          \<comment> \<open>Helper: Cauchy--Schwarz $\left(\int_I f'\right)^2 \le (b-a) \cdot \int_I (f')^2$ for $I = \{a..b\} \subseteq \{0..2\pi\}$\<close>
        have cs_sub: "(integral {a..b} f')\<^sup>2 \<le> (b-a) * integral {a..b} (\<lambda>t. (f' t)\<^sup>2)"
          if sub: "{a..b} \<subseteq> {0..2*pi}" and ab: "a < b" for a b
        proof -
          define \<mu> where "\<mu> \<equiv> integral {a..b} f' / (b-a)"
          have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {a..b}" by (rule f'2_int_sub[OF sub])
          have int1: "(\<lambda>t. - (2 * \<mu>) * f' t) integrable_on {a..b}"
            using integrable_cmul[OF f'_int_sub[OF sub], of "- (2 * \<mu>)"] by (simp add: scaleR_conv_of_real)
          have sub_int: "(\<lambda>t. (f' t - \<mu>)\<^sup>2) integrable_on {a..b}"
            using integrable_add[OF f'2I integrable_add[OF int1 integrable_const_ivl]]
            by (simp add: power2_eq_square algebra_simps)
          have "0 \<le> integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2)"
            by (rule integral_nonneg[OF sub_int]) (simp add: zero_le_power2)
          also have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                integral {a..b} (\<lambda>t. (f' t)\<^sup>2) + (- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b-a))"
          proof -
            have "integral {a..b} (\<lambda>t. (f' t - \<mu>)\<^sup>2) =
                  integral {a..b} (\<lambda>t. (f' t)\<^sup>2 + (- (2 * \<mu>) * f' t + \<mu>\<^sup>2))"
              by (rule integral_cong) (simp add: power2_eq_square algebra_simps)
            also have "\<dots> = integral {a..b} (\<lambda>t. (f' t)\<^sup>2) +
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2)"
              by (rule integral_add[OF f'2I integrable_add[OF int1 integrable_const_ivl]])
            also have "integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t + \<mu>\<^sup>2) =
                  integral {a..b} (\<lambda>t. - (2 * \<mu>) * f' t) + integral {a..b} (\<lambda>t. \<mu>\<^sup>2)"
              by (rule integral_add[OF int1 integrable_const_ivl])
            finally show ?thesis using ab by simp
          qed
          also have "- (2 * \<mu>) * integral {a..b} f' + \<mu>\<^sup>2 * (b-a) = - (integral {a..b} f')\<^sup>2 / (b-a)"
            using ab unfolding \<mu>_def by (simp add: power2_eq_square divide_simps)
          finally show ?thesis using ab by (simp add: pos_divide_le_eq mult.commute)
        qed
        show ?thesis
        proof (cases "c \<le> x")
          case True
          with cs_sub c_in xin ftc_sub show ?thesis by fastforce
        next
          case False
          with c_in xin show ?thesis by (simp add: cs_sub ftc_sub power2_commute)
        qed
      qed
      define F where "F \<equiv> \<lambda>x. integral {0..x} (\<lambda>t. (f' t)\<^sup>2)"
      have F_cont: "continuous_on {0..2*pi} F"
        unfolding F_def by (rule indefinite_integral_continuous_1[OF f'2])
      have F_eq: "integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2) = \<bar>F x - F c\<bar>"
        if "x \<in> {0..2*pi}" for x
      proof (cases "c \<le> x")
        case True
        have sub: "{c..x} \<subseteq> {0..2*pi}" using c_in that True by auto
        have "integral {0..c} (\<lambda>t. (f' t)\<^sup>2) + integral {c..x} (\<lambda>t. (f' t)\<^sup>2) =
                integral {0..x} (\<lambda>t. (f' t)\<^sup>2)"
          by (metis Henstock_Kurzweil_Integration.integral_combine True atLeastatMost_subset_iff f'2
              integrable_on_subinterval order_refl sub)
        moreover have "0 \<le> integral {c..x} (\<lambda>t. (f' t)\<^sup>2)"
          by (metis integral_nonneg not_integrable_integral order.refl zero_le_power2)
        ultimately show ?thesis using True by (simp add: F_def min_def max_def)
      next
        case False
        hence xc: "x \<le> c" by simp
        have sub: "{x..c} \<subseteq> {0..2*pi}" using c_in that xc by auto
        have "integral {0..x} (\<lambda>t. (f' t)\<^sup>2) + integral {x..c} (\<lambda>t. (f' t)\<^sup>2) 
                  = integral {0..c} (\<lambda>t. (f' t)\<^sup>2)"
          by (metis Henstock_Kurzweil_Integration.integral_combine atLeastatMost_subset_iff f'2
              integrable_subinterval_real order.refl sub xc)
        moreover have "0 \<le> integral {x..c} (\<lambda>t. (f' t)\<^sup>2)"
          by (metis integral_nonneg not_integrable_integral order.refl zero_le_power2)
        ultimately show ?thesis using xc by (simp add: F_def min_def max_def)
      qed
      have "((\<lambda>x. \<bar>F x - F c\<bar>) \<longlongrightarrow> 0) (at c within {0..2*pi})"
        by (metis F_cont LIM_zero_iff c_in continuous_on_def tendsto_rabs_zero)
      then have f'2_int_tends_0: "((\<lambda>x. integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)) \<longlongrightarrow> 0) (at c within {0..2*pi})"
        by (smt (verit, best) F_eq Lim_cong_within)
      have "\<forall>\<^sub>F x in at c. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> < 2"
        by real_asymp
      then have sinc_ratio_bounded:
        "\<forall>\<^sub>F x in at c within {0..2*pi}. \<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2"
        by (metis (no_types, lifting) UNIV_I eventually_at_topological less_imp_le)
          \<comment> \<open>Now combine everything.\<close>
      show "(g \<longlongrightarrow> 0) (at c within {0..2*pi})"
      proof (rule Lim_null_comparison[where g = "\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"])
        have mem: "\<forall>\<^sub>F x in at c within {0..2*pi}. x \<in> {0..2*pi}"
          unfolding at_within_def eventually_inf_principal by simp
        show "\<forall>\<^sub>F x in at c within {0..2*pi}. norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
        proof (rule eventually_mono[OF eventually_conj[OF sinc_ratio_bounded mem]])
          fix x assume H: "\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar> \<le> 2 \<and> x \<in> {0..2*pi}"
          have "\<bar>g x\<bar> = (f x - f c)\<^sup>2 * \<bar>cos (x - c)\<bar> / \<bar>sin (x - c)\<bar>"
            using g_eq2 by (simp add: abs_mult)
          also have "\<dots> \<le> (f x - f c)\<^sup>2 * 1 / \<bar>sin (x - c)\<bar>"
            by (simp add: Groups.mult_ac(2) divide_right_mono mult_left_le_one_le)
          also have "\<dots> = (f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar>" by simp
          also have "\<dots> \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
          proof -
            have sub: "{min c x..max c x} \<subseteq> {0..2*pi}" using c_in H by auto
            have f'2I: "(\<lambda>t. (f' t)\<^sup>2) integrable_on {min c x..max c x}"
              by (rule integrable_subinterval_real[OF f'2 sub])
            show ?thesis
            proof (cases "sin (x - c) = 0")
              case False
              define I where "I = integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)"
              have Ige: "I \<ge> 0"
                unfolding I_def by (rule integral_nonneg[OF f'2I]) auto
              have "(f x - f c)\<^sup>2 / \<bar>sin (x - c)\<bar> \<le> (\<bar>x - c\<bar> / \<bar>sin (x - c)\<bar>) * I"
                using H by (simp add: I_def cs_bound divide_right_mono)
              also have "\<dots> \<le> 2 * I"
                by (meson H Ige mult_mono order.refl zero_le_numeral)
              finally show ?thesis unfolding I_def .
            qed (use integral_nonneg[OF f'2I] in auto)
          qed
          finally show "norm (g x) \<le> 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)" by simp
        qed
        show "((\<lambda>x. 2 * integral {min c x..max c x} (\<lambda>t. (f' t)\<^sup>2)) \<longlongrightarrow> 0) (at c within {0..2*pi})"
          using tendsto_mult_right_zero[OF f'2_int_tends_0] by simp
      qed
    qed
  qed
qed

text \<open>The integral over mainly trouble-free intervals:
    we only need \<open>sin(x - a) \<noteq> 0\<close> on the open interior, allowing zeros at the endpoints.\<close>

lemma g'_absint:
  assumes "c \<le> d" and cd_sub: "{c..d} \<subseteq> {0..2*pi}" and sin_nz: "\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0"
  shows "g' absolutely_integrable_on {c..d}"
proof -
  have f'2_abs: "(\<lambda>x. (f' x)\<^sup>2) absolutely_integrable_on {0..2*pi}"
    by (rule abs_absolutely_integrableI_1[OF f'2]) (simp add: integrable_eq[OF f'2])
  have ffa_abs: "(\<lambda>x. (f x - f a)\<^sup>2) absolutely_integrable_on {0..2*pi}"
    by (rule absolutely_integrable_continuous_real)
      (intro continuous_intros contf)
  have g'_int_sub: "g' integrable_on {u..v}" if uv_sub: "{u..v} \<subseteq> {c<..<d}" for u v
  proof (cases "u \<le> v")
    case True
    then have uv_mem: "u \<in> {c<..<d}" "v \<in> {c<..<d}" and  uv_2pi: "{u..v} \<subseteq> {0..2*pi}"
      using uv_sub cd_sub by auto
    have sin_nz': "sin (x - a) \<noteq> 0" if "x \<in> {u..v}" for x
      using sin_nz that uv_sub by blast
    show ?thesis
      using has_integral_integrable[OF trouble_free[OF True uv_2pi sin_nz']] by auto
  qed (simp add: not_le integrable_on_empty)
  have g'_int: "g' integrable_on {c'..d'}" if "{c'..d'} \<subseteq> {c<..<d}" for c' d'
    using \<open>{c'..d'} \<subseteq> {c<..<d}\<close> g'_int_sub by blast
  have abs_g_cont: \<open>continuous_on {0..2 * pi} (\<lambda>x. \<bar>g x\<bar>)\<close>
    by (intro continuous_intros g_cont)
  obtain h where h_abs: "h absolutely_integrable_on {c..d}" 
    and h_bounded: "(\<forall>x\<in>{c..d}. g' x \<le> h x) \<or> (\<forall>x\<in>{c..d}. h x \<le> g' x)"
    using absolutely_integrable_on_subinterval[OF f'2_abs cd_sub]
    by (simp add: g'_def) 
  show ?thesis
  proof (intro g'_int absolutely_integrable_improper [of c d , unfolded box_real])
    obtain w where "0 \<le> w" "w \<le> 2*pi" and w: "\<forall>y. 0\<le>y \<longrightarrow> y \<le> 2*pi \<longrightarrow> \<bar>g y\<bar> \<le> \<bar>g w\<bar>"
      using continuous_attains_sup [of \<open>{0..2*pi}\<close> \<open>\<lambda>x. \<bar>g x\<bar>\<close>]
      by (metis Arg2pi abs_g_cont atLeastAtMost_iff compact_Icc empty_iff less_eq_real_def)
    show "bounded {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
    proof (rule boundedI)
      fix x assume "x \<in> {integral {c'..d'} g' |c' d'. {c'..d'} \<subseteq> {c<..<d}}"
      then obtain c' d' where cd': "{c'..d'} \<subseteq> {c<..<d}" and xeq: "x = integral {c'..d'} g'"
        by auto
      show "norm x \<le> 2 * \<bar>g w\<bar>"
      proof (cases "c' \<le> d'")
        case True
        have sub_2pi: "{c'..d'} \<subseteq> {0..2*pi}"
          using cd' cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
        have "sin (t-a) \<noteq> 0" if "t \<in> {c'..d'}" for t
          using that cd' sin_nz by (meson greaterThanLessThan_subseteq_atLeastAtMost_iff subsetD)
        then have "integral {c'..d'} g' = g d' - g c'"
          using True sub_2pi trouble_free by blast
        then have "\<bar>x\<bar> \<le> \<bar>g d'\<bar> + \<bar>g c'\<bar>"
          using xeq by linarith
        also have "\<dots> \<le> \<bar>g w\<bar> + \<bar>g w\<bar>"
          by (metis True w add_mono atLeastatMost_subset_iff order_trans sub_2pi)
        also have "\<dots> = 2 * \<bar>g w\<bar>" by algebra
        finally show ?thesis by (simp add: xeq)
      qed (simp add: xeq)
    qed
  qed (use h_abs h_bounded in auto)
qed

lemma mainly_trouble_free: 
  assumes "c \<le> d" and cd_sub: "{c..d} \<subseteq> {0..2*pi}" 
    and sin_nz: "\<And>x. x \<in> {c<..<d} \<Longrightarrow> sin (x - a) \<noteq> 0"
  shows "(g' has_integral g d - g c) {c..d}"
proof -
  have g'_int: "g' integrable_on {c..d}"
    using assms g'_absint set_lebesgue_integral_eq_integral(1) by blast
  have g_cont_cd: "continuous_on {c..d} g"
    using continuous_on_subset[OF g_cont cd_sub] .
  have goal: "integral {c..d} g' = g d - g c"
  proof (cases "c < d")
    case True
      \<comment> \<open>Pick sequences $c_n \to c$ and $d_n \to d$ from inside $(c,d)$\<close>
    define c_n where "c_n \<equiv> \<lambda>n. c + (d - c) / (real n + 2)"
    define d_n where "d_n \<equiv> \<lambda>n. d - (d - c) / (real n + 2)"
    have pos: "0 < (d - c) / (real n + 2)" for n
      using True by auto
    have lt_dc: "(d - c) / (real n + 2) < d - c" for n
      using True by (simp add: divide_less_eq)
    have c_n_le_d_n: "c_n n \<le> d_n n" for n
    proof -
      have "c * real n \<le> d * real n"
        using True by (intro mult_right_mono) auto
      then have "2 * ((d - c) / (real n + 2)) \<le> d - c"
        using True by (simp add: field_simps)
      then show ?thesis unfolding c_n_def d_n_def by linarith
    qed
    have frac_lim: "(\<lambda>n. (d - c) / (real n + 2)) \<longlonglongrightarrow> 0"
    proof (rule real_tendsto_sandwich)
      show "\<forall>\<^sub>F n in sequentially. 0 \<le> (d - c) / (real n + 2)"
        using True by (intro always_eventually allI) (auto simp: field_simps)
      show "\<forall>\<^sub>F n in sequentially. (d - c) / (real n + 2) \<le> (d - c) * (1 / real n)"
        using True by (intro eventually_sequentiallyI[of 1]) (auto simp: field_simps)
    qed (auto simp: lim_const_over_n)
    have c_n_lim: "c_n \<longlonglongrightarrow> c"
      unfolding c_n_def using tendsto_add[OF tendsto_const frac_lim] by simp
    have d_n_lim: "d_n \<longlonglongrightarrow> d"
      unfolding d_n_def using tendsto_diff[OF tendsto_const frac_lim] by simp
        \<comment> \<open>On each $\{c_n..d_n\}$, \<open>trouble_free\<close> applies\<close>
    have c_n_in: "c_n n \<in> {c<..<d}" and d_n_in: "d_n n \<in> {c<..<d}" for n
      using pos[of n] lt_dc[of n] unfolding c_n_def d_n_def by auto
    have sub_n: "{c_n n..d_n n} \<subseteq> {c<..<d}" for n
      using c_n_in[of n] d_n_in[of n] c_n_le_d_n[of n] by auto
    have sub_2pi_n: "{c_n n..d_n n} \<subseteq> {0..2*pi}" for n
      using sub_n[of n] cd_sub greaterThanLessThan_subseteq_atLeastAtMost_iff by blast
    have sin_nz_n: "sin (x - a) \<noteq> 0" if "x \<in> {c_n n..d_n n}" for n x
      using that sub_n[of n] sin_nz
      by (meson greaterThanLessThan_subseteq_atLeastAtMost_iff subsetD)
    have tf_n: "(g' has_integral g (d_n n) - g (c_n n)) {c_n n..d_n n}" for n
      using trouble_free[OF c_n_le_d_n sub_2pi_n sin_nz_n] .
    have int_n: "integral {c_n n..d_n n} g' = g (d_n n) - g (c_n n)" for n
      using tf_n[of n] by (rule integral_unique)
    have indef_cont: "continuous_on {c..d} (\<lambda>x. integral {c..x} g')"
      by (rule indefinite_integral_continuous_1[OF g'_int])
    have c_n_cd: "c_n n \<in> {c..d}" and  d_n_cd: "d_n n \<in> {c..d}" for n
      using c_n_in d_n_in less_eq_real_def by auto
    have split: "integral {c_n n..d_n n} g' = integral {c..d_n n} g' - integral {c..c_n n} g'" for n
    proof -
      have cn_le: "c \<le> c_n n" using c_n_in[of n] by auto
      have int_cdn: "g' integrable_on {c..d_n n}"
        by (rule integrable_subinterval_real[OF g'_int]) (use d_n_cd[of n] \<open>c\<le>d\<close> in auto)
      have "integral {c..c_n n} g' + integral {c_n n..d_n n} g' = integral {c..d_n n} g'"
        by (rule Henstock_Kurzweil_Integration.integral_combine[OF cn_le c_n_le_d_n int_cdn])
      then show ?thesis by linarith
    qed
    have "(\<lambda>n. integral {c..d_n n} g') \<longlonglongrightarrow> integral {c..d} g'"
      by (rule continuous_on_tendsto_compose[OF indef_cont d_n_lim])
        (use d_n_cd \<open>c\<le>d\<close> in \<open>auto intro: always_eventually\<close>)
    moreover have "(\<lambda>n. integral {c..c_n n} g') \<longlonglongrightarrow> integral {c..c} g'"
      by (rule continuous_on_tendsto_compose[OF indef_cont c_n_lim])
        (use c_n_cd \<open>c\<le>d\<close> in \<open>auto intro: always_eventually\<close>)
    ultimately have "(\<lambda>n. integral {c..d_n n} g' - integral {c..c_n n} g') \<longlonglongrightarrow> integral {c..d} g' - 0"
      by (intro tendsto_diff) simp_all
    then have int_lim: "(\<lambda>n. integral {c_n n..d_n n} g') \<longlonglongrightarrow> integral {c..d} g'"
      using split by simp
    moreover have "(\<lambda>n. g (d_n n) - g (c_n n)) \<longlonglongrightarrow> g d - g c"
    proof (intro tendsto_diff)
      obtain d_n_cd: "d_n n \<in> {c..d}" and c_n_cd: "c_n n \<in> {c..d}" for n
        using c_n_in d_n_in less_eq_real_def by force
      show "(\<lambda>n. g (d_n n)) \<longlonglongrightarrow> g d"
        by (rule continuous_on_tendsto_compose[OF g_cont_cd d_n_lim])
          (use d_n_cd \<open>c\<le>d\<close> in \<open>auto intro: always_eventually\<close>)
      show "(\<lambda>n. g (c_n n)) \<longlonglongrightarrow> g c"
        by (rule continuous_on_tendsto_compose[OF g_cont_cd c_n_lim])
          (use c_n_cd \<open>c\<le>d\<close> in \<open>auto intro: always_eventually\<close>)
    qed
    ultimately show ?thesis
      using int_n LIMSEQ_unique by auto
  qed (use \<open>c\<le>d\<close> in auto)
  show ?thesis
    using integrable_integral[OF g'_int] goal by auto
qed

end

theorem Wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes f'hsd: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and feq: "f (2*pi) = f 0"
    and f0: "(f has_integral 0) {0..2*pi}"
    and f'2: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..2*pi}"
  shows "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    and "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    and "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
         \<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
proof -
  have contf: \<open>continuous_on {0..2*pi} f\<close>
  proof (rule continuous_on_eq)
    show \<open>continuous_on {0..2*pi} (\<lambda>x. integral {0..x} f' + f 0)\<close>
      using f'hsd [of \<open>2*pi\<close>] 
      by (intro continuous_on_add indefinite_integral_continuous_1  continuous_on_const) auto
    show \<open>\<And>x. x \<in> {0..2*pi} \<Longrightarrow> integral {0..x} f' + f 0 = f x\<close>
      using f'hsd by (auto simp: has_integral_integrable_integral)
  qed
  define h where "h \<equiv> \<lambda>x. f (x + pi) - f x"
  have hcont: "continuous_on {0..pi} h"
    unfolding h_def by (intro continuous_intros continuous_on_compose2 [OF contf]) auto
  have heq: "h 0 + h pi = 0"
    unfolding h_def using feq by simp
  have iv: "is_interval (h ` {0..pi})"
    using is_interval_connected_1 connected_continuous_image [OF hcont connected_Icc]
    by blast
  have"h 0 \<in> h ` {0..pi}"  "h pi \<in> h ` {0..pi}"
    using pi_gt_zero by auto
  with heq obtain a where "a \<in> {0..pi}" "h a = 0"
    by (smt (verit, best) imageE is_interval_1 iv)
  then obtain a where a: "0 \<le> a" "a < pi" "f (a + pi) = f a"
    using pi_gt_zero heq h_def by (force simp: less_eq_real_def)
  interpret W f f' a
    using W.intro a assms by blast
  show "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_on_power contf)

  have sin_nz_1: "sin (x - a) \<noteq> 0" if "a + pi < x" "x < 2*pi" for x
    by (smt (verit) \<open>0 \<le> a\<close> sin_lt_zero that)
  have sin_nz_2: "sin (x - a) \<noteq> 0" if "a < x" "x < a + pi" for x
    by (smt (verit, ccfv_threshold) sin_gt_zero that)
  have sin_nz_3: "sin (x - a) \<noteq> 0" if "0 < x" "x < a" for x
    using \<open>a < pi\<close> sin_zero_pi_iff that by auto
      \<comment> \<open>Apply \<open>mainly_trouble_free\<close> on three intervals.\<close>
  have int1: "(g' has_integral g (2*pi) - g (a + pi)) {a + pi..2*pi}"
    by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_1 in auto)
  have int2: "(g' has_integral g (a + pi) - g a) {a..a + pi}"
    by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_2 in auto)
  have int3: "(g' has_integral g a - g 0) {0..a}"
    by (rule mainly_trouble_free) (use \<open>0 \<le> a\<close> \<open>a < pi\<close> sin_nz_3 in auto)
      \<comment> \<open>Combine the three integrals using \<open>has_integral_combine\<close>.\<close>
  have api_le: "a \<le> a + pi" and api_le2: "a + pi \<le> 2*pi"
    using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
  have a_le_2pi: "a \<le> 2*pi" using \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
  have int12: "(g' has_integral (g (a + pi) - g a) + (g (2*pi) - g (a + pi))) {a..2*pi}"
    by (rule has_integral_combine[OF api_le api_le2 int2 int1])
  have int_all: "(g' has_integral (g a - g 0) + ((g (a + pi) - g a) + (g (2*pi) - g (a + pi)))) {0..2*pi}"
    by (rule has_integral_combine[OF \<open>0 \<le> a\<close> a_le_2pi int3 int12])
      \<comment> \<open>Simplify: the telescoping sum gives $g(2\pi) - g(0)$.\<close>
  have int_all': "(g' has_integral g (2*pi) - g 0) {0..2*pi}"
    using int_all by (simp add: algebra_simps)
      \<comment> \<open>Show $g(2\pi) = g(0)$, so the integral of $g'$ is $0$.\<close>
  have "g (2*pi) = g 0"
    unfolding g_def using feq by (simp add: tan_def)
  hence g'_zero: "(g' has_integral 0) {0..2*pi}"
    using int_all' by simp
      \<comment> \<open>Extract the inequality from $\int g' = 0$.\<close>
  have ffa_int: "(\<lambda>x. (f x - f a)\<^sup>2) integrable_on {0..2*pi}"
    by (intro integrable_continuous_interval continuous_intros contf)
  have g'_int: "g' integrable_on {0..2*pi}"
    using g'_zero by (auto simp: has_integral_integrable_integral)
  have diff_int: "((\<lambda>x. (f' x)\<^sup>2 - g' x) has_integral integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2) - 0) {0..2*pi}"
    by (rule has_integral_diff[OF integrable_integral[OF f'2] g'_zero])
  have diff_eq: "(f' x)\<^sup>2 - g' x = (f x - f a)\<^sup>2 + (f' x - (f x - f a) / tan (x - a))\<^sup>2" for x
    unfolding g'_def by (simp add: algebra_simps)
  have diff_ge: "(f' x)\<^sup>2 - g' x \<ge> (f x - f a)\<^sup>2" for x
    unfolding diff_eq by (simp add: zero_le_power2)
  have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x)"
    by (rule integral_le[OF ffa_int]) (use diff_int has_integral_integrable_integral in \<open>auto intro: diff_ge\<close>)
  also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    using diff_int has_integral_integrable_integral by auto
  finally have ineq_ffa: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)" .
      \<comment> \<open>Show $\int f(x)^2 \le \int (f(x)-f(a))^2$ using $\int f = 0$.\<close>
  have "(f x)\<^sup>2 \<le> (f x - f a)\<^sup>2 + 2 * f a * f x - (f a)\<^sup>2" for x
    by (simp add: power2_eq_square algebra_simps)
  have fx_eq: "(f x)\<^sup>2 = (f x - f a)\<^sup>2 + 2 * f a * f x - (f a)\<^sup>2" for x
    by (simp add: power2_eq_square algebra_simps)
  have f_int: "f integrable_on {0..2*pi}"
    by (rule integrable_continuous_interval[OF contf])
  have f_integral_0: "integral {0..2*pi} f = 0"
    using f0 by (auto simp: has_integral_integrable_integral)
  have ffa_eq: "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2)
        = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - 2 * f a * integral {0..2*pi} f + (f a)\<^sup>2 * (2*pi)"
  proof -
    have eq: "(f x - f a)\<^sup>2 = (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2" for x
      by (simp add: power2_eq_square algebra_simps)
    have fx2_int: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..2*pi}"
      by (intro integrable_continuous_interval continuous_intros contf)
    have ffa_2fa_int: "(\<lambda>x. 2 * f a * f x) integrable_on {0..2*pi}"
      using f_int integrable_on_mult_right by blast
    have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x + (f a)\<^sup>2)"
      by (simp add: eq)
    also have "\<dots> = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) + integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2)"
      by (rule Henstock_Kurzweil_Integration.integral_add)
        (auto intro: integrable_diff fx2_int ffa_2fa_int)
    also have "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2 - 2 * f a * f x) =
        integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) - integral {0..2*pi} (\<lambda>x. 2 * f a * f x)"
      by (rule Henstock_Kurzweil_Integration.integral_diff[OF fx2_int ffa_2fa_int])
    also have "integral {0..2*pi} (\<lambda>x. 2 * f a * f x) = 2 * f a * integral {0..2*pi} f"
      using integral_cmul by simp
    also have "integral {0..2*pi} (\<lambda>x. (f a)\<^sup>2) = (f a)\<^sup>2 * (2*pi)"
      by simp
    finally show ?thesis by linarith
  qed
  with f_integral_0 
  have ffa_le: "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2)"
    by auto
  thus "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
    using ineq_ffa by linarith
  show "\<exists>c a. \<forall>x \<in> {0..2*pi}. f x = c * sin (x - a)"
    if eq_hyp: "integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
  proof -    \<comment> \<open>From the equality, all intermediate inequalities are equalities.\<close>
    have fa0: "f a = 0"
      by (smt (verit, best) a eq_hyp f_integral_0 ffa_eq ffa_le ineq_ffa mult_eq_0_iff
          power_eq_0_iff)
    \<comment> \<open>Step 2: The "rest" term integrates to 0.\<close>
    define rest where "rest \<equiv> \<lambda>x. f' x - (f x - f a) / tan (x - a)"
    have diff_eq: "(f' x)\<^sup>2 - g' x = (f x - f a)\<^sup>2 + (rest x)\<^sup>2" for x
      unfolding g'_def rest_def by (simp add: algebra_simps)
    have rest_sq_int: "(\<lambda>x. (rest x)\<^sup>2) integrable_on {0..2*pi}"
    proof -
      have diff_int: "(\<lambda>x. (f' x)\<^sup>2 - g' x) integrable_on {0..2*pi}"
        using has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
              has_integral_integrable by blast
      have eq: "(\<lambda>x. (rest x)\<^sup>2) = (\<lambda>x. (f' x)\<^sup>2 - g' x - (f x - f a)\<^sup>2)"
        by (rule ext) (use diff_eq in \<open>simp add: algebra_simps\<close>)
      show ?thesis unfolding eq
        by (rule integrable_diff[OF diff_int ffa_int])
    qed
    have rest_sq_zero: "integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2) = 0"
    proof -
      have "integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x) =
        integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2)"
        using has_integral_diff[OF integrable_integral[OF f'2] g'_zero]
              has_integral_integrable_integral by auto
      moreover have "integral {0..2*pi} (\<lambda>x. (f' x)\<^sup>2 - g' x) =
        integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) + integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2)"
        using Henstock_Kurzweil_Integration.integral_add ffa_int local.diff_eq rest_sq_int by auto
      moreover have "integral {0..2*pi} (\<lambda>x. (f x - f a)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (f x)\<^sup>2)"
        using ffa_eq fa0 by simp
      ultimately show ?thesis using eq_hyp by linarith
    qed
    \<comment> \<open>Integral of $c \sin(x - a)$ via the fundamental theorem of calculus.\<close>
    have csin_integral: "integral {u..v} (\<lambda>x. c * sin (x - a)) =
        c * (cos (u - a) - cos (v - a))" if "u \<le> v" for u v c
    proof -
      have "((\<lambda>x. - (c * cos (x - a))) has_real_derivative c * sin (x - a)) (at x)" for x
        by (auto intro!: derivative_eq_intros simp: algebra_simps)
      hence hvd: "((\<lambda>x. - (c * cos (x - a))) has_vector_derivative c * sin (x - a))
        (at x within {u..v})" for x
        by (meson has_real_derivative_iff_has_vector_derivative has_vector_derivative_at_within)
      hence "((\<lambda>x. c * sin (x - a)) has_integral
        (- (c * cos (v - a)) - (- (c * cos (u - a))))) {u..v}"
        using that by (intro fundamental_theorem_of_calculus) auto
      thus ?thesis
        by (simp add: has_integral_integrable_integral algebra_simps)
    qed
    \<comment> \<open>Key fact: on intervals where $\sin(x-a) \neq 0$, @{term f} equals $c \sin(x-a)$.\<close>
    have key_fact: "\<exists>c. \<forall>x\<in>{u..v}. f x = c * sin (x - a)"
      if huv: "0 \<le> u" "u < v" "v \<le> 2*pi"
        and hsin: "\<And>x. x \<in> {u<..<v} \<Longrightarrow> sin (x - a) \<noteq> 0"
      for u v
    proof -
      \<comment> \<open>Open-interval version (to be proved later).\<close>
      have open_ver: "\<exists>c. \<forall>x\<in>{u<..<v}. f x = c * sin (x - a)"
      proof -
        \<comment> \<open>Step 1: $\int_u^v \mathit{rest}^2 = 0$ from $\int_0^{2\pi} \mathit{rest}^2 = 0$ and nonnegativity.\<close>
        have rest_sq_sub: "(\<lambda>x. (rest x)\<^sup>2) integrable_on {u..v}"
          by (rule integrable_subinterval_real[OF rest_sq_int])
             (use huv in auto)
        have "integral {u..v} (\<lambda>x. (rest x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (rest x)\<^sup>2)"
          by (simp add: huv integral_subset_le rest_sq_int rest_sq_sub)
        moreover have "0 \<le> integral {u..v} (\<lambda>x. (rest x)\<^sup>2)"
          by (simp add: integral_nonneg rest_sq_sub)
        ultimately have rest_sq_sub_zero: "integral {u..v} (\<lambda>x. (rest x)\<^sup>2) = 0"
          using rest_sq_zero by linarith
        \<comment> \<open>Step 2: $\mathit{rest} = 0$ a.e. on $\{u..v\}$ via Lebesgue theory.\<close>
        have rest_ae_zero: "AE x in lebesgue_on {u..v}. rest x = 0"
        proof -
          have uv_meas: "{u..v} \<in> sets lebesgue" by simp
          have rest_sq_leb: "integrable (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2)"
            by (simp add: absolutely_integrable_imp_integrable nonnegative_absolutely_integrable_1 rest_sq_sub)
          have "integral\<^sup>L (lebesgue_on {u..v}) (\<lambda>x. (rest x)\<^sup>2) = integral {u..v} (\<lambda>x. (rest x)\<^sup>2)"
            by (rule lebesgue_integral_eq_integral[OF rest_sq_leb uv_meas])
          thus ?thesis
            using integral_nonneg_eq_0_iff_AE[OF rest_sq_leb] rest_sq_sub_zero by simp
        qed
        \<comment> \<open>Step 3: $h(x) = f(x)/\sin(x-a)$ is constant on $(u,v)$.
           For any $\{s..t\} \subseteq (u,v)$, @{term h} is absolutely continuous and $h' = \mathit{rest}/\sin$ a.e.,
           so $h(t) - h(s) = \int_s^t \mathit{rest}/\sin = 0$.\<close>
        have h_const: "f s / sin (s - a) = f t / sin (t-a)"
          if hst: "s \<in> {u<..<v}" "t \<in> {u<..<v}" for s t
        proof (cases "s = t")
          case False
          \<comment> \<open>WLOG s < t\<close>
          define s' where "s' = min s t"
          define t' where "t' = max s t"
          have st': "u < s'" "t' < v" "s' < t'"
            using hst False unfolding s'_def t'_def by auto
          have st'_sub: "{s'..t'} \<subseteq> {u<..<v}"
            using st' by auto
          have st'_sub2: "{s'..t'} \<subseteq> {0..2*pi}"
            using st' huv by auto
          \<comment> \<open>$\sin(x - a) \neq 0$ on $\{s'..t'\}$\<close>
          have sin_nz_st: "sin (x - a) \<noteq> 0" if "x \<in> {s'..t'}" for x
            using hsin st'_sub that by auto
          \<comment> \<open>$h = f/\sin$ is absolutely continuous on $\{s'..t'\}$\<close>
          define h where "h \<equiv> \<lambda>x. f x / sin (x - a)"
          have ac_f: "absolutely_continuous_on {0..2*pi} f"
            using absolute_integral_absolutely_continuous_derivative_eq f'abs f'hsd by blast
          have ac_f_st: "absolutely_continuous_on {s'..t'} f"
            using absolutely_continuous_on_subset[OF ac_f st'_sub2] .
          \<comment> \<open>$1/\sin(x-a)$ is absolutely continuous on $\{s'..t'\}$ via a Lipschitz bound\<close>
          have ac_inv_sin: "absolutely_continuous_on {s'..t'} (\<lambda>x. inverse (sin (x - a)))"
          proof -
            \<comment> \<open>The derivative $-\cos/\sin^2$ is bounded on $\{s'..t'\}$ since $\sin$ is bounded away from $0$\<close>
            define deriv where "deriv \<equiv> \<lambda>x::real. - cos (x - a) / (sin (x - a))\<^sup>2"
            have cont_deriv: "continuous_on {s'..t'} deriv"
              unfolding deriv_def
              by (intro continuous_intros) (use sin_nz_st in auto)
            have bdd: "bounded (deriv ` {s'..t'})"
              using compact_continuous_image compact_imp_bounded cont_deriv by blast
            then obtain B where B: "\<And>x. x \<in> {s'..t'} \<Longrightarrow> \<bar>deriv x\<bar> \<le> B"
              by (meson bounded_real imageI)
            have lipschitz: "\<bar>inverse (sin (x - a)) - inverse (sin (y - a))\<bar> \<le> B * \<bar>x - y\<bar>"
              if hx: "s' \<le> x" "x \<le> t'" and hy: "s' \<le> y" "y \<le> t'" for x y
            proof -
              have deriv_at: "((\<lambda>x. inverse (sin (x - a))) has_real_derivative deriv z)
                              (at z within {s'..t'})"
                if hz: "z \<in> {s'..t'}" for z
                using sin_nz_st[OF hz] unfolding deriv_def power2_eq_square
                by (intro derivative_eq_intros | simp add: divide_inverse)+
              have "norm (inverse (sin (x - a)) - inverse (sin (y - a))) \<le> B * norm (x - y)"
              proof (rule field_differentiable_bound[OF convex_real_interval(5)])
              qed (use B hx hy deriv_at in auto)
              then show ?thesis by (simp add: real_norm_def)
            qed
            then show ?thesis
              by (intro Lipschitz_imp_absolutely_continuous strip; auto)
          qed
          have ac_h: "absolutely_continuous_on {s'..t'} h"
            using absolutely_continuous_on_mul[OF ac_f_st ac_inv_sin]
            by (simp add: divide_real_def h_def)
          \<comment> \<open>@{term h} has derivative $\mathit{rest}/\sin$ a.e. on $\{s'..t'\}$\<close>
          obtain k where negk: "negligible k"
                and derivf: "\<And>t. t \<in> {0..2*pi} - k \<Longrightarrow>
                  ((\<lambda>u. integral {0..u} f') has_vector_derivative f' t) (at t within {0..2*pi})"
            using f' has_vector_derivative_indefinite_integral by blast
          have f_eq: "f t = f 0 + integral {0..t} f'" if "t \<in> {0..2*pi}" for t
            using f'hsd[OF that] by (auto simp: has_integral_integrable_integral)
          have fderiv: "(f has_vector_derivative f' t) (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
          proof -
            have t02: "t \<in> {0..2*pi}" using that st'_sub2 by auto
            have "t \<in> {0..2*pi} - k" using that st'_sub2 by auto
            then have "((\<lambda>u. integral {0..u} f') has_vector_derivative f' t)
                       (at t within {0..2*pi})"
              using derivf by auto
            then have "((\<lambda>u. f u - f 0) has_vector_derivative f' t)
                       (at t within {0..2*pi})"
              using has_vector_derivative_transform_within t02
              by (smt (verit, best) f_eq has_vector_derivative_transform)
            then have "(f has_vector_derivative f' t) (at t within {0..2*pi})"
              using has_vector_derivative_diff_const by blast
            then show ?thesis
              by (rule has_vector_derivative_within_subset) (use st'_sub2 in auto)
          qed
          \<comment> \<open>Derivative of $h = f/\sin$ via the quotient rule\<close>
          have hderiv: "(h has_vector_derivative (f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2)
              (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
          proof -
            have fd: "(f has_real_derivative f' t) (at t within {s'..t'})"
              using fderiv that by (simp add: has_real_derivative_iff_has_vector_derivative)
            have sd: "((\<lambda>x. sin (x - a)) has_real_derivative cos (t-a))
                      (at t within {s'..t'})"
              by (auto intro!: derivative_eq_intros)
            have "((\<lambda>x. f x / sin (x - a)) has_real_derivative (f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2)
                  (at t within {s'..t'})"
              using DERIV_quotient[OF fd sd] sin_nz_st that
              by (simp add: power2_eq_square algebra_simps)
            then show ?thesis unfolding h_def
              by (simp add: has_real_derivative_iff_has_vector_derivative)
          qed
          \<comment> \<open>The derivative of @{term h} equals $\mathit{rest}/\sin$\<close>
          have hderiv_eq: "(f' t * sin (t-a) - f t * cos (t-a)) / (sin (t-a))\<^sup>2 = rest t / sin (t-a)"
            if "t \<in> {s'..t'}" for t
            using that unfolding rest_def fa0
            by (simp add: power2_eq_square divide_simps Multiseries_Expansion.tan_conv_sin_cos)
          have hderiv': "(h has_vector_derivative rest t / sin (t-a)) (at t within {s'..t'})"
            if "t \<in> {s'..t'} - k" for t
            using hderiv[OF that] hderiv_eq[of t] that by auto
          \<comment> \<open>$\mathit{rest} = 0$ a.e. on $\{u..v\}$, so obtain a negligible set @{term N}\<close>
          obtain N where negN: "negligible N" and restN: "\<And>x. x \<in> {u..v} - N \<Longrightarrow> rest x = 0"
          proof -
            from rest_ae_zero[unfolded eventually_ae_filter[of _ "lebesgue_on {u..v}"]]
            obtain N0 where N0: "N0 \<in> null_sets (lebesgue_on {u..v})"
              and sub: "{x \<in> space (lebesgue_on {u..v}). rest x \<noteq> 0} \<subseteq> N0"
              by auto
            have "negligible N0"
              using null_sets_restrict_space[of "{u..v}"] N0 negligible_iff_null_sets 
              by auto
            moreover have "rest x = 0" if "x \<in> {u..v} - N0" for x
              using sub that by (auto simp: space_lebesgue_on)
            ultimately show ?thesis using that by blast
          qed
          \<comment> \<open>@{term h} has derivative $0$ a.e. on $\{s'..t'\}$\<close>
          have hderiv_zero: "(h has_vector_derivative 0) (at t within {s'..t'})"
            if "t \<in> {s'..t'} - (k \<union> N)" for t
            using restN[of t] that st'_sub hderiv' using st'(2) by fastforce
          have neg_kN: "negligible (k \<union> N)"
            using negk negN by (rule negligible_Un)
          \<comment> \<open>By the FTC for AC functions: $h(t') - h(s') = \int 0 = 0$\<close>
          have "h t' - h s' = integral {s'..t'} (\<lambda>x. 0::real)"
            using fundamental_theorem_of_calculus_absolutely_continuous [OF neg_kN _ ac_h hderiv_zero]
            using st' by auto
          then have "h s' = h t'" by simp
          \<comment> \<open>Translate back to $f/\sin$\<close>
          then show ?thesis
            unfolding h_def s'_def t'_def by (auto split: if_splits)
        qed auto
        obtain x where "x \<in> {u<..<v}"
          using huv dense by (metis greaterThanLessThan_iff)
        with eq_divide_eq hsin h_const that show ?thesis
          by metis
      qed
      then obtain c where hc: "\<forall>x\<in>{u<..<v}. f x = c * sin (x - a)"
        by auto
      \<comment> \<open>Extend to the closed interval by continuity.\<close>
      have "f x - c * sin (x - a) = 0" if "x \<in> {u..v}" for x
      proof (rule continuous_constant_on_closure[of "{u<..<v}" "\<lambda>x. f x - c * sin (x - a)" 0])
        show "continuous_on (closure {u<..<v}) (\<lambda>x. f x - c * sin (x - a))"
          unfolding closure_greaterThanLessThan[OF huv(2)]
          by (intro continuous_intros continuous_on_subset[OF contf])
            (use huv in auto)
        show "\<And>y. y \<in> {u<..<v} \<Longrightarrow> f y - c * sin (y - a) = 0"
          using hc by simp
        show "x \<in> closure {u<..<v}"
          unfolding closure_greaterThanLessThan[OF huv(2)] using that by auto
      qed
      thus ?thesis by auto
    qed
    show ?thesis
    proof (cases "a=0")
      case True
      then show ?thesis
      proof -
        obtain c1 where c1: "\<forall>x\<in>{0..pi}. f x = c1 * sin (x - a)"
          using key_fact[of 0 pi] sin_nz_2 True pi_gt_zero by auto
        obtain c2 where c2: "\<forall>x\<in>{pi..2*pi}. f x = c2 * sin (x - a)"
          using key_fact[of pi "2*pi"] sin_nz_1 True pi_gt_zero by auto
        \<comment> \<open>Use $\int f = 0$ and \<open>csin_integral\<close> to show $c_1 = c_2$.\<close>
        have eq1: "integral {0..pi} f = c1 * (cos (0 - a) - cos (pi - a))"
          by (metis (lifting) integral_cong True add_0 api_le c1 csin_integral)
        have eq2: "integral {pi..2*pi} f = c2 * (cos (pi - a) - cos (2*pi - a))"
          by (metis (lifting) integral_cong True add_0 api_le2 c2 csin_integral)
        have int_split: "integral {0..2*pi} f = integral {0..pi} f + integral {pi..2*pi} f"
            using Henstock_Kurzweil_Integration.integral_combine[OF pi_ge_zero]
            by (metis True add_cancel_left_left api_le2 assms(3) integrable_on_def)
        have "integral {0..2*pi} f = 0"
          using f0 by (simp add: has_integral_integrable_integral)
        hence "c1 = c2" using True int_split eq1 eq2
          by (simp add: cos_two_pi cos_pi)
        then show ?thesis
          by (metis atLeastAtMost_iff c1 c2 nle_le)
      qed
    next
      case False
      then show ?thesis
      proof -
        have a_pos: "0 < a" using \<open>0 \<le> a\<close> False by auto
        \<comment> \<open>Three intervals where $\sin(x-a) \neq 0$\<close>
        obtain c1 where c1: "\<forall>x\<in>{0..a}. f x = c1 * sin (x - a)"
          using key_fact[of 0 a] sin_nz_3 a_pos \<open>a < pi\<close> by auto
        obtain c2 where c2: "\<forall>x\<in>{a..a+pi}. f x = c2 * sin (x - a)"
          using key_fact[of a "a+pi"] sin_nz_2 a_pos \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
        obtain c3 where c3: "\<forall>x\<in>{a+pi..2*pi}. f x = c3 * sin (x - a)"
          using key_fact[of "a+pi" "2*pi"] sin_nz_1 \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
        \<comment> \<open>Show $c_1 = c_3$ using $f(2\pi) = f(0)$\<close>
        have sin_a_nz: "sin a \<noteq> 0"
          using sin_gt_zero[OF a_pos \<open>a < pi\<close>] by (simp add: less_imp_le)
        have f0_eq: "f 0 = c1 * sin (0 - a)"
          using c1 \<open>0 \<le> a\<close> by auto
        have f2pi_eq: "f (2*pi) = c3 * sin (2*pi - a)"
          using c3 \<open>0 \<le> a\<close> \<open>a < pi\<close> by auto
        \<comment> \<open>Compute integrals on each interval\<close>
        have eq1: "integral {0..a} f = c1 * (cos (0 - a) - cos (a - a))"
          by (metis (no_types, lifting) integral_cong \<open>0 \<le> a\<close> c1 csin_integral)
        have eq2: "integral {a..a+pi} f = c2 * (cos (a - a) - cos ((a+pi) - a))"
          by (metis (no_types, lifting) api_le integral_cong c2 csin_integral)
        have eq3: "integral {a+pi..2*pi} f = c3 * (cos ((a+pi) - a) - cos (2*pi - a))"
          by (metis (mono_tags, lifting) integral_cong api_le2 c3 csin_integral)
        \<comment> \<open>Split the integral into three parts\<close>
        have f_int: "f integrable_on {0..2*pi}"
          using f0 has_integral_integrable by blast
        have "a \<le> a + pi" "a + pi \<le> 2 * pi" using pi_gt_zero \<open>a < pi\<close> by linarith+
        then have int_split: "integral {0..2*pi} f = integral {0..a} f + integral {a..a+pi} f + integral {a+pi..2*pi} f"
          by (metis Henstock_Kurzweil_Integration.integral_combine a(1) pi_ge_zero add_increasing 
              atLeastatMost_subset_iff f_int integrable_on_subinterval order_refl)
        \<comment> \<open>Use $\int f = 0$ to show $c_1 = c_2$\<close>
        have "integral {0..2*pi} f = 0"
          using f0 by (simp add: has_integral_integrable_integral)
        hence sum_eq: "c1 * (cos (0 - a) - cos (a - a)) + c2 * (cos (a - a) - cos ((a+pi) - a)) +
          c3 * (cos ((a+pi) - a) - cos (2*pi - a)) = 0"
          using int_split eq1 eq2 eq3 by linarith
        have "c1 * (cos a - 1) + 2 * c2 + c1 * (- 1 - cos a) = 0"
          using f0_eq f2pi_eq feq sin_a_nz sum_eq by fastforce
        hence c12_eq: "c1 = c2"
          by (simp add: algebra_simps)
        show "\<exists>c a. \<forall>x\<in>{0..2 * pi}. f x = c * sin (x - a)"
          using f0_eq feq sin_a_nz c1 c2 c3 c12_eq by fastforce
      qed
    qed
  qed
qed

corollary scaled_Wirtinger_inequality:
  fixes f f' :: "real \<Rightarrow> real"
  assumes f': "\<And>x. x \<in> {0..1} \<Longrightarrow> (f' has_integral (f x - f 0)) {0..x}"
    and "f 1 = f 0"
    and f_int: "(f has_integral 0) {0..1}"
    and f'_int: "(\<lambda>x. (f' x)\<^sup>2) integrable_on {0..1}"
  shows "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..1}"
    and "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    and "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
      \<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)"
proof -
  define g where "g \<equiv> \<lambda>x. f (x / (2*pi))"
  define g' where "g' \<equiv> \<lambda>x. (1/(2*pi)) * f' (x / (2*pi))"
  have twopi_pos: "2 * pi > 0" and twopi_nz: "2 * pi \<noteq> 0"
    and inv_twopi_pos: "1/(2*pi) > 0" and inv_twopi_nz: "1/(2*pi) \<noteq> (0::real)"
    using pi_gt_zero by auto
  have img: "(\<lambda>x. x / (1/(2*pi))) ` {0..1} = {0..2*pi}"
    using image_divide_atLeastAtMost[OF inv_twopi_pos] by simp
  have prec1: "\<And>x. x \<in> {0..2*pi} \<Longrightarrow> (g' has_integral (g x - g 0)) {0..x}"
  proof -
    fix x :: real assume x: "x \<in> {0..2*pi}"
    have *: "((\<lambda>s. f' (1/(2*pi) * s)) has_integral (2*pi) *\<^sub>R (f (x/(2*pi)) - f 0))
                 ((\<lambda>s. s / (1/(2*pi))) ` {0..x/(2*pi)})"
      using x has_integral_stretch_real[OF f' inv_twopi_nz] inv_twopi_pos by simp
    have **: "((\<lambda>s. f' (s/(2*pi))) has_integral (2*pi) * (f (x/(2*pi)) - f 0)) {0..x}"
      using * image_divide_atLeastAtMost[OF inv_twopi_pos, of 0 "x/(2*pi)"]
      using twopi_pos by (simp add: field_simps)
    have val: "1/(2*pi) * ((2*pi) * (f (x/(2*pi)) - f 0)) = f (x/(2*pi)) - f 0"
      using twopi_nz by simp
    show "(g' has_integral (g x - g 0)) {0..x}"
      using has_integral_mult_right[OF **, of "1/(2*pi)"] twopi_nz 
      unfolding g'_def g_def val by (simp add: field_simps)
  qed
  have prec2: "g (2*pi) = g 0"
    unfolding g_def using assms(2) by simp
  have prec3: "(g has_integral 0) {0..2*pi}"
    using has_integral_stretch_real_iff[OF inv_twopi_nz, of f 0 0 1]  f_int g_def img by auto
  have int: "(\<lambda>x. (f' (x/(2*pi)))\<^sup>2) integrable_on {0..2*pi}"
    using f'_int integrable_stretch_real[OF _ inv_twopi_nz, of "\<lambda>x. (f' x)\<^sup>2" 0 1] img 
    by (simp add: field_simps)
  then have prec4: "(\<lambda>x. (g' x)\<^sup>2) integrable_on {0..2*pi}"
    unfolding g'_def power_mult_distrib
    using integrable_on_cmult_left[OF int, of "(1/(2*pi))\<^sup>2"] by (simp add: algebra_simps)
  text \<open>Apply unscaled Wirtinger inequality\<close>
  have W1: "(\<lambda>x. (g x)\<^sup>2) integrable_on {0..2*pi}"
    and W2: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) \<le> integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2)"
    and W3: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) \<Longrightarrow>
         \<exists>c a. \<forall>x \<in> {0..2*pi}. g x = c * sin (x - a)"
    using Wirtinger_inequality[OF prec1 prec2 prec3 prec4] by auto
  text \<open>Transfer conclusions back to scaled domain\<close>
  have g_unfold: "\<And>x. (g x)\<^sup>2 = (f (1/(2*pi) * x))\<^sup>2"
    unfolding g_def by (simp add: field_simps)
  have g'_unfold: "\<And>x. (g' x)\<^sup>2 = (1/(2*pi))\<^sup>2 * (f' (1/(2*pi) * x))\<^sup>2"
    unfolding g'_def by (simp add: power_mult_distrib field_simps)
  text \<open>Show 1: integrability of $f(x)^2$ on $\{0..1\}$\<close>
  show int_f2: "(\<lambda>x. (f x)\<^sup>2) integrable_on {0..1}"
    using integrable_stretch_real_iff[OF inv_twopi_nz, of "\<lambda>x. (f x)\<^sup>2" 0 1] W1 g_def img by force 
  text \<open>Show 2: the scaled inequality\<close>
  have lhs_stretch: "integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (f (1/(2*pi) * x))\<^sup>2)
             = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
    using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (f x)\<^sup>2"] by simp
  have lhs: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = 2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2)"
    using lhs_stretch img inv_twopi_pos by (simp add: g_unfold)
  have rhs_stretch: "integral ((\<lambda>x. x / (1/(2*pi))) ` {0..1}) (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' (1/(2*pi) * x))\<^sup>2)
             = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
    using integral_stretch_real[OF inv_twopi_nz, of 0 1 "\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2"] by simp
  have factor_out: "integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2) = (1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    by (simp add: integral_mult_right)
  have "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) = (1 / \<bar>1/(2*pi)\<bar>) *\<^sub>R integral {0..1} (\<lambda>x. (1/(2*pi))\<^sup>2 * (f' x)\<^sup>2)"
    using img rhs_stretch by (simp add: g'_unfold)
  also have "\<dots> = 2*pi * ((1/(2*pi))\<^sup>2 * integral {0..1} (\<lambda>x. (f' x)\<^sup>2))"
    using inv_twopi_pos factor_out by simp
  finally have rhs: "integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2) = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    by (simp add: power2_eq_square)
  from W2 lhs rhs
  have ineq: "2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2) \<le> (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    by linarith
  then have "(2*pi)\<^sup>2 * integral {0..1} (\<lambda>x. (f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    using twopi_pos by (simp add: power2_eq_square field_simps)
  then show "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) \<le> integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    by (simp add: power_mult_distrib)
  text \<open>Show 3: the equality case\<close>
  show "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2) \<Longrightarrow>
      \<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)"
  proof -
    assume "integral {0..1} (\<lambda>x. (2*pi * f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
    then have "(2*pi)\<^sup>2 * integral {0..1} (\<lambda>x. (f x)\<^sup>2) = integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      by (simp add: power_mult_distrib)
    then have "2*pi * integral {0..1} (\<lambda>x. (f x)\<^sup>2) = (1/(2*pi)) * integral {0..1} (\<lambda>x. (f' x)\<^sup>2)"
      using twopi_pos by (simp add: power2_eq_square field_simps)
    then have weq: "integral {0..2*pi} (\<lambda>x. (g x)\<^sup>2) = integral {0..2*pi} (\<lambda>x. (g' x)\<^sup>2)"
      using lhs rhs by linarith
    from W3[OF weq] obtain c a where ca: "\<forall>x \<in> {0..2*pi}. g x = c * sin (x - a)" by auto
    have "f x = c * sin (2*pi*x - a)" if "x \<in> {0..1}" for x
    proof  -
      have "2*pi*x \<in> {0..2*pi}" using twopi_pos that by auto
      with ca show "f x = c * sin (2*pi*x - a)"
        by (metis g_def nonzero_mult_div_cancel_left twopi_nz)
    qed
    then show "\<exists>c a. \<forall>x \<in> {0..1}. f x = c * sin (2*pi*x - a)" by auto
  qed
qed

section \<open>Part 2: a very special case of Green's theorem for a convex area\<close>

subsection \<open>Area under an arc.\<close>

locale Area =
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex" and u v S
  assumes uv: "u \<le> v"
    and Re_g_le: "Re (g u) \<le> Re (g v)"
    and acont_g: "absolutely_continuous_on {u..v} g"
    and gim: "g ` {u..v} \<subseteq> {z. Im z \<ge> 0}"
    and inj_g: "inj_on g {u..v}"
    and inj_Re: "inj_on Re (g ` {u..v})"
    and negS: "negligible S"
    and gder: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"

begin

lemma below_arclet:
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
proof -
  obtain h where h: "\<And>x. x \<in> {u..v} \<Longrightarrow> h (Re (g x)) = x"
    by (metis inj_g inj_Re comp_def comp_inj_on inv_into_f_f)
  define A where "A \<equiv> (\<lambda>t. Re (g t)) ` {u..v}"
  have cont_h: "continuous_on A h"
    unfolding A_def
    by (simp add: absolutely_continuous_on_imp_continuous acont_g continuous_on_Re continuous_on_inv h)
  have cont_g: "continuous_on {u..v} g"
    by (simp add: absolutely_continuous_on_imp_continuous acont_g)
  have gp_ai: "g' absolutely_integrable_on {u..v}"
    by (meson absolutely_integrable_absolutely_continuous_derivative acont_g gder
        has_vector_derivative_at_within negS)
  have Re_gp_ai: "(\<lambda>t. Re (g' t)) absolutely_integrable_on {u..v}"
    using Re_absolutely_integrable_on gp_ai by blast
  have Im_g_cont: "continuous_on {u..v} (\<lambda>t. Im (g t))"
    by (intro continuous_intros cont_g)
  have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {u..v})"
    by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
  have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {u..v})"
    using continuous_imp_measurable_on_sets_lebesgue[OF Im_g_cont] atLeastAtMost_borel lborelD
    by (metis sets_completionI_sets)
  show "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    using absolutely_integrable_bounded_measurable_product_real [OF Im_g_meas _ Im_g_bdd Re_gp_ai]
    by (simp add: mult.commute)
  have cont_Reg: "continuous_on {u..v} (\<lambda>t. Re (g t))"
    by (intro continuous_intros cont_g)
  have inj_Reg: "inj_on (\<lambda>t. Re (g t)) {u..v}"
    using comp_inj_on[OF inj_g inj_Re] by (simp add: o_def)
  have Aeq: "A = {Re (g u)..Re (g v)}"
  proof (rule antisym)
    show "A \<subseteq> {Re (g u)..Re (g v)}"
    proof (cases "u = v")
      case False
      with uv 
      have "strict_mono_on {u..v} (\<lambda>t. Re (g t)) \<or> strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
        using injective_eq_monotone_map[OF is_interval_cc cont_Reg] inj_Reg by auto
      with False \<open>u \<le> v\<close> have mono: "strict_mono_on {u..v} (\<lambda>t. Re (g t))"
        by (smt (verit, ccfv_threshold) Re_g_le atLeastAtMost_iff monotone_onD)
      show ?thesis
        using mono by (auto simp: monotone_on_def A_def less_eq_real_def)
    qed (auto simp: A_def)
  next
    show "{Re (g u)..Re (g v)} \<subseteq> A"
      using ivt_increasing_component_on_1[OF uv cont_g, of 1] by (force simp: A_def)
  qed
  define f where "f \<equiv> (\<lambda>x. Im (g (h x)))"
  have h_range: "h ` A \<subseteq> {u..v}"
    using h by (force simp: A_def)
  have cont_f: "continuous_on A f"
    using cont_g cont_h continuous_on_Im continuous_on_compose2 f_def h_range by blast
  have f_nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
    unfolding f_def using gim h_range by blast
  have mono_Reg: "Re (g x) \<le> Re (g y)" if "x \<in> {u..v}" "y \<in> {u..v}" "x \<le> y" for x y
  proof -
    have "strict_mono_on {u..v} (\<lambda>t. Re (g t)) \<or> strict_antimono_on {u..v} (\<lambda>t. Re (g t))"
      using injective_eq_monotone_map[OF is_interval_cc cont_Reg] inj_Reg by auto
    with Re_g_le atLeastAtMost_iff leD  order_le_less uv 
    have "mono_on {u..v} (\<lambda>t. Re (g t))"
      unfolding monotone_on_def by metis
    with that show "Re (g x) \<le> Re (g y)" by (auto simp: mono_on_def)
  qed
  have acont_Reg: "absolutely_continuous_on {u..v} (\<lambda>t. Re (g t))"
    using absolutely_continuous_on_compose_linear[OF acont_g bounded_linear_Re[THEN bounded_linear.linear]]
    by (simp add: o_def)
  have deriv_Reg: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> ((\<lambda>t. Re (g t)) has_vector_derivative Re (g' t)) (at t)"
    using bounded_linear_Re[THEN bounded_linear.has_vector_derivative] gder by blast
      \<comment> \<open>Apply substitution: $\int_{Re(g\,u)}^{Re(g\,v)} f = \int_u^v Re(g') \cdot f(Re(g)) = \int_u^v Re(g') \cdot Im(g)$\<close>
  have subst: "((\<lambda>t. Re (g' t) * f (Re (g t))) has_integral (integral {Re (g u)..Re (g v)} f)) {u..v}"
    using has_integral_substitution_ac[OF uv Re_g_le acont_Reg negS deriv_Reg _ mono_Reg] cont_f Aeq
    using negS by blast
      \<comment> \<open>Since $f(Re(g\,t)) = Im(g\,t)$, the left-hand side simplifies\<close>
  have "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) = integral {Re (g u)..Re (g v)} f"
    using h has_integral_spike[OF negligible_empty _ subst] integral_unique
    by (fastforce simp: f_def)
      \<comment> \<open>Apply area-under-curve: measure of the subgraph $= \int f$\<close>
  also have "\<dots> = measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
  proof -
    \<comment> \<open>First show the subgraph set equals the area under the graph of @{term f}\<close>
    have set_eq: "{z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w} =
                  {z. Re (g u) \<le> Re z \<and> Re z \<le> Re (g v) \<and> 0 \<le> Im z \<and> Im z \<le> f (Re z)}" (is "?L=?R")
    proof (intro antisym subsetI)
      fix z assume "z \<in> ?L" then show "z \<in> ?R"
        using h Aeq by (force simp: A_def f_def)
    next
      fix z assume z: "z \<in> ?R"
      then have Rez: "Re z \<in> A" using Aeq by auto
      then show "z \<in> ?L"
        using h z by (fastforce simp: A_def f_def)
    qed
    show ?thesis unfolding set_eq
      using has_integral_area_under_curve[OF Re_g_le _ _] cont_f f_nonneg Aeq
      by (metis (no_types, lifting))
  qed
  finally show "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}" .
qed

end

subsection \<open>Area above an arc.\<close>

lemma area_above_arclet:
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
  assumes "u \<le> v"
    and Re_g_ge: "Re (g v) \<le> Re (g u)"
    and ac_g: "absolutely_continuous_on {u..v} g"
    and gim: "g ` {u..v} \<subseteq> {z. Im z \<le> 0}"
    and injg: "inj_on g {u..v}"
    and injRe: "inj_on Re (g ` {u..v})"
    and "negligible S"
    and vder_g: "\<And>t. t \<in> {u..v} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    and "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
proof -
  \<comment> \<open>Symmetry: define $h(t) = \overline{g(u+v-t)}$ and apply \<open>area_below_arclet\<close>\<close>
  define \<phi> where "\<phi> \<equiv> \<lambda>t. u + v - t"
  define h where "h \<equiv> cnj \<circ> g \<circ> \<phi>"
  define h' where "h' \<equiv> \<lambda>t. - cnj (g' (\<phi> t))"
  have integrand_eq: "\<And>t. Re (h' t) * Im (h t) = Re (g' (\<phi> t)) * Im (g (\<phi> t))"
    unfolding h_def h'_def by (simp add: o_def cnj.sel)
  have integral_eq: "integral {u..v} (\<lambda>t. Re (g' (\<phi> t)) * Im (g (\<phi> t))) =
                     integral {u..v} (\<lambda>t. Re (g' t) * Im (g t))"
    using integral_shift_Icc_real[of "-v" "-u" "\<lambda>t. Re (g' t) * Im (g t)" "u+v"] 
    unfolding \<phi>_def comp_def
    by (smt (verit, ccfv_SIG) Henstock_Kurzweil_Integration.integral_cong
        Henstock_Kurzweil_Integration.integral_reflect_real)
  have Re_gp_ai: "(\<lambda>t. Re (g' t)) absolutely_integrable_on {u..v}"
    using Re_absolutely_integrable_on has_vector_derivative_at_within assms
    by (metis vder_g absolutely_integrable_absolutely_continuous_derivative)
  have Im_g_cont: "continuous_on {u..v} (\<lambda>t. Im (g t))"
    by (simp add: absolutely_continuous_on_imp_continuous assms(3) continuous_on_Im)
  have Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {u..v})"
    by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])
  have Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {u..v})"
    using Im_g_cont integrable_continuous_real integrable_imp_measurable by blast
  show "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {u..v}"
    using absolutely_integrable_bounded_measurable_product_real [OF Im_g_meas _ Im_g_bdd Re_gp_ai]
    by (simp add: mult.commute)
  have measure_eq: "measure lebesgue {z. \<exists>w \<in> h ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w} =
                    measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
  proof -
    have \<phi>_image: "\<phi> ` {u..v} = {u..v}"
      using assms(1) unfolding \<phi>_def by (auto simp: image_iff)
    have h_image: "h ` {u..v} = cnj ` (g ` {u..v})"
      by (metis \<phi>_image h_def image_comp)
    define A where "A \<equiv> {z. \<exists>w \<in> h ` {u..v}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
    define B where "B \<equiv> {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
    have AB: "A = cnj ` B"
      unfolding A_def h_image B_def by (force simp: in_image_cnj_iff)
    have cont_g_uv: "continuous_on {u..v} g"
      using assms(3) absolutely_continuous_on_imp_continuous is_interval_cc by blast
    define \<psi> where "\<psi> \<equiv> \<lambda>(t,s). Complex (Re (g t)) ((1 - s) * Im (g t))"
    have cont_\<psi>: "continuous_on ({u..v} \<times> {0..1}) \<psi>"
      unfolding \<psi>_def split_def 
      by (auto intro!: continuous_intros continuous_on_compose2[OF cont_g_uv])
    have  "\<psi> ` ({u..v} \<times> {0..1}) = (\<lambda>(x, y). Complex x y) ` ((\<lambda>(w,s). (Re w, (1 - s) * Im w)) ` (g ` {u..v} \<times> {0..1}))"
      by (force simp: \<psi>_def)
    have img: "\<psi> ` ({u..v} \<times> {0..1}) = B"
    proof -
      have "\<exists>z. (\<exists>t\<ge>u. t \<le> v \<and> Re z = Re (g t) \<and> Im z = Im (g t)) \<and> Re z = Re (g t) \<and> Im z \<le> (1 - s) * Im (g t) \<and> (1 - s) * Im (g t) \<le> 0"
        if "u \<le> t" "t \<le> v" and "0 \<le> s" "s \<le> 1" for t s
      proof -
        have "Im (g t) \<le> 0"
          using gim atLeastAtMost_iff that by blast
        with that segment_bound_lemma[OF order.refl, of "Im(g t)" 0 s] show ?thesis
          by (smt (verit, best) mult_le_0_iff)
      qed
      moreover have "\<exists>a\<ge>u. a \<le> v \<and> (\<exists>b\<ge>0. b \<le> 1 \<and> Re w = Re (g a) \<and> Im w = (1 - b) * Im (g a))"
        if "Re (g t) = Re w" and "u \<le> t" "t \<le> v"
          and "Im (g t) \<le> Im w" and "Im w \<le> 0" and "Re z = Re w" and Imz: "Im z = Im (g t)"
        for w z t
      proof (cases "Im (g t) = 0")
        case False
        define s where "s \<equiv> 1 - Im w / Im (g t)"
        have "s \<in> {0..1}" "Im w = (1 - s) * Im (g t)"
          using False that by (auto simp: s_def divide_nonpos_neg)
        then show ?thesis
          using that by (metis atLeastAtMost_iff)
      qed (use that in \<open>force simp: less_eq_real_def\<close>)
      ultimately show ?thesis
        by (auto simp: B_def \<psi>_def Bex_def image_iff complex_eq_iff)
    qed
    then have "compact B"
      using img compact_continuous_image[OF cont_\<psi>] by (simp add: compact_Times)
    then have B_meas: "B \<in> lmeasurable" using lmeasurable_compact by blast    
    show ?thesis
      using AB measure_linear_image[OF linear_cnj B_meas] det_complex by (simp add: A_def B_def)
  qed
  interpret Area h h' u v "\<phi> ` S"
  proof
    show  "u \<le> v" "Re (h u) \<le> Re (h v)"
      by (simp_all add: \<open>u \<le> v\<close> \<phi>_def Re_g_ge h_def)
    show "absolutely_continuous_on {u..v} h"
      by (simp add: \<phi>_def absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect assms(3)
          h_def linear_cnj)
    show "inj_on h {u..v}" "h ` {u..v} \<subseteq> {z. 0 \<le> Im z}"
      using injg gim by (fastforce simp: inj_on_def h_def \<phi>_def image_subset_iff)+
    show "inj_on Re (h ` {u..v})"
      using injRe by (fastforce simp: inj_on_def h_def \<phi>_def)
    have "\<phi> ` S = (+) (u + v) ` (uminus ` S)"
      unfolding \<phi>_def image_image by (simp add: algebra_simps image_subset_iff)
    then show "negligible (\<phi> ` S)"
      by (simp add: \<open>negligible S\<close> linear_uminus negligible_linear_image negligible_translation)
    show "\<And>t. t \<in> {u..v} - (\<phi>`S) \<Longrightarrow> (h has_vector_derivative h' t) (at t)"
      unfolding has_vector_derivative_def h_def h'_def \<phi>_def 
      by (rule vder_g [unfolded has_vector_derivative_def] derivative_eq_intros | force)+
  qed
  show "integral {u..v} (\<lambda>t. Re (g' t) * Im (g t)) =
      measure lebesgue {z. \<exists>w \<in> g ` {u..v}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
    using below_arclet(2) integrand_eq integral_eq measure_eq by (simp add: o_def)
qed

subsection \<open>Lemmas for Green's theorem\<close>

definition Green_concl :: "(real \<Rightarrow> complex) \<Rightarrow> (real \<Rightarrow> complex) \<Rightarrow> bool" where
  "Green_concl g g' \<equiv> (\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}
    \<and> \<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> = measure lebesgue (inside (path_image g))"

text \<open>At most two points on the frontier of a $2$-dimensional convex body can share the same
  inner product with a non-zero vector. Consequence: if three distinct points
  on the frontier have the same @{term Re} (or @{term Im}), the body must lie on one side.\<close>
lemma frontier_vertical_at_most_two:
  fixes S :: "complex set" and c :: real
  assumes "convex S" "compact S" "interior S \<noteq> {}"
    and sides: "\<exists>p \<in> S. Re p < c" "\<exists>q \<in> S. c < Re q"
    and xyz: "x \<in> frontier S" "y \<in> frontier S" "z \<in> frontier S"
      "Re x = c" "Re y = c" "Re z = c"
  shows "\<not> (x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z)"
proof -
  define T where "T \<equiv> {w :: complex. 1 \<bullet> w = c}"
  have aff_T: "affine T" unfolding T_def by (rule affine_hyperplane)
  have T_eq: "T = {w. Re w = c}" unfolding T_def by (simp add: complex_inner_1)
  have xT: "x \<in> T" "y \<in> T" "z \<in> T"
    using xyz unfolding T_eq by auto
  \<comment> \<open>The interior of @{term S} intersects @{term T}\<close>
  have int_T: "interior S \<inter> T \<noteq> {}"
  proof -
    have cl: "closed S" using assms(2) compact_imp_closed by blast
    have cl_int: "closure (interior S) = S"
      using convex_closure_interior[OF assms(1) assms(3)] cl
      by (simp add: closure_closed)
    \<comment> \<open>Find interior points on each side of $Re = c$\<close>
    obtain p where p: "p \<in> interior S" "Re p < c"
    proof -
      obtain p0 ps where p0: "p0 \<in> S" "Re p0 < c" and ps: "\<forall>n. ps n \<in> interior S" "ps \<longlonglongrightarrow> p0"
        using cl_int closure_sequential sides by blast
      then obtain n where "Re (ps n) < c" using eventually_sequentially
        by (metis LIMSEQ_le_const not_less \<open>Re p0 < c\<close> tendsto_complex_iff)
      then show thesis using that ps by auto
    qed
    obtain q where q: "q \<in> interior S" "c < Re q"
    proof -
      obtain q0 qs where q0: "q0 \<in> S" "c < Re q0" and qs: "\<forall>n. qs n \<in> interior S" "qs \<longlonglongrightarrow> q0"
        using cl_int closure_sequential sides by blast
      then obtain n where "c < Re (qs n)" using eventually_sequentially
        by (metis LIMSEQ_le_const2 not_less \<open>c < Re q0\<close> tendsto_complex_iff)
      then show thesis using that qs by auto
    qed
    \<comment> \<open>IVT on the segment $\{p..q\} \subseteq \mathit{interior}\ S$\<close>
    have conv_int: "convex (interior S)" using convex_interior assms(1) by auto
    then have seg_sub: "closed_segment p q \<subseteq> interior S"
      using closed_segment_subset p(1) q(1) by auto
    have "1 \<bullet> p \<le> c" "c \<le> 1 \<bullet> q" using p(2) q(2) by auto
    then obtain r where "r \<in> closed_segment p q" "1 \<bullet> r = c"
      using connected_ivt_hyperplane[OF connected_segment] by blast
    then show ?thesis
      using T_eq seg_sub by auto
  qed
  \<comment> \<open>Apply \<open>convex_affine_rel_frontier_Int\<close>\<close>
  have rf_eq: "rel_frontier (S \<inter> T) = frontier S \<inter> T"
    using convex_affine_rel_frontier_Int[OF assms(1) aff_T int_T] .
  \<comment> \<open>@{term "S \<inter> T"} is a compact convex collinear set, hence a closed segment\<close>
  have ST_ne: "S \<inter> T \<noteq> {}"
    using int_T interior_subset by blast
  have ST_compact: "compact (S \<inter> T)"
    by (metis aff_T affine_hull_eq assms(2) closed_affine_hull compact_Int_closed)
  have ST_convex: "convex (S \<inter> T)"
    using assms(1) convex_Int aff_T affine_imp_convex by auto
  have "aff_dim T = 1" 
    unfolding T_def using aff_dim_hyperplane [of "1::complex" c] by simp
  then have ST_collinear: "collinear (S \<inter> T)"
    by (metis collinear_aff_dim collinear_subset Int_lower2 int_one_le_iff_zero_less zero_less_one)
  obtain p q where pq: "S \<inter> T = closed_segment p q"
    using compact_convex_collinear_segment[OF ST_ne ST_compact ST_convex ST_collinear] by auto
  \<comment> \<open>The @{term rel_frontier} of a closed segment has at most two elements\<close>
  have rf_sub: "rel_frontier (S \<inter> T) \<subseteq> {p, q}"
  proof (cases "p = q")
    case True
    then show ?thesis unfolding pq by (simp add: rel_frontier_sing)
  next
    case False
    have "rel_frontier (closed_segment p q) = closed_segment p q - rel_interior (closed_segment p q)"
      unfolding rel_frontier_def by (simp add: closure_closed_segment)
    also have "\<dots> = closed_segment p q - open_segment p q"
      using rel_interior_closed_segment[of p q] False by simp
    also have "\<dots> = {p, q}"
      by (simp add: double_diff segment(1))
    finally show ?thesis using pq by simp
  qed
  then show ?thesis
    by (metis IntI insertE rf_eq singletonD subsetD xT xyz)
qed


locale Green =
  fixes g :: "real \<Rightarrow> complex" and g' :: "real \<Rightarrow> complex"
    and U :: "real set"
    and a b :: "complex"
  assumes g: "simple_path g" "pathstart g = a" "pathfinish g = a"
    and b: "b \<in> path_image g" "Re a < Re b" "Im a = Im b"
    and dab: "dist a b = diameter (path_image g)"
    and conv: "convex (inside (path_image g))"
    and cont: "absolutely_continuous_on {0..1} g"
    and U: "negligible U"
    and vder: "\<And>t. t \<in> {0..1} - U \<Longrightarrow> (g has_vector_derivative g' t) (at t)"

begin

definition "gop \<equiv> cnj \<circ> reversepath g"
definition "gop' \<equiv> uminus \<circ> cnj \<circ> reversepath g'"

lemma Im_g_cont: "continuous_on {0..1} (\<lambda>t. Im (g t))"
  by (simp add: absolutely_continuous_on_imp_continuous cont continuous_on_Im)

lemma Im_g_bdd: "bounded ((\<lambda>t. Im (g t)) ` {0..1})"
  by (intro compact_imp_bounded compact_continuous_image[OF Im_g_cont compact_Icc])

lemma Im_g_meas: "(\<lambda>t. Im (g t)) \<in> borel_measurable (lebesgue_on {0..1})"
  using Im_g_cont continuous_imp_integrable_real by blast

lemma gp_ai: "g' absolutely_integrable_on {0..1}"
  using absolutely_integrable_absolutely_continuous_derivative[OF cont U]
    vder has_vector_derivative_at_within by blast

lemma cnj_rev: "Green gop gop' ((\<lambda>t. 1-t) ` U) (cnj a) (cnj b)"
proof
  show "simple_path gop"
    using g by (simp add: simple_path_def gop_def loop_free_reversepath loop_free_cnj)
  show "pathstart gop = cnj a"
    using g by (simp add: gop_def pathstart_compose)
  show "pathfinish gop = cnj a"
    using g by (simp add: gop_def pathfinish_compose)
  show "cnj b \<in> path_image gop"
    using b by (simp add: gop_def path_image_compose)
  show "Re (cnj a) < Re (cnj b)" "Im (cnj a) = Im (cnj b)"
    using b by auto
  show "dist (cnj a) (cnj b) = diameter (path_image gop)"
    by (simp add: gop_def dab diameter_image_cnj path_image_compose flip: dab)
  show "convex (inside (path_image gop))"
    unfolding gop_def
    by (metis conv convex_linear_vimage image_cnj_conv_vimage_cnj 
        inside_cnj_image linear_cnj path_image_compose path_image_reversepath)
  show "absolutely_continuous_on {0..1} gop"
    using cont unfolding gop_def
    by (simp add: absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect linear_cnj
        reversepath_o)
  have "negligible (uminus ` U)"
    by (simp add: U linear_uminus negligible_linear_image_eq)
  then have "negligible (((+)1) ` uminus ` U)"
    using negligible_translation by blast
  then show "negligible ((-) 1 ` U)"
    by (simp add: image_subset_iff negligible_subset)
next
  fix t :: real
  note vder [unfolded has_vector_derivative_def, derivative_intros]
  assume "t \<in> {0..1} - (-) 1 ` U"
  then have "0 \<le> t" "t \<le> 1" "1-t \<notin> U"
    by (auto simp: image_iff)
  then show "(gop has_vector_derivative gop' t) (at t)"
    unfolding gop_def gop'_def has_vector_derivative_def reversepath_o
    by - (rule derivative_eq_intros | simp add: o_def | assumption)+
qed

lemma rev: "Green (reversepath g) (uminus \<circ> reversepath g') ((\<lambda>t. 1-t) ` U) a b"
proof
  show "simple_path (reversepath g)"
    using g by (simp add: simple_path_def loop_free_reversepath)
  show "dist a b = diameter (path_image (reversepath g))"
    by (simp add: gop_def dab path_image_compose flip: dab)
  show "convex (inside (path_image (reversepath g)))"
    by (simp add: gop_def conv)
  show "absolutely_continuous_on {0..1} (reversepath g)"
    using cont unfolding gop_def
    by (simp add: absolutely_continuous_on_compose_linear absolutely_continuous_on_reflect linear_cnj
        reversepath_o)
  have "negligible (uminus ` U)"
    by (simp add: U linear_uminus negligible_linear_image_eq)
  then have "negligible (((+)1) ` uminus ` U)"
    using negligible_translation by blast
  then show "negligible ((-) 1 ` U)"
    using Green.U cnj_rev by blast
next
  fix t :: real
  note vder [unfolded has_vector_derivative_def, derivative_intros]
  assume "t \<in> {0..1} - (-) 1 ` U"
  then have "0 \<le> t" "t \<le> 1" "1-t \<notin> U"
    by (auto simp: image_iff)
  then show "((reversepath g) has_vector_derivative (uminus \<circ> reversepath g') t) (at t)"
    unfolding gop_def gop'_def has_vector_derivative_def reversepath_o
    by - (rule derivative_eq_intros | simp add: o_def | assumption)+
qed (use g b in \<open>auto simp: pathstart_compose pathfinish_compose path_image_compose\<close>)

lemma f_abs_int: "(\<lambda>s. Re (g' s) * Im (g s)) absolutely_integrable_on {0..1}"
  using absolutely_integrable_bounded_measurable_product_real[OF Im_g_meas _ Im_g_bdd Re_absolutely_integrable_on] gp_ai
  by (simp add: mult.commute)

lemma arc_inj_on: "inj_on g {u..v}"
  if huv: "0 \<le> u" "v \<le> 1" "u < v" and hne: "u > 0 \<or> v < 1" 
proof (rule inj_onI)
  fix s1 s2 assume s1: "s1 \<in> {u..v}" and s2: "s2 \<in> {u..v}" and eq: "g s1 = g s2"
  have s1_01: "s1 \<in> {0..1}" using s1 huv by auto
  have s2_01: "s2 \<in> {0..1}" using s2 huv by auto
  show "s1 = s2"
  proof (rule ccontr)
    assume neq: "s1 \<noteq> s2"
    with g have "s1 = s2 \<or> s1 = 0 \<and> s2 = 1 \<or> s1 = 1 \<and> s2 = 0"
      unfolding simple_path_def loop_free_def
      using eq  s1_01 s2_01 by blast
    with neq show False using s1 s2 huv hne by auto
  qed
qed

lemma arc_Re_inj_on: "inj_on Re (g ` {u..v})"
  if hinj: "inj_on g {u..v}"
    and hRe: "\<And>s1 s2. \<lbrakk>s1 \<in> {u..v}; s2 \<in> {u..v}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
               \<Longrightarrow> Re (g u) = Re (g v)"
    and hne: "Re (g u) \<noteq> Re (g v)"
proof (rule inj_onI)
  fix x y assume "x \<in> g ` {u..v}" "y \<in> g ` {u..v}" "Re x = Re y"
  then obtain s1 s2 where "s1 \<in> {u..v}" "x = g s1" "s2 \<in> {u..v}" "y = g s2" by auto
  then show "x = y"
    using \<open>Re x = Re y\<close> that by blast
qed

lemma Re_inj_upper_gen: 
  assumes s1t: "s1 \<in> {0..t}" and s2t: "s2 \<in> {0..t}"
    and Re_eq: "Re (g s1) = Re (g s2)" and neq: "s1 \<noteq> s2"
    and geq0: "g 0 = 0" "g 1 = 0"
    and ht: "0 < t" "t < 1" "g t = b"
  shows "(s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0)"
proof (rule ccontr)
  assume not_endpts: "\<not> ((s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0))"
    \<comment> \<open>Define @{term "S \<equiv> convex hull (path_image g)"}. This is the right set for
       \<open>frontier_vertical_at_most_two\<close>.\<close>
  define S where "S \<equiv> convex hull (path_image g)"
  have S_convex: "convex S" unfolding S_def by (rule convex_convex_hull)
  have S_compact: "compact S" unfolding S_def
    using compact_simple_path_image[OF g(1)] compact_convex_hull by auto
  have frontier_S: "frontier S = path_image g"
    unfolding S_def using frontier_convex_hull_eq_path_image[OF g(1) _ conv] g(2,3) by auto
  have S_int_ne: "interior S \<noteq> {}"
    unfolding S_def using g
    by (simp add: Jordan_inside_outside conv convex_hull_eq_closure_inside convex_interior_closure
        interior_open)
      \<comment> \<open>Step 1: At least one of $s_1$, $s_2$ is in the open interval $(0,t)$.\<close>
  have interior_param: "s1 \<in> {0<..<t} \<or> s2 \<in> {0<..<t}"
    using s1t s2t neq not_endpts by auto
      \<comment> \<open>Step 2: $g\,s_1 \neq g\,s_2$ (from injectivity of @{term g} on $\{0..t\}$, which is a proper sub-arc).\<close>
  have inj_sub: "inj_on g {0..t}"
    using arc_inj_on[of 0 t] ht by auto
  have g_neq: "g s1 \<noteq> g s2"
    by (meson neq inj_on_def inj_sub s1t s2t)
      \<comment> \<open>Step 3: Both $g\,s_1$ and $g\,s_2$ are on @{term "frontier S"} $=$ @{term "path_image g"}.\<close>
  have s1_01: "s1 \<in> {0..1}" using s1t ht(2) by auto
  have s2_01: "s2 \<in> {0..1}" using s2t ht(2) by auto
  have gs1_frontier: "g s1 \<in> frontier S"
    using frontier_S s1_01 by (auto simp: path_image_def)
  have gs2_frontier: "g s2 \<in> frontier S"
    using frontier_S s2_01 by (auto simp: path_image_def)
      \<comment> \<open>Step 4: Find a third distinct point on @{term "frontier S"} with the same real part.\<close>
  define c where "c \<equiv> Re (g s1)"
    \<comment> \<open>Step 4a: Show $c \in \{0, Re\,b\}$ forces $s_1$ or $s_2$ to an endpoint, contradicting \<open>not_endpts\<close>.\<close>
  have c_strict: "0 < c \<and> c < Re b"
  proof -
    have a0: "a = 0" using geq0(1) g(2) by (simp add: pathstart_def)
    have Imb: "Im b = 0" using b(3) a0 by simp
    have Reb: "Re b > 0" using b(2) a0 by simp
    have bdd: "bounded (path_image g)"
      using compact_simple_path_image[OF g(1)] compact_imp_bounded by blast
    have gs1_pi: "g s1 \<in> path_image g" using s1_01 by (auto simp: path_image_def)
    have gs2_pi: "g s2 \<in> path_image g" using s2_01 by (auto simp: path_image_def)
    have g0_pi: "0 \<in> path_image g" using geq0(1) by (metis pathstart_def pathstart_in_path_image)
    have diam_eq: "dist 0 b = diameter (path_image g)" using dab a0 by simp
    have dist_0b: "dist 0 b = Re b"
      using Imb Reb cmod_eq_Re by auto
        \<comment> \<open>Every point on the curve is within distance $Re\,b$ of both $0$ and $b$\<close>
    have d1: "dist (g s1) b \<le> Re b"
      using diameter_bounded_bound[OF bdd gs1_pi b(1)] diam_eq dist_0b by simp
    have d2: "dist 0 (g s1) \<le> Re b"
      using diameter_bounded_bound[OF bdd g0_pi gs1_pi] diam_eq dist_0b by simp
    have cmod_sq: "(Re z)\<^sup>2 + (Im z)\<^sup>2 \<le> (Re b)\<^sup>2" if "cmod z \<le> Re b" for z
      by (metis cmod_power2 norm_ge_zero power_mono that)
    have cmod_sq_b: "(Re z - Re b)\<^sup>2 + (Im z)\<^sup>2 \<le> (Re b)\<^sup>2" if "cmod (z - b) \<le> Re b" for z
      using Imb cmod_sq that by force
    have eq_0: "s = 0" if "g s = 0" "s \<in> {0..t}" for s
      using geq0(1) inj_onD inj_sub that by fastforce
    have eq_t: "s = t" if "g s = b" "s \<in> {0..t}" for s
      using ht(3) inj_on_contraD inj_sub that by fastforce
    have "c \<noteq> 0"
    proof
      assume "c = 0"
      then have Re0: "Re (g s1) = 0" unfolding c_def by simp
      have "(Re (g s1) - Re b)\<^sup>2 + (Im (g s1))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq_b d1 by (simp add: dist_norm)
      then have "(Im (g s1))\<^sup>2 \<le> 0" using Re0 by (simp add: power2_eq_square)
      moreover have "(Re (g s2) - Re b)\<^sup>2 + (Im (g s2))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq_b[of "g s2"] diameter_bounded_bound[OF bdd gs2_pi b(1)]
          diam_eq dist_0b by (simp add: dist_norm)
      then have "(Im (g s2))\<^sup>2 \<le> 0"
        using Re0 Re_eq by fastforce
      ultimately show False using neq
        by (metis Re_eq complex.collapse g_neq power2_less_eq_zero_iff)
    qed
    moreover have "c \<noteq> Re b"
    proof
      assume c: "c = Re b"
      have "(Re (g s1))\<^sup>2 + (Im (g s1))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq d2 by (simp add: dist_norm)
      moreover have "Re (g s2) = Re b" using Re_eq \<open>c = Re b\<close> c_def by simp
      then have "(Re (g s2))\<^sup>2 + (Im (g s2))\<^sup>2 \<le> (Re b)\<^sup>2"
        using cmod_sq[of "g s2"] diameter_bounded_bound[OF bdd g0_pi gs2_pi]
          diam_eq dist_0b by (simp add: dist_norm)
      then have "g s2 = b" using \<open>Re (g s2) = Re b\<close> Imb by (auto simp: complex_eq_iff)
      ultimately show False using neq eq_t s2t g_neq
        by (simp add: Imb Re_eq complex_eq_iff)
    qed
    ultimately show ?thesis
      by (smt (verit) abs_Re_le_cmod c_def d1 d2 dist_0_norm dist_norm minus_complex.sel(1))
  qed
    \<comment> \<open>Step 4b: By the IVT on $\{t..1\}$, find $s_3$ with $Re(g\,s_3) = c$.\<close>
  have cont_Re_g: "continuous_on {t..1} (Re \<circ> g)"
    using absolutely_continuous_on_imp_continuous assms(2) cont continuous_on_Re
      continuous_on_eq continuous_on_subset by fastforce
  obtain s3 where s3: "s3 \<in> {t..1}" "Re (g s3) = c"
  proof -
    have img_iv: "is_interval ((Re \<circ> g) ` {t..1})"
      using is_interval_connected_1 connected_continuous_image connected_interval cont_Re_g by blast 
    have Regt_in: "Re b \<in> (Re \<circ> g) ` {t..1}" using ht(3) \<open>t < 1\<close> by fastforce
    have "Re (g 1) \<in> (Re \<circ> g) ` {t..1}" using ht(2) by (auto simp: image_def)
    then have Re0_in: "0 \<in> (Re \<circ> g) ` {t..1}" using geq0 by simp
    then have "c \<in> (Re \<circ> g) ` {t..1}"
      using img_iv[unfolded is_interval_1] Regt_in c_strict by auto
    then show ?thesis using that by (auto simp: image_def)
  qed
    \<comment> \<open>Step 4c: $g\,s_3$ is on @{term "frontier S"} and distinct from $g\,s_1$ and $g\,s_2$.\<close>
  have s3_01: "s3 \<in> {0..1}" using s3(1) ht(1) by auto
  have loopfr_g: "loop_free g" using g by (simp add: simple_path_def)
  have gs3_frontier: "g s3 \<in> frontier S"
    using frontier_S s3_01 by (auto simp: path_image_def)
  have gs3_ne_gs1: "g s3 \<noteq> g s1"
  proof
    assume eq: "g s3 = g s1"
    with loopfr_g have "s3 = s1 \<or> s3 = 0 \<and> s1 = 1 \<or> s3 = 1 \<and> s1 = 0"
      using loop_free_def s1_01 s3_01 by blast
    then show False
      using assms(1) c_def c_strict eq geq0(2) ht(3) s3(1) by auto
  qed
  have gs3_ne_gs2: "g s3 \<noteq> g s2"
  proof
    assume eq: "g s3 = g s2"
    with loopfr_g have "s3 = s2 \<or> s3 = 0 \<and> s2 = 1 \<or> s3 = 1 \<and> s2 = 0"
      using eq loop_free_def s2_01 s3_01 by blast
    then show False
      using assms(2) c_strict geq0(2) ht(3) s3(1,2) by fastforce
  qed
    \<comment> \<open>Step 5: The ``sides'' condition for \<open>frontier_vertical_at_most_two\<close>.\<close>
  have side_left: "\<exists>p \<in> S. Re p < c"
    by (metis S_def assms(5) c_strict hull_inc pathstart_def pathstart_in_path_image
        zero_complex.sel(1))
  have side_right: "\<exists>q \<in> S. c < Re q"
    by (metis S_def b(1) c_strict hull_inc)
      \<comment> \<open>Step 6: Apply \<open>frontier_vertical_at_most_two\<close> for the contradiction.\<close>
  have three_distinct: "g s1 \<noteq> g s2 \<and> g s1 \<noteq> g s3 \<and> g s2 \<noteq> g s3"
    using g_neq gs3_ne_gs1 gs3_ne_gs2 by auto
  have Re_all_c: "Re (g s1) = c" "Re (g s2) = c" "Re (g s3) = c"
    unfolding c_def using Re_eq s3(2) c_def by auto
  have "\<not> (g s1 \<noteq> g s2 \<and> g s1 \<noteq> g s3 \<and> g s2 \<noteq> g s3)"
    using frontier_vertical_at_most_two[OF S_convex S_compact S_int_ne side_left side_right
        gs1_frontier gs2_frontier gs3_frontier Re_all_c] .
  then show False using three_distinct by auto
qed

lemma not_all_above:
  assumes Reb: "Re b > 0"
  assumes "a = 0"
  assumes real_on_curve: "\<And>z. z \<in> path_image g \<Longrightarrow> Im z = 0 \<Longrightarrow> z = 0 \<or> z = b"
  shows "\<not> (path_image g \<subseteq> {z. 0 \<le> Im z})"
proof -
  have seg_infinite: "\<not> finite (open_segment a b)"
    using Reb assms by force
  have Im_b: "Im b = 0" using b(3) assms by simp
  have seg_Im0: "open_segment a b \<subseteq> {z. Im z = 0}"
    using assms Im_b by (auto simp: in_segment complex_eq_iff)
  have seg_in_closure: "open_segment a b \<subseteq> closure (inside (path_image g))"
    by (metis b(1) conv convex_contains_open_segment convex_convex_hull convex_hull_eq_closure_inside
        g hull_inc pathfinish_in_path_image)
  have frontier_eq: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast
  show ?thesis
  proof
    assume above: "path_image g \<subseteq> {z. 0 \<le> Im z}"
    then have hull_above: "convex hull (path_image g) \<subseteq> {z. 0 \<le> Im z}"
      by (intro hull_minimal convex_halfspace_Im_ge)
    then have inside_above: "inside (path_image g) \<subseteq> {z. 0 < Im z}"
    proof -
      have sub: "inside (path_image g) \<subseteq> {z. (0::real) \<le> \<i> \<bullet> z}"
        using hull_above closure_subset conv convex_hull_eq_closure_inside g by auto
      then have "inside (path_image g) \<subseteq> interior {z. (0::real) \<le> \<i> \<bullet> z}"
        using interior_maximal open_inside Jordan_inside_outside g by blast
      also have "\<dots> = {z. 0 < \<i> \<bullet> z}"
        by (rule interior_halfspace_ge) simp
      finally show ?thesis by (simp add: complex_inner_i_right)
    qed
    have "open_segment a b \<subseteq> path_image g"
      using frontier_def frontier_eq inside_above interior_open open_inside seg_Im0 seg_in_closure
      by (smt (verit, best) DiffI Jordan_inside_outside g mem_Collect_eq subset_eq)
    then have "open_segment a b \<subseteq> {z \<in> path_image g. Im z = 0}"
      using seg_Im0 by auto
    also have "\<dots> \<subseteq> {0, b}"
      using real_on_curve by blast
    finally show False using seg_infinite finite_subset by blast
  qed
qed

end


context Green
begin

interpretation CR: Green gop gop' "(\<lambda>t. 1-t) ` U" "cnj a" "cnj b"
  by (rule cnj_rev)

lemma Green_area_zero_A:
  assumes "a = 0" 
    and t: "0 < t" "t < 1"
    and hgt: "g t = b"
    and above: "g ` {0..t} \<subseteq> {z. 0 \<le> Im z}"
    and below: "g ` {t..1} \<subseteq> {z. Im z \<le> 0}"
  shows "Green_concl g g'"
proof -
  \<comment> \<open>Common facts used by both split_case and split_case'\<close>
  have g0: "g 0 = 0" using assms g(2) by (simp add: pathstart_def)
  have g1: "g 1 = 0" using assms g(3) by (simp add: pathfinish_def)
  have lfg: "loop_free g" using g by (simp add: simple_path_def)
  have Reb: "Re b > 0" using b(2) assms by simp
  have Imb: "Im b = 0" using b(3) assms by simp
      \<comment> \<open>Re-injectivity: on each arc, @{term "Re \<circ> g"} is injective (except at endpoints).
       Otherwise \<open>frontier_vertical_at_most_two\<close> gives a contradiction via three points
       on $\mathit{frontier}\,(\mathit{closure}\,(\mathit{inside}))$ with the same real part.\<close>
  have Re_inj_upper: "\<lbrakk>s1 \<in> {0..t}; s2 \<in> {0..t}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = 0 \<and> s2 = t) \<or> (s1 = t \<and> s2 = 0)" for s1 s2
    using Re_inj_upper_gen g0 g1 using hgt t by presburger
  have Re_inj_lower: "\<lbrakk>s1 \<in> {t..1}; s2 \<in> {t..1}; Re (g s1) = Re (g s2); s1 \<noteq> s2\<rbrakk>
        \<Longrightarrow> (s1 = t \<and> s2 = 1) \<or> (s1 = 1 \<and> s2 = t)" for s1 s2
    using CR.Re_inj_upper_gen[of "1-s1" "1-t" "1-s2"] hgt t using g g0 g1 assms
    by (auto simp add: gop_def reversepath_def)
      \<comment> \<open>Step 0: absolute integrability (needed for integral splitting)\<close>
  define f where "f \<equiv> \<lambda>s. Re (g' s) * Im (g s)"
  have f_int: "f integrable_on {0..1}"
    using set_lebesgue_integral_eq_integral(1)[OF f_abs_int] f_def by argo
      \<comment> \<open>Step 1: the integral splits over $\{0..t\}$ and $\{t..1\}$\<close>
  have split_int: "integral {0..1} f = integral {0..t} f + integral {t..1} f"
    using Henstock_Kurzweil_Integration.integral_combine[of 0 t 1 f] t f_int by auto
      \<comment> \<open>Step 2: upper arc integral $\ge 0$.
       By the change of variables $x = Re(g(s))$ and Re-injectivity, the integral
       $\int_0^t Re(g') \cdot Im(g)\,ds = \int_0^{Re\,b} f_{\mathit{upper}}(x)\,dx \ge 0$
       since $f_{\mathit{upper}} = Im \circ g \circ Re^{-1} \ge 0$ on the upper arc.\<close>
  interpret Area g g' 0 t U
  proof
    show "Re (g 0) \<le> Re (g t)" 
      using g0 hgt Reb by simp
    show "absolutely_continuous_on {0..t} g"
      using absolutely_continuous_on_subset[OF cont] t by auto
    show "inj_on g {0..t}"
      using arc_inj_on t less_eq_real_def by presburger
    then show "inj_on Re (g ` {0..t})"
      using Reb Re_inj_upper g0 t
      by (intro arc_Re_inj_on; fastforce simp: assms b(2))
  qed (use above U vder t in auto)
  have upper_int: "integral {0..t} f \<ge> 0"
    unfolding f_def using below_arclet(2) by auto
      \<comment> \<open>Step 3: lower arc integral $\ge 0$ as well.
       On $\{t..1\}$, @{term g} goes from $b$ back to $0$ ($Re$ decreasing) with $Im(g) \le 0$.
       By the change of variables $x = Re(g(s))$:
       $\int_t^1 Re(g') \cdot Im(g)\,ds = \int_{Re\,b}^0 f_{\mathit{lower}}(x)\,dx = -\int_0^{Re\,b} f_{\mathit{lower}}(x)\,dx \ge 0$
       since $f_{\mathit{lower}} \le 0$.\<close>
  have t_le1: "t \<le> 1" using t(2) by linarith
  have Re_le': "Re (g 1) \<le> Re (g t)" using g1 hgt Reb by simp
  have ac_sub': "absolutely_continuous_on {t..1} g"
    using absolutely_continuous_on_subset[OF cont] t by auto
  have inj_g_lower: "inj_on g {t..1}"
    using arc_inj_on t(2) less_eq_real_def t by presburger
  then have inj_Re_lower: "inj_on Re (g ` {t..1})"
    using Reb Re_inj_lower g1 t
    by (intro arc_Re_inj_on; fastforce simp: assms b(2))
  have lower_int: "integral {t..1} f \<ge> 0"
    unfolding f_def
    using vder t(1) area_above_arclet(2)[OF t_le1 Re_le' ac_sub' below inj_g_lower inj_Re_lower U]
    by auto
      \<comment> \<open>Step 4: total integral $=$ area of the inside.
       The inside decomposes as the region between the two arcs:
       $\mathit{inside}\,(\mathit{path\_image}\ g) = \{z \mid Re\,z \in (0, Re\,b) \wedge f_{\mathit{lower}}(Re\,z) < Im\,z < f_{\mathit{upper}}(Re\,z)\}$.
       By Fubini, its area $= \int_0^{Re\,b} (f_{\mathit{upper}}(x) - f_{\mathit{lower}}(x))\,dx$,
       and by the change-of-variables computations above, this equals
       @{term "integral {0..t} f + integral {t..1} f"} $=$ @{term "integral {0..1} f"}.\<close>
      \<comment> \<open>Re-derive the integral-equals-measure identities (proved locally in \<open>upper_int\<close>/\<open>lower_int\<close>)\<close>
  have t_le: "0 \<le> t" using t(1) by linarith
  have t_le1: "t \<le> 1" using t(2) by linarith
  have Re_le: "Re (g 0) \<le> Re (g t)" using g0 hgt Reb by simp
  have Re_le': "Re (g 1) \<le> Re (g t)" using g1 hgt Reb by simp
  have ac_sub: "absolutely_continuous_on {0..t} g"
    using absolutely_continuous_on_subset[OF cont] t by auto
  have ac_sub': "absolutely_continuous_on {t..1} g"
    using absolutely_continuous_on_subset[OF cont] t by auto
  have inj_g_upper: "inj_on g {0..t}"
    using arc_inj_on[of 0 t] t by auto
  then have inj_Re_upper: "inj_on Re (g ` {0..t})"
    using Reb Re_inj_upper g0 t
    by (intro arc_Re_inj_on; fastforce simp: assms b(2))
  have inj_g_lower: "inj_on g {t..1}"
    using arc_inj_on[of t 1] t by auto
  then have inj_Re_lower: "inj_on Re (g ` {t..1})"
    using Reb Re_inj_lower g1 t
    by (intro arc_Re_inj_on; fastforce simp: assms b(2))
  have vder_sub: "\<And>s. s \<in> {0..t} - U \<Longrightarrow> (g has_vector_derivative g' s) (at s)"
    using vder t(2) by auto
  have vder_sub': "\<And>s. s \<in> {t..1} - U \<Longrightarrow> (g has_vector_derivative g' s) (at s)"
    using vder t(1) by auto
      \<comment> \<open>The integral-equals-measure identities\<close>
  define Au where "Au \<equiv> {z. \<exists>w \<in> g ` {0..t}. Re w = Re z \<and> 0 \<le> Im z \<and> Im z \<le> Im w}"
  define Al where "Al \<equiv> {z. \<exists>w \<in> g ` {t..1}. Re w = Re z \<and> Im w \<le> Im z \<and> Im z \<le> 0}"
  have int_upper: "integral {0..t} f = measure lebesgue Au"
    using below_arclet(2) unfolding f_def Au_def by auto
  have int_lower: "integral {t..1} f = measure lebesgue Al"
    using area_above_arclet(2)[OF t_le1 Re_le' ac_sub' below inj_g_lower inj_Re_lower U vder_sub']
    unfolding f_def Al_def by blast
      \<comment> \<open>Step A: @{term Au} and @{term Al} are measurable (compact, hence @{term lmeasurable})\<close>
  have Au_meas: "Au \<in> lmeasurable"
  proof -
    have cont_g_upper: "continuous_on {0..t} g"
      using absolutely_continuous_on_imp_continuous[OF ac_sub] is_interval_cc by blast
    define \<phi> where "\<phi> \<equiv> \<lambda>(s,r). Complex (Re (g s)) (r * Im (g s))"
    have cont_\<phi>: "continuous_on ({0..t} \<times> {0..1}) \<phi>"
      unfolding \<phi>_def split_def
      by (intro continuous_intros continuous_on_compose2[OF cont_g_upper] continuous_on_fst) auto
    have img: "\<phi> ` ({0..t} \<times> {0..1}) = Au"
    proof (rule set_eqI)
      fix z :: complex
      show "z \<in> \<phi> ` ({0..t} \<times> {0..1}) \<longleftrightarrow> z \<in> Au"
      proof
        assume "z \<in> \<phi> ` ({0..t} \<times> {0..1})"
        then obtain s r where sr: "s \<in> {0..t}" "r \<in> {0..1}" "z = Complex (Re (g s)) (r * Im (g s))"
          unfolding \<phi>_def by auto
        have "g s \<in> g ` {0..t}" using sr(1) by auto
        moreover have Im_ge: "Im (g s) \<ge> 0"
          using subsetD[OF above imageI[OF sr(1)]] by simp
        ultimately show "z \<in> Au" unfolding Au_def
          using mult_left_le_one_le sr(2,3) by fastforce
      next
        assume "z \<in> Au"
        then obtain w where w: "w \<in> g ` {0..t}" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
          unfolding Au_def by auto
        then obtain s where s: "s \<in> {0..t}" "w = g s" by auto
        show "z \<in> \<phi> ` ({0..t} \<times> {0..1})"
        proof (cases "Im w = 0")
          case True 
          then have "z = \<phi> (s, 0)" unfolding \<phi>_def using w s(2) by (simp add: complex_eq_iff)
          then show ?thesis using s(1) by auto
        next
          case False
          define r where "r \<equiv> Im z / Im w"
          then have "r \<in> {0..1}" unfolding r_def using False w(3,4) by (auto simp: field_simps)
          moreover have "z = \<phi> (s, r)"
            unfolding \<phi>_def r_def using False w(2) s(2) by (simp add: complex_eq_iff)
          ultimately show ?thesis using s(1) by auto
        qed
      qed
    qed
    with compact_Times compact_Icc img compact_continuous_image[OF cont_\<phi>]
    show ?thesis using lmeasurable_compact by metis
  qed
  have Al_meas: "Al \<in> lmeasurable" \<comment> \<open>duality\<close>
  proof -
    have cont_g_lower: "continuous_on {t..1} g"
      using absolutely_continuous_on_imp_continuous[OF ac_sub'] is_interval_cc by blast
    define \<psi> where "\<psi> \<equiv> \<lambda>(s::real, r::real). Complex (Re (g s)) (r * Im (g s))"
    have cont_\<psi>: "continuous_on ({t..1} \<times> {0..1}) \<psi>"
      unfolding \<psi>_def split_def
      by (intro continuous_intros continuous_on_compose2[OF cont_g_lower] continuous_on_fst) auto
    have img: "\<psi> ` ({t..1} \<times> {0..1}) = Al"
    proof (rule set_eqI)
      fix z :: complex
      show "z \<in> \<psi> ` ({t..1} \<times> {0..1}) \<longleftrightarrow> z \<in> Al"
      proof
        assume "z \<in> \<psi> ` ({t..1} \<times> {0..1})"
        then obtain s r where sr: "s \<in> {t..1}" "r \<in> {0..1}" "z = Complex (Re (g s)) (r * Im (g s))"
          unfolding \<psi>_def by auto
        have "g s \<in> g ` {t..1}" using sr(1) by auto
        moreover have Im_le: "Im (g s) \<le> 0"
          using subsetD[OF below imageI[OF sr(1)]] by simp
        moreover have "Re (g s) = Re z" using sr(3) by simp
        moreover have "Im (g s) \<le> Im z"
          by (metis atLeastAtMost_iff calculation(2) complex.sel(2) linorder_not_le mult_less_cancel_right2
              sr(2,3))
        moreover have "Im z \<le> 0"
          using sr(3) sr(2) Im_le mult_nonneg_nonpos[of r "Im (g s)"] by simp
        ultimately show "z \<in> Al" unfolding Al_def
          by blast
      next
        assume "z \<in> Al"
        then obtain w where w: "w \<in> g ` {t..1}" "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
          unfolding Al_def by auto
        then obtain s where s: "s \<in> {t..1}" "w = g s" by auto
        show "z \<in> \<psi> ` ({t..1} \<times> {0..1})"
        proof (cases "Im w = 0")
          case True
          then have "z = \<psi> (s, 0)" unfolding \<psi>_def using w s(2) by (simp add: complex_eq_iff)
          then show ?thesis using s(1) by auto
        next
          case False
          define r where "r \<equiv> Im z / Im w"
          then have "r \<in> {0..1}" unfolding r_def using False w(3,4)
            by (auto simp: field_simps)
          moreover have "z = \<psi> (s, r)"
            unfolding \<psi>_def r_def using False w(2) s(2) by (simp add: complex_eq_iff)
          ultimately show ?thesis using s(1) by auto
        qed
      qed
    qed
    have "compact ({t..1} \<times> {0..1::real})" by (intro compact_Times compact_Icc)
    then show ?thesis using lmeasurable_compact img compact_continuous_image[OF cont_\<psi>] by simp
  qed
    \<comment> \<open>Step B+C: @{term "inside (path_image g) \<subseteq> Au \<union> Al"} and @{term "Au \<union> Al \<subseteq> closure (inside (path_image g))"},
         and the gap $\mathit{closure}\,(\mathit{inside}) \setminus \mathit{inside} = \mathit{path\_image}\ g$ is negligible,
         so $\mathit{measure}\,(\mathit{inside}) = \mathit{measure}\,(Au \cup Al)$.\<close>
  have ch_eq: "convex hull (path_image g) = closure (inside (path_image g))"
    using convex_hull_eq_closure_inside[OF g(1) _ conv] g(2,3) by auto
  have zero_in_ch: "0 \<in> convex hull (path_image g)"
    using hull_subset[of "path_image g" convex] g0
    by (auto simp: path_image_def intro!: imageI[of 0])
  have b_in_ch: "b \<in> convex hull (path_image g)"
    using hull_subset[of "path_image g" convex] b(1) by auto
  have real_seg: "closed_segment 0 b \<subseteq> convex hull (path_image g)"
    using closed_segment_subset_convex_hull[OF zero_in_ch b_in_ch] .
  have bdd_pi: "bounded (path_image g)"
    using compact_simple_path_image[OF g(1)] compact_imp_bounded by blast
  have zero_in_pi: "(0::complex) \<in> path_image g"
    using g0 by (auto simp: path_image_def intro!: imageI[of 0])
  have Re_bounds: "0 \<le> Re w \<and> Re w \<le> Re b" if "w \<in> path_image g" for w
  proof -
    have d0: "dist w 0 \<le> diameter (path_image g)"
      using diameter_bounded_bound[OF bdd_pi that zero_in_pi] .
    have db: "dist w b \<le> diameter (path_image g)"
      using diameter_bounded_bound[OF bdd_pi that b(1)] .
    have "diameter (path_image g) = dist 0 b" using dab g0 g1 assms by simp
    then have diam_eq: "diameter (path_image g) = Re b"
      using Imb Re_le cmod_eq_Re g0 hgt by auto
    from d0 have ub: "cmod w \<le> Re b" using diam_eq by (simp add: dist_norm)
    moreover from db have "cmod (w - b) \<le> Re b" using diam_eq by (simp add: dist_norm)
    ultimately show ?thesis
      by (smt (verit, ccfv_SIG) abs_Re_le_cmod minus_complex.sel(1))
  qed
    \<comment> \<open>Sublemma: @{term "Complex (Re w) 0 \<in> closed_segment 0 b"} for any @{term w} on the path\<close>
  have real_point_in_seg: "Complex (Re w) 0 \<in> closed_segment 0 b"
    if "w \<in> path_image g" for w
  proof -
    have bds: "0 \<le> Re w" "Re w \<le> Re b" using Re_bounds[OF that] by auto
    define u where "u \<equiv> Re w / Re b"
    have "0 \<le> u" "u \<le> 1" unfolding u_def using bds Reb by auto
    have "Complex (Re w) 0 = (1 - u) *\<^sub>R 0 + u *\<^sub>R b"
      unfolding u_def using Reb Imb
      by (simp add: complex_eq_iff scaleR_complex.ctr)
    then show ?thesis using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>
      unfolding closed_segment_def by auto
  qed
    \<comment> \<open>Sublemma: any @{term z} between $p = \mathit{Complex}\,(Re\,w)\,0$ and @{term w} is in the convex hull\<close>
  have in_ch_via_seg: "z \<in> convex hull (path_image g)"
    if w_pi: "w \<in> path_image g"
      and Re_eq: "Re w = Re z"
      and Im_between: "(0 \<le> Im z \<and> Im z \<le> Im w) \<or> (Im w \<le> Im z \<and> Im z \<le> 0)"
    for z w
  proof -
    define p where "p \<equiv> Complex (Re w) 0"
    have p_in_ch: "p \<in> convex hull (path_image g)"
      using real_point_in_seg[OF w_pi] real_seg
      using p_def by blast
    have w_in_ch: "w \<in> convex hull (path_image g)"
      using hull_subset[of "path_image g" convex] w_pi by auto
    show "z \<in> convex hull (path_image g)"
    proof (cases "Im w = 0")
      case True
      then show ?thesis using p_in_ch complex_eqI that(2,3) w_in_ch by force
    next
      case False
      define u where "u \<equiv> Im z / Im w"
      have "0 \<le> u" "u \<le> 1" unfolding u_def using Im_between False
        by (auto simp: field_simps split: if_splits)
      have "z = (1 - u) *\<^sub>R p + u *\<^sub>R w"
        unfolding p_def u_def using False Re_eq
        by (simp add: complex_eq_iff scaleR_complex.ctr) argo
      then have "z \<in> closed_segment p w" using \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>
        unfolding closed_segment_def by auto
      then show ?thesis
        using closed_segment_subset_convex_hull[OF p_in_ch w_in_ch] by auto
    qed
  qed
  have Au_sub: "Au \<subseteq> convex hull (path_image g)"
  proof (rule subsetI)
    fix z assume "z \<in> Au"
    then obtain w where w: "w \<in> g ` {0..t}" "Re w = Re z" "0 \<le> Im z" "Im z \<le> Im w"
      unfolding Au_def by auto
    then show "z \<in> convex hull (path_image g)"
      using t in_ch_via_seg[of w z] w by (auto simp: path_image_def)
  qed
  have "Al \<subseteq> convex hull (path_image g)"
  proof (rule subsetI)
    fix z assume "z \<in> Al"
    then obtain w where "w \<in> g ` {t..1}" and w: "Re w = Re z" "Im w \<le> Im z" "Im z \<le> 0"
      unfolding Al_def by auto
    with t have "w \<in> path_image g" by (auto simp: path_image_def)
    then show "z \<in> convex hull (path_image g)"
      using in_ch_via_seg[of w z] w by auto
  qed
  with Au_sub have Au_Al_sub_closure: "Au \<union> Al \<subseteq> closure (inside (path_image g))"
    using Au_sub ch_eq by auto

  have inside_sub_Au_Al: "inside (path_image g) \<subseteq> Au \<union> Al"
  proof (rule subsetI)
    fix z assume z_in: "z \<in> inside (path_image g)"
      \<comment> \<open>Set up the convex hull S and its key properties\<close>
    define S where "S \<equiv> convex hull (path_image g)"
    have S_bounded: "bounded S"
      by (simp add: S_def bdd_pi bounded_convex_hull)
    have ch_eq: "S = closure (inside (path_image g))"
      unfolding S_def using convex_hull_eq_closure_inside[OF g(1) _ conv] g(2,3) by auto
    have frontier_S: "frontier S = path_image g"
      unfolding S_def using frontier_convex_hull_eq_path_image[OF g(1) _ conv] g(2,3) by auto
    have inside_eq_int: "inside (path_image g) = interior S"
      by (metis S_bounded S_def convex_convex_hull frontier_S inside_frontier_eq_interior)
    have S_int_ne: "interior S \<noteq> {}"
      using z_in inside_eq_int by auto
    have rel_int_eq: "rel_interior S = interior S"
      using rel_interior_nonempty_interior[OF S_int_ne] .
    have rel_fr_eq: "rel_frontier S = frontier S"
      using rel_frontier_nonempty_interior[OF S_int_ne] .
    have z_int: "z \<in> interior S" using z_in inside_eq_int by auto
        \<comment> \<open>@{term S} is full-dimensional, so @{term "affine hull S = UNIV"}\<close>
    show "z \<in> Au \<union> Al"
    proof (cases "Im z \<ge> 0")
      case True
        \<comment> \<open>Shoot a ray upward from @{term z} in direction @{term \<i>}.
             By \<open>ray_to_rel_frontier\<close>, we hit a point on @{term "frontier S"} $=$ @{term "path_image g"}.\<close>
      obtain d where d: "d > 0" "z + d *\<^sub>R \<i> \<in> rel_frontier S"
        by (metis S_bounded complex_i_not_zero ray_to_frontier rel_fr_eq z_int)
      define w where "w \<equiv> z + d *\<^sub>R \<i>"
      have w_on_path: "w \<in> path_image g" and Re_w: "Re w = Re z" and Im_w: "Im w = Im z + d"
        using d(2) rel_fr_eq frontier_S w_def by auto
      have Im_w_pos: "Im w > 0" using True d(1) Im_w by linarith
          \<comment> \<open>Since $Im\,w > 0$ and the lower arc has $Im \le 0$, @{term w} must be on the upper arc\<close>
      have "{0..1} = {0..t} \<union> {t..1}" using t_le t_le1 by (auto simp: ivl_disj_un_two_touch)
      then have "path_image g = g ` {0..t} \<union> g ` {t..1}"
        unfolding path_image_def by (simp add: image_Un)
      moreover have "w \<notin> g ` {t..1}"
        using below Im_w_pos by (auto simp: subset_iff)
      ultimately have "z \<in> Au"
        using Au_def Im_w Re_w True d(1) w_on_path by auto
      then show "z \<in> Au \<union> Al" ..
    next
      case Im_z_neg: False \<comment>\<open>symmetric with the proof above\<close>
      obtain d where d: "d > 0" "z + d *\<^sub>R (-\<i>) \<in> frontier S"
        by (metis S_bounded complex_i_not_zero neg_equal_0_iff_equal ray_to_frontier z_int)
      have d2: "z - d *\<^sub>R \<i> \<in> rel_frontier S"
        using d(2) rel_fr_eq by (simp add: real_vector.scale_minus_right)
      define w where "w \<equiv> z - d *\<^sub>R \<i>"
      have w_on_path: "w \<in> path_image g" and Re_w: "Re w = Re z" and Im_w: "Im w = Im z - d"
        using d2 rel_fr_eq frontier_S w_def by auto
      have Im_w_neg: "Im w < 0" using Im_z_neg d(1) Im_w by linarith
      have "{0..1} = {0..t} \<union> {t..1}" using t_le t_le1 by (auto simp: ivl_disj_un_two_touch)
      then have "path_image g = g ` {0..t} \<union> g ` {t..1}"
        unfolding path_image_def by (simp add: image_Un)
      moreover have "w \<notin> g ` {0..t}"
        using above Im_w_neg by (auto simp: subset_iff)
      ultimately 
      have "z \<in> Al" using Al_def Im_w Im_z_neg Re_w d(1) w_on_path by auto
      then show "z \<in> Au \<union> Al" ..
    qed
  qed

  have inside_eq: "measure lebesgue (inside (path_image g)) = measure lebesgue (Au \<union> Al)"
  proof -
    have frontier_inside: "frontier (inside (path_image g)) = path_image g"
      using Jordan_inside_outside[OF g(1)] g(2,3) by auto
    have inside_meas: "inside (path_image g) \<in> lmeasurable"
      by (simp add: bdd_pi bounded_inside conv measurable_convex)
    have AuAl_meas: "Au \<union> Al \<in> lmeasurable"
      using fmeasurable.Un[OF Au_meas Al_meas] .
        \<comment> \<open>The symmetric difference is contained in @{term "path_image g"}, which is negligible\<close>
    have "inside (path_image g) \<Delta> (Au \<union> Al) \<subseteq> path_image g"
      by (metis Au_Al_sub_closure Diff_mono Diff_subset_conv closure_Un_frontier frontier_inside inside_sub_Au_Al
          le_iff_sup)
    then have "negligible (inside (path_image g) \<Delta> (Au \<union> Al))"
      by (metis conv frontier_inside negligible_convex_frontier negligible_subset)
    then show ?thesis
      using measure_negligible_symdiff[OF inside_meas]
      by presburger
  qed
    \<comment> \<open>Step D: @{term "Au \<inter> Al \<subseteq> {z. Im z = 0}"}, which is negligible in $\mathbb{R}^2$.
         Therefore $\mathit{measure}\,(Au \cup Al) = \mathit{measure}\,Au + \mathit{measure}\,Al$.\<close>
  have inter_null: "Au \<inter> Al \<subseteq> {z. Im z = 0}"
    unfolding Au_def Al_def by auto
  have "measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al"
  proof -
    have "negligible {z :: complex. Im z = 0}"
      using negligible_hyperplane[of \<i> 0] by (simp add: complex_inner_i_left)
    then have "negligible (Au \<inter> Al)"
      using negligible_subset inter_null by blast
    moreover have "measure lebesgue (Au \<union> Al) = measure lebesgue Au + measure lebesgue Al - measure lebesgue (Au \<inter> Al)"
      using measure_Un3[of Au lebesgue Al] Au_meas Al_meas by auto
    ultimately show ?thesis
      by (simp add: negligible_imp_measure0)
  qed
  then have area_decomp: "measure lebesgue (inside (path_image g)) = integral {0..t} f + integral {t..1} f"
    using inside_eq int_lower int_upper by presburger
  then  show ?thesis 
    using f_abs_int lower_int split_int upper_int by (auto simp: f_def Green_concl_def)
qed

end

subsection \<open>Green's theorem special case at zero\<close>

context Green
begin

interpretation CR: Green gop gop' "(\<lambda>t. 1-t) ` U" "cnj a" "cnj b"
  by (rule cnj_rev)

interpretation R: Green "reversepath g" "uminus \<circ> reversepath g'" "(\<lambda>t. 1-t) ` U" a b
  by (rule rev)

lemma Green_area_zero:
  assumes "a = 0"
  shows "Green_concl g g'"
proof -
  have g0: "g 0 = 0" using assms g(2) by (simp add: pathstart_def)
  have g1: "g 1 = 0" using assms g(3) by (simp add: pathfinish_def)
  define f where "f \<equiv> \<lambda>s. Re (g' s) * Im (g s)"
  have split_case': "Green_concl g g'"
    if t: "0 < t" "t < 1" and hgt: "g t = b"
      and below: "g ` {0..t} \<subseteq> {z. Im z \<le> 0}"
      and above: "g ` {t..1} \<subseteq> {z. 0 \<le> Im z}"
    for t :: real
  proof -
    have "Green_concl (reversepath g) (uminus \<circ> reversepath g')"
    proof (intro R.Green_area_zero_A)
      show "reversepath g ` {0..1-t} \<subseteq> {z. 0 \<le> Im z}"
        using above by (force simp: reversepath_def image_subset_iff)
    qed (use assms that in \<open>force simp: image_subset_iff reversepath_def\<close>)+
    moreover have "integral {0..1} (\<lambda>t. Re (reversepath g' t) * Im (reversepath g t)) 
                 = integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))"
      using has_integral_affinity [of f _ 0 1 "-1" 1] f_abs_int
      by (fastforce simp add: reversepath_def f_def absolutely_integrable_on_def)
    ultimately show ?thesis
      using f_abs_int by (auto simp: Green_concl_def)
  qed

  have Reb: "Re b > 0" using b(2) assms by simp
  have Im_b: "Im b = 0" using b(3) \<open>a=0\<close> by simp
  have path_g: "path g" using g(1) simple_path_imp_path by blast
  have cont_g: "continuous_on {0..1} g"
    using path_g by (simp add: path_def)
  obtain t where t: "g t = b" "0 < t" "t < 1"
    using b Reb g0 g1 by (fastforce simp: path_image_def)
  have "g ` {0..t} \<subseteq> {z. 0 \<le> Im z} \<and> g ` {t..1} \<subseteq> {z. Im z \<le> 0} \<or>
        g ` {0..t} \<subseteq> {z. Im z \<le> 0} \<and> g ` {t..1} \<subseteq> {z. 0 \<le> Im z}"
  proof -
    have "open_segment 0 b \<subseteq> frontier (inside (path_image g)) \<or>
          open_segment 0 b \<subseteq> interior (inside (path_image g))"
    proof (rule convex_open_segment_cases_alt)
      show "0 \<in> closure (inside (path_image g))"
        using hull_inc convex_hull_eq_closure_inside
        by (metis assms conv g pathfinish_in_path_image)
      show "b \<in> closure (inside (path_image g))"
        using hull_inc convex_hull_eq_closure_inside
        using R.g(2) b(1) conv g(1,2) by fastforce
    qed (simp add: conv)
    then consider "open_segment 0 b \<subseteq> path_image g" | "open_segment 0 b \<subseteq> inside (path_image g)"
      by (metis Jordan_inside_outside g interior_subset subset_trans)
    then show ?thesis
    proof cases
      case 1
      then have conn: "connectedin (subtopology euclidean (path_image g)) (open_segment 0 b)"
        by (simp add: connectedin_subtopology convex_connected)
      have pi1: "g ` {0<..<t} \<subseteq> path_image g" and pi2: "g ` {t<..<1} \<subseteq> path_image g"
        using t by (auto simp: path_image_def image_iff)
      have "closed (g ` {t..1})"
        using compact_continuous_image[OF continuous_on_subset[OF cont_g]]
        by (simp add: compact_imp_closed less_eq_real_def t(2))
      then have "closure (g ` {t<..<1}) \<subseteq> g ` {t..1}"
        by (metis closure_minimal image_mono interior_atLeastAtMost_real interior_subset)
      then have "closure (path_image g \<inter> g ` {t<..<1}) \<subseteq> g ` {t..1}"
        by (meson Int_lower2 closure_mono dual_order.trans)
      then have cl1: "g ` {0<..<t} \<inter> path_image g \<inter> closure (path_image g \<inter> g ` {t<..<1}) = {}"
        using g t by (fastforce simp: loop_free_def simple_path_def)
      have closed_img: "closed (g ` {0..t})"
        using \<open>t < 1\<close> by (simp add: compact_continuous_image compact_imp_closed continuous_on_path path_g)
      have "closure (g ` {0<..<t}) \<subseteq> g ` {0..t}"
        by (metis closed_img closure_greaterThanLessThan closure_minimal closure_subset image_mono t)
      then have "closure (path_image g \<inter> g ` {0<..<t}) \<subseteq> g ` {0..t}"
        by (meson Int_lower2 closure_mono dual_order.trans)
      then have cl2: "g ` {t<..<1} \<inter> path_image g \<inter> closure (path_image g \<inter> g ` {0<..<t}) = {}"
        using g t by (fastforce simp: loop_free_def simple_path_def)
      have decomp: "path_image g \<subseteq> g ` {0<..<t} \<union> g ` {t<..<1} \<union> {0, b}"
      proof
        fix z assume "z \<in> path_image g"
        then obtain s where s: "s \<in> {0..1}" "g s = z" by (auto simp: path_image_def)
        then consider "s = 0" | "s \<in> {0<..<t}" | "s = t" | "s \<in> {t<..<1}" | "s = 1"
          using t by force
        then show "z \<in> g ` {0<..<t} \<union> g ` {t<..<1} \<union> {0, b}"
          using \<open>g s = z\<close> t g0 g1 by blast 
      qed
      have "open_segment 0 b \<inter> {0, b} = {}"
        unfolding open_segment_def by auto
      then have sub: "open_segment 0 b \<subseteq> g ` {0<..<t} \<union> g ` {t<..<1}"
        using 1 decomp by auto
      have sep: "separatedin (subtopology euclidean (path_image g)) (g ` {0<..<t}) (g ` {t<..<1})"
      proof -
        have d1: "g ` {0<..<t} \<inter> closure (g ` {t<..<1}) = {}"
          by (metis Int_absorb1 Int_commute cl1 pi1 pi2)
        have d2: "g ` {t<..<1} \<inter> closure (g ` {0<..<t}) = {}"
          by (metis Int_absorb1 Int_commute cl2 pi1 pi2)
        have "separatedin euclidean (g ` {0<..<t}) (g ` {t<..<1})"
          using d1 d2 by (simp add: separatedin_def)
        then show ?thesis
          using pi1 pi2 by (simp add: separatedin_subtopology)
      qed
      have "open_segment 0 b \<subseteq> g ` {0<..<t} \<or> open_segment 0 b \<subseteq> g ` {t<..<1}"
        using connectedin_subset_separated_union[OF conn sep sub] .
      then have "closed_segment 0 b \<subseteq> g ` {0..t} \<or> closed_segment 0 b \<subseteq> g ` {t..1}"
        unfolding closed_segment_eq_open
        by (elim disj_forward) (use g0 g1 t in auto)
      then have seg_eq: "g ` {0..t} = closed_segment 0 b \<or> g ` {t..1} = closed_segment 0 b"
      proof (elim disjE)
        assume sub: "closed_segment 0 b \<subseteq> g ` {0..t}"
        have inj: "inj_on g {0..t}" using arc_inj_on[of 0 t] t by auto
        then have cont_inv: "continuous_on (g ` {0..t}) (the_inv_into {0..t} g)"
          by (simp add: continuous_on_inv_into continuous_on_path less_eq_real_def path_g t)
        have eq0: "the_inv_into {0..t} g 0 = 0"
          using the_inv_into_f_f[OF inj, of 0] g0 t by auto
        have eqt: "the_inv_into {0..t} g b = t"
          using the_inv_into_f_f[OF inj, of t] t by auto
        have conn: "connected (the_inv_into {0..t} g ` closed_segment 0 b)"
          by (intro connected_continuous_image continuous_on_subset[OF cont_inv sub]
              connected_segment)
        have "0 \<in> the_inv_into {0..t} g ` closed_segment 0 b"
          using eq0 by (auto intro: rev_image_eqI)
        moreover have "t \<in> the_inv_into {0..t} g ` closed_segment 0 b"
          using eqt by (auto intro: rev_image_eqI)
        ultimately have "{0..t} \<subseteq> the_inv_into {0..t} g ` closed_segment 0 b"
          using connected_contains_Icc[OF conn] by auto
        then have "g ` {0..t} \<subseteq> g ` (the_inv_into {0..t} g ` closed_segment 0 b)"
          by (rule image_mono)
        also have "\<dots> \<subseteq> closed_segment 0 b"
          using f_the_inv_into_f[OF inj] sub by (auto simp: image_image)
        finally show ?thesis using sub by auto
      next
        assume sub: "closed_segment 0 b \<subseteq> g ` {t..1}"
        have inj: "inj_on g {t..1}" using arc_inj_on[of t 1] t by auto
        then have cont_inv: "continuous_on (g ` {t..1}) (the_inv_into {t..1} g)"
          by (simp add: continuous_on_inv_into continuous_on_path less_eq_real_def path_g t)
        have eqt: "the_inv_into {t..1} g b = t"
          using the_inv_into_f_f[OF inj, of t] t by auto
        have eq1: "the_inv_into {t..1} g 0 = 1"
          using the_inv_into_f_f[OF inj, of 1] g1 t by auto
        have conn: "connected (the_inv_into {t..1} g ` closed_segment 0 b)"
          by (intro connected_continuous_image continuous_on_subset[OF cont_inv sub]
              connected_segment)
        have "t \<in> the_inv_into {t..1} g ` closed_segment 0 b"
          using eqt by (auto intro: rev_image_eqI)
        moreover have "1 \<in> the_inv_into {t..1} g ` closed_segment 0 b"
          using eq1 by (auto intro: rev_image_eqI)
        ultimately have "{t..1} \<subseteq> the_inv_into {t..1} g ` closed_segment 0 b"
          using connected_contains_Icc[OF conn] by auto
        then have "g ` {t..1} \<subseteq> g ` (the_inv_into {t..1} g ` closed_segment 0 b)"
          by (rule image_mono)
        also have "\<dots> \<subseteq> closed_segment 0 b"
          using f_the_inv_into_f[OF inj] sub by (auto simp: image_image)
        finally show ?thesis using sub by auto
      qed
        \<comment> \<open>Use \<open>convex_triple_rel_frontier\<close> to show the inside is on one side of $Im = 0$\<close>
      have inside_side: "inside (path_image g) \<subseteq> {z. Im z \<le> 0} \<or>
                         inside (path_image g) \<subseteq> {z. 0 \<le> Im z}"
      proof -
        have J: "inside (path_image g) \<noteq> {}" "open (inside (path_image g))"
          "frontier (inside (path_image g)) = path_image g"
          using Jordan_inside_outside g by blast+
        have rf_eq: "rel_frontier (inside (path_image g)) = frontier (inside (path_image g))"
          by (simp add: J interior_open rel_frontier_nonempty_interior)
        have rf0: "(0::complex) \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) g0 by (auto simp: path_image_def intro!: image_eqI[of _ _ 0])
        have rfb: "b \<in> rel_frontier (inside (path_image g))"
          using rf_eq J(3) b(1) by auto
        have rfm: "midpoint 0 b \<in> rel_frontier (inside (path_image g))"
          using "1" J(3) R.b(2) assms rf_eq by fastforce
        have ne1: "(0::complex) \<noteq> b" using b(2) assms by (auto simp: complex_eq_iff)
        have ne2: "(0::complex) \<noteq> midpoint 0 b"
          using ne1 by (simp add: midpoint_def complex_eq_iff)
        have ne3: "b \<noteq> midpoint 0 b"
          using ne1 by (simp add: midpoint_def complex_eq_iff)
        have ip: "\<i> \<bullet> (0::complex) = 0" "\<i> \<bullet> b = 0" "\<i> \<bullet> midpoint 0 b = 0" using Im_b by (auto simp: midpoint_def)
        have "inside (path_image g) \<subseteq> {x. \<i> \<bullet> x \<le> 0} \<or>
              inside (path_image g) \<subseteq> {x. \<i> \<bullet> x \<ge> 0}"
          using convex_triple_rel_frontier[OF conv rf0 rfb rfm ne1 ne2 ne3 ip] .
        then show ?thesis by auto
      qed
      have pi_sub: "path_image g \<subseteq> closure (inside (path_image g))"
        using hull_subset[of "path_image g" convex] convex_hull_eq_closure_inside[OF g(1)] g(2,3) conv by force
          \<comment> \<open>The closed segment from $0$ to $b$ has $Im = 0$, so lies in both half-planes.\<close>
      have seg_both: "closed_segment 0 b \<subseteq> {z. Im z \<le> 0}" "closed_segment 0 b \<subseteq> {z. 0 \<le> Im z}"
        using Im_b by (auto simp: closed_segment_def)
          \<comment> \<open>If the inside is contained in a half-plane, then so is @{term "path_image g"} (by closure).\<close>
      have side_le: "inside (path_image g) \<subseteq> {z. Im z \<le> 0} \<Longrightarrow> path_image g \<subseteq> {z. Im z \<le> 0}"
        using pi_sub closure_minimal[OF _ closed_halfspace_le[of \<i> 0, simplified complex_inner_i_left]]
        by auto
      have side_ge: "inside (path_image g) \<subseteq> {z. 0 \<le> Im z} \<Longrightarrow> path_image g \<subseteq> {z. 0 \<le> Im z}"
        using pi_sub closure_minimal[OF _ closed_halfspace_ge[of 0 \<i>, simplified complex_inner_i_left]]
        by auto
      from seg_eq inside_side show ?thesis
        using side_le side_ge seg_both t unfolding path_image_def image_subset_iff
        by (elim disjE; simp; blast)
    next
      case seg_inside:2
      have real_on_curve: "z = 0 \<or> z = b" 
        if z_on: "z \<in> path_image g" and z_real: "Im z = 0" for z
      proof (rule ccontr)
        assume non: "\<not> ?thesis"
          \<comment> \<open>Step 1: Basic setup\<close>
          \<comment> \<open>Step 2: diameter bounds force @{term z} into @{term "closed_segment 0 b"}.
       $\mathit{dist}\,0\,z \le \mathit{diam} = Re\,b$ gives $|Re\,z| \le Re\,b$.
       $\mathit{dist}\,z\,b \le \mathit{diam} = Re\,b$ gives $|Re\,z - Re\,b| \le Re\,b$, hence $Re\,z \ge 0$.
       So @{term z} is real with $0 \le Re\,z \le Re\,b$, i.e. @{term "z \<in> closed_segment 0 b"}.\<close>
        have bdd: "bounded (path_image g)"
          using g(1) bounded_simple_path_image by blast
        have z0_on: "0 \<in> path_image g"
          using pathstart_in_path_image[of g] g(2) \<open>a=0\<close> by simp
        have diam_eq: "diameter (path_image g) = Re b"
          using dab \<open>a=0\<close> Im_b Reb by (simp add: dist_complex_def cmod_eq_Re)
        have d1: "dist 0 z \<le> Re b"
          using diameter_bounded_bound[OF bdd z0_on z_on] diam_eq by simp
        have d2: "dist z b \<le> Re b"
          using diameter_bounded_bound[OF bdd z_on b(1)] diam_eq by simp
        have Re_le: "Re z \<le> Re b"
          using d1 z_real by (simp add: dist_complex_def cmod_eq_Re)
        have Re_ge: "Re z \<ge> 0"
          using d2 z_real Im_b by (simp add: dist_complex_def cmod_eq_Re)
        have z_eq: "z = of_real (Re z)"
          using z_real complex_is_Real_iff of_real_Re by metis
        have b_eq: "b = of_real (Re b)"
          using Im_b complex_is_Real_iff of_real_Re by metis
        have z_in_seg: "z \<in> closed_segment 0 b"
          by (metis Re_ge Re_le Reb atLeastAtMost_iff b_eq closed_segment_eq_real_ivl1
              less_eq_real_def of_real_0 of_real_closed_segment z_eq)
          \<comment> \<open>Step 4: @{term z} is on the curve, so @{term "z \<notin> inside (path_image g)"}. Hence @{term "z \<notin> open_segment 0 b"}.
       Combined with @{term "z \<in> closed_segment 0 b"}, we get $z = 0 \vee z = b$.\<close>
        have "z \<notin> inside (path_image g)"
          using inside_no_overlap z_on by blast
        then show False
          using non seg_inside z_in_seg by (auto simp: closed_segment_eq_open)
      qed
\<comment> \<open>@{term "Im \<circ> g"} doesn't change sign on either arc: if it did, the IVT gives a real point
     in the interior of the arc, contradicting \<open>real_on_curve\<close> and injectivity.\<close>
      have no_cross: "(\<forall>s \<in> {u..v}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {u..v}. Im (g s) \<le> 0)"
        if huv: "u < v" "{u..v} \<subseteq> {0..1}" and hinj: "inj_on g {u..v}"
          and hend: "Im (g u) = 0" "Im (g v) = 0" for u v
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain s\<^sub>1 s\<^sub>2 where s1: "s\<^sub>1 \<in> {u..v}" "Im (g s\<^sub>1) > 0" and s2: "s\<^sub>2 \<in> {u..v}" "Im (g s\<^sub>2) < 0"
          by (meson linorder_not_le)
        have cont_uv: "continuous_on {u..v} g"
          using cont_g continuous_on_subset huv(2) by blast
            \<comment> \<open>The IVT gives $s \in (u,v)$ with $Im(g\,s) = 0$\<close>
        obtain s where s: "s \<in> {u..v}" "Im (g s) = 0" "s \<noteq> u" "s \<noteq> v"
        proof (cases "s\<^sub>1 \<le> s\<^sub>2")
          case True
          obtain s where hs: "s \<in> {s\<^sub>1..s\<^sub>2}" "Im (g s) = 0"
            using ivt_decreasing_component_on_1[OF True, of g \<i> 0]
              continuous_on_subset[OF cont_uv] s1 s2
            by (force simp: complex_inner_i_right)
          have "s \<in> {u..v}" using hs(1) s1(1) s2(1) by auto
          then show thesis using that hend s1 s2 hs by fastforce
        next
          case False
          then have le: "s\<^sub>2 \<le> s\<^sub>1" by linarith
          obtain s where hs: "s \<in> {s\<^sub>2..s\<^sub>1}" "Im (g s) = 0"
            using ivt_increasing_component_on_1[OF le, of g \<i> 0]
              continuous_on_subset[OF cont_uv] s1 s2
            by (force simp: complex_inner_i_right)
          have "s \<in> {u..v}" using hs(1) s1(1) s2(1) by auto
          then show thesis using that hend s1 s2 hs by fastforce
        qed
        have "g s \<in> path_image g"
          using s(1) huv(2) by (auto simp: path_image_def subset_iff)
        then have "g s = 0 \<or> g s = b" using real_on_curve s(2) by blast
        moreover have "g s \<noteq> g u" "g s \<noteq> g v"
          using inj_onD[OF hinj] s by auto
        moreover have "g u \<in> {0, b}" "g v \<in> {0, b}"
          using real_on_curve hend huv by (auto simp: path_image_def subset_iff)
        ultimately show False
          using \<open>u < v\<close> inj_onD [OF hinj] by (auto simp: order_class.less_le)
      qed
      have no_cross_1: "(\<forall>s \<in> {0..t}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {0..t}. Im (g s) \<le> 0)"
        using no_cross[of 0 t] arc_inj_on[of 0 t] t g0 Im_b by auto
      have no_cross_2: "(\<forall>s \<in> {t..1}. Im (g s) \<ge> 0) \<or> (\<forall>s \<in> {t..1}. Im (g s) \<le> 0)"
        using no_cross[of t 1] arc_inj_on[of t 1] t g1 Im_b by auto
      have not_all_above: "\<not> (path_image g \<subseteq> {z. 0 \<le> Im z})"
        using Reb assms not_all_above real_on_curve t Im_b by blast
      have not_all_below: "\<not> (path_image g \<subseteq> {z. Im z \<le> 0})"
        using CR.not_all_above using g g0 g1 assms Reb real_on_curve
        by (force simp add: gop_def  path_image_compose)
      have pi1: "path_image g = g ` {0..t} \<union> g ` {t..1}"
        unfolding path_image_def using t(2,3)
        by (metis image_Un ivl_disj_un_two_touch(4) less_eq_real_def)
      from no_cross_1 no_cross_2 not_all_above not_all_below pi1
      show ?thesis by (auto simp: image_subset_iff)
    qed
  qed
  then show ?thesis
    using assms split_case' t Green_area_zero_A by blast
qed


subsection \<open>Conclusion of Green's theorem and the signed area formula for a convex closed curve.\<close>

lemma Green_invariant:
  assumes "\<And>g g' U b. Green g g' U 0 b \<Longrightarrow> Green_concl g g'"
  shows "Green_concl g g'"
proof -
  have *: "Green_concl ((\<lambda>x. -a+x) \<circ> g) g'"
  proof (intro assms)
    show "Green ((+) (- a) \<circ> g) g' U 0 (-a+b)"
    proof
      show "simple_path ((+) (- a) \<circ> g)"
        by (simp add: g simple_path_translation_eq)
      show "pathstart ((+) (- a) \<circ> g) = 0"
        by (simp add: g pathstart_compose)
      show "pathfinish ((+) (- a) \<circ> g) = 0"
        by (simp add: g pathfinish_compose)
      show "- a + b \<in> path_image ((+) (- a) \<circ> g)"
        by (simp add: b path_image_translation)
       show "dist 0 (- a + b) = diameter (path_image ((+) (- a) \<circ> g))"
         by (metis add.commute dab diameter_translation dist_0_norm dist_commute dist_norm path_image_compose pth_2)
      show "convex (inside (path_image ((+) (- a) \<circ> g)))"
        by (metis path_image_translation inside_translation convex_translation_eq conv)
      show "absolutely_continuous_on {0..1} ((+) (- a) \<circ> g)"
        by (metis (no_types, lifting) ext absolutely_continuous_on_add absolutely_continuous_on_const cont o_apply)
    next
      fix t
      assume "t \<in> {0..1} - U"
      then show "((+) (- a) \<circ> g has_vector_derivative g' t) (at t)"
        using has_vector_derivative_shift vder by blast
    qed (use b U in auto)
  qed
  have ai_translated: "(\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t)) absolutely_integrable_on {0..1}"
    using * unfolding Green_concl_def by auto
  have Ima_ai: "(\<lambda>t. Im a * Re (g' t)) absolutely_integrable_on {0..1}"
    by (simp add: Re_absolutely_integrable_on gp_ai)
  show ?thesis
    unfolding Green_concl_def
  proof (intro conjI absolutely_integrable_integrable_bound)
    fix t :: real assume "t \<in> {0..1}"
    show "norm (Re (g' t) * Im (g t)) \<le> \<bar>Re (g' t) * Im (((+) (- a) \<circ> g) t)\<bar> + \<bar>Im a * Re (g' t)\<bar>"
      by (simp add: o_def plus_complex.sel uminus_complex.sel real_norm_def algebra_simps)
  next
    show "(\<lambda>t. Re (g' t) * Im (g t)) integrable_on {0..1}"
      using absolutely_integrable_on_def f_abs_int by blast
    show "(\<lambda>t. \<bar>Re (g' t) * Im (((+) (- a) \<circ> g) t)\<bar> + \<bar>Im a * Re (g' t)\<bar>) integrable_on {0..1}"
      using ai_translated Ima_ai unfolding absolutely_integrable_on_def
      by (metis (no_types, lifting)  integrable_cong real_norm_def integrable_add)
  next
    show "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> = Sigma_Algebra.measure lebesgue (inside (path_image g))"
    proof -
      have meas_eq: "measure lebesgue (inside (path_image ((+) (- a) \<circ> g)))
                   = measure lebesgue (inside (path_image g))"
        by (metis path_image_translation inside_translation measure_translation)
      have "(g' has_integral (g 1 - g 0)) {0..1}"
        using fundamental_theorem_of_calculus_absolutely_continuous[OF U _ cont, of g']
        by (metis zero_le_one vder has_vector_derivative_at_within)
      then have int_g': "(g' has_integral 0) {0..1}"
        using g by (simp add: pathstart_def pathfinish_def)
      have Re_has_int: "((\<lambda>t. Re (g' t)) has_integral 0) {0..1}"
        using has_integral_Re[OF int_g'] by simp
      have Ima_has_int: "((\<lambda>t. Im a * Re (g' t)) has_integral 0) {0..1}"
        using has_integral_mult_right[OF Re_has_int] by simp
      have int_extra: "integral {0..1} (\<lambda>t. Im a * Re (g' t)) = 0"
        using integral_unique[OF Ima_has_int] .
      have translated_eq: "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t))\<bar>
                         = measure lebesgue (inside (path_image g))"
        using * unfolding Green_concl_def using meas_eq by auto
      have ai_translated: "(\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t)) integrable_on {0..1}"
        using * unfolding Green_concl_def absolutely_integrable_on_def by auto
      have Ima_integrable: "(\<lambda>t. Im a * Re (g' t)) integrable_on {0..1}"
        using Ima_has_int by (rule has_integral_integrable)
      have "integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))
          = integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t) + Im a * Re (g' t))"
        by (simp add: o_def plus_complex.sel uminus_complex.sel algebra_simps)
      also have "\<dots> = integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t))
                    + integral {0..1} (\<lambda>t. Im a * Re (g' t))"
        using integral_add[OF ai_translated Ima_integrable] .
      also have "\<dots> = integral {0..1} (\<lambda>t. Re (g' t) * Im (((+) (- a) \<circ> g) t))"
        unfolding int_extra by simp
      finally show ?thesis
        using translated_eq by simp
    qed
  qed
qed

theorem area_theorem:
  obtains "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    and "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> =
      measure lebesgue (inside (path_image g))"
  using Green.Green_area_zero Green_concl_def Green_invariant by blast

end

section \<open>Part 3: Isoperimetric theorem for convex curves\<close>

text \<open>The kernel lemma: the isoperimetric inequality for a convex curve that has been
  normalized to arc-length parametrization with zero-mean imaginary part and
  diameter along the real axis starting at a point with $Re = 0$.
  This is where the Wirtinger inequality is applied.\<close>

proposition isoperimetric_kernel:
  fixes g :: "real \<Rightarrow> complex" and L :: real and a b :: complex
  assumes "0 < L"
    and conv_in: "convex (inside (path_image g))"
    and ab: "a \<in> path_image g" "b \<in> path_image g"
    and dist_ab: "dist a b = diameter (path_image g)"
    and bma: "b - a = of_real (dist a b)"
    and ga: "pathstart g = a" "pathfinish g = a"
    and g: "rectifiable_path g" "simple_path g"
    and L: "path_length g = L"
    and arc_length: "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g) = L * t"
    and lipschitz: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
    and "Re a = 0"
    and "(Im \<circ> g has_integral 0) {0..1}"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>c r. path_image g = sphere c r"
proof -
  define S where "S = {x \<in> {0..1}. \<not> g differentiable (at x)}"
  have bdd: "bounded (path_image g)"
    using g bounded_simple_path_image by blast
  then have "a \<noteq> b"
    using diameter_eq_0  ab dist_ab g nonempty_simple_path_endless by fastforce
  have acont_g: "absolutely_continuous_on {0..1} g"
    by (metis Lipschitz_imp_absolutely_continuous lipschitz dist_norm real_norm_def)
  then have negS: "negligible S"
    unfolding S_def using Lebesgue_differentiation_thm g
    using is_interval_cc rectifiable_path_def by blast
  define g' where "g' = (\<lambda>x. vector_derivative g (at x))"
  have g'_deriv: "\<And>x. x \<in> {0..1} - S \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
    by (simp add: S_def g'_def vector_derivative_works)
  have g'_integral: "g' absolutely_integrable_on {0..1} \<and> (\<forall>x\<in>{0..1}. (g' has_integral g x - g 0) {0..x})"
    unfolding absolute_integral_absolutely_continuous_derivative_eq
    by (metis has_vector_derivative_at_within acont_g negS g'_deriv)
  then have g'_int: "g' absolutely_integrable_on {0..t} \<and> integral {0..t} g' = g t - a" 
    if "t \<in> {0..1::real}" for t
    using ga that unfolding pathstart_def
    by (metis absolutely_integrable_on_subinterval atLeastAtMost_iff atLeastatMost_subset_iff
        order.refl integral_unique)
  have norm_g'_int: "(\<lambda>x. norm (g' x)) absolutely_integrable_on {0..t} \<and> integral {0..t} (\<lambda>x. norm (g' x)) = L * t"
    if "t \<in> {0..1}" for t
  proof -
    have acont_gt: "absolutely_continuous_on {0..t} g"
      using absolutely_continuous_on_subset[OF acont_g] that by auto
    have g'_deriv_t: "\<And>x. x \<in> {0..t} - S \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
      using g'_deriv that by auto
    have "vector_variation {0..t} g = integral {0..t} (\<lambda>u. norm (g' u))"
      using vector_variation_integral_norm_derivative[OF negS _ acont_gt g'_deriv_t] that
      by presburger
    moreover have "vector_variation {0..t} g = L * t"
      using that \<open>rectifiable_path g\<close> path_length_subpath_eq [of 0 t, symmetric] arc_length
      by (fastforce simp: closed_segment_eq_real_ivl1)
    ultimately show ?thesis
      using that g'_int set_integrable_norm that by auto
  qed
  have norm_g'_le: "norm (g' x) \<le> L" if "x \<in> {0..1} - S" for x
  proof -
    have gd: "(g has_vector_derivative g' x) (at x)" using g'_deriv that by auto
    have xlimpt: "x islimpt {0..1::real}"
      using limpt_of_convex[of "{0..1::real}" x] that by auto
    have Ld: "((\<lambda>t. L * t) has_vector_derivative L) (at x within {0..1})"
      using has_vector_derivative_mult_right[OF has_vector_derivative_id] by simp
    have ev: "\<forall>\<^sub>F y in at x within {0..1}. norm (g y - g x) \<le> norm (L * y - L * x)"
      unfolding eventually_at_filter
    proof (intro always_eventually allI impI)
      fix y assume "y \<noteq> x" "y \<in> {0..1}"
      have "dist (g y) (g x) \<le> L * dist y x"
        using lipschitz \<open>y \<in> {0..1}\<close> that by auto
      then have "norm (g y - g x) \<le> L * \<bar>y - x\<bar>"
        by (simp add: dist_norm dist_real_def)
      also have "\<dots> = \<bar>L * (y - x)\<bar>"
        using \<open>0 < L\<close> by (simp add: abs_mult)
      also have "\<dots> = norm (L * y - L * x)"
        by (simp add: right_diff_distrib)
      finally show "norm (g y - g x) \<le> norm (L * y - L * x)" .
    qed
    show "norm (g' x) \<le> L"
      using \<open>0 < L\<close> norm_vector_derivatives_le_within [OF _ Ld ev] xlimpt gd has_vector_derivative_at_within
      by (force simp add: trivial_limit_within) 
  qed
  have norm_g'_sq_int: "(\<lambda>x. (norm (g' x))\<^sup>2) absolutely_integrable_on {0..1}"
  proof (rule measurable_bounded_by_integrable_imp_absolutely_integrable_ae)
    show "(\<lambda>x. (norm (g' x))\<^sup>2) \<in> borel_measurable (lebesgue_on {0..1})"
      by (simp add: absolutely_integrable_imp_integrable borel_measurable_integrable
          borel_measurable_power norm_g'_int)
    show "negligible S" by (rule negS)
    show "\<And>x. x \<in> {0..1} - S \<Longrightarrow> norm ((norm (g' x))\<^sup>2) \<le> L\<^sup>2"
      by (simp add: norm_g'_le power_mono)
  qed auto
  have integral_norm_g'_sq: "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x. (norm (g' x))\<^sup>2) = L\<^sup>2"
  proof -
    have norm_g'_abs: "(\<lambda>x. norm (g' x)) absolutely_integrable_on {0..1}"
      using norm_g'_int[of 1] by auto
    have norm_g'_leb: "integrable (lebesgue_on {0..1}) (\<lambda>x. norm (g' x))"
      by (simp add: absolutely_integrable_imp_integrable norm_g'_abs)
    have int_norm_g': "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x. norm (g' x)) = L"
      by (simp add: lebesgue_integral_eq_integral norm_g'_int norm_g'_leb)
    have int_const: "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x::real. L) = L"
      using lebesgue_integral_const[of "lebesgue_on {0..1}" L]
      by (simp add: measure_restrict_space)
    have ae_le: "AE x in lebesgue_on {0..1}. norm (g' x) \<le> L"
    proof -
      have "S \<inter> {0..1} \<in> null_sets (lebesgue_on {0..1})"
        using negS negligible_iff_null_sets null_sets_restrict_space
        by (metis atLeastAtMost_borel inf_le2 negligible_Int sets_completionI_sets sets_lborel)
      then have "AE x in lebesgue_on {0..1}. x \<notin> S"
        by (metis AE_not_in Collect_subset S_def inf.orderE)
      then show ?thesis
        using norm_g'_le by (auto elim: eventually_mono)
    qed
    have ae_eq: "AE x in lebesgue_on {0..1}. norm (g' x) = L"
      using integral_ineq_eq_0_then_AE[OF ae_le norm_g'_leb] int_norm_g' int_const by simp
    have ae_sq: "AE x in lebesgue_on {0..1}. (norm (g' x))\<^sup>2 = L\<^sup>2"
      using ae_eq by (rule AE_mp) auto
    have meas_sq: "(\<lambda>x. (norm (g' x))\<^sup>2) \<in> borel_measurable (lebesgue_on {0..1})"
        using absolutely_integrable_imp_borel_measurable[OF conjunct1[OF g'_int]]
              borel_measurable_power norm_g'_leb by blast
    have "integral\<^sup>L (lebesgue_on {0..1::real}) (\<lambda>x. (norm (g' x))\<^sup>2) =
          integral\<^sup>L (lebesgue_on {0..1::real}) (\<lambda>x. L\<^sup>2)"
      by (rule integral_cong_AE[OF meas_sq _ ae_sq]) simp
    also have "\<dots> = L\<^sup>2"
      using lebesgue_integral_const[of "lebesgue_on {0..1::real}" "L\<^sup>2"]
      by (simp add: measure_restrict_space)
    finally show ?thesis .
  qed

  text \<open>Use the Green formula for the area inside the curve.\<close>
  have "Re a < Re b"
    by (metis Re_complex_of_real \<open>a \<noteq> b\<close> \<open>Re a = 0\<close> bma diff_zero dist_nz minus_complex.sel(1))
  moreover have "Im a = Im b"
    using bma by (simp add: complex_of_real_def complex_eq_iff)
  ultimately interpret G: Green g g' S a b
  proof unfold_locales
  qed (use g ga ab negS dist_ab conv_in acont_g g'_deriv in auto)
  have green_ai: "(\<lambda>t. Re (g' t) * Im (g t)) absolutely_integrable_on {0..1}"
    and green_area: "\<bar>integral {0..1} (\<lambda>t. Re (g' t) * Im (g t))\<bar> = measure lebesgue (inside (path_image g))"
    by (metis (full_types) G.area_theorem)+
  then have integrable: "(\<lambda>t. Re (g' t) * Im (g t)) integrable_on {0..1}"
    using absolutely_integrable_on_def by blast
  obtain sgn where sgn2: "sgn\<^sup>2 = 1"
    and has_int_green: "((\<lambda>t. Re (g' t) * Im (g t)) has_integral
                         (sgn * measure lebesgue (inside (path_image g)))) {0..1}"
    using green_area
    by (smt (verit) has_integral_iff integrable mult_cancel_right2 mult_minus_left power2_eq_square)

  have int_on: "(\<lambda>x. (norm (g' x))\<^sup>2) integrable_on {0..1}"
    using norm_g'_sq_int absolutely_integrable_on_def by blast
  have "integral {0..1} (\<lambda>x. (norm (g' x))\<^sup>2) = L\<^sup>2"
    using integral_norm_g'_sq norm_g'_sq_int
      lebesgue_integral_eq_integral[of "{0..1}" "\<lambda>x. (norm (g' x))\<^sup>2"]
      absolutely_integrable_imp_integrable[OF norm_g'_sq_int]
    by auto
  then have has_int_norm_sq: "((\<lambda>x. (norm (g' x))\<^sup>2) has_integral L\<^sup>2) {0..1}"
    using int_on by (simp add: has_integral_integrable_integral)
  have has_int_key: "((\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 +
    (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2) has_integral
    (L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi)) {0..1}"
  proof -
    have sgn_sq: "sgn * sgn = 1" using sgn2 by (metis power2_eq_square)
    have integrand_eq: "(Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 + (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2 =
      (norm (g' x))\<^sup>2 - 4 * pi * sgn * Re (g' x) * Im (g x)" for x
    proof -
      have "(Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 + (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2 =
            (Re (g' x))\<^sup>2 + (Im (g' x))\<^sup>2 - 4 * pi * sgn * Re (g' x) * Im (g x)"
        using sgn_sq by (simp add: power2_eq_square algebra_simps)
      then show ?thesis 
        by (simp add: cmod_power2)
    qed
    have scaled_green: "((\<lambda>t. 4 * pi * sgn * (Re (g' t) * Im (g t))) has_integral
      (4 * pi * sgn * (sgn * measure lebesgue (inside (path_image g))))) {0..1}"
      using has_integral_mult_right[OF has_int_green, of "4 * pi * sgn"] .
    have val: "4 * pi * sgn * (sgn * measure lebesgue (inside (path_image g))) =
      measure lebesgue (inside (path_image g)) * 4 * pi"
      using sgn_sq by (simp add: algebra_simps)
    have scaled_green': "((\<lambda>t. 4 * pi * sgn * Re (g' t) * Im (g t)) has_integral
      (measure lebesgue (inside (path_image g)) * 4 * pi)) {0..1}"
      using scaled_green unfolding val by (simp add: algebra_simps)
    then show ?thesis
      using has_integral_diff[OF has_int_norm_sq scaled_green'] integrand_eq by presburger
  qed

  have key: "0 \<le> L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi \<and>
             (L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi = 0 \<longrightarrow>
             (\<exists>c r. path_image g = sphere c r))"
  proof (cases "inside(path_image g) = {}")
    case False
    have Im_g'_has_int: "((\<lambda>t. Im (g' t)) has_integral (Im (g x) - Im (g 0))) {0..x}"
      if "x \<in> {0..1}" for x
      by (metis g'_integral has_integral_Im minus_complex.simps(2) that)
    have Im_g_periodic: "Im (g 1) = Im (g 0)"
      using ga by (simp add: pathstart_def pathfinish_def)
    have Im_g_zero_mean: "((\<lambda>x. Im (g x)) has_integral 0) {0..1}"
      using assms by (simp add: o_def)
    have Im_g'_sq_int: "(\<lambda>x. (Im (g' x))\<^sup>2) integrable_on {0..1}"
    proof -
      have "(\<lambda>x. (Im (g' x))\<^sup>2) absolutely_integrable_on {0..1}"
      proof (rule measurable_bounded_by_integrable_imp_absolutely_integrable_ae)
        show "(\<lambda>x. (Im (g' x))\<^sup>2) \<in> borel_measurable (lebesgue_on {0..1})"
          by (simp add: Im_absolutely_integrable_on absolutely_integrable_imp_borel_measurable
              borel_measurable_power g'_integral)
        show "negligible S" by (rule negS)
        fix x assume "x \<in> {0..1} - S"
        then have "norm (g' x) \<le> L" using norm_g'_le by auto
        then show "norm ((Im (g' x))\<^sup>2) \<le> L\<^sup>2"
          by (metis abs_Im_le_cmod order.trans norm_ge_zero norm_power power_mono real_norm_def)
      qed auto
      then show ?thesis
        using absolutely_integrable_on_def by blast
    qed
    have wirt1: "(\<lambda>x. (Im (g x))\<^sup>2) integrable_on {0..1}"
      and wirt2: "integral {0..1} (\<lambda>x. (2*pi * Im (g x))\<^sup>2) \<le> integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2)"
      and wirt3: "integral {0..1} (\<lambda>x. (2*pi * Im (g x))\<^sup>2) = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2) \<Longrightarrow>
        \<exists>c a. \<forall>x \<in> {0..1}. Im (g x) = c * sin (2*pi*x - a)"
      using scaled_Wirtinger_inequality[OF Im_g'_has_int Im_g_periodic Im_g_zero_mean Im_g'_sq_int]
      by auto
    obtain w where w: "((\<lambda>x. (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2) has_integral w) {0..1}"
    proof -
      have sq: "(\<lambda>x. (2 * pi * Im (g x))\<^sup>2) integrable_on {0..1}"
        using integrable_cmul[OF wirt1, of "(2*pi)\<^sup>2"] by (simp add: power_mult_distrib mult.commute)
      with that show ?thesis
        using integrable_diff[OF Im_g'_sq_int sq] by force
    qed
    then have "w = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2 - (2 * pi * Im (g x))\<^sup>2)"
      by (simp add: integral_unique)
    also have "\<dots> = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2) - integral {0..1} (\<lambda>x. (2 * pi * Im (g x))\<^sup>2)"
      using integrable_cmul[OF wirt1, of "(2*pi)\<^sup>2"]
      by (metis (no_types, lifting) integral_cong integral_diff Im_g'_sq_int power_mult_distrib real_scaleR_def)
    finally have w_eq: "w = integral {0..1} (\<lambda>x. (Im (g' x))\<^sup>2) - integral {0..1} (\<lambda>x. (2 * pi * Im (g x))\<^sup>2)" .
    have w_nonneg: "w\<ge>0"
      using w_eq wirt2 by linarith
    have w_zero: "w = 0 \<Longrightarrow> \<exists>c a. \<forall>x \<in> {0..1}. Im (g x) = c * sin (2*pi*x - a)"
      by (simp add: w_eq wirt3)
    define d where "d = L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi - w"
    have key_eq: "L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi = d + w"
      unfolding d_def by linarith

    have sq_has_int: "((\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) has_integral d) {0..1}"
      using has_integral_diff[OF has_int_key w] by (simp add: d_def)
    have "0 \<le> integral {0..1} (\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2)"
      using integral_nonneg sq_has_int zero_le_power2 by blast
    then have d_nonneg: "0 \<le> d"
      using integral_unique[OF sq_has_int] by linarith
    have dw_nonneg: "0 \<le> d + w"
      using d_nonneg w_nonneg by linarith
    moreover have "\<exists>c r. path_image g = sphere c r"  if "d + w = 0"
    proof -
      have d0: "d = 0" and w0: "w = 0"
        using that d_nonneg w_nonneg by linarith+
      obtain C A where CA: "\<And>x. x \<in> {0..1} \<Longrightarrow> Im (g x) = C * sin (2*pi*x - A)"
        using w_zero[OF w0] by blast
      have sq_zero: "((\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) has_integral 0) {0..1}"
        using sq_has_int d0 by simp
      have sq_abs: "(\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) absolutely_integrable_on {0..1}"
        using nonnegative_absolutely_integrable_1[OF has_integral_integrable[OF sq_zero]]
        by (simp add: zero_le_power2)
      have sq_leb: "integrable (lebesgue_on {0..1}) (\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2)"
        by (rule absolutely_integrable_imp_integrable[OF sq_abs]) simp
      have leb_zero: "integral\<^sup>L (lebesgue_on {0..1}) (\<lambda>x. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2) = 0"
        using lebesgue_integral_eq_integral[OF sq_leb] integral_unique[OF sq_zero] by simp
      have "AE x in lebesgue_on {0..1}. (Re (g' x) - 2 * pi * sgn * Im (g x))\<^sup>2 = 0"
        using integral_nonneg_eq_0_iff_AE[OF sq_leb] leb_zero by simp
      then have ae: "AE x in lebesgue_on {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) = 0"
        by (rule AE_mp) (auto simp: power2_eq_square)
      from ae[unfolded eventually_ae_filter[of _ "lebesgue_on {0..1}"]]
      obtain N0 where N0: "N0 \<in> null_sets (lebesgue_on {0..1})"
        and sub: "{x \<in> space (lebesgue_on {0..1}). Re (g' x) - 2 * pi * sgn * Im (g x) \<noteq> 0} \<subseteq> N0"
        by auto
      have "negligible N0"
        by (meson N0 fmeasurableD lmeasurable_interval(1) negligible_iff_null_sets null_sets_restrict_space)
      moreover have "{x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) \<noteq> 0} \<subseteq> N0"
        using sub by auto
      ultimately have neg_Re: "negligible {x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * Im (g x) \<noteq> 0}"
        by (meson negligible_subset)
      have neg_Re': "negligible {x \<in> {0..1}. Re (g' x) - 2 * pi * sgn * C * sin (2*pi*x - A) \<noteq> 0}"
        by (smt (verit, best) CA Collect_cong more_arith_simps(11) neg_Re)
      have Re_g: "Re (g x) = - sgn * C * (cos (2*pi*x - A) - cos A)"
        if "x \<in> {0..1}" for x
      proof -
        have "(g' has_integral (g x - a)) {0..x}"
          by (metis G.g(2) g'_integral pathstart_def that)
        then have Re_g'_int: "((\<lambda>t. Re (g' t)) has_integral Re (g x)) {0..x}"
          using \<open>Re a = 0\<close> by (metis diff_zero has_integral_Re minus_complex.simps(1))
        have "((\<lambda>t. - sgn * C * cos (2 * pi * t - A)) has_vector_derivative
            2 * pi * sgn * C * sin (2 * pi * t - A)) (at t within {0..x})" for t
          by (auto intro!: derivative_eq_intros simp: algebra_simps
              simp flip: has_real_derivative_iff_has_vector_derivative)
        then have "((\<lambda>t. 2 * pi * sgn * C * sin (2 * pi * t - A)) has_integral
            ((- sgn * C * cos (2 * pi * x - A)) - (- sgn * C * cos (2 * pi * 0 - A)))) {0..x}"
          using that fundamental_theorem_of_calculus 
          by (metis (no_types, lifting) atLeastAtMost_iff)
        then have sin_int: "((\<lambda>t. 2 * pi * sgn * C * sin (2 * pi * t - A)) has_integral
          (- sgn * C * (cos (2 * pi * x - A) - cos A))) {0..x}" by (simp add: algebra_simps)
        have diff_int: "((\<lambda>t. Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A)) has_integral
          (Re (g x) - (- sgn * C * (cos (2 * pi * x - A) - cos A)))) {0..x}"
          using has_integral_diff[OF Re_g'_int sin_int] by simp
        have neg_sub: "negligible {t \<in> {0..x}. Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A) \<noteq> 0}"
          by (smt (verit) atLeastAtMost_iff mem_Collect_eq neg_Re' negligible_subset subsetI that)
        have zero_int: "((\<lambda>t. Re (g' t) - 2 * pi * sgn * C * sin (2 * pi * t - A)) has_integral 0) {0..x}"
          by (rule has_integral_spike[OF neg_sub _ has_integral_0]) auto
        show ?thesis
          using has_integral_unique[OF diff_int zero_int] by linarith
      qed
      define c where "c = Complex (sgn * C * cos A) 0"
      have subset: "path_image g \<subseteq> sphere c \<bar>C\<bar>"
      proof -
        have "cmod (g t - c) = \<bar>C\<bar>" if "t \<in> {0..1}" for t
        proof -
          have eq_gt: "g t - c = Complex (- sgn * C * cos (2*pi*t - A)) (C * sin (2*pi*t - A))"
          proof (rule complex_eqI)
            show "Re (g t - c) = Re (Complex (- sgn * C * cos (2*pi*t - A)) (C * sin (2*pi*t - A)))"
              unfolding c_def using Re_g[OF that] by (simp add: algebra_simps)
            show "Im (g t - c) = Im (Complex (- sgn * C * cos (2*pi*t - A)) (C * sin (2*pi*t - A)))"
              unfolding c_def using CA[OF that] by simp
          qed
          have "(cmod (g t - c))\<^sup>2 = (sgn * C * cos (2*pi*t - A))\<^sup>2 + (C * sin (2*pi*t - A))\<^sup>2"
            using eq_gt by (simp add: complex_norm power2_eq_square)
          also have "\<dots> = C\<^sup>2 * (sgn\<^sup>2 * (cos (2*pi*t - A))\<^sup>2 + (sin (2*pi*t - A))\<^sup>2)"
            by (simp add: algebra_simps power2_eq_square)
          also have "\<dots> = \<bar>C\<bar>\<^sup>2"
            using sgn2 by (simp add: sin_cos_squared_add3)
          finally show "cmod (g t - c) = \<bar>C\<bar>"
            using cmod_def by force
        qed
        then show ?thesis
          by (auto simp: path_image_def sphere_def dist_norm norm_minus_commute)
      qed
      have supset: "sphere c \<bar>C\<bar> \<subseteq> path_image g"
      proof (cases "C = 0")
        case True then show ?thesis
          using subset by auto
      next
        case Cne: False
        show ?thesis
        proof 
          fix z assume z: "z \<in> sphere c \<bar>C\<bar>"
          then have zc_norm: "cmod (z - c) = \<bar>C\<bar>"
            by (simp add: sphere_def dist_norm norm_minus_commute)
          \<comment> \<open>Find the angle for $(z-c)$ scaled to the unit circle\<close>
          have unit: "cmod (Complex (- Re (z - c) / (sgn * C)) (Im (z - c) / C)) = 1"
          proof -
            have "(cmod (Complex (- Re (z - c) / (sgn * C)) (Im (z - c) / C)))\<^sup>2
                = (Re (z - c))\<^sup>2 / (sgn\<^sup>2 * C\<^sup>2) + (Im (z - c))\<^sup>2 / C\<^sup>2"
              by (metis (no_types, opaque_lifting) cmod_power2 complex.sel(1,2) power2_minus
                  power_divide power_mult_distrib)
            also have "\<dots> = ((Re (z - c))\<^sup>2 + (Im (z - c))\<^sup>2) / C\<^sup>2"
              using sgn2 by (simp add: add_divide_distrib)
            also have "\<dots> = (cmod (z - c))\<^sup>2 / C\<^sup>2"
              by (simp add: cmod_power2)
            also have "\<dots> = 1"
              using Cne zc_norm by simp
            finally show ?thesis
              using norm_ge_zero by (simp add: abs_square_eq_1)
          qed
          obtain \<theta> where \<theta>_bounds: "0 \<le> \<theta>" "\<theta> < 2*pi"
            and \<theta>_eq: "Complex (- Re (z - c) / (sgn * C)) (Im (z - c) / C) = Complex (cos \<theta>) (sin \<theta>)"
            using complex_unimodular_polar[OF unit] by auto
          have \<theta>_Re: "- Re (z - c) / (sgn * C) = cos \<theta>" and \<theta>_Im: "Im (z - c) / C = sin \<theta>"
            using \<theta>_eq by (simp_all add: complex.expand)
          define t where "t = frac ((\<theta> + A) / (2 * pi))"
          have t01: "t \<in> {0..1}"
            using frac_ge_0[of t] frac_lt_1[of t] by (simp add: t_def)
          have "2*pi*t - A = \<theta> - of_int \<lfloor>(\<theta> + A) / (2*pi)\<rfloor> * (2*pi)"
            by (simp add: t_def frac_def divide_simps)
          then have angle_eq: "cos (2*pi*t - A) = cos \<theta>" "sin (2*pi*t - A) = sin \<theta>"
            by (auto simp: mult_of_int_commute sin_diff cos_diff)
          have "g t = z"
          proof (rule complex_eqI)
            have "sgn \<noteq> 0" using sgn2 by (metis power2_eq_square mult_zero_left zero_neq_one)
            have "Re (g t) = - sgn * C * (cos (2*pi*t - A) - cos A)"
              using Re_g[OF t01] .
            also have "\<dots> = - sgn * C * cos \<theta> + sgn * C * cos A"
              using angle_eq(1) by (simp add: algebra_simps)
            also have "\<dots> = Re (z - c) + Re c"
              using \<theta>_Re Cne \<open>sgn \<noteq> 0\<close> by (simp add: c_def field_simps)
            finally show "Re (g t) = Re z" by simp
            show "Im (g t) = Im z"
              using CA[OF t01] \<theta>_Im Cne angle_eq(2) c_def by (simp add: nonzero_divide_eq_eq)
          qed
          then show "z \<in> path_image g"
            using t01 by (auto simp: path_image_def)
        qed
      qed
      show ?thesis
        using subset supset by (auto intro!: exI[of _ c] exI[of _ "\<bar>C\<bar>"])
    qed
    ultimately show ?thesis
      using key_eq by presburger
  qed (use \<open>L>0\<close> in auto)
  show "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    using key by (simp add: field_simps)
  show "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
    \<exists>c r. path_image g = sphere c r"
  proof -
    assume eq: "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi)"
    have "L\<^sup>2 - measure lebesgue (inside (path_image g)) * 4 * pi = 0"
      using eq by (simp add: field_simps)
    then show "\<exists>c r. path_image g = sphere c r"
      using key by blast
  qed
qed

text \<open>Reduction lemmas for the reparametrization steps.\<close>

corollary isoperimetric_reduce_shift:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L" "a \<in> path_image g"
  obtains h where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h" "pathstart h = a"
    "convex (inside (path_image h))"
    "path_length h = L" "path_image h = path_image g"
proof -
  obtain t where t: "t \<in> {0..1}" "g t = a"
    using assms(6) by (auto simp: path_image_def)
  define h where "h \<equiv> shiftpath t g"
  have "rectifiable_path h"
    unfolding h_def using rectifiable_path_shiftpath[OF assms(1) assms(3) t(1)] .
  moreover have "simple_path h"
    unfolding h_def using simple_path_shiftpath[OF assms(2) assms(3)] t(1) by auto
  moreover have "pathfinish h = pathstart h"
    unfolding h_def using pathfinish_shiftpath[of t g] pathstart_shiftpath[of t g]
      t(1) assms(3) by auto
  moreover have "pathstart h = a"
    unfolding h_def using pathstart_shiftpath[of t g] t by auto
  moreover have "path_image h = path_image g"
    unfolding h_def using path_image_shiftpath[OF t(1) assms(3)] .
  moreover have "path_length h = L"
    unfolding h_def using path_length_shiftpath[OF assms(1) assms(3) t(1)] assms(5) by simp
  ultimately show thesis using that assms(4) by presburger
qed

lemma isoperimetric_reduce_rotate_translate:
  fixes g :: "real \<Rightarrow> complex" and a b :: complex
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g" "pathstart g = a"
    "convex (inside (path_image g))"
    "path_length g = L"
    "b \<in> path_image g" "dist a b = diameter (path_image g)"
    "a \<noteq> b"
  obtains h a' b' where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h" "pathstart h = a'"
    "convex (inside (path_image h))"
    "path_length h = L"
    "b' \<in> path_image h" "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "Re a' = 0"
    "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
    "\<And>c r. path_image h = sphere c r \<Longrightarrow> \<exists>c' r'. path_image g = sphere c' r'"
proof -
  define r where "r = cis (- Arg (b - a))"
  define h where "h = (*) r \<circ> (+) (-a) \<circ> g"
  define a' where "a' = r * (a - a)"
  define b' where "b' = r * (b - a)"
  have r_norm: "norm r = 1" unfolding r_def by simp
  have r_ne: "r \<noteq> 0" using r_norm by auto
  have lin_r: "linear ((*) r)" by (intro linearI) (auto simp: algebra_simps scaleR_conv_of_real)
  have inj_r: "inj ((*) r)" using r_ne by (simp add: inj_def)
  have norm_r: "\<And>x. norm (r * x) = norm x" using r_norm
    by (simp add: norm_mult)
  have dist_r: "\<And>x y. dist (r * x) (r * y) = dist x y"
    by (simp add: dist_mult_left r_norm)
  \<comment> \<open>Translation step: @{term "g1 = (+) (-a) \<circ> g"}\<close>
  define g1 where "g1 = (+) (-a) \<circ> g"
  have rect_g1: "rectifiable_path g1"
    unfolding g1_def using assms(1) rectifiable_path_translation_eq by blast
  have sp_g1: "simple_path g1"
    unfolding g1_def using assms(2) simple_path_translation_eq by blast
  have pi_g1: "path_image g1 = (+) (-a) ` path_image g"
    unfolding g1_def by (simp add: path_image_compose image_comp)
  have ps_g1: "pathstart g1 = 0"
    unfolding g1_def using assms(4) by (simp add: pathstart_compose)
  have pf_g1: "pathfinish g1 = 0"
    unfolding g1_def using assms(3,4) by (simp add: pathstart_compose pathfinish_compose)
  have pl_g1: "path_length g1 = L"
    unfolding g1_def using assms(6) path_length_translation by blast
  \<comment> \<open>Rotation step: @{term "h = (*) r \<circ> g1"}\<close>
  have h_eq: "h = (*) r \<circ> g1" unfolding h_def g1_def by (simp add: comp_assoc)
  have pi_h: "path_image h = (*) r ` path_image g1"
    unfolding h_eq by (simp add: path_image_compose image_comp)
  have a'_eq: "a' = 0" unfolding a'_def by simp
  have b'_eq: "b' = r * (b - a)" unfolding b'_def by simp
  \<comment> \<open>Key: $r \cdot (b-a)$ is a positive real\<close>
  have ba_ne: "b - a \<noteq> 0" using assms(9) by auto
  have "r * (b - a) = cis (- Arg (b-a)) * (b-a)"
    unfolding r_def by simp
  also have "\<dots> = of_real (cmod (b-a))"
    by (subst (2) rcis_cmod_Arg[symmetric, of "b - a"]) (simp add: rcis_def cis_mult)
  finally have rb_real: "b' = of_real (cmod (b-a))" unfolding b'_def by simp
  show ?thesis
  proof 
    show "rectifiable_path h"
      unfolding h_eq using rect_g1 rectifiable_path_linear_image_eq[OF lin_r inj_r] by simp
    show "simple_path h"
      unfolding h_eq using sp_g1 simple_path_linear_image_eq[OF lin_r inj_r] by simp
    show "pathfinish h = pathstart h"
      unfolding h_eq using pf_g1 ps_g1 by (simp add: pathstart_compose pathfinish_compose)
    show "pathstart h = a'"
      unfolding h_eq a'_eq using ps_g1 by (simp add: pathstart_compose)
    show "path_length h = L"
      unfolding h_eq using pl_g1 path_length_linear_image[OF lin_r norm_r] by simp
    show "b' \<in> path_image h"
      unfolding pi_h b'_def g1_def using assms(7)
      by (auto simp: path_image_compose image_comp image_iff)
    show "Re a' = 0" unfolding a'_eq by simp
    show "b' - a' = of_real (dist a' b')"
      unfolding a'_eq using rb_real by (simp add: dist_norm)
    show "dist a' b' = diameter (path_image h)"
    proof -
      have "diameter (path_image h) = diameter ((*) r ` path_image g1)"
        unfolding pi_h by simp
      also have "\<dots> = diameter (path_image g1)"
      proof -
        have "(\<lambda>(x,y). dist x y) ` ((*) r ` path_image g1 \<times> (*) r ` path_image g1) =
              (\<lambda>(x,y). dist x y) ` (path_image g1 \<times> path_image g1)"
          by (force simp: image_iff dist_r)
        then show ?thesis by (simp add: diameter_def)
      qed
      also have "\<dots> = diameter ((+) (-a) ` path_image g)"
        unfolding pi_g1 by simp
      also have "\<dots> = diameter (path_image g)"
        by (metis diameter_translation)
      finally have diam_eq: "diameter (path_image h) = diameter (path_image g)" .
      have "dist a' b' = dist a b"
        unfolding a'_eq b'_def by (simp add: dist_norm norm_r norm_minus_commute)
      then show ?thesis using diam_eq assms(8) by simp
    qed
    have "inside ((*) r ` path_image g1) = (*) r ` inside (path_image g1)"
    proof (rule set_eqI)
      fix x
      define y where "y = inverse r * x"
      then have xy: "x = r * y" using r_ne by simp
      have bij_r: "bij ((*) r)"
        unfolding bij_def using lin_r inj_r eucl.linear_inj_imp_surj[OF lin_r inj_r] by blast
      have compl_img: "(*) r ` (- path_image g1) = - ((*) r ` path_image g1)"
        using bij_image_Compl_eq[OF bij_r] .
      have homeo: "homeomorphism (- path_image g1) ((*) r ` (- path_image g1)) ((*) r) ((*) (inverse r))"
      proof (intro continuous_intros homeomorphismI)
        show "(*) r ` (- path_image g1) \<subseteq> (*) r ` (- path_image g1)" by simp
        show "(*) (inverse r) ` ((*) r ` (- path_image g1)) \<subseteq> - path_image g1"
          using r_ne apply (auto simp: image_iff)
          by (metis divide_inverse_commute nonzero_mult_div_cancel_left)
      qed (use r_ne in auto)
      have cc: "connected_component_set (- ((*) r ` path_image g1)) x =
                    (*) r ` connected_component_set (- path_image g1) y"
      proof (cases "y \<in> path_image g1")
        case True
        then have "x \<in> (*) r ` path_image g1"  "y \<notin> - path_image g1" using True xy by auto
        then show ?thesis
          using connected_component_eq_empty by blast
      next
        case False
        then have y_in: "y \<in> - path_image g1" by simp
        have "connected_component_set ((*) r ` (- path_image g1)) (r * y) =
                  (*) r ` connected_component_set (- path_image g1) y"
          using connected_component_set_homeomorphism[OF homeo y_in] .
        then show ?thesis using compl_img xy by simp
      qed
      have "bounded ((*) r ` connected_component_set (- path_image g1) y) =
            bounded (connected_component_set (- path_image g1) y)"
        by (simp add: bounded_iff norm_r)
      then show "(x \<in> inside ((*) r ` path_image g1)) = (x \<in> (*) r ` inside (path_image g1))"
        using cc xy r_ne by (auto simp: inside_def image_iff)
    qed
    then  have "inside (path_image h) = (*) r ` inside (path_image g1)" unfolding pi_h .
    also have "inside (path_image g1) = (+) (-a) ` inside (path_image g)"
      unfolding pi_g1 using inside_translation[of "-a" "path_image g"] by simp
    finally have inside_h: "inside (path_image h) = (*) r ` (+) (-a) ` inside (path_image g)" .
    show "convex (inside (path_image h))"
      using inside_h assms(5)
      by (metis convex_linear_image convex_translation_eq lin_r)
    show "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
    proof -
      have meas_g: "inside (path_image g) \<in> lmeasurable"
        using Jordan_inside_outside measurable_convex assms by metis 
      have "measure lebesgue ((*) r ` (+) (-a) ` inside (path_image g)) =
            measure lebesgue ((+) (-a) ` inside (path_image g))"
        using measure_linear_image[OF lin_r ] meas_g measurable_translation
      proof -
        have meas_t: "(+) (-a) ` inside (path_image g) \<in> lmeasurable"
          using meas_g measurable_translation by blast
        have "\<bar>eucl.det ((*) r)\<bar> = 1"
          unfolding det_complex r_def by simp
        then show ?thesis
          using measure_linear_image[OF lin_r meas_t] by simp
      qed
      also have "\<dots> = measure lebesgue (inside (path_image g))"
        using measure_translation[of "-a" "inside (path_image g)"] by simp
      finally show ?thesis using inside_h by simp
    qed
    show "\<exists>c' r'. path_image g = sphere c' r'" if "path_image h = sphere c0 r0" for c0 r0
    proof -
      have eq1: "(*) r ` (+) (-a) ` path_image g = sphere c0 r0"
        using that unfolding pi_h pi_g1 image_image by (simp add: comp_def)
      have *: "\<And>z. inverse r * (r * z) = z"
        using r_ne by (metis left_inverse mult.assoc mult_1)
      have eq2: "(+) (-a) ` path_image g = (*) (inverse r) ` sphere c0 r0"
        by (simp add: * image_image flip: eq1)
      have eq3: "path_image g = (+) a ` (*) (inverse r) ` sphere c0 r0"
        by (auto simp: image_comp o_def simp flip: eq2)
      moreover have "(*) (inverse r) ` sphere c0 r0 = sphere (inverse r * c0) r0"
        by (auto simp: nonzero_norm_inverse r_ne r_norm sphere_cscale)
      moreover have "(+) a ` sphere (inverse r * c0) r0 = sphere (a + inverse r * c0) r0"
        using sphere_translation[of a "inverse r * c0" r0] by simp
      ultimately show "\<exists>c' r'. path_image g = sphere c' r'" by auto
    qed
  qed
qed


lemma isoperimetric_reduce_arc_length:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L" "0 < L"
  obtains h where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h" "pathstart h = pathstart g"
    "convex (inside (path_image h))"
    "path_length h = L"
    "path_image h = path_image g"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
proof -
  obtain h where h: "rectifiable_path h" "path_image h = path_image g"
    "pathstart h = pathstart g" "pathfinish h = pathfinish g"
    "path_length h = path_length g"
    "arc g \<Longrightarrow> arc h" "simple_path g \<Longrightarrow> simple_path h"
    "\<forall>t\<in>{0..1}. path_length (subpath 0 t h) = path_length g * t"
    "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. dist (h x) (h y) \<le> path_length g * dist x y"
    using arc_length_reparametrization [OF assms(1)] by metis
  have "simple_path h" using h(7) assms(2) by auto
  moreover have "pathfinish h = pathstart h"
    using h(3,4) assms(3) by simp
  moreover have "pathstart h = pathstart g" using h(3) .
  moreover have "convex (inside (path_image h))"
    using assms(4) h(2) by simp
  moreover have "path_length h = L" using h(5) assms(5) by simp
  moreover have "path_image h = path_image g" using h(2) .
  moreover have "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    using h(8) assms(5) by auto
  moreover have "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    using h(9) assms(5) by auto
  ultimately show thesis using that h(1) by blast
qed

lemma isoperimetric_reduce_zero_mean:
  fixes g :: "real \<Rightarrow> complex" and b :: complex
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
    "b \<in> path_image g"
    "dist (pathstart g) b = diameter (path_image g)"
    "b - pathstart g = of_real (dist (pathstart g) b)"
    "Re (pathstart g) = 0"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
  obtains h a' b' where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h"
    "convex (inside (path_image h))"
    "path_length h = L"
    "a' \<in> path_image h" "b' \<in> path_image h"
    "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "pathstart h = a'" "pathfinish h = a'"
    "Re a' = 0"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    "(Im \<circ> h has_integral 0) {0..1}"
    "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
    "\<And>c r. path_image h = sphere c r \<Longrightarrow> \<exists>c' r'. path_image g = sphere c' r'"
proof -
  define c where "c = integral {0..1} (Im \<circ> g)"
  define d where "d = -(\<i> * (of_real c :: complex))"
  define h where "h = (+) d \<circ> g"
  define a' where "a' = pathstart g + d"
  define b' where "b' = b + d"
  have h_eq: "\<And>t. h t = g t + d" unfolding h_def comp_def by simp
  have pi_h: "path_image h = (+) d ` path_image g"
    unfolding h_def image_comp [symmetric] path_image_compose by simp
  show ?thesis
  proof (rule that[of h a' b'])
    show "rectifiable_path h"
      unfolding h_def using assms(1) rectifiable_path_translation_eq[of d g] by simp
    show "simple_path h"
      unfolding h_def using assms(2) simple_path_translation_eq[of d g] by simp
    show "pathfinish h = pathstart h"
      unfolding h_def using assms(3) by (simp add: pathstart_compose pathfinish_compose)
    show "path_length h = L"
      unfolding h_def using assms(5) path_length_translation[of d g] by simp
    show "pathstart h = a'" unfolding h_def a'_def by (simp add: pathstart_compose)
    show "pathfinish h = a'" unfolding h_def a'_def
      using assms(3) by (simp add: pathstart_compose pathfinish_compose)
    show "a' \<in> path_image h"
      unfolding a'_def using pi_h path_image_def pathstart_def by fastforce
    show "b' \<in> path_image h"
      unfolding b'_def using pi_h assms(6) by auto
    show "b' - a' = of_real (dist a' b')"
      unfolding a'_def b'_def using assms(8) by (simp add: dist_norm)
    show "dist a' b' = diameter (path_image h)"
      using pi_h diameter_translation[of d "path_image g"] assms(7)
      unfolding a'_def b'_def by (simp add: dist_norm)
    show "Re a' = 0" unfolding a'_def d_def using assms(9) by simp
    show "convex (inside (path_image h))"
      using pi_h inside_translation[of d "path_image g"]
        convex_translation_eq[of d "inside (path_image g)"] assms(4) by simp
    show "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    proof -
      fix t :: real assume "t \<in> {0..1}"
      have "subpath 0 t h = (+) d \<circ> subpath 0 t g"
        unfolding h_def subpath_def comp_def by (auto simp: algebra_simps)
      then have "path_length (subpath 0 t h) = path_length (subpath 0 t g)"
        using path_length_translation[of d "subpath 0 t g"] by simp
      also have "\<dots> = L * t" using assms(10) \<open>t \<in> {0..1}\<close> by simp
      finally show "path_length (subpath 0 t h) = L * t" .
    qed
    show "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    proof -
      fix x y :: real assume "x \<in> {0..1}" "y \<in> {0..1}"
      have "dist (h x) (h y) = dist (g x) (g y)"
        unfolding h_eq by (simp add: dist_norm)
      also have "\<dots> \<le> L * dist x y" using assms(11)[OF \<open>x \<in> {0..1}\<close> \<open>y \<in> {0..1}\<close>] .
      finally show "dist (h x) (h y) \<le> L * dist x y" .
    qed
    show "(Im \<circ> h has_integral 0) {0..1}"
    proof -
      have cont_g: "continuous_on {0..1} g"
        using rectifiable_path_imp_path[OF assms(1)] unfolding path_def .
      have int_Im_g: "(\<lambda>t. Im (g t)) integrable_on {0..1}"
        using integrable_continuous_real[OF continuous_on_Im[OF cont_g]] .
      have Im_h: "\<And>t. Im (h t) = Im (g t) - c"
        unfolding h_def comp_def d_def by simp
      have eq: "\<And>t. (Im \<circ> h) t = (\<lambda>t. Im (g t) - c) t"
        using Im_h unfolding comp_def by simp
      have int_sub: "(\<lambda>t. Im (g t) - c) integrable_on {0..1}"
        by (rule integrable_diff[OF int_Im_g integrable_const_ivl])
      have int_h: "(Im \<circ> h) integrable_on {0..1}"
        using integrable_spike_finite[OF finite.emptyI _ int_sub] eq by simp
      have "integral {0..1} (Im \<circ> h) = integral {0..1} (\<lambda>t. Im (g t) - c)"
        using integral_cong[of "{0..1}" "Im \<circ> h" "\<lambda>t. Im (g t) - c"] eq by simp
      also have "\<dots> = integral {0..1} (\<lambda>t. Im (g t)) - integral {0..1} (\<lambda>_::real. c::real)"
        using integral_diff[OF int_Im_g integrable_const_ivl] by simp
      also have "\<dots> = 0" unfolding c_def comp_def by simp
      finally show ?thesis using int_h has_integral_iff by blast
    qed
    show "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
      using pi_h inside_translation[of d "path_image g"]
        measure_translation[of d "inside (path_image g)"] by simp
    show "\<And>c0 r. path_image h = sphere c0 r \<Longrightarrow> \<exists>c' r'. path_image g = sphere c' r'"
    proof -
      fix c0 r assume "path_image h = sphere c0 r"
      then have "(+) d ` path_image g = sphere c0 r" using pi_h by simp
      then have "(+) (- d) ` (+) d ` path_image g = (+) (- d) ` sphere c0 r" by simp
      then have "path_image g = (+) (- d) ` sphere c0 r"
        using translation_assoc[of "- d" d "path_image g"] by simp
      also have "\<dots> = sphere (c0 + (- d)) r"
        using sphere_translation[of "-d" c0 r] by simp
      finally show "\<exists>c' r'. path_image g = sphere c' r'" by blast
    qed
  qed
qed

theorem isoperimetric_theorem_convex:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "convex (inside (path_image g))"
    "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
proof -
  have Lpos: "0 < L"
    using simple_path_length_pos_lt[OF assms(1,2)] assms(5) by simp
  text \<open>Step 1: obtain diameter endpoints\<close>
  have compact_pi: "compact (path_image g)"
    using compact_simple_path_image[OF assms(2)] .
  have nonempty_pi: "path_image g \<noteq> {}"
    using path_image_nonempty .
  obtain a b where ab: "a \<in> path_image g" "b \<in> path_image g"
    "dist a b = diameter (path_image g)"
    using diameter_compact_attained[OF compact_pi nonempty_pi] by auto
  text \<open>Step 2: shift start to diameter endpoint a\<close>
  obtain g1 where g1: "rectifiable_path g1" "simple_path g1"
    "pathfinish g1 = pathstart g1" "pathstart g1 = a"
    "convex (inside (path_image g1))"
    "path_length g1 = L" "path_image g1 = path_image g"
    using isoperimetric_reduce_shift[OF assms(1,2,3,4,5) ab(1)] by metis
  have ab1: "a \<in> path_image g1" "b \<in> path_image g1"
    "dist a b = diameter (path_image g1)"
    using ab g1(7) by auto
  have a_ne_b: "a \<noteq> b"
  proof
    assume "a = b"
    then have "diameter (path_image g) = 0" using ab(3) by simp
    then have "path_image g = {a}"
      by (metis ab(1) compact_eq_bounded_closed compact_pi diameter_eq_0 equals0D
          insertE)
    then show False using simple_path_image_uncountable[OF assms(2)]
      by (simp add: countable_finite)
  qed
  text \<open>Step 3: rotate and translate to normalize diameter direction\<close>
  obtain g2 a2 b2 where g2: "rectifiable_path g2" "simple_path g2"
    "pathfinish g2 = pathstart g2" "pathstart g2 = a2"
    "convex (inside (path_image g2))"
    "path_length g2 = L"
    "b2 \<in> path_image g2" "dist a2 b2 = diameter (path_image g2)"
    "b2 - a2 = of_real (dist a2 b2)"
    "Re a2 = 0"
    "measure lebesgue (inside (path_image g2)) = measure lebesgue (inside (path_image g))"
    and sphere_back2: "\<And>c r. path_image g2 = sphere c r \<Longrightarrow>
      \<exists>c' r'. path_image g = sphere c' r'"
    using isoperimetric_reduce_rotate_translate[OF g1(1,2,3) g1(4) g1(5,6) ab1(2,3) a_ne_b]
    by (metis g1(7))
  text \<open>Step 4: arc-length reparametrization\<close>
  obtain g3 where g3: "rectifiable_path g3" "simple_path g3"
    "pathfinish g3 = pathstart g3" "pathstart g3 = pathstart g2"
    "convex (inside (path_image g3))"
    "path_length g3 = L"
    "path_image g3 = path_image g2"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t g3) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g3 x) (g3 y) \<le> L * dist x y"
    using isoperimetric_reduce_arc_length[OF g2(1,2,3,5,6) Lpos] by metis
  have g3_facts: "b2 \<in> path_image g3" "dist (pathstart g3) b2 = diameter (path_image g3)"
    "b2 - pathstart g3 = of_real (dist (pathstart g3) b2)" "Re (pathstart g3) = 0"
    using g2(7,8,9,10) g3(4,7) g2(4) by auto
  text \<open>Step 5: vertical translation for zero-mean imaginary part\<close>
  obtain h a' b' where h: "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h"
    "convex (inside (path_image h))"
    "path_length h = L"
    "a' \<in> path_image h" "b' \<in> path_image h"
    "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "pathstart h = a'" "pathfinish h = a'"
    "Re a' = 0"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    "(Im \<circ> h has_integral 0) {0..1}"
    and meas_eq5: "measure lebesgue (inside (path_image h)) =
      measure lebesgue (inside (path_image g3))"
    and sphere_back5: "\<And>c r. path_image h = sphere c r \<Longrightarrow>
      \<exists>c' r'. path_image g3 = sphere c' r'"
    using isoperimetric_reduce_zero_mean[OF g3(1,2,3,5,6) g3_facts(1,2,3,4) g3(8,9)]
    by blast
  have meas_eq: "measure lebesgue (inside (path_image h)) =
    measure lebesgue (inside (path_image g))"
    using meas_eq5 g3(5,7) g2(11) by simp
  have sphere_back: "\<And>c r. path_image h = sphere c r \<Longrightarrow>
    \<exists>c' r'. path_image g = sphere c' r'"
  proof -
    fix c r assume "path_image h = sphere c r"
    then obtain c2 r2 where "path_image g2 = sphere c2 r2"
      using sphere_back5 g3(7) by metis
    then show "\<exists>c' r'. path_image g = sphere c' r'"
      using sphere_back2 by auto
  qed
  text \<open>Step 6: apply the kernel lemma\<close>
  have kernel_hyps: "0 < L" "convex (inside (path_image h))"
    "a' \<in> path_image h" "b' \<in> path_image h"
    "dist a' b' = diameter (path_image h)"
    "b' - a' = of_real (dist a' b')"
    "pathstart h = a'" "pathfinish h = a'"
    "rectifiable_path h" "simple_path h"
    "path_length h = L"
    "Re a' = 0"
    "(Im \<circ> h has_integral 0) {0..1}"
    using Lpos h by auto
  have ineq_h: "measure lebesgue (inside (path_image h)) \<le> L\<^sup>2 / (4 * pi)"
    using isoperimetric_kernel(1)[OF kernel_hyps(1-11) h(13,14) kernel_hyps(12,13)] .
  show "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    using ineq_h meas_eq by simp
  show "\<exists>a r. path_image g = sphere a r"
    if "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi)"
  proof -
    have "measure lebesgue (inside (path_image h)) = L\<^sup>2 / (4 * pi)"
      using that meas_eq by simp
    then obtain c r where "path_image h = sphere c r"
      using isoperimetric_kernel(2)[OF kernel_hyps(1-11) h(13,14) kernel_hyps(12,13)] by auto
    then show ?thesis using sphere_back by auto
  qed
qed

section \<open>Part 4: Convexification\<close>

text \<open>A connected subset of a segment that contains both endpoints is the whole segment.
  (HOL Light: CONNECTED\_SUBSET\_SEGMENT.)\<close>

lemma connected_subset_segment:
  fixes a b :: "'a::euclidean_space"
  assumes "connected S" "S \<subseteq> closed_segment a b" "a \<in> S" "b \<in> S"
  shows "S = closed_segment a b"
proof (cases "a = b")
  case True
  then show ?thesis using assms by auto
next
  case False
  define f where "f = (\<lambda>x::'a. (b - a) \<bullet> x)"
  define K where "K = (b - a) \<bullet> (b - a)"
  have contf: "continuous_on S f" by (auto simp: f_def continuous_intros)
  have conn_fS: "connected (f ` S)" using assms(1) contf connected_continuous_image by blast
  have nz: "K > 0" using False by (simp add: K_def inner_gt_zero_iff)
  have fseg: "\<And>u. f ((1-u) *\<^sub>R a + u *\<^sub>R b) = (b - a) \<bullet> a + u * K"
    by (simp add: f_def K_def inner_diff_right algebra_simps inner_diff_left inner_commute)
  have fa: "f a = (b - a) \<bullet> a" by (simp add: f_def)
  have fb: "f b = (b - a) \<bullet> a + K" using fseg[of 1] by simp
  show ?thesis
  proof (rule subset_antisym[OF assms(2)])
    show "closed_segment a b \<subseteq> S"
    proof
      fix x assume "x \<in> closed_segment a b"
      then obtain u where u: "x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 \<le> u" "u \<le> 1"
        by (auto simp: in_segment)
      have fx: "f x = (b - a) \<bullet> a + u * K" using u(1) fseg by simp
      have mem: "f x \<in> closed_segment (f a) (f b)"
        unfolding closed_segment_eq_real_ivl using nz u(2,3) fa fb fx
        by (auto simp: mult_left_le_one_le)
      have "closed_segment (f a) (f b) \<subseteq> f ` S"
        using conn_fS assms(3,4) connected_contains_Icc
        by (metis closed_segment_eq_real_ivl image_eqI)
      then have "f x \<in> f ` S" using mem by blast
      then obtain s where s: "s \<in> S" "f s = f x" by auto
      have "s \<in> closed_segment a b" using s(1) assms(2) by blast
      then obtain v where v: "s = (1 - v) *\<^sub>R a + v *\<^sub>R b" "0 \<le> v" "v \<le> 1"
        by (auto simp: in_segment)
      have "(b - a) \<bullet> a + v * K = (b - a) \<bullet> a + u * K"
        using s(2) v(1) fseg fx by simp
      then have "v = u" using nz by simp
      then show "x \<in> S" using s(1) v(1) u(1) by simp
    qed
  qed
qed

text \<open>A connected subset of two arcs joined only at their common endpoints, containing both
  endpoints, must contain one of the two arcs in full. (HOL Light: CONNECTED\_SUBSET\_ARC\_PAIR.)\<close>

lemma connected_subset_arc_pair:
  fixes g h :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc g" "arc h"
    "pathstart g = pathstart h" "pathfinish g = pathfinish h"
    "path_image g \<inter> path_image h = {pathstart g, pathfinish g}"
    "connected S" "S \<subseteq> path_image g \<union> path_image h"
    "pathstart g \<in> S" "pathfinish g \<in> S"
  shows "path_image g \<subseteq> S \<or> path_image h \<subseteq> S"
proof (rule ccontr)
  assume "\<not> (path_image g \<subseteq> S \<or> path_image h \<subseteq> S)"
  then have ng: "\<not> path_image g \<subseteq> S" and nh: "\<not> path_image h \<subseteq> S" by auto
  from ng obtain pg where pg: "pg \<in> path_image g" "pg \<notin> S" by blast
  then obtain p where p: "p \<in> {0..1}" "g p = pg" by (auto simp: path_image_def)
  from nh obtain ph where ph: "ph \<in> path_image h" "ph \<notin> S" by blast
  then obtain q where q: "q \<in> {0..1}" "h q = ph" by (auto simp: path_image_def)
  have gp: "g p \<notin> S" using p(2) pg(2) by simp
  have hq: "h q \<notin> S" using q(2) ph(2) by simp
  have pathg: "path g" and pathh: "path h" using assms(1,2) arc_imp_path by auto
  have img_g0p: "path_image (subpath 0 p g) = g ` {0..p}" using p(1) by (simp add: path_image_subpath)
  have img_gp1: "path_image (subpath p 1 g) = g ` {p..1}" using p(1) by (simp add: path_image_subpath)
  have img_h0q: "path_image (subpath 0 q h) = h ` {0..q}" using q(1) by (simp add: path_image_subpath)
  have img_hq1: "path_image (subpath q 1 h) = h ` {q..1}" using q(1) by (simp add: path_image_subpath)
  have comb_g: "g ` {0..p} \<union> g ` {p..1} = path_image g"
    using p(1) by (simp add: path_image_def image_Un [symmetric]) (metis ivl_disj_un_two_touch(4))
  have comb_h: "h ` {0..q} \<union> h ` {q..1} = path_image h"
    using q(1) by (simp add: path_image_def image_Un [symmetric]) (metis ivl_disj_un_two_touch(4))
  define E1 where "E1 = S - (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h))"
  define E2 where "E2 = S - (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h))"
  have cl_gp1: "closed (path_image (subpath p 1 g))"
    using pathg p(1) by (simp add: closed_path_image path_subpath)
  have cl_hq1: "closed (path_image (subpath q 1 h))"
    using pathh q(1) by (simp add: closed_path_image path_subpath)
  have cl_g0p: "closed (path_image (subpath 0 p g))"
    using pathg p(1) by (simp add: closed_path_image path_subpath)
  have cl_h0q: "closed (path_image (subpath 0 q h))"
    using pathh q(1) by (simp add: closed_path_image path_subpath)
  have openE1: "openin (top_of_set S) E1"
  proof -
    have "E1 = S \<inter> (- (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h)))"
      unfolding E1_def by blast
    moreover have "open (- (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h)))"
      using cl_gp1 cl_hq1 by blast
    ultimately show ?thesis by (simp add: openin_open_Int)
  qed
  have openE2: "openin (top_of_set S) E2"
  proof -
    have "E2 = S \<inter> (- (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h)))"
      unfolding E2_def by blast
    moreover have "open (- (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h)))"
      using cl_g0p cl_h0q by blast
    ultimately show ?thesis by (simp add: openin_open_Int)
  qed
  have injg: "inj_on g {0..1}" using assms(1) by (simp add: arc_def)
  have injh: "inj_on h {0..1}" using assms(2) by (simp add: arc_def)
  have p_pos: "p > 0"
  proof (rule ccontr)
    assume "\<not> p > 0" then have "p = 0" using p(1) by simp
    then have "g p = pathstart g" by (simp add: pathstart_def)
    then show False using gp assms(8) by simp
  qed
  have q_pos: "q > 0"
  proof (rule ccontr)
    assume "\<not> q > 0" then have "q = 0" using q(1) by simp
    then have "h q = pathstart h" by (simp add: pathstart_def)
    then show False using hq assms(8) assms(3) by simp
  qed
  have p_lt1: "p < 1"
  proof (rule ccontr)
    assume "\<not> p < 1" then have "p = 1" using p(1) by simp
    then have "g p = pathfinish g" by (simp add: pathfinish_def)
    then show False using gp assms(9) by simp
  qed
  have q_lt1: "q < 1"
  proof (rule ccontr)
    assume "\<not> q < 1" then have "q = 1" using q(1) by simp
    then have "h q = pathfinish h" by (simp add: pathfinish_def)
    then show False using hq assms(9) assms(4) by simp
  qed
  have ne_E1: "pathstart g \<in> E1"
  proof -
    have "g 0 \<notin> g ` {p..1}"
    proof
      assume "g 0 \<in> g ` {p..1}"
      then obtain t where t: "t \<in> {p..1}" "g 0 = g t" by auto
      have "0 = t" using injg t p(1) p_pos by (force simp: inj_on_def)
      then show False using t(1) p_pos by simp
    qed
    moreover have "g 0 \<notin> h ` {q..1}"
    proof
      assume "g 0 \<in> h ` {q..1}"
      then have "h 0 \<in> h ` {q..1}" using assms(3) by (simp add: pathstart_def)
      then obtain t where t: "t \<in> {q..1}" "h 0 = h t" by auto
      have "0 = t" using injh t q(1) q_pos by (force simp: inj_on_def)
      then show False using t(1) q_pos by simp
    qed
    ultimately show ?thesis
      unfolding E1_def using assms(8) img_gp1 img_hq1 by (simp add: pathstart_def)
  qed
  have ne_E2: "pathfinish g \<in> E2"
  proof -
    have "g 1 \<notin> g ` {0..p}"
    proof
      assume "g 1 \<in> g ` {0..p}"
      then obtain t where t: "t \<in> {0..p}" "g 1 = g t" by auto
      have "1 = t" using injg t p(1) by (force simp: inj_on_def)
      then show False using t(1) p_lt1 by simp
    qed
    moreover have "g 1 \<notin> h ` {0..q}"
    proof
      assume "g 1 \<in> h ` {0..q}"
      then have "h 1 \<in> h ` {0..q}" using assms(4) by (simp add: pathfinish_def)
      then obtain t where t: "t \<in> {0..q}" "h 1 = h t" by auto
      have "1 = t" using injh t q(1) by (force simp: inj_on_def)
      then show False using t(1) q_lt1 by simp
    qed
    moreover have "pathfinish g \<in> S" using assms(9) .
    ultimately show ?thesis
      unfolding E2_def using img_g0p img_h0q by (simp add: pathfinish_def)
  qed
  have ps_g: "pathstart g = g 0" by (simp add: pathstart_def)
  have pf_g: "pathfinish g = g 1" by (simp add: pathfinish_def)
  have cross_gh: "\<And>s t. s \<in> {0..1} \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> g s = h t \<Longrightarrow> g s = g 0 \<or> g s = g 1"
  proof -
    fix s t assume s: "s \<in> {0..1}" and t: "t \<in> {0..1}" and eq: "g s = h t"
    have "g s \<in> path_image g" using s by (auto simp: path_image_def)
    moreover have "g s \<in> path_image h" using t eq by (auto simp: path_image_def)
    ultimately have "g s \<in> {pathstart g, pathfinish g}" using assms(5) by blast
    then show "g s = g 0 \<or> g s = g 1" using ps_g pf_g by auto
  qed
  have sub_p1: "{p..1} \<subseteq> {0..1}" using p(1) by auto
  have sub_0p: "{0..p} \<subseteq> {0..1}" using p(1) by auto
  have sub_q1: "{q..1} \<subseteq> {0..1}" using q(1) by auto
  have sub_0q: "{0..q} \<subseteq> {0..1}" using q(1) by auto
  have gh11: "g 1 = h 1" using assms(4) by (simp add: pathfinish_def)
  have gh00: "g 0 = h 0" using assms(3) by (simp add: pathstart_def)
  have cover_False: "\<And>x. x \<in> S \<Longrightarrow> x \<in> g ` {p..1} \<union> h ` {q..1} \<Longrightarrow> x \<in> g ` {0..p} \<union> h ` {0..q} \<Longrightarrow> False"
  proof -
    fix x assume xS: "x \<in> S" and inR1: "x \<in> g ` {p..1} \<union> h ` {q..1}" and inR2: "x \<in> g ` {0..p} \<union> h ` {0..q}"
    from inR1 consider (g1) "x \<in> g ` {p..1}" | (h1) "x \<in> h ` {q..1}" by auto
    then show False
    proof cases
      case g1
      then obtain s where s: "s \<in> {p..1}" "x = g s" by auto
      from inR2 consider (a) "x \<in> g ` {0..p}" | (b) "x \<in> h ` {0..q}" by auto
      then show False
      proof cases
        case a
        then obtain t where t: "t \<in> {0..p}" "x = g t" by auto
        have "s = t" using injg s t sub_p1 sub_0p s(2) t(2) by (force simp: inj_on_def)
        then have "s = p" using s(1) t(1) by simp
        then show False using gp xS s(2) by simp
      next
        case b
        then obtain t where t: "t \<in> {0..q}" "x = h t" by auto
        have eq: "g s = h t" using s(2) t(2) by simp
        have "g s = g 0 \<or> g s = g 1" using cross_gh s(1) sub_p1 t(1) sub_0q eq by blast
        then show False
        proof
          assume "g s = g 0"
          then have "s = 0" using injg s(1) sub_p1 by (force simp: inj_on_def)
          then show False using s(1) p_pos by simp
        next
          assume "g s = g 1"
          then have "h t = h 1" using eq gh11 by simp
          then have "t = 1" using injh t(1) sub_0q by (force simp: inj_on_def)
          then show False using t(1) q_lt1 by simp
        qed
      qed
    next
      case h1
      then obtain s where s: "s \<in> {q..1}" "x = h s" by auto
      from inR2 consider (a) "x \<in> g ` {0..p}" | (b) "x \<in> h ` {0..q}" by auto
      then show False
      proof cases
        case a
        then obtain t where t: "t \<in> {0..p}" "x = g t" by auto
        have eq: "g t = h s" using s(2) t(2) by simp
        have "g t = g 0 \<or> g t = g 1" using cross_gh t(1) sub_0p s(1) sub_q1 eq by blast
        then show False
        proof
          assume "g t = g 1"
          then have "t = 1" using injg t(1) sub_0p by (force simp: inj_on_def)
          then show False using t(1) p_lt1 by simp
        next
          assume "g t = g 0"
          then have "h s = h 0" using eq gh00 by simp
          then have "s = 0" using injh s(1) sub_q1 by (force simp: inj_on_def)
          then show False using s(1) q_pos by simp
        qed
      next
        case b
        then obtain t where t: "t \<in> {0..q}" "x = h t" by auto
        have "s = t" using injh s t sub_q1 sub_0q s(2) t(2) by (force simp: inj_on_def)
        then have "s = q" using s(1) t(1) by simp
        then show False using hq xS s(2) by simp
      qed
    qed
  qed
  have cover: "S \<subseteq> E1 \<union> E2"
  proof
    fix x assume xS: "x \<in> S"
    show "x \<in> E1 \<union> E2"
    proof (rule ccontr)
      assume "x \<notin> E1 \<union> E2"
      then have "x \<in> g ` {p..1} \<union> h ` {q..1}" and "x \<in> g ` {0..p} \<union> h ` {0..q}"
        using xS unfolding E1_def E2_def img_gp1 img_hq1 img_g0p img_h0q by auto
      then show False using cover_False xS by blast
    qed
  qed
  have disjoint: "E1 \<inter> E2 = {}"
  proof -
    have "(g ` {p..1} \<union> h ` {q..1}) \<union> (g ` {0..p} \<union> h ` {0..q}) = path_image g \<union> path_image h"
      using comb_g comb_h by blast
    moreover have "S \<subseteq> path_image g \<union> path_image h" using assms(7) .
    ultimately show ?thesis unfolding E1_def E2_def img_gp1 img_hq1 img_g0p img_h0q by blast
  qed
  from assms(6) have "\<not> (\<exists>E1 E2. openin (top_of_set S) E1 \<and> openin (top_of_set S) E2 \<and> S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
    by (simp add: connected_openin)
  moreover have "openin (top_of_set S) E1 \<and> openin (top_of_set S) E2 \<and> S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {}"
    using openE1 openE2 cover disjoint ne_E1 ne_E2 by auto
  ultimately show False by blast
qed

text \<open>If two frontier points of a bounded convex $2$-dimensional set are joined by a frontier arc whose
  interior (the arc minus the two points) stays connected and whose convex hull is the whole set,
  then the straight segment between the two points also lies on the frontier. The connectedness of
  the arc-minus-endpoints is what rules out the spurious ``chord through the interior'' case.\<close>

lemma seg_frontier_aux:
  fixes S :: "complex set"
  assumes cvx: "convex S" and cpt: "compact S" and intne: "interior S \<noteq> {}"
    and ga_fr: "ga \<in> frontier S" and gb_fr: "gb \<in> frontier S" and ne: "ga \<noteq> gb"
    and D1fr: "path_image D1 \<subseteq> frontier S"
    and D1con: "connected (path_image D1 - {ga, gb})"
    and gaD1: "ga \<in> path_image D1" and gbD1: "gb \<in> path_image D1"
    and hullD1: "convex hull (path_image D1) = S"
  shows "closed_segment ga gb \<subseteq> frontier S"
proof -
  have clSh: "closed S" using cpt by (rule compact_imp_closed)
  have relfr: "rel_frontier S = frontier S" using intne by (rule rel_frontier_nonempty_interior)
  have ga_cl: "ga \<in> closure S" and gb_cl: "gb \<in> closure S"
    using ga_fr gb_fr by (auto simp: frontier_def)
  have dich: "open_segment ga gb \<subseteq> frontier S \<or> open_segment ga gb \<subseteq> interior S"
    using convex_open_segment_cases_alt[OF cvx ga_cl gb_cl] .
  define A where "A = \<i> * (gb - ga)"
  have A_nz: "A \<noteq> 0" using ne by (simp add: A_def)
  define e where "e = inner A ga"
  have eb: "inner A gb = e"
  proof -
    have "inner A (gb - ga) = 0" unfolding A_def inner_complex_def by (simp add: algebra_simps)
    then show ?thesis using e_def by (simp add: inner_diff_right)
  qed
  have opfr: "open_segment ga gb \<subseteq> frontier S"
  proof (rule ccontr)
    assume "\<not> open_segment ga gb \<subseteq> frontier S"
    then have segint: "open_segment ga gb \<subseteq> interior S" using dich by blast
    have mid_int: "midpoint ga gb \<in> interior S"
      using segint ne by (simp add: midpoint_in_open_segment subsetD)
    have mid_e: "inner A (midpoint ga gb) = e"
      using e_def eb by (simp add: midpoint_def inner_add_right inner_diff_right field_simps)
    have not_le: "\<not> (path_image D1 \<subseteq> {x. inner A x \<le> e})"
    proof
      assume "path_image D1 \<subseteq> {x. inner A x \<le> e}"
      then have "convex hull (path_image D1) \<subseteq> {x. inner A x \<le> e}"
        by (simp add: convex_halfspace_le hull_minimal)
      then have "S \<subseteq> {x. inner A x \<le> e}" using hullD1 by simp
      then have "interior S \<subseteq> interior {x. inner A x \<le> e}" by (rule interior_mono)
      also have "interior {x. inner A x \<le> e} = {x. inner A x < e}"
        using A_nz by (simp add: interior_halfspace_le)
      finally have "inner A (midpoint ga gb) < e" using mid_int by blast
      then show False using mid_e by simp
    qed
    have not_ge: "\<not> (path_image D1 \<subseteq> {x. e \<le> inner A x})"
    proof
      assume "path_image D1 \<subseteq> {x. e \<le> inner A x}"
      then have "convex hull (path_image D1) \<subseteq> {x. e \<le> inner A x}"
        by (simp add: convex_halfspace_ge hull_minimal)
      then have "S \<subseteq> {x. e \<le> inner A x}" using hullD1 by simp
      then have "interior S \<subseteq> interior {x. e \<le> inner A x}" by (rule interior_mono)
      also have "interior {x. e \<le> inner A x} = {x. e < inner A x}"
        using A_nz by (simp add: interior_halfspace_ge)
      finally have "e < inner A (midpoint ga gb)" using mid_int by blast
      then show False using mid_e by simp
    qed
    from not_le obtain x1 where x1: "x1 \<in> path_image D1" "inner A x1 > e" by force
    from not_ge obtain x2 where x2: "x2 \<in> path_image D1" "inner A x2 < e" by force
    have x1ne: "x1 \<notin> {ga, gb}" using x1(2) e_def eb by auto
    have x2ne: "x2 \<notin> {ga, gb}" using x2(2) e_def eb by auto
    have x1D: "x1 \<in> path_image D1 - {ga,gb}" using x1(1) x1ne by simp
    have x2D: "x2 \<in> path_image D1 - {ga,gb}" using x2(1) x2ne by simp
    obtain w where w: "w \<in> path_image D1 - {ga,gb}" "inner A w = e"
      using connected_ivt_hyperplane[OF D1con x2D x1D, where a=A and b=e] x1(2) x2(2) by force
    have w_fr: "w \<in> rel_frontier S" using w(1) D1fr relfr by auto
    have ga_rf: "ga \<in> rel_frontier S" using ga_fr relfr by simp
    have gb_rf: "gb \<in> rel_frontier S" using gb_fr relfr by simp
    have wne: "w \<noteq> ga" "w \<noteq> gb" using w(1) by auto
    have triple: "S \<subseteq> {x. inner A x \<le> e} \<or> S \<subseteq> {x. e \<le> inner A x}"
    proof (rule convex_triple_rel_frontier[OF cvx ga_rf gb_rf w_fr ne])
      show "ga \<noteq> w" using wne(1) by simp
      show "gb \<noteq> w" using wne(2) by simp
      show "inner A ga = e" using e_def by simp
      show "inner A gb = e" using eb by simp
      show "inner A w = e" using w(2) by simp
    qed
    have D1S: "path_image D1 \<subseteq> S" using D1fr relfr hullD1 hull_subset by (metis frontier_def Diff_subset dual_order.trans)
    from triple show False
    proof
      assume "S \<subseteq> {x. inner A x \<le> e}"
      then have "path_image D1 \<subseteq> {x. inner A x \<le> e}" using D1S by blast
      then show False using not_le by simp
    next
      assume "S \<subseteq> {x. e \<le> inner A x}"
      then have "path_image D1 \<subseteq> {x. e \<le> inner A x}" using D1S by blast
      then show False using not_ge by simp
    qed
  qed
  have "{ga, gb} \<subseteq> frontier S" using ga_fr gb_fr by simp
  then show ?thesis using opfr by (simp add: closed_segment_eq_open)
qed

text \<open>The step lemma: replacing an arc that deviates from the convex hull frontier
  with a straight segment shortens the path while preserving the convex hull.\<close>

lemma step_lemma:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
    and "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g x) (g y) \<le> L * dist x y"
    and "a < b"
    and ab01: "a \<in> {0..1}" "b \<in> {0..1}"
    and "g a \<in> frontier (convex hull (path_image g))"
    and "g b \<in> frontier (convex hull (path_image g))"
    and "g ` {a<..<b} \<inter> frontier (convex hull (path_image g)) = {}"
  obtains h where "simple_path h"
    and "pathstart h = pathstart g" and "pathfinish h = pathstart g"
    and "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    and "path_length h < path_length g"
    and "convex hull (path_image h) = convex hull (path_image g)"
    and "\<And>x. x \<notin> {a<..<b} \<Longrightarrow> h x = g x"
    and "h ` {a..b} \<subseteq> frontier (convex hull (path_image g))"
proof (cases "box a b = {}")
  case True
  with \<open>a<b\<close> show ?thesis by auto
next
  case False
  have interior_subset: "g ` {a<..<b} \<subseteq> interior (convex hull (path_image g))"
  proof -
    have "g ` {a<..<b} \<subseteq> path_image g"
      using ab01 unfolding path_image_def
      by (intro image_mono) (auto simp: greaterThanLessThan_subseteq_atLeastAtMost_iff)
    also have "\<dots> \<subseteq> convex hull (path_image g)"
      by (rule hull_subset)
    finally have sub: "g ` {a<..<b} \<subseteq> convex hull (path_image g)" .
    have closed: "closed (convex hull (path_image g))"
      using compact_convex_hull[OF compact_simple_path_image[OF \<open>simple_path g\<close>]]
      by (rule compact_imp_closed)
    with sub have "g ` {a<..<b} \<subseteq> frontier (convex hull (path_image g)) \<union> interior (convex hull (path_image g))"
      unfolding frontier_def by auto
    with assms(9) show ?thesis by auto
  qed
  have interior_ne: "interior (convex hull (path_image g)) \<noteq> {}"
    using interior_subset \<open>a<b\<close> by fastforce
  show ?thesis
  proof (cases "g a = g b")
    case True
    then show ?thesis
    proof -
      have ab_eq: "a = 0" "b = 1"
      proof -
        from True have "g a = g b" .
        with \<open>simple_path g\<close> ab01 have "a = b \<or> a = 0 \<and> b = 1 \<or> a = 1 \<and> b = 0"
          unfolding simple_path_def loop_free_def by auto
        with \<open>a < b\<close> show "a = 0" "b = 1" by auto
      qed
      have g01: "g 0 = g 1"
        using assms(2) by (simp add: pathfinish_def pathstart_def)
      have pi_eq: "path_image g = {g 0} \<union> g ` {0<..<1}"
        using g01 by (fastforce simp: path_image_def image_iff)
      have int_sub: "g ` {0<..<1} \<subseteq> interior (convex hull (path_image g))"
        using interior_subset ab_eq by simp
      \<comment> \<open>Every extreme point of the convex hull lies in @{term "path_image g"} but not in the interior\<close>
      have ext_sub: "{x. x extreme_point_of (convex hull (path_image g))} \<subseteq> {g 0}"
      proof (rule subsetI, clarsimp)
        fix x assume ext: "x extreme_point_of convex hull (path_image g)"
        then have "x \<in> path_image g"
          using extreme_point_of_convex_hull by blast
        moreover have "x \<notin> interior (convex hull (path_image g))"
          using extreme_point_not_in_interior[OF ext] .
        ultimately show "x = g 0"
          using int_sub pi_eq by auto
      qed
      \<comment> \<open>By Krein--Milman, the convex hull collapses to a single point\<close>
      have compact_hull: "compact (convex hull (path_image g))"
        by (rule compact_convex_hull[OF compact_simple_path_image[OF \<open>simple_path g\<close>]])
      have "convex hull (path_image g) = convex hull {x. x extreme_point_of (convex hull (path_image g))}"
        using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull] by simp
      also have "\<dots> \<subseteq> convex hull {g 0}"
        using ext_sub by (intro hull_mono)
      also have "\<dots> = {g 0}" by (simp add: convex_hull_singleton)
      finally have "convex hull (path_image g) \<subseteq> {g 0}" .
      then have "interior (convex hull (path_image g)) \<subseteq> interior {g 0}"
        by (rule interior_mono)
      then have "interior (convex hull (path_image g)) = {}"
        by (simp add: interior_singleton)
      with interior_ne show ?thesis by contradiction
    qed
  next
    case False
    have hull_eq: "convex hull (g ` ({0..1} - {a<..<b})) = convex hull (path_image g)"
    proof
      show "convex hull (g ` ({0..1} - {a<..<b})) \<subseteq> convex hull (path_image g)"
        by (intro hull_mono image_mono) (auto simp: path_image_def)
          \<comment> \<open>For $\supseteq$, use extreme points: they lie in @{term "path_image g"} but not in the interior\<close>
      have compact_hull: "compact (convex hull (path_image g))"
        by (rule compact_convex_hull[OF compact_simple_path_image[OF \<open>simple_path g\<close>]])
      have ext_in_rest: "{x. x extreme_point_of (convex hull (path_image g))} \<subseteq> g ` ({0..1} - {a<..<b})"
      proof (rule subsetI, clarsimp)
        fix x assume ext: "x extreme_point_of convex hull (path_image g)"
        then have "x \<in> path_image g"
          using extreme_point_of_convex_hull by blast
        moreover have "x \<notin> interior (convex hull (path_image g))"
          using extreme_point_not_in_interior[OF ext] .
        moreover have "g ` {a<..<b} \<subseteq> interior (convex hull (path_image g))"
          using interior_subset .
        ultimately have "x \<in> path_image g" "x \<notin> g ` {a<..<b}"
          by blast+
        then show "x \<in> g ` ({0..1} - {a<..<b})"
          unfolding path_image_def by blast
      qed
      show "convex hull (path_image g) \<subseteq> convex hull (g ` ({0..1} - {a<..<b}))"
        using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull]
        using ext_in_rest hull_mono by blast
    qed
    have hull_seg_eq: "convex hull (closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})) = convex hull (path_image g)"
    proof
      have "g a \<in> g ` ({0..1} - {a<..<b})" "g b \<in> g ` ({0..1} - {a<..<b})"
        using ab01 \<open>a < b\<close> by auto
      then have seg_sub: "closed_segment (g a) (g b) \<subseteq> convex hull (g ` ({0..1} - {a<..<b}))"
        by (meson closed_segment_subset convex_convex_hull hull_inc)
      show "convex hull (closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})) \<subseteq> convex hull (path_image g)"
        by (metis hull_eq convex_convex_hull hull_subset le_supI seg_sub subset_hull)
      show "convex hull (path_image g) \<subseteq> convex hull (closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b}))"
        by (metis Un_commute Un_upper1 hull_eq hull_mono)
    qed
  \<comment> \<open>Step 1: double arc decomposition of @{term g}\<close>
    obtain g0 g1 where arcs:
      "arc g0" "arc g1"
      "pathstart g0 = g a" "pathfinish g0 = g b"
      "pathstart g1 = g b" "pathfinish g1 = g a"
      "path_image g0 = g ` {a..b}"
      "path_image g1 = g ` ({0..1} - {a<..<b})"
      "(path_image g0) \<inter> (path_image g1) = {g a, g b}"
      "(path_image g0) \<union> (path_image g1) = path_image g"
      using exists_double_arc_explicit[OF \<open>simple_path g\<close> \<open>pathfinish g = pathstart g\<close>
          ab01(1) ab01(2) less_imp_le[OF \<open>a < b\<close>] False] by blast

    \<comment> \<open>Step 2: the frontier of the convex hull admits a rectifiable simple loop parametrization
       (this corresponds to HOL Light's \<open>RECTIFIABLE_LOOP_RELATIVE_FRONTIER_CONVEX\<close>)\<close>
    have frontier_eq_rel: "rel_frontier (convex hull (path_image g)) = frontier (convex hull (path_image g))"
      using rel_frontier_nonempty_interior[OF interior_ne] by simp
    obtain d where d_props:
      "simple_path d" "pathfinish d = pathstart d" "rectifiable_path d"
      "path_image d = frontier (convex hull (path_image g))"
    proof -
      have "convex (convex hull (path_image g))" by (rule convex_convex_hull)
      moreover have "bounded (convex hull (path_image g))"
        by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image \<open>simple_path g\<close>)
      moreover have "interior (convex hull (path_image g)) \<noteq> {}"
        by (rule interior_ne)
      moreover note frontier_eq_rel
      ultimately show ?thesis 
        using rectifiable_loop_frontier_convex that by blast
    qed

\<comment> \<open>Step 4: double arc decomposition of the frontier loop @{term d}, with inside decomposition\<close>
    have ga_ne_gb: "g a \<noteq> g b" using False .
    obtain d0 d1 where d_split:
      "arc d0" "arc d1"
      "pathstart d0 = g a" "pathfinish d0 = g b"
      "pathstart d1 = g b" "pathfinish d1 = g a"
      "path_image d0 \<inter> path_image d1 = {g a, g b}"
      "path_image d0 \<union> path_image d1 = path_image d"
      "inside (path_image d0 \<union> path_image g0) \<inter>
       inside (path_image d1 \<union> path_image g0) = {}"
      "inside (path_image d0 \<union> path_image g0) \<union>
       inside (path_image d1 \<union> path_image g0) \<union>
       (path_image g0 - {g a, g b}) =
       interior (convex hull (path_image g))"
      "(path_image g1 - {g b, g a}) \<inter> path_image d0 = {}"
    proof -
      have ga_d: "g a \<in> path_image d" and gb_d: "g b \<in> path_image d"
        using d_props(4) assms(7,8) by simp_all
      obtain d0 d1 where da:
        "arc d0" "arc d1"
        "pathstart d0 = g a" "pathfinish d0 = g b"
        "pathstart d1 = g b" "pathfinish d1 = g a"
        "path_image d0 \<inter> path_image d1 = {g a, g b}"
        "path_image d0 \<union> path_image d1 = path_image d"
        using exists_double_arc[OF d_props(1) d_props(2) ga_d gb_d ga_ne_gb] by metis
      \<comment> \<open>Endpoints and basic simple-path facts for the frontier arcs @{term d0}, @{term d1}\<close>
      have sp_d0: "simple_path d0" and sp_d1: "simple_path d1"
        using da(1,2) arc_imp_simple_path by blast+
      have rev_ends: "pathstart (reversepath d1) = g a" "pathfinish (reversepath d1) = g b"
        using da(5,6) by (simp_all add: pathstart_reversepath pathfinish_reversepath)
      have rev_pi: "path_image (reversepath d1) = path_image d1"
        by (simp add: path_image_reversepath)
      have sp_rev_d1: "simple_path (reversepath d1)"
        using sp_d1 by (simp add: simple_path_reversepath)
      have sp_g0: "simple_path g0" using arcs(1) arc_imp_simple_path by blast
      note g0_ends = arcs(3,4)
      have gab_g0: "g a \<in> path_image g0" "g b \<in> path_image g0"
        using g0_ends by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have gab_d0: "g a \<in> path_image d0" "g b \<in> path_image d0"
        using da(3,4) by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have gab_d1: "g a \<in> path_image d1" "g b \<in> path_image d1"
        using da(5,6) by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have d0_sub: "path_image d0 \<subseteq> path_image d" and d1_sub: "path_image d1 \<subseteq> path_image d"
        using da(8) by blast+
      \<comment> \<open>The open part of @{term g0} lies in the interior, hence @{term g0} meets the frontier only at $g\,a$, $g\,b$\<close>
      have g0_decomp: "path_image g0 = g ` {a<..<b} \<union> {g a, g b}"
      proof -
        have "{a..b} = {a<..<b} \<union> {a, b}"
          using \<open>a < b\<close> by auto
        then have "g ` {a..b} = g ` {a<..<b} \<union> {g a, g b}"
          by (simp add: image_Un)
        then show ?thesis using arcs(7) by simp
      qed
      have g0_d_int: "path_image g0 \<inter> path_image d = {g a, g b}"
      proof -
        have "g ` {a<..<b} \<inter> path_image d = {}"
          using assms(9) d_props(4) by simp
        moreover have "{g a, g b} \<subseteq> path_image d"
          using ga_d gb_d by simp
        ultimately show ?thesis
          using g0_decomp by blast
      qed
      have d0_g0_int: "path_image d0 \<inter> path_image g0 = {g a, g b}"
      proof
        show "path_image d0 \<inter> path_image g0 \<subseteq> {g a, g b}"
          using d0_sub g0_d_int by blast
        show "{g a, g b} \<subseteq> path_image d0 \<inter> path_image g0"
          using gab_d0 gab_g0 by blast
      qed
      have d1_g0_int: "path_image d1 \<inter> path_image g0 = {g a, g b}"
      proof
        show "path_image d1 \<inter> path_image g0 \<subseteq> {g a, g b}"
          using d1_sub g0_d_int by blast
        show "{g a, g b} \<subseteq> path_image d1 \<inter> path_image g0"
          using gab_d1 gab_g0 by blast
      qed
      \<comment> \<open>Split the inside via \<open>SPLIT_INSIDE_SIMPLE_CLOSED_CURVE\<close> on @{term d0}, @{term "reversepath d1"}, @{term g0}\<close>
      have d_union: "path_image d0 \<union> path_image (reversepath d1) = path_image d"
        using da(8) rev_pi by simp
      have inside_eq: "inside (path_image d0 \<union> path_image (reversepath d1)) = interior (convex hull path_image g)"
      proof -
        have "bounded (convex hull path_image g)"
          by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image \<open>simple_path g\<close>)
        then have "inside (frontier (convex hull path_image g)) = interior (convex hull path_image g)"
          using inside_frontier_eq_interior convex_convex_hull by blast
        then show ?thesis
          using d_union d_props(4) by simp
      qed
      have g0_inside_ne: "path_image g0 \<inter> inside (path_image d0 \<union> path_image (reversepath d1)) \<noteq> {}"
      proof -
        have "g ` {a<..<b} \<noteq> {}"
          using \<open>a < b\<close> by auto
        moreover have "g ` {a<..<b} \<subseteq> path_image g0"
          using g0_decomp by blast
        moreover have "g ` {a<..<b} \<subseteq> interior (convex hull path_image g)"
          using interior_subset by blast
        ultimately show ?thesis
          using inside_eq by blast
      qed
      have d0_rev_int: "path_image d0 \<inter> path_image (reversepath d1) = {g a, g b}"
        using da(7) rev_pi by simp
      have split:
        "inside (path_image d0 \<union> path_image g0) \<inter> inside (path_image (reversepath d1) \<union> path_image g0) = {}"
        "inside (path_image d0 \<union> path_image g0) \<union> inside (path_image (reversepath d1) \<union> path_image g0) \<union> (path_image g0 - {g a, g b}) = inside (path_image d0 \<union> path_image (reversepath d1))"
        using split_inside_simple_closed_curve[OF sp_d0 da(3,4) sp_rev_d1 rev_ends sp_g0 g0_ends ga_ne_gb
            d0_rev_int d0_g0_int _ g0_inside_ne]
        by (simp_all add: rev_pi d1_g0_int)
      have split1: "inside (path_image d0 \<union> path_image g0) \<inter> inside (path_image d1 \<union> path_image g0) = {}"
        using split(1) rev_pi by simp
      have split2: "inside (path_image d0 \<union> path_image g0) \<union> inside (path_image d1 \<union> path_image g0) \<union> (path_image g0 - {g a, g b}) = interior (convex hull path_image g)"
        using split(2) rev_pi inside_eq by simp
      \<comment> \<open>Step 4 (cont.): orient the split so that @{term g1}'s interior avoids @{term d0}.
          This is a connectedness argument on @{term "path_image g1 - {g a, g b}"}.\<close>
      have arc_rev_g0: "arc (reversepath g0)" using arcs(1) by (simp add: arc_reversepath)
      have J0_loop: "simple_path (d0 +++ reversepath g0)"
      proof (rule simple_path_join_loop)
        show "arc d0" by (rule da(1))
        show "arc (reversepath g0)" by (rule arc_rev_g0)
        show "pathfinish d0 = pathstart (reversepath g0)"
          using da(4) g0_ends by (simp add: pathstart_reversepath)
        show "pathfinish (reversepath g0) = pathstart d0"
          using da(3) g0_ends by (simp add: pathfinish_reversepath)
        show "path_image d0 \<inter> path_image (reversepath g0) \<subseteq> {pathstart d0, pathstart (reversepath g0)}"
          using d0_g0_int da(3) g0_ends by (simp add: path_image_reversepath pathstart_reversepath)
      qed
      have J0_close: "pathfinish (d0 +++ reversepath g0) = pathstart (d0 +++ reversepath g0)"
        using da(3) g0_ends by (simp add: pathstart_reversepath pathfinish_reversepath)
      have J0_pi: "path_image (d0 +++ reversepath g0) = path_image d0 \<union> path_image g0"
        using da(4) g0_ends by (simp add: path_image_join pathstart_reversepath path_image_reversepath)
      have J1_loop: "simple_path (reversepath d1 +++ reversepath g0)"
      proof (rule simple_path_join_loop)
        show "arc (reversepath d1)" using da(2) by (simp add: arc_reversepath)
        show "arc (reversepath g0)" by (rule arc_rev_g0)
        show "pathfinish (reversepath d1) = pathstart (reversepath g0)"
          using da(5) g0_ends by (simp add: pathstart_reversepath pathfinish_reversepath)
        show "pathfinish (reversepath g0) = pathstart (reversepath d1)"
          using da(6) g0_ends by (simp add: pathstart_reversepath pathfinish_reversepath)
        show "path_image (reversepath d1) \<inter> path_image (reversepath g0) \<subseteq> {pathstart (reversepath d1), pathstart (reversepath g0)}"
          using d1_g0_int da(6) g0_ends by (simp add: path_image_reversepath pathstart_reversepath pathfinish_reversepath)
      qed
      have J1_close: "pathfinish (reversepath d1 +++ reversepath g0) = pathstart (reversepath d1 +++ reversepath g0)"
        using da(6) g0_ends by (simp add: pathstart_reversepath pathfinish_reversepath)
      have J1_pi: "path_image (reversepath d1 +++ reversepath g0) = path_image d1 \<union> path_image g0"
        using da(5) g0_ends by (simp add: path_image_join pathstart_reversepath pathfinish_reversepath path_image_reversepath)
      have J0_jio: "frontier (inside (path_image d0 \<union> path_image g0)) = path_image d0 \<union> path_image g0"
        using Jordan_inside_outside[OF J0_loop J0_close] J0_pi by simp
      have J1_jio: "frontier (inside (path_image d1 \<union> path_image g0)) = path_image d1 \<union> path_image g0"
        using Jordan_inside_outside[OF J1_loop J1_close] J1_pi by simp
      have cl_J0: "closure (inside (path_image d0 \<union> path_image g0)) = inside (path_image d0 \<union> path_image g0) \<union> path_image d0 \<union> path_image g0"
        using closure_Un_frontier[of "inside (path_image d0 \<union> path_image g0)"] J0_jio by (simp add: Un_assoc)
      have cl_J1: "closure (inside (path_image d1 \<union> path_image g0)) = inside (path_image d1 \<union> path_image g0) \<union> path_image d1 \<union> path_image g0"
        using closure_Un_frontier[of "inside (path_image d1 \<union> path_image g0)"] J1_jio by (simp add: Un_assoc)
      have sp_g1: "simple_path g1" using arcs(2) arc_imp_simple_path by blast
      define S where "S = path_image g1 - {g b, g a}"
      have S_conn: "connected S"
        using connected_simple_path_endless[OF sp_g1] arcs(5,6) unfolding S_def
        by (simp add: insert_commute)
      have g1_g0_int: "path_image g1 \<inter> path_image g0 = {g a, g b}"
        using arcs(9) by (simp add: Int_commute)
      have S_g0: "S \<inter> path_image g0 = {}"
        using g1_g0_int unfolding S_def by blast
      have d0d1_front: "path_image d0 \<union> path_image d1 = frontier (convex hull path_image g)"
        using da(8) d_props(4) by simp
      have cldd0: "closed (path_image d0 \<union> path_image g0)"
        using da(1) arcs(1) by (simp add: closed_path_image arc_imp_path closed_Un)
      have cldd1: "closed (path_image d1 \<union> path_image g0)"
        using da(2) arcs(1) by (simp add: closed_path_image arc_imp_path closed_Un)
      have op_in0: "open (inside (path_image d0 \<union> path_image g0))" using cldd0 by (rule open_inside)
      have op_in1: "open (inside (path_image d1 \<union> path_image g0))" using cldd1 by (rule open_inside)
      have g1_in_hull: "path_image g1 \<subseteq> convex hull path_image g"
      proof -
        have "path_image g1 \<subseteq> path_image g" using arcs(10) by blast
        also have "\<dots> \<subseteq> convex hull path_image g" by (rule hull_subset)
        finally show ?thesis .
      qed
      have hull_closed: "closed (convex hull path_image g)"
        by (simp add: compact_imp_closed compact_convex_hull compact_simple_path_image \<open>simple_path g\<close>)
      have g1_cover: "path_image g1 \<subseteq> interior (convex hull path_image g) \<union> frontier (convex hull path_image g)"
        using g1_in_hull hull_closed by (simp add: frontier_def closure_closed) blast
      \<comment> \<open>@{term S} (which is @{term g1} minus its endpoints) is covered by the two \<open>inside\<close>-plus-arc regions ...\<close>
      have cover: "\<And>z. z \<in> S \<Longrightarrow> z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<union> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
      proof -
        fix z assume zS: "z \<in> S"
        have zg1: "z \<in> path_image g1" and zng0: "z \<notin> path_image g0"
          using zS S_def g1_g0_int by auto
        consider "z \<in> interior (convex hull path_image g)" | "z \<in> frontier (convex hull path_image g)"
          using g1_cover zg1 by blast
        then show "z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<union> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
        proof cases
          case 1
          then have "z \<in> inside (path_image d0 \<union> path_image g0) \<union> inside (path_image d1 \<union> path_image g0) \<union> (path_image g0 - {g a, g b})"
            using split2 by simp
          then show ?thesis using zng0 by blast
        next
          case 2
          then have "z \<in> path_image d0 \<union> path_image d1" using d0d1_front by simp
          then show ?thesis by blast
        qed
      qed
      have ic0: "inside (path_image d1 \<union> path_image g0) \<inter> closure (inside (path_image d0 \<union> path_image g0)) = {}"
      proof -
        have "inside (path_image d1 \<union> path_image g0) \<inter> inside (path_image d0 \<union> path_image g0) = {}"
          using split1 by (simp add: Int_commute)
        then show ?thesis using open_Int_closure_eq_empty[OF op_in1, of "inside (path_image d0 \<union> path_image g0)"] by simp
      qed
      have ic1: "inside (path_image d0 \<union> path_image g0) \<inter> closure (inside (path_image d1 \<union> path_image g0)) = {}"
      proof -
        have "inside (path_image d0 \<union> path_image g0) \<inter> inside (path_image d1 \<union> path_image g0) = {}"
          using split1 by simp
        then show ?thesis using open_Int_closure_eq_empty[OF op_in0, of "inside (path_image d1 \<union> path_image g0)"] by simp
      qed
      have d0_cl: "path_image d0 \<subseteq> closure (inside (path_image d0 \<union> path_image g0))"
        using cl_J0 by blast
      have d1_cl: "path_image d1 \<subseteq> closure (inside (path_image d1 \<union> path_image g0))"
        using cl_J1 by blast
      have in1_d0: "inside (path_image d1 \<union> path_image g0) \<inter> path_image d0 = {}"
        using ic0 d0_cl by blast
      have d1_in0: "path_image d1 \<inter> inside (path_image d0 \<union> path_image g0) = {}"
        using ic1 d1_cl by blast
      have in1_in0: "inside (path_image d1 \<union> path_image g0) \<inter> inside (path_image d0 \<union> path_image g0) = {}"
        using split1 by (simp add: Int_commute)
      have d1_d0_S: "\<And>z. z \<in> S \<Longrightarrow> \<not>(z \<in> path_image d1 \<and> z \<in> path_image d0)"
        using da(7) unfolding S_def by blast
      \<comment> \<open>... and the two regions are disjoint on @{term S}, so @{term S} splits into two relatively clopen pieces\<close>
      have disj: "\<And>z. z \<in> S \<Longrightarrow> \<not>(z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<and> z \<in> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0)))"
      proof -
        fix z assume zS: "z \<in> S"
        show "\<not>(z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<and> z \<in> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0)))"
          using in1_d0 in1_in0 d1_in0 d1_d0_S[OF zS] by blast
      qed
      have eqA: "S - closure (inside (path_image d1 \<union> path_image g0)) = S \<inter> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
      proof -
        have "S - closure (inside (path_image d1 \<union> path_image g0)) = S - (inside (path_image d1 \<union> path_image g0) \<union> path_image d1)"
          using cl_J1 S_g0 by blast
        also have "\<dots> = S \<inter> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
          using cover disj by blast
        finally show ?thesis .
      qed
      have eqB: "S - closure (inside (path_image d0 \<union> path_image g0)) = S \<inter> (path_image d1 \<union> inside (path_image d1 \<union> path_image g0))"
      proof -
        have "S - closure (inside (path_image d0 \<union> path_image g0)) = S - (inside (path_image d0 \<union> path_image g0) \<union> path_image d0)"
          using cl_J0 S_g0 by blast
        also have "\<dots> = S \<inter> (path_image d1 \<union> inside (path_image d1 \<union> path_image g0))"
          using cover disj by blast
        finally show ?thesis .
      qed
      have opA: "openin (top_of_set S) (S - closure (inside (path_image d1 \<union> path_image g0)))"
      proof -
        have "S - closure (inside (path_image d1 \<union> path_image g0)) = S \<inter> (- closure (inside (path_image d1 \<union> path_image g0)))"
          by blast
        moreover have "open (- closure (inside (path_image d1 \<union> path_image g0)))"
          by (simp add: open_Compl)
        ultimately show ?thesis
          by (simp add: openin_open_Int)
      qed
      have opB: "openin (top_of_set S) (S - closure (inside (path_image d0 \<union> path_image g0)))"
      proof -
        have "S - closure (inside (path_image d0 \<union> path_image g0)) = S \<inter> (- closure (inside (path_image d0 \<union> path_image g0)))"
          by blast
        moreover have "open (- closure (inside (path_image d0 \<union> path_image g0)))"
          by (simp add: open_Compl)
        ultimately show ?thesis
          by (simp add: openin_open_Int)
      qed
      have AB_cover: "(S - closure (inside (path_image d1 \<union> path_image g0))) \<union> (S - closure (inside (path_image d0 \<union> path_image g0))) = S"
        using eqA eqB cover by blast
      have AB_disj: "(S - closure (inside (path_image d1 \<union> path_image g0))) \<inter> (S - closure (inside (path_image d0 \<union> path_image g0))) = {}"
        using eqA eqB in1_d0 in1_in0 d1_in0 d1_d0_S split1 by auto
      have one_empty: "(S - closure (inside (path_image d1 \<union> path_image g0))) = {} \<or> (S - closure (inside (path_image d0 \<union> path_image g0))) = {}"
        using S_conn opA opB AB_cover AB_disj connected_openin by blast
      have disjunction: "S \<inter> path_image d0 = {} \<or> S \<inter> path_image d1 = {}"
      proof -
        consider "S - closure (inside (path_image d1 \<union> path_image g0)) = {}" | "S - closure (inside (path_image d0 \<union> path_image g0)) = {}"
          using one_empty by blast
        then show ?thesis
        proof cases
          case 1
          then have "S \<inter> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0)) = {}" using eqA by simp
          then show ?thesis by blast
        next
          case 2
          then have "S \<inter> (path_image d1 \<union> inside (path_image d1 \<union> path_image g0)) = {}" using eqB by simp
          then show ?thesis by blast
        qed
      qed
      \<comment> \<open>Whichever arc @{term S} avoids becomes @{term d0} (reversing the pair in the second case)\<close>
      show thesis
      proof (cases "S \<inter> path_image d0 = {}")
        case True
        then have c11: "(path_image g1 - {g b, g a}) \<inter> path_image d0 = {}" unfolding S_def by simp
        show thesis
          by (rule that[OF da(1) da(2) da(3) da(4) da(5) da(6) da(7) da(8) split1 split2 c11])
      next
        case False
        then have d1e: "(path_image g1 - {g b, g a}) \<inter> path_image d1 = {}"
          using disjunction unfolding S_def by blast
        have r1: "arc (reversepath d1)" using da(2) by (simp add: arc_reversepath)
        have r2: "arc (reversepath d0)" using da(1) by (simp add: arc_reversepath)
        have r3: "pathstart (reversepath d1) = g a" using da(6) by (simp add: pathstart_reversepath)
        have r4: "pathfinish (reversepath d1) = g b" using da(5) by (simp add: pathfinish_reversepath)
        have r5: "pathstart (reversepath d0) = g b" using da(4) by (simp add: pathstart_reversepath)
        have r6: "pathfinish (reversepath d0) = g a" using da(3) by (simp add: pathfinish_reversepath)
        have r7: "path_image (reversepath d1) \<inter> path_image (reversepath d0) = {g a, g b}"
          using da(7) by (simp add: path_image_reversepath Int_commute)
        have r8: "path_image (reversepath d1) \<union> path_image (reversepath d0) = path_image d"
          using da(8) by (simp add: path_image_reversepath Un_commute)
        have r9: "inside (path_image (reversepath d1) \<union> path_image g0) \<inter> inside (path_image (reversepath d0) \<union> path_image g0) = {}"
          using split1 by (simp add: path_image_reversepath Int_commute)
        have r10: "inside (path_image (reversepath d1) \<union> path_image g0) \<union> inside (path_image (reversepath d0) \<union> path_image g0) \<union> (path_image g0 - {g a, g b}) = interior (convex hull path_image g)"
          using split2 by (simp add: path_image_reversepath Un_commute Un_left_commute)
        have r11: "(path_image g1 - {g b, g a}) \<inter> path_image (reversepath d1) = {}"
          using d1e by (simp add: path_image_reversepath)
        show thesis
          by (rule that[OF r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11])
      qed
    qed
    \<comment> \<open>Step 3: $g(a)$ and $g(b)$ are on the @{term "path_image d"}\<close>
    have ga_in_d: "g a \<in> path_image d" and gb_in_d: "g b \<in> path_image d"
      using d_props(4) assms(7,8) by auto
    \<comment> \<open>Step 4: build @{term h} as the straight segment from $g(a)$ to $g(b)$ on $(a,b)$, unchanged elsewhere.
       (\<open>front_arc\<close> is no longer used; see \<open>step_lemma_proof_body.thy\<close> in memory for derivation notes.)\<close>
    show ?thesis
    proof -
      have hull_closed: "closed (convex hull path_image g)"
        by (simp add: compact_imp_closed compact_convex_hull compact_simple_path_image \<open>simple_path g\<close>)
      have compact_hull: "compact (convex hull path_image g)"
        by (simp add: compact_convex_hull compact_simple_path_image \<open>simple_path g\<close>)
      have d1_sub_hull: "convex hull (path_image d1) \<subseteq> convex hull (path_image g)"
      proof -
        have "path_image d1 \<subseteq> path_image d" using d_split(8) by blast
        also have "\<dots> = frontier (convex hull path_image g)" using d_props(4) .
        also have "\<dots> \<subseteq> convex hull path_image g"
          using hull_closed by (simp add: frontier_def closure_closed)
        finally have "path_image d1 \<subseteq> convex hull path_image g" .
        then show ?thesis by (simp add: hull_minimal)
      qed
      have km_ext: "convex hull path_image g = convex hull {x. x extreme_point_of (convex hull path_image g)}"
        using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull] by simp
      have test_cl: "\<And>x. x \<in> path_image g \<Longrightarrow> x \<in> closure (convex hull path_image g)"
        using closure_subset hull_subset by (meson subset_iff)
      have test_front: "\<And>x. x \<in> closure (convex hull path_image g) \<Longrightarrow> x \<notin> interior (convex hull path_image g) \<Longrightarrow> x \<in> frontier (convex hull path_image g)"
        by (simp add: frontier_def)
      have ext_in_g_front: "\<And>x. x extreme_point_of (convex hull path_image g) \<Longrightarrow> x \<in> path_image g \<inter> path_image d"
      proof -
        fix x assume e: "x extreme_point_of (convex hull path_image g)"
        have xg: "x \<in> path_image g" using extreme_point_of_convex_hull[OF e] .
        then have "x \<in> closure (convex hull path_image g)" using test_cl by blast
        moreover have "x \<notin> interior (convex hull path_image g)"
          using extreme_point_not_in_interior[OF e] .
        ultimately have "x \<in> frontier (convex hull path_image g)" using test_front by blast
        then have "x \<in> path_image d" using d_props(4) by simp
        with xg show "x \<in> path_image g \<inter> path_image d" by simp
      qed
      have gab_d1: "g a \<in> path_image d1" "g b \<in> path_image d1"
        using d_split(5,6) by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have g0_int_d: "path_image g0 \<inter> path_image d = {g a, g b}"
      proof -
        have "g ` {a<..<b} \<inter> path_image d = {}" using assms(9) d_props(4) by simp
        moreover have "path_image g0 = g ` {a<..<b} \<union> {g a, g b}"
        proof -
          have "{a..b} = {a<..<b} \<union> {a, b}" using \<open>a < b\<close> by auto
          then have "g ` {a..b} = g ` {a<..<b} \<union> {g a, g b}" by (simp add: image_Un)
          then show ?thesis using arcs(7) by simp
        qed
        moreover have "{g a, g b} \<subseteq> path_image d" using ga_in_d gb_in_d by simp
        ultimately show ?thesis by blast
      qed
      have g1_int_d: "path_image g1 \<inter> path_image d \<subseteq> path_image d1"
      proof -
        have "path_image g1 \<inter> path_image d0 \<subseteq> {g a, g b}" using d_split(11) by blast
        then have "path_image g1 \<inter> path_image d0 \<subseteq> path_image d1" using gab_d1 by blast
        moreover have "path_image g1 \<inter> path_image d1 \<subseteq> path_image d1" by blast
        moreover have "path_image d = path_image d0 \<union> path_image d1" using d_split(8) by simp
        ultimately show ?thesis by blast
      qed
      have hull_d1_eq: "convex hull (path_image d1) = convex hull (path_image g)"
      proof (rule subset_antisym)
        show "convex hull (path_image d1) \<subseteq> convex hull (path_image g)" by (rule d1_sub_hull)
      next
        have "path_image g \<inter> path_image d \<subseteq> path_image d1"
        proof -
          have "path_image g = path_image g0 \<union> path_image g1" using arcs(10) by simp
          then have "path_image g \<inter> path_image d = (path_image g0 \<inter> path_image d) \<union> (path_image g1 \<inter> path_image d)" by blast
          also have "\<dots> \<subseteq> {g a, g b} \<union> path_image d1" using g0_int_d g1_int_d by blast
          also have "\<dots> \<subseteq> path_image d1" using gab_d1 by blast
          finally show ?thesis .
        qed
        then have "{x. x extreme_point_of (convex hull path_image g)} \<subseteq> path_image d1"
          using ext_in_g_front by blast
        then have "convex hull {x. x extreme_point_of (convex hull path_image g)} \<subseteq> convex hull (path_image d1)"
          by (rule hull_mono)
        then show "convex hull (path_image g) \<subseteq> convex hull (path_image d1)" using km_ext by simp
      qed
      \<comment> \<open>The straight segment between $g(a)$ and $g(b)$ lies on the frontier, via \<open>seg_frontier_aux\<close>
         applied to the arc @{term d1} (whose hull is the whole convex hull by \<open>hull_d1_eq\<close>).\<close>
      have seg_in_frontier: "closed_segment (g a) (g b) \<subseteq> frontier (convex hull path_image g)"
      proof (rule seg_frontier_aux[of _ _ _ d1])
        show "convex (convex hull path_image g)" by (rule convex_convex_hull)
        show "compact (convex hull path_image g)" by (rule compact_hull)
        show "interior (convex hull path_image g) \<noteq> {}" by (rule interior_ne)
        show "g a \<in> frontier (convex hull path_image g)" by (rule assms(7))
        show "g b \<in> frontier (convex hull path_image g)" by (rule assms(8))
        show "g a \<noteq> g b" by (rule ga_ne_gb)
        show "path_image d1 \<subseteq> frontier (convex hull path_image g)"
          using d_split(8) d_props(4) by blast
        show "connected (path_image d1 - {g a, g b})"
          using connected_simple_path_endless[OF arc_imp_simple_path[OF d_split(2)]] d_split(5,6)
          by (simp add: insert_commute)
        show "g a \<in> path_image d1" by (rule gab_d1(1))
        show "g b \<in> path_image d1" by (rule gab_d1(2))
        show "convex hull path_image d1 = convex hull path_image g" by (rule hull_d1_eq)
      qed
      have rev_d1_arc: "arc (reversepath d1)" using d_split(2) by (simp add: arc_reversepath)
      have rev_d1_start: "pathstart (reversepath d1) = g a" using d_split(6) by (simp add: pathstart_reversepath)
      have rev_d1_finish: "pathfinish (reversepath d1) = g b" using d_split(5) by (simp add: pathfinish_reversepath)
      have rev_d1_pi: "path_image (reversepath d1) = path_image d1" by (simp add: path_image_reversepath)
      have d0d1_pi: "path_image d0 \<union> path_image (reversepath d1) = frontier (convex hull path_image g)"
        using rev_d1_pi d_split(8) d_props(4) by simp
      have int_ends: "path_image d0 \<inter> path_image (reversepath d1) = {pathstart d0, pathfinish d0}"
        using d_split(7) rev_d1_pi d_split(3,4) by simp
      have seg_sub_union: "closed_segment (g a) (g b) \<subseteq> path_image d0 \<union> path_image (reversepath d1)"
        using seg_in_frontier d0d1_pi by simp
      have dich: "path_image d0 \<subseteq> closed_segment (g a) (g b) \<or> path_image (reversepath d1) \<subseteq> closed_segment (g a) (g b)"
      proof (rule connected_subset_arc_pair[where g=d0 and h="reversepath d1"])
        show "arc d0" by (rule d_split(1))
        show "arc (reversepath d1)" by (rule rev_d1_arc)
        show "pathstart d0 = pathstart (reversepath d1)" using d_split(3) rev_d1_start by simp
        show "pathfinish d0 = pathfinish (reversepath d1)" using d_split(4) rev_d1_finish by simp
        show "path_image d0 \<inter> path_image (reversepath d1) = {pathstart d0, pathfinish d0}" by (rule int_ends)
        show "connected (closed_segment (g a) (g b))" by simp
        show "closed_segment (g a) (g b) \<subseteq> path_image d0 \<union> path_image (reversepath d1)" by (rule seg_sub_union)
        show "pathstart d0 \<in> closed_segment (g a) (g b)" using d_split(3) by simp
        show "pathfinish d0 \<in> closed_segment (g a) (g b)" using d_split(4) by simp
      qed
      have not_d1: "\<not> (path_image (reversepath d1) \<subseteq> closed_segment (g a) (g b))"
      proof
        assume "path_image (reversepath d1) \<subseteq> closed_segment (g a) (g b)"
        then have "path_image d1 \<subseteq> closed_segment (g a) (g b)" using rev_d1_pi by simp
        then have "convex hull (path_image d1) \<subseteq> convex hull (closed_segment (g a) (g b))"
          by (rule hull_mono)
        also have "convex hull (closed_segment (g a) (g b)) = closed_segment (g a) (g b)"
          by (simp add: hull_same convex_closed_segment)
        finally have "convex hull (path_image g) \<subseteq> closed_segment (g a) (g b)"
          using hull_d1_eq by simp
        then have "interior (convex hull (path_image g)) \<subseteq> interior (closed_segment (g a) (g b))"
          by (rule interior_mono)
        also have "interior (closed_segment (g a) (g b)) = {}"
          by (rule interior_closed_segment_ge2) simp
        finally show False using interior_ne by simp
      qed
      have d0_sub_seg: "path_image d0 \<subseteq> closed_segment (g a) (g b)"
        using dich not_d1 by blast
      have d0_eq_seg: "path_image d0 = closed_segment (g a) (g b)"
      proof (rule connected_subset_segment)
        show "connected (path_image d0)" using d_split(1) by (simp add: connected_arc_image)
        show "path_image d0 \<subseteq> closed_segment (g a) (g b)" by (rule d0_sub_seg)
        show "g a \<in> path_image d0" using gab_d1 d_split(3) by (metis pathstart_in_path_image)
        show "g b \<in> path_image d0" using d_split(4) by (metis pathfinish_in_path_image)
      qed
      define h where "h \<equiv> \<lambda>t. if t \<in> {a<..<b} then g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a) else g t"
      have interval_img: "(\<lambda>t. (t - a)/(b - a)) ` {a..b} = {0..1}"
      proof -
        have nz: "b - a > 0" using \<open>a < b\<close> by simp
        have "(\<lambda>t. (t - a)/(b - a)) ` {a..b} = (\<lambda>t. t/(b-a) - a/(b-a)) ` {a..b}"
          by (simp add: diff_divide_distrib)
        also have "\<dots> = {a/(b-a) - a/(b-a) .. b/(b-a) - a/(b-a)}"
          using nz by (subst image_affinity_atLeastAtMost_div_diff) auto
        also have "\<dots> = {0..1}" using nz by (simp add: diff_divide_distrib [symmetric] divide_self_if)
        finally show ?thesis .
      qed
      have lin: "(\<lambda>t. g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)) ` {a..b} = closed_segment (g a) (g b)"
      proof -
        have "(\<lambda>t. g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)) ` {a..b}
            = (\<lambda>u. g a + u *\<^sub>R (g b - g a)) ` ((\<lambda>t. (t-a)/(b-a)) ` {a..b})"
          by (simp add: image_image)
        also have "\<dots> = (\<lambda>u. g a + u *\<^sub>R (g b - g a)) ` {0..1}"
          using interval_img by simp
        also have "\<dots> = closed_segment (g a) (g b)"
          by (simp add: closed_segment_image_interval algebra_simps cong: image_cong)
        finally show ?thesis .
      qed
      have hh_eq_lin: "\<And>t. t \<in> {a..b} \<Longrightarrow> h t = g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)"
      proof -
        fix t assume t: "t \<in> {a..b}"
        show "h t = g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)"
        proof (cases "t \<in> {a<..<b}")
          case True then show ?thesis by (simp add: h_def)
        next
          case False
          with t have "t = a \<or> t = b" by auto
          then show ?thesis using \<open>a < b\<close> by (auto simp: h_def)
        qed
      qed
      have hh_seg: "h ` {a..b} = closed_segment (g a) (g b)"
      proof -
        have "h ` {a..b} = (\<lambda>t. g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)) ` {a..b}"
          by (rule image_cong[OF refl hh_eq_lin])
        with lin show ?thesis by simp
      qed
      have a_ge0: "0 \<le> a" and b_le1: "b \<le> 1" using ab01 by auto
      have hh_0: "h 0 = g 0" using a_ge0 by (simp add: h_def)
      have hh_1: "h 1 = g 1" using b_le1 by (simp add: h_def)
      have hh_start: "pathstart h = pathstart g" by (simp add: pathstart_def hh_0)
      have hh_finish: "pathfinish h = pathstart g"
        using assms(2) by (simp add: pathstart_def pathfinish_def hh_1)
      have hh_frontier: "h ` {a..b} \<subseteq> frontier (convex hull path_image g)"
        using hh_seg seg_in_frontier by simp
      have hh_out_img: "h ` ({0..1} - {a<..<b}) = g ` ({0..1} - {a<..<b})"
      proof (rule image_cong[OF refl])
        fix x assume x: "x \<in> {0..1} - {a<..<b}"
        have "x \<notin> {a<..<b}" using x by simp
        then show "h x = g x" unfolding h_def by presburger
      qed
      have univ: "{0..1} = {a..b} \<union> ({0..1} - {a<..<b})"
        using ab01 \<open>a < b\<close> by auto
      have pi_h: "path_image h = closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})"
      proof -
        have "path_image h = h ` {0..1}" by (simp add: path_image_def)
        also have "\<dots> = h ` {a..b} \<union> h ` ({0..1} - {a<..<b})"
          by (subst univ) (simp add: image_Un)
        also have "\<dots> = closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})"
          using hh_seg hh_out_img by simp
        finally show ?thesis .
      qed
      have front_in_hull: "frontier (convex hull path_image g) \<subseteq> convex hull path_image g"
        using hull_closed by (simp add: frontier_def closure_closed)
      have seg_in: "closed_segment (g a) (g b) \<subseteq> convex hull path_image g"
        using seg_in_frontier front_in_hull by (rule subset_trans)
      have out_in: "g ` ({0..1} - {a<..<b}) \<subseteq> convex hull path_image g"
      proof -
        have "g ` ({0..1} - {a<..<b}) \<subseteq> path_image g" by (auto simp: path_image_def)
        also have "path_image g \<subseteq> convex hull path_image g" by (rule hull_subset)
        finally show ?thesis .
      qed
      have hull_hh: "convex hull (path_image h) = convex hull (path_image g)"
      proof (rule subset_antisym)
        show "convex hull (path_image h) \<subseteq> convex hull (path_image g)"
          using pi_h seg_in out_in by (simp add: hull_minimal)
      next
        have "convex hull (path_image g) = convex hull (g ` ({0..1} - {a<..<b}))"
          using hull_eq by simp
        also have "\<dots> \<subseteq> convex hull (path_image h)"
          using pi_h by (simp add: hull_mono)
        finally show "convex hull (path_image g) \<subseteq> convex hull (path_image h)" .
      qed
      have L_nonneg: "0 \<le> L"
      proof -
        have le: "dist (g a) (g b) \<le> L * dist a b" using assms(3) ab01 by blast
        have pos: "0 < dist a b" using \<open>a < b\<close> by simp
        have "0 \<le> dist (g a) (g b)" by simp
        with le have "0 \<le> L * dist a b" by linarith
        with pos show ?thesis by (simp add: zero_le_mult_iff)
      qed
      have dab: "dist (g a) (g b) \<le> L * (b - a)"
      proof -
        have "dist (g a) (g b) \<le> L * dist a b" using assms(3) ab01 by blast
        also have "dist a b = b - a" using \<open>a < b\<close> by (simp add: dist_real_def)
        finally show ?thesis .
      qed
      have lip_mid: "L-lipschitz_on {a..b} h"
      proof (rule lipschitz_onI)
        show "0 \<le> L" by (rule L_nonneg)
        fix x y assume xy: "x \<in> {a..b}" "y \<in> {a..b}"
        have hx: "h x = g a + ((x - a)/(b - a)) *\<^sub>R (g b - g a)" using hh_eq_lin xy(1) .
        have hy: "h y = g a + ((y - a)/(b - a)) *\<^sub>R (g b - g a)" using hh_eq_lin xy(2) .
        have factor: "h x - h y = ((x - a)/(b - a) - (y - a)/(b - a)) *\<^sub>R (g b - g a)"
          by (simp add: hx hy scaleR_left_diff_distrib)
        have e1: "dist (h x) (h y) = \<bar>(x - a)/(b - a) - (y - a)/(b - a)\<bar> * norm (g b - g a)"
          by (simp add: dist_norm factor)
        have diff_eq: "(x - a)/(b - a) - (y - a)/(b - a) = (x - y)/(b - a)"
          by (simp add: diff_divide_distrib)
        have e2: "\<bar>(x - a)/(b - a) - (y - a)/(b - a)\<bar> = \<bar>x - y\<bar> / (b - a)"
          using \<open>a < b\<close> by (simp add: diff_eq abs_divide)
        have e3: "norm (g b - g a) / (b - a) \<le> L"
        proof -
          have "norm (g b - g a) = dist (g a) (g b)" by (simp add: dist_norm norm_minus_commute)
          then show ?thesis using dab \<open>a < b\<close> by (simp add: divide_le_eq)
        qed
        have "dist (h x) (h y) = (norm (g b - g a) / (b - a)) * \<bar>x - y\<bar>"
          using e1 e2 by simp
        also have "\<dots> \<le> L * \<bar>x - y\<bar>"
          using mult_right_mono[OF e3 abs_ge_zero] by simp
        finally show "dist (h x) (h y) \<le> L * dist x y" by (simp add: dist_real_def)
      qed
      have lip_g: "L-lipschitz_on {0..1} g"
        by (rule lipschitz_onI[OF _ L_nonneg]) (rule assms(3))
      have hh_lo: "\<And>x. x \<in> {0..a} \<Longrightarrow> h x = g x"
        by (auto simp: h_def)
      have hh_hi: "\<And>x. x \<in> {b..1} \<Longrightarrow> h x = g x"
        using \<open>a < b\<close> by (auto simp: h_def)
      have lip_lo: "L-lipschitz_on {0..a} h"
      proof -
        have "{0..a} \<subseteq> {0..1}" using a_ge0 b_le1 \<open>a<b\<close> by auto
        then have "L-lipschitz_on {0..a} g" using lip_g lipschitz_on_subset by blast
        then show ?thesis by (rule lipschitz_on_transform) (simp add: hh_lo)
      qed
      have lip_hi: "L-lipschitz_on {b..1} h"
      proof -
        have "{b..1} \<subseteq> {0..1}" using a_ge0 b_le1 \<open>a<b\<close> by auto
        then have "L-lipschitz_on {b..1} g" using lip_g lipschitz_on_subset by blast
        then show ?thesis by (rule lipschitz_on_transform) (simp add: hh_hi)
      qed
      have lip_lomid: "L-lipschitz_on {0..b} h"
      proof -
        have "L-lipschitz_on {0..b} (\<lambda>x. if x \<le> a then h x else h x)"
          using lip_lo lip_mid by (rule lipschitz_on_concat) simp
        then show ?thesis by simp
      qed
      have lip_hh: "L-lipschitz_on {0..1} h"
      proof -
        have "L-lipschitz_on {0..1} (\<lambda>x. if x \<le> b then h x else h x)"
          using lip_lomid lip_hi by (rule lipschitz_on_concat) simp
        then show ?thesis by simp
      qed
      have path_hh: "path h"
        using lip_hh by (simp add: path_def lipschitz_on_continuous_on)
      have g1_img: "g ` ({0..1} - {a<..<b}) = path_image g1" using arcs(8) by simp
      have opse_in_d0: "open_segment (g a) (g b) \<subseteq> path_image d0"
        using d0_eq_seg by (simp add: open_segment_def)
      have opse_g1_disj: "open_segment (g a) (g b) \<inter> path_image g1 = {}"
      proof -
        have "open_segment (g a) (g b) \<inter> {g b, g a} = {}"
          by (simp add: open_segment_def)
        moreover have "(path_image g1 - {g b, g a}) \<inter> path_image d0 = {}" using d_split(11) .
        ultimately show ?thesis using opse_in_d0 by blast
      qed
      have hh_in_opse: "\<And>x. x \<in> {a<..<b} \<Longrightarrow> h x \<in> open_segment (g a) (g b)"
      proof -
        fix x assume x: "x \<in> {a<..<b}"
        have "(x - a)/(b - a) \<in> {0<..<1}"
          using x \<open>a < b\<close> by (auto simp: divide_simps)
        then have "g a + ((x-a)/(b-a)) *\<^sub>R (g b - g a) \<in> open_segment (g a) (g b)"
          using ga_ne_gb by (auto simp: in_segment algebra_simps)
        then show "h x \<in> open_segment (g a) (g b)" using x by (simp add: h_def)
      qed
      have hh_inj_mid: "\<And>x y. x \<in> {a<..<b} \<Longrightarrow> y \<in> {a<..<b} \<Longrightarrow> h x = h y \<Longrightarrow> x = y"
      proof -
        fix x y assume x: "x \<in> {a<..<b}" and y: "y \<in> {a<..<b}" and eq: "h x = h y"
        have "g a + ((x-a)/(b-a)) *\<^sub>R (g b - g a) = g a + ((y-a)/(b-a)) *\<^sub>R (g b - g a)"
          using eq x y by (simp add: h_def)
        then have "((x-a)/(b-a)) *\<^sub>R (g b - g a) = ((y-a)/(b-a)) *\<^sub>R (g b - g a)" by simp
        then have eqfrac: "(x-a)/(b-a) = (y-a)/(b-a)"
          using ga_ne_gb by (simp add: real_vector.scale_right_imp_eq)
        show "x = y" using eqfrac \<open>a < b\<close> by (simp add: divide_cancel_right)
      qed
      have g_loop_free: "loop_free g" using assms(1) by (simp add: simple_path_def)
      have hh_out_g: "\<And>x. x \<notin> {a<..<b} \<Longrightarrow> h x = g x" unfolding h_def by presburger
      have hh_out_in_g1: "\<And>x. x \<in> {0..1} \<Longrightarrow> x \<notin> {a<..<b} \<Longrightarrow> h x \<in> path_image g1"
        using hh_out_g g1_img by blast
      have gloopD: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> g x = g y \<Longrightarrow> x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
        using g_loop_free unfolding loop_free_def by blast
      have testM1: "\<And>x y. x \<in> {a<..<b} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> y \<notin> {a<..<b} \<Longrightarrow> h x = h y \<Longrightarrow> False"
      proof -
        fix x y assume xb: "x \<in> {a<..<b}" and y01: "y \<in> {0..1}" and yo: "y \<notin> {a<..<b}" and eq: "h x = h y"
        have "h x \<in> open_segment (g a) (g b)" using hh_in_opse xb .
        then have "h y \<in> open_segment (g a) (g b)" using eq by simp
        moreover have "h y \<in> path_image g1" using hh_out_in_g1 y01 yo .
        ultimately have "h y \<in> open_segment (g a) (g b) \<inter> path_image g1" by simp
        then show False using opse_g1_disj by simp
      qed
      have loopfree_hh: "loop_free h"
        unfolding loop_free_def
      proof (intro ballI impI)
        fix x y assume x: "x \<in> {0..1}" and y: "y \<in> {0..1}" and eq: "h x = h y"
        consider (II) "x \<in> {a<..<b}" "y \<in> {a<..<b}"
          | (OO) "x \<notin> {a<..<b}" "y \<notin> {a<..<b}"
          | (M1) "x \<in> {a<..<b}" "y \<notin> {a<..<b}"
          | (M2) "x \<notin> {a<..<b}" "y \<in> {a<..<b}"
          by blast
        then show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
        proof cases
          case II
          then show ?thesis using hh_inj_mid eq by blast
        next
          case OO
          then have "g x = g y" using eq hh_out_g by simp
          then show ?thesis using gloopD x y by blast
        next
          case M1
          then have False using testM1 x y eq by blast
          then show ?thesis ..
        next
          case M2
          then have False using testM1[of y x] x y eq by simp
          then show ?thesis ..
        qed
      qed
      have simple_hh: "simple_path h"
        using path_hh loopfree_hh by (simp add: simple_path_def)
      have lip_imp_bv: "\<And>(f::real\<Rightarrow>complex) M c d. M-lipschitz_on {c..d} f \<Longrightarrow> has_bounded_variation_on f {c..d}"
      proof -
        fix f :: "real \<Rightarrow> complex" and M c d assume lip: "M-lipschitz_on {c..d} f"
        show "has_bounded_variation_on f {c..d}"
          unfolding has_bounded_variation_on_interval
        proof (intro exI[where x="max 0 (M * (d - c))"] allI impI)
          fix D assume D: "D division_of {c..d}"
          have Mnn: "0 \<le> M" using lip by (simp add: lipschitz_on_nonneg)
          have elem: "\<And>k. k \<in> D \<Longrightarrow> norm (f (Sup k) - f (Inf k)) \<le> M * content k"
          proof -
            fix k assume k: "k \<in> D"
            obtain a' b' where ab': "k = cbox a' b'" using division_ofD(4)[OF D k] by blast
            have ksub: "k \<subseteq> {c..d}" using division_ofD(2)[OF D k] by simp
            have kne: "k \<noteq> {}" using division_ofD(3)[OF D k] by simp
            then have leab: "a' \<le> b'" using ab' by (simp add: box_ne_empty)
            have infk: "Inf k = a'" and supk: "Sup k = b'" using ab' leab by auto
            have mem: "a' \<in> {c..d}" "b' \<in> {c..d}" using ksub ab' leab by auto
            have "norm (f b' - f a') = dist (f b') (f a')" by (simp add: dist_norm)
            also have "\<dots> \<le> M * dist b' a'" using lipschitz_onD[OF lip] mem by simp
            also have "dist b' a' = b' - a'" using leab by (simp add: dist_real_def)
            also have "M * (b' - a') = M * content k" using ab' leab by (simp add: content_real)
            finally show "norm (f (Sup k) - f (Inf k)) \<le> M * content k" using infk supk by simp
          qed
          have "(\<Sum>k\<in>D. norm (f (Sup k) - f (Inf k))) \<le> (\<Sum>k\<in>D. M * content k)"
            by (rule sum_mono) (rule elem)
          also have "\<dots> = M * (\<Sum>k\<in>D. content k)" by (simp add: sum_distrib_left)
          also have "(\<Sum>k\<in>D. content k) = content {c..d}"
            using additive_content_division[OF D[unfolded box_real(2)[symmetric]]] by (simp add: box_real(2))
          also have "M * content {c..d} \<le> max 0 (M * (d - c))"
            using Mnn by (simp add: content_real_if)
          finally show "(\<Sum>k\<in>D. norm (f (Sup k) - f (Inf k))) \<le> max 0 (M * (d - c))" .
        qed
      qed
      have bv_hh: "has_bounded_variation_on h {0..1}" using lip_imp_bv[OF lip_hh] .
      have bv_g: "has_bounded_variation_on g {0..1}" using lip_imp_bv[OF lip_g] .
      have bv_hh_ab: "has_bounded_variation_on h {a..b}"
        using bv_hh has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff dual_order.refl)
      have bv_g_ab: "has_bounded_variation_on g {a..b}"
        using bv_g has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff dual_order.refl)
      have a01: "a \<in> {0..1}" and b01: "b \<in> {0..1}" using ab01 by auto
      have bv_hh_a1: "has_bounded_variation_on h {a..1}"
        using bv_hh has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff order_refl)
      have bv_g_a1: "has_bounded_variation_on g {a..1}"
        using bv_g has_bounded_variation_on_subset a_ge0 b_le1 \<open>a<b\<close> by (meson atLeastatMost_subset_iff order_refl)
      have split_hh: "vector_variation {0..1} h = vector_variation {0..a} h + vector_variation {a..b} h + vector_variation {b..1} h"
      proof -
        have "vector_variation {0..1} h = vector_variation {0..a} h + vector_variation {a..1} h"
          using vector_variation_combine[OF bv_hh a01] .
        moreover have "vector_variation {a..1} h = vector_variation {a..b} h + vector_variation {b..1} h"
          using vector_variation_combine[OF bv_hh_a1, of b] \<open>a<b\<close> b_le1 by simp
        ultimately show ?thesis by simp
      qed
      have split_g: "vector_variation {0..1} g = vector_variation {0..a} g + vector_variation {a..b} g + vector_variation {b..1} g"
      proof -
        have "vector_variation {0..1} g = vector_variation {0..a} g + vector_variation {a..1} g"
          using vector_variation_combine[OF bv_g a01] .
        moreover have "vector_variation {a..1} g = vector_variation {a..b} g + vector_variation {b..1} g"
          using vector_variation_combine[OF bv_g_a1, of b] \<open>a<b\<close> b_le1 by simp
        ultimately show ?thesis by simp
      qed
      have lo_eq: "vector_variation {0..a} h = vector_variation {0..a} g"
        by (rule vector_variation_cong) (simp add: hh_lo)
      have hi_eq: "vector_variation {b..1} h = vector_variation {b..1} g"
        by (rule vector_variation_cong) (simp add: hh_hi)
      have hh_a: "h a = g a" using \<open>a<b\<close> by (simp add: h_def)
      have hh_b: "h b = g b" using \<open>a<b\<close> by (simp add: h_def)
      have mid_hh_ge: "vector_variation {a..b} h \<ge> norm (g b - g a)"
      proof -
        have "norm (h b - h a) \<le> vector_variation {a..b} h"
          using vector_variation_ge_norm_function[OF bv_hh_ab, of b a] \<open>a<b\<close> by simp
        then show ?thesis using hh_a hh_b by (simp add: norm_minus_commute)
      qed
      have mid_hh_le: "vector_variation {a..b} h \<le> norm (g b - g a)"
      proof -
        have key: "\<And>D. D division_of {a..b} \<Longrightarrow> (\<Sum>k\<in>D. norm (h (Sup k) - h (Inf k))) \<le> norm (g b - g a)"
        proof -
          fix D assume D: "D division_of {a..b}"
          have elem: "\<And>k. k \<in> D \<Longrightarrow> norm (h (Sup k) - h (Inf k)) = ((Sup k - Inf k)/(b-a)) * norm (g b - g a)"
          proof -
            fix k assume k: "k \<in> D"
            obtain a' b' where ab': "k = cbox a' b'" using division_ofD(4)[OF D k] by blast
            have ksub: "k \<subseteq> {a..b}" using division_ofD(2)[OF D k] by simp
            have kne: "k \<noteq> {}" using division_ofD(3)[OF D k] by simp
            then have leab: "a' \<le> b'" using ab' by (simp add: box_ne_empty)
            have infk: "Inf k = a'" and supk: "Sup k = b'" using ab' leab by auto
            have mem: "a' \<in> {a..b}" "b' \<in> {a..b}" using ksub ab' leab by auto
            have ha: "h a' = g a + ((a'-a)/(b-a)) *\<^sub>R (g b - g a)" using hh_eq_lin mem(1) .
            have hb: "h b' = g a + ((b'-a)/(b-a)) *\<^sub>R (g b - g a)" using hh_eq_lin mem(2) .
            have "h b' - h a' = (((b'-a)/(b-a)) - ((a'-a)/(b-a))) *\<^sub>R (g b - g a)"
              by (simp add: ha hb scaleR_left_diff_distrib)
            also have "((b'-a)/(b-a)) - ((a'-a)/(b-a)) = (b'-a')/(b-a)"
              by (simp add: diff_divide_distrib)
            finally have "h b' - h a' = ((b'-a')/(b-a)) *\<^sub>R (g b - g a)" by simp
            then have "norm (h b' - h a') = \<bar>(b'-a')/(b-a)\<bar> * norm (g b - g a)" by simp
            also have "\<bar>(b'-a')/(b-a)\<bar> = (b'-a')/(b-a)" using leab \<open>a<b\<close> by simp
            finally show "norm (h (Sup k) - h (Inf k)) = ((Sup k - Inf k)/(b-a)) * norm (g b - g a)"
              using infk supk by simp
          qed
          have content_elem: "\<And>k. k \<in> D \<Longrightarrow> (Sup k - Inf k) = content k"
          proof -
            fix k assume k: "k \<in> D"
            obtain a' b' where ab': "k = cbox a' b'" using division_ofD(4)[OF D k] by blast
            have kne: "k \<noteq> {}" using division_ofD(3)[OF D k] by simp
            then have leab: "a' \<le> b'" using ab' by (simp add: box_ne_empty)
            then show "(Sup k - Inf k) = content k" using ab' by (simp add: content_real)
          qed
          have "(\<Sum>k\<in>D. norm (h (Sup k) - h (Inf k))) = (\<Sum>k\<in>D. ((Sup k - Inf k)/(b-a)) * norm (g b - g a))"
            by (rule sum.cong[OF refl]) (rule elem)
          also have "\<dots> = ((\<Sum>k\<in>D. (Sup k - Inf k))/(b-a)) * norm (g b - g a)"
            by (simp add: sum_distrib_right sum_divide_distrib)
          also have "(\<Sum>k\<in>D. (Sup k - Inf k)) = (\<Sum>k\<in>D. content k)"
            by (rule sum.cong[OF refl]) (rule content_elem)
          also have "(\<Sum>k\<in>D. content k) = content {a..b}"
            using additive_content_division[OF D[unfolded box_real(2)[symmetric]]] by (simp add: box_real(2))
          also have "content {a..b} = b - a" using \<open>a<b\<close> by (simp add: content_real)
          also have "((b-a)/(b-a)) * norm (g b - g a) = norm (g b - g a)" using \<open>a<b\<close> by simp
          finally show "(\<Sum>k\<in>D. norm (h (Sup k) - h (Inf k))) \<le> norm (g b - g a)" by simp
        qed
        show ?thesis
          using bv_hh_ab key has_bounded_vector_variation_on_interval by blast
      qed
      have mid_hh_eq: "vector_variation {a..b} h = norm (g b - g a)"
        using mid_hh_ge mid_hh_le by simp
      define c where "c = (a + b)/2"
      have c_mem: "c \<in> {a<..<b}" using \<open>a<b\<close> by (simp add: c_def)
      have ac: "a < c" and cb: "c < b" using c_mem by auto
      have gc_not_seg: "g c \<notin> closed_segment (g a) (g b)"
      proof
        assume "g c \<in> closed_segment (g a) (g b)"
        then have "g c \<in> frontier (convex hull path_image g)" using seg_in_frontier by blast
        moreover have "g c \<in> g ` {a<..<b}" using c_mem by blast
        ultimately show False using assms(9) by blast
      qed
      have strict_tri: "dist (g a) (g b) < dist (g a) (g c) + dist (g c) (g b)"
      proof -
        have "\<not> between (g a, g b) (g c)" using gc_not_seg by (simp add: between_mem_segment)
        then have "dist (g a) (g c) + dist (g c) (g b) \<noteq> dist (g a) (g b)"
          by (simp add: between)
        moreover have "dist (g a) (g b) \<le> dist (g a) (g c) + dist (g c) (g b)"
          by (rule dist_triangle)
        ultimately show ?thesis by linarith
      qed
      have c_in_ab: "c \<in> {a..b}" using ac cb by simp
      have bv_g_ac: "has_bounded_variation_on g {a..c}"
        using bv_g_ab has_bounded_variation_on_subset ac cb by (meson atLeastatMost_subset_iff order_refl less_imp_le)
      have bv_g_cb: "has_bounded_variation_on g {c..b}"
        using bv_g_ab has_bounded_variation_on_subset ac cb by (meson atLeastatMost_subset_iff order_refl less_imp_le)
      have mid_g_gt: "vector_variation {a..b} g > norm (g b - g a)"
      proof -
        have split: "vector_variation {a..b} g = vector_variation {a..c} g + vector_variation {c..b} g"
          using vector_variation_combine[OF bv_g_ab c_in_ab] .
        have ge1: "norm (g c - g a) \<le> vector_variation {a..c} g"
          using vector_variation_ge_norm_function[OF bv_g_ac, of c a] ac cb by (simp add: norm_minus_commute)
        have ge2: "norm (g b - g c) \<le> vector_variation {c..b} g"
          using vector_variation_ge_norm_function[OF bv_g_cb, of b c] ac cb by (simp add: norm_minus_commute)
        have "norm (g b - g a) < norm (g c - g a) + norm (g b - g c)"
          using strict_tri by (simp add: dist_norm norm_minus_commute)
        also have "\<dots> \<le> vector_variation {a..c} g + vector_variation {c..b} g"
          using ge1 ge2 by simp
        also have "\<dots> = vector_variation {a..b} g" using split by simp
        finally show ?thesis .
      qed
      have path_length_lt: "path_length h < path_length g"
      proof -
        have "path_length h = vector_variation {0..a} g + vector_variation {a..b} h + vector_variation {b..1} g"
          using split_hh lo_eq hi_eq by (simp add: path_length_def)
        also have "vector_variation {a..b} h = norm (g b - g a)" using mid_hh_eq .
        finally have hh_val: "path_length h = vector_variation {0..a} g + norm (g b - g a) + vector_variation {b..1} g" .
        have "path_length g = vector_variation {0..a} g + vector_variation {a..b} g + vector_variation {b..1} g"
          using split_g by (simp add: path_length_def)
        with hh_val mid_g_gt show ?thesis by simp
      qed
      have lip_show: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
        using lipschitz_onD[OF lip_hh] .
      have hh_agree: "\<And>x. x \<notin> {a<..<b} \<Longrightarrow> h x = g x" using hh_out_g .
      show thesis
        using that[OF simple_hh hh_start hh_finish lip_show path_length_lt hull_hh hh_agree hh_frontier] .
    qed
  qed
qed

text \<open>A nonempty bounded open connected subset of the reals is an open interval.\<close>

lemma open_bounded_connected_real_is_interval:
  fixes c :: "real set"
  assumes "open c" "connected c" "c \<noteq> {}" "bounded c"
  shows "c = {Inf c<..<Sup c}"
proof -
  have isiv: "is_interval c" using assms(2) by (simp add: is_interval_connected_1)
  have bb: "bdd_below c" and ba: "bdd_above c" using assms(4) bounded_imp_bdd_below bounded_imp_bdd_above by auto
  have InfnotIn: "Inf c \<notin> c"
  proof
    assume "Inf c \<in> c"
    then obtain b where "b < Inf c" "{b<..Inf c} \<subseteq> c" using open_left[OF assms(1) \<open>Inf c \<in> c\<close>, of "Inf c - 1"] by auto
    then have "(Inf c + b)/2 \<in> c" by auto
    moreover have "(Inf c + b)/2 < Inf c" using \<open>b < Inf c\<close> by simp
    ultimately show False using bb cInf_lower leD by blast
  qed
  have SupnotIn: "Sup c \<notin> c"
  proof
    assume "Sup c \<in> c"
    then obtain b where "Sup c < b" "{Sup c..<b} \<subseteq> c" using open_right[OF assms(1) \<open>Sup c \<in> c\<close>, of "Sup c + 1"] by auto
    then have "(Sup c + b)/2 \<in> c" by auto
    moreover have "Sup c < (Sup c + b)/2" using \<open>Sup c < b\<close> by simp
    ultimately show False using ba cSup_upper leD by blast
  qed
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> c"
    then have "Inf c \<le> x" "x \<le> Sup c" using bb ba cInf_lower cSup_upper by auto
    moreover have "x \<noteq> Inf c" using \<open>x \<in> c\<close> InfnotIn by auto
    moreover have "x \<noteq> Sup c" using \<open>x \<in> c\<close> SupnotIn by auto
    ultimately show "x \<in> {Inf c<..<Sup c}" by auto
  next
    fix x assume x: "x \<in> {Inf c<..<Sup c}"
    obtain u where u: "u \<in> c" "u < x" using x assms(3) bb
      by (metis cInf_lessD greaterThanLessThan_iff)
    obtain v where v: "v \<in> c" "x < v" using x assms(3) ba
      by (metis less_cSupD greaterThanLessThan_iff)
    show "x \<in> c" using isiv u v by (meson is_interval_1 less_imp_le)
  qed
qed

text \<open>The reduced convexification subgoal: a unit-speed (Lipschitz) simple closed rectifiable loop
  starting on the frontier of its convex hull can be replaced by a no-longer loop with the same
  convex hull whose image IS that frontier. The components of the part of the parameter interval
  whose image avoids the frontier are countably many open intervals; this is captured by
  @{text decomp} (still to be proved), and the deviating arcs are then straightened via
  @{text step_lemma}.\<close>

lemma convexification_unit_speed:
  fixes \<gamma> :: "real \<Rightarrow> complex"
  assumes rect: "rectifiable_path \<gamma>" and simp: "simple_path \<gamma>" and loop: "pathfinish \<gamma> = pathstart \<gamma>"
    and frstart: "pathstart \<gamma> \<in> frontier (convex hull (path_image \<gamma>))"
    and lip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (\<gamma> x) (\<gamma> y) \<le> path_length \<gamma> * dist x y"
  shows "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length \<gamma> \<and> convex hull (path_image h) = convex hull (path_image \<gamma>) \<and> path_image h = frontier (convex hull (path_image \<gamma>))"
proof (cases "path_image \<gamma> \<subseteq> frontier (convex hull (path_image \<gamma>))")
  case True
  \<comment> \<open>Already on the frontier: @{term \<gamma>} itself works (its image equals the frontier).\<close>
  have "path_image \<gamma> = frontier (convex hull (path_image \<gamma>))"
    using frontier_convex_hull_subset_path_image[OF simp loop True] True by blast
  then show ?thesis using rect simp loop by (intro exI[of _ \<gamma>]) auto
next
  case False
  have path\<gamma>: "path \<gamma>" using simp by (rule simple_path_imp_path)
  define F where "F = frontier (convex hull (path_image \<gamma>))"
  define s where "s = {t \<in> {0..1}. \<gamma> t \<notin> F}"
  have clF: "closed F" unfolding F_def by simp
  have cont\<gamma>: "continuous_on {0..1} \<gamma>" using path\<gamma> by (simp add: path_def)
  have g0F: "\<gamma> 0 \<in> F" using frstart F_def by (simp add: pathstart_def)
  have g1F: "\<gamma> 1 \<in> F" using frstart loop F_def by (simp add: pathstart_def pathfinish_def)
  \<comment> \<open>Since both endpoints map into @{term F}, the deviating set @{term s} avoids $0$ and $1$, hence is open in $\mathbb{R}$.\<close>
  have s_sub: "s \<subseteq> {0<..<1}"
  proof
    fix t assume "t \<in> s"
    then have t01: "t \<in> {0..1}" and tnF: "\<gamma> t \<notin> F" unfolding s_def by auto
    have "t \<noteq> 0" using tnF g0F by auto
    moreover have "t \<noteq> 1" using tnF g1F by auto
    ultimately show "t \<in> {0<..<1}" using t01 by auto
  qed
  have s_openin: "openin (top_of_set {0..1}) s"
  proof -
    have "openin (top_of_set {0..1}) ({0..1} \<inter> \<gamma> -` (- F))"
      using cont\<gamma> clF by (intro continuous_openin_preimage_gen) auto
    moreover have "{0..1} \<inter> \<gamma> -` (- F) = s" unfolding s_def by auto
    ultimately show ?thesis by simp
  qed
  have opens: "open s"
  proof -
    have "openin (top_of_set {0<..<1}) s"
      using s_openin s_sub by (metis greaterThanLessThan_subseteq_atLeastAtMost_iff openin_subset_trans order_refl zero_le_one)
    then show ?thesis by (metis open_greaterThanLessThan openin_open_trans)
  qed
  have s_ne: "s \<noteq> {}"
  proof -
    from False obtain z where "z \<in> path_image \<gamma>" "z \<notin> F" unfolding F_def by blast
    then obtain t where "t \<in> {0..1}" "\<gamma> t = z" by (auto simp: path_image_def)
    then have "t \<in> s" using \<open>z \<notin> F\<close> unfolding s_def by auto
    then show ?thesis by auto
  qed
  \<comment> \<open>Component decomposition: the components of @{term s} are countably many open intervals
     \<open>{a n<..<b n}\<close>, each with both endpoints mapped by @{term \<gamma>} onto the frontier @{term F}.\<close>
  have decomp: "\<exists>a b::nat\<Rightarrow>real. (\<forall>n. a n \<in> {0..1}) \<and> (\<forall>n. b n \<in> {0..1}) \<and> (\<forall>n. a n \<le> b n) \<and> (\<forall>n. \<gamma> (a n) \<in> F) \<and> (\<forall>n. \<gamma> (b n) \<in> F) \<and> components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
  proof -
    have comp_open: "\<And>c. c \<in> components s \<Longrightarrow> open c" using opens by (rule open_components)
    have comp_disj: "disjoint (components s)"
      using pairwise_disjoint_components by (simp add: disjoint_def pairwise_def disjnt_def)
    have comp_count: "countable (components s)"
      using comp_open comp_disj by (rule countable_disjoint_open_subsets)
    have comp_ne: "components s \<noteq> {}" using s_ne by (simp add: components_eq_empty)
    define q where "q = from_nat_into (components s)"
    have q_range: "range q = components s"
      unfolding q_def using comp_ne comp_count by (rule range_from_nat_into)
    have q_comp: "\<And>n. q n \<in> components s" using q_range by auto
    have s_sub01: "s \<subseteq> {0..1}" using s_sub by auto
    have s_bdd: "bounded s" using s_sub01 bounded_closed_interval bounded_subset by blast
    have qsub: "\<And>n. q n \<subseteq> s" using q_comp in_components_subset by blast
    have q_interval: "\<And>n. q n = {Inf (q n)<..<Sup (q n)}"
    proof -
      fix n
      have o: "open (q n)" using q_comp comp_open by blast
      have c: "connected (q n)" using q_comp in_components_connected by blast
      have nem: "q n \<noteq> {}" using q_comp in_components_nonempty by blast
      have bd: "bounded (q n)" using qsub s_bdd bounded_subset by blast
      show "q n = {Inf (q n)<..<Sup (q n)}" using o c nem bd by (rule open_bounded_connected_real_is_interval)
    qed
    define a where "a = (\<lambda>n. Inf (q n))"
    define b where "b = (\<lambda>n. Sup (q n))"
    have qab: "\<And>n. q n = {a n<..<b n}" using q_interval by (simp add: a_def b_def)
    have ablt: "\<And>n. a n < b n"
    proof -
      fix n
      have "q n \<noteq> {}" using q_comp in_components_nonempty by blast
      then show "a n < b n" using qab by (metis greaterThanLessThan_empty_iff not_less)
    qed
    have clq: "\<And>n. closure (q n) = {a n..b n}" using qab ablt by (simp add: closure_greaterThanLessThan)
    have cls01: "closure s \<subseteq> {0..1}"
      using s_sub closure_mono[of s "{0<..<1}"] closure_greaterThanLessThan[of "0::real" 1] by simp
    have ab01: "\<And>n. a n \<in> {0..1} \<and> b n \<in> {0..1}"
    proof -
      fix n
      have "{a n..b n} = closure (q n)" using clq by simp
      also have "closure (q n) \<subseteq> closure s" using qsub by (simp add: closure_mono)
      also have "closure s \<subseteq> {0..1}" using cls01 by simp
      finally have sub: "{a n..b n} \<subseteq> {0..1}" .
      have "a n \<in> {a n..b n}" "b n \<in> {a n..b n}" using ablt[of n] by auto
      then show "a n \<in> {0..1} \<and> b n \<in> {0..1}" using sub by blast
    qed
    have a_notin: "\<And>n. a n \<notin> s"
    proof (rule ccontr)
      fix n assume "\<not> a n \<notin> s"
      then have ains: "a n \<in> s" by simp
      have qns: "q n \<subseteq> s" by (rule qsub)
      have sub: "{a n..<b n} \<subseteq> s"
      proof
        fix x assume "x \<in> {a n..<b n}"
        then have "x = a n \<or> x \<in> {a n<..<b n}" by auto
        then show "x \<in> s" using ains qns qab by auto
      qed
      moreover have "connected {a n..<b n}" by (rule connected_Ico)
      moreover have "{a n..<b n} \<noteq> {}" using ablt[of n] by auto
      moreover have "q n \<subseteq> {a n..<b n}" using qab by auto
      ultimately have "{a n..<b n} = q n"
        using q_comp[of n] in_components_maximal by blast
      then show False using ablt[of n] qab by (metis atLeastLessThan_iff greaterThanLessThan_iff less_irrefl order_refl)
    qed
    have b_notin: "\<And>n. b n \<notin> s"
    proof (rule ccontr)
      fix n assume "\<not> b n \<notin> s"
      then have bins: "b n \<in> s" by simp
      have qns: "q n \<subseteq> s" by (rule qsub)
      have sub: "{a n<..b n} \<subseteq> s"
      proof
        fix x assume "x \<in> {a n<..b n}"
        then have "x = b n \<or> x \<in> {a n<..<b n}" by auto
        then show "x \<in> s" using bins qns qab by auto
      qed
      moreover have "connected {a n<..b n}" by (rule connected_Ioc)
      moreover have "{a n<..b n} \<noteq> {}" using ablt[of n] by auto
      moreover have "q n \<subseteq> {a n<..b n}" using qab by auto
      ultimately have "{a n<..b n} = q n"
        using q_comp[of n] in_components_maximal by blast
      then show False using ablt[of n] qab by (metis greaterThanAtMost_iff greaterThanLessThan_iff less_irrefl order_refl)
    qed
    have gaF: "\<And>n. \<gamma> (a n) \<in> F"
    proof -
      fix n
      have "a n \<in> {0..1}" using ab01 by simp
      moreover have "a n \<notin> s" by (rule a_notin)
      ultimately show "\<gamma> (a n) \<in> F" unfolding s_def by auto
    qed
    have gbF: "\<And>n. \<gamma> (b n) \<in> F"
    proof -
      fix n
      have "b n \<in> {0..1}" using ab01 by simp
      moreover have "b n \<notin> s" by (rule b_notin)
      ultimately show "\<gamma> (b n) \<in> F" unfolding s_def by auto
    qed
    have comp_eq: "components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
    proof -
      have "components s = range q" using q_range by simp
      also have "\<dots> = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}" using qab by auto
      finally show ?thesis .
    qed
    show "\<exists>a b::nat\<Rightarrow>real. (\<forall>n. a n \<in> {0..1}) \<and> (\<forall>n. b n \<in> {0..1}) \<and> (\<forall>n. a n \<le> b n) \<and> (\<forall>n. \<gamma> (a n) \<in> F) \<and> (\<forall>n. \<gamma> (b n) \<in> F) \<and> components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
      using ab01 ablt gaF gbF comp_eq by (intro exI[of _ a] exI[of _ b]) (auto simp: less_imp_le)
  qed
  note [[quick_and_dirty]]
  \<comment> \<open>Extract the deviating arcs from the decomposition.\<close>
  from decomp obtain a b :: "nat \<Rightarrow> real" where
    ab01: "\<And>n. a n \<in> {0..1}" "\<And>n. b n \<in> {0..1}" and
    able: "\<And>n. a n \<le> b n" and
    gaF: "\<And>n. \<gamma> (a n) \<in> F" and gbF: "\<And>n. \<gamma> (b n) \<in> F" and
    comps: "components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}" by auto
  \<comment> \<open>@{term "U n"} collects the first @{term n} deviating arcs; @{term "P n h"} is the invariant for the @{term n}-th
     approximation: a Lipschitz simple closed loop with the same convex hull, mapping the
     first @{term n} arcs onto the frontier and equal to @{term \<gamma>} elsewhere.\<close>
  define U where "U = (\<lambda>n::nat. \<Union> {{a m<..<b m} | m. m < n})"
  define P where "P = (\<lambda>n h. simple_path h \<and> rectifiable_path h \<and> pathstart h = pathstart \<gamma> \<and> pathfinish h = pathfinish \<gamma> \<and> convex hull (path_image h) = convex hull (path_image \<gamma>) \<and> (\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. dist (h x) (h y) \<le> path_length \<gamma> * dist x y) \<and> (\<forall>x\<in>U n. h x \<in> F) \<and> (\<forall>x. x \<notin> U n \<longrightarrow> h x = \<gamma> x))"
  have U0: "U 0 = {}" by (simp add: U_def)
  have base: "P 0 \<gamma>"
    unfolding P_def using simp rect lip by (simp add: U0)
  have arc_comp: "\<And>n. {a n<..<b n} \<in> components s" using comps by auto
  have arc_in_s: "\<And>n. {a n<..<b n} \<subseteq> s" using arc_comp in_components_subset by blast
  have arc_off_F: "\<And>n x. x \<in> {a n<..<b n} \<Longrightarrow> \<gamma> x \<notin> F"
    using arc_in_s s_def by blast
  have USuc: "\<And>n. U (Suc n) = U n \<union> {a n<..<b n}"
    by (auto simp: U_def less_Suc_eq)
  have U_sub_s: "\<And>n. U n \<subseteq> s"
  proof -
    fix n
    show "U n \<subseteq> s"
    proof
      fix x assume "x \<in> U n"
      then obtain m where "m < n" "x \<in> {a m<..<b m}" by (auto simp: U_def)
      then show "x \<in> s" using arc_in_s by blast
    qed
  qed
  have an_notin_s: "\<And>n. a n \<notin> s" using gaF s_def by blast
  have bn_notin_s: "\<And>n. b n \<notin> s" using gbF s_def by blast
  have an_notin_U: "\<And>n. a n \<notin> U n" using an_notin_s U_sub_s by blast
  have bn_notin_U: "\<And>n. b n \<notin> U n" using bn_notin_s U_sub_s by blast
  have arc_sub_U: "\<And>i j::nat. i < j \<Longrightarrow> {a i<..<b i} \<subseteq> U j"
  proof -
    fix i j :: nat assume "i < j"
    then have "{a i<..<b i} \<in> {{a k<..<b k} | k. k < j}" by auto
    then show "{a i<..<b i} \<subseteq> U j" by (auto simp: U_def)
  qed
  have U_mem: "\<And>x n. x \<in> U n \<Longrightarrow> \<exists>i<n. x \<in> {a i<..<b i}"
  proof -
    fix x n assume "x \<in> U n"
    then show "\<exists>i<n. x \<in> {a i<..<b i}" unfolding U_def by blast
  qed
  have arc_disj: "\<And>i j. {a i<..<b i} \<noteq> {a j<..<b j} \<Longrightarrow> {a i<..<b i} \<inter> {a j<..<b j} = {}"
    using arc_comp components_nonoverlap by blast
  have arc_disj_U: "\<And>n. \<not> {a n<..<b n} \<subseteq> U n \<Longrightarrow> {a n<..<b n} \<inter> U n = {}"
  proof -
    fix n assume nsub: "\<not> {a n<..<b n} \<subseteq> U n"
    show "{a n<..<b n} \<inter> U n = {}"
    proof (rule ccontr)
      assume "{a n<..<b n} \<inter> U n \<noteq> {}"
      then obtain x where x: "x \<in> {a n<..<b n} \<inter> U n" by blast
      then have x1: "x \<in> {a n<..<b n}" and x2: "x \<in> U n" by auto
      from x2 obtain i where i: "i < n" "x \<in> {a i<..<b i}" using U_mem by blast
      have eq: "{a n<..<b n} = {a i<..<b i}" using x1 i(2) arc_disj by blast
      have "{a i<..<b i} \<subseteq> U n" using i(1) arc_sub_U by blast
      then show False using nsub eq by simp
    qed
  qed
  have F_eq: "F = frontier (convex hull (path_image \<gamma>))" by (simp add: F_def)
  \<comment> \<open>Inductive step: straighten the @{term n}-th arc with \<open>step_lemma\<close> (unless it is empty or already
     handled), preserving the invariant.\<close>
  have step: "\<And>n h. P n h \<Longrightarrow> \<exists>h'. P (Suc n) h' \<and> (\<forall>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<longrightarrow> h' x = h x)"
  proof -
    fix n h assume Ph: "P n h"
    have hsimple: "simple_path h" and hrect: "rectifiable_path h"
      and hps: "pathstart h = pathstart \<gamma>" and hpf: "pathfinish h = pathfinish \<gamma>"
      and hhull: "convex hull (path_image h) = convex hull (path_image \<gamma>)"
      and hlip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> path_length \<gamma> * dist x y"
      and hUF: "\<And>x. x \<in> U n \<Longrightarrow> h x \<in> F"
      and hoff: "\<And>x. x \<notin> U n \<Longrightarrow> h x = \<gamma> x"
      using Ph unfolding P_def by auto
    have hloop: "pathfinish h = pathstart h" using hps hpf loop by simp
    have hF: "frontier (convex hull (path_image h)) = F" using hhull F_eq by simp
    show "\<exists>h'. P (Suc n) h' \<and> (\<forall>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<longrightarrow> h' x = h x)"
    proof (cases "{a n<..<b n} = {} \<or> {a n<..<b n} \<subseteq> U n")
      case True
      then have "U (Suc n) = U n" using USuc by auto
      then have "P (Suc n) h" using Ph by (simp add: P_def)
      then show ?thesis by (intro exI[of _ h]) auto
    next
      case False
      then have ne: "{a n<..<b n} \<noteq> {}" and nsub: "\<not> {a n<..<b n} \<subseteq> U n" by auto
      have ablt_n: "a n < b n" using ne by simp
      have arc_disj_Un: "{a n<..<b n} \<inter> U n = {}" using nsub arc_disj_U by blast
      have ha: "h (a n) = \<gamma> (a n)" using hoff an_notin_U by simp
      have hb: "h (b n) = \<gamma> (b n)" using hoff bn_notin_U by simp
      have harc: "\<And>x. x \<in> {a n<..<b n} \<Longrightarrow> h x = \<gamma> x" using hoff arc_disj_Un by blast
      have haF: "h (a n) \<in> frontier (convex hull (path_image h))" using ha gaF hF by simp
      have hbF: "h (b n) \<in> frontier (convex hull (path_image h))" using hb gbF hF by simp
      have harc_offF: "h ` {a n<..<b n} \<inter> frontier (convex hull (path_image h)) = {}"
      proof -
        have "h ` {a n<..<b n} \<subseteq> {y. y \<notin> F}" using harc arc_off_F by auto
        then show ?thesis using hF by auto
      qed
      obtain h' where h'simple: "simple_path h'"
        and h'ps: "pathstart h' = pathstart h" and h'pf: "pathfinish h' = pathstart h"
        and h'lip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h' x) (h' y) \<le> path_length \<gamma> * dist x y"
        and h'len: "path_length h' < path_length h"
        and h'hull: "convex hull (path_image h') = convex hull (path_image h)"
        and h'off: "\<And>x. x \<notin> {a n<..<b n} \<Longrightarrow> h' x = h x"
        and h'arcF: "h' ` {a n..b n} \<subseteq> frontier (convex hull (path_image h))"
        using step_lemma[OF hsimple hloop hlip ablt_n ab01(1)[of n] ab01(2)[of n] haF hbF harc_offF]
        by metis
      have h'rect: "rectifiable_path h'"
        by (rule lipschitz_imp_rectifiable_path[where B="path_length \<gamma>"])
           (use h'lip in \<open>simp add: dist_norm\<close>)
      have h'agree: "\<And>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<Longrightarrow> h' x = h x"
      proof -
        fix x assume "\<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n)"
        then have "x \<notin> {a n<..<b n}" using arc_disj_Un by blast
        then show "h' x = h x" using h'off by simp
      qed
      have h'UF: "\<And>x. x \<in> U (Suc n) \<Longrightarrow> h' x \<in> F"
      proof -
        fix x assume "x \<in> U (Suc n)"
        then have "x \<in> U n \<or> x \<in> {a n<..<b n}" using USuc by auto
        then show "h' x \<in> F"
        proof
          assume xUn: "x \<in> U n"
          then have "x \<notin> {a n<..<b n}" using arc_disj_Un by blast
          then have "h' x = h x" using h'off by simp
          then show "h' x \<in> F" using xUn hUF by simp
        next
          assume "x \<in> {a n<..<b n}"
          then have "x \<in> {a n..b n}" by auto
          then have "h' x \<in> frontier (convex hull (path_image h))" using h'arcF by auto
          then show "h' x \<in> F" using hF by simp
        qed
      qed
      have h'offSuc: "\<And>x. x \<notin> U (Suc n) \<Longrightarrow> h' x = \<gamma> x"
      proof -
        fix x assume "x \<notin> U (Suc n)"
        then have xn: "x \<notin> U n" and xarc: "x \<notin> {a n<..<b n}" using USuc by auto
        have "h' x = h x" using xarc h'off by simp
        also have "h x = \<gamma> x" using xn hoff by simp
        finally show "h' x = \<gamma> x" .
      qed
      have PSuc: "P (Suc n) h'"
        unfolding P_def
        using h'simple h'rect h'ps hps h'pf loop h'hull hhull h'lip h'UF h'offSuc
        by simp
      show ?thesis using PSuc h'agree by blast
    qed
  qed
  \<comment> \<open>Dependent choice yields the sequence of approximations @{term f}.\<close>
  obtain f where f: "\<And>n. P n (f n)"
    and fstep: "\<And>n x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<Longrightarrow> f (Suc n) x = f n x"
    using dependent_nat_choice[where P=P and Q="\<lambda>n h h'. \<forall>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<longrightarrow> h' x = h x"]
      base step by metis
  \<comment> \<open>For each parameter @{term x} the sequence @{term "f n x"} is eventually constant: either @{term x} lies in no arc
     (so $f\,n\,x = \gamma\,x$ throughout), or it lies in the arc with least index @{term N}, after which @{term f} is fixed.\<close>
  have evconst: "\<forall>x\<in>{0..1}. \<exists>y. eventually (\<lambda>n. f n x = y) sequentially"
  proof
    fix x :: real assume x01: "x \<in> {0..1}"
    show "\<exists>y. eventually (\<lambda>n. f n x = y) sequentially"
    proof (cases "\<exists>n. x \<in> {a n<..<b n}")
      case False
      have stab: "f n x = f 0 x" for n
      proof (induct n)
        case 0 show ?case by simp
      next
        case (Suc n)
        have "f (Suc n) x = f n x" using fstep False by blast
        then show ?case using Suc by simp
      qed
      then have "eventually (\<lambda>n. f n x = f 0 x) sequentially" by simp
      then show ?thesis by blast
    next
      case True
      define N where "N = (LEAST n. x \<in> {a n<..<b n})"
      have xN: "x \<in> {a N<..<b N}" using True LeastI_ex N_def by (metis (mono_tags, lifting))
      have stab2: "\<And>m. N < m \<Longrightarrow> f (Suc m) x = f m x"
      proof -
        fix m assume Nm: "N < m"
        have "x \<in> U m" using Nm xN arc_sub_U by blast
        then have "\<not>(x \<in> {a m<..<b m} \<and> x \<notin> U m)" by simp
        then show "f (Suc m) x = f m x" using fstep by blast
      qed
      have stab3: "\<And>d. f (Suc N + d) x = f (Suc N) x"
      proof -
        fix d show "f (Suc N + d) x = f (Suc N) x"
        proof (induct d)
          case 0 show ?case by simp
        next
          case (Suc d)
          have "f (Suc (Suc N + d)) x = f (Suc N + d) x" using stab2 by simp
          then show ?case using Suc by simp
        qed
      qed
      have "eventually (\<lambda>n. f n x = f (Suc N) x) sequentially"
      proof (rule eventually_sequentiallyI[where c="Suc N"])
        fix n assume "Suc N \<le> n"
        then obtain d where "n = Suc N + d" using le_Suc_ex by blast
        then show "f n x = f (Suc N) x" using stab3 by simp
      qed
      then show ?thesis by blast
    qed
  qed
  \<comment> \<open>Skolemize to obtain the limit path @{term h}: $f\,n\,x = h\,x$ eventually, for each @{term x}.\<close>
  obtain h where h: "\<And>x. x \<in> {0..1} \<Longrightarrow> eventually (\<lambda>n. f n x = h x) sequentially"
    using evconst by (metis (mono_tags))
  \<comment> \<open>Properties of the approximants @{term "f n"}, extracted from the invariant @{term P}.\<close>
  have fsimple: "\<And>n. simple_path (f n)" using f unfolding P_def by blast
  have fps: "\<And>n. pathstart (f n) = pathstart \<gamma>" using f unfolding P_def by blast
  have fpf: "\<And>n. pathfinish (f n) = pathfinish \<gamma>" using f unfolding P_def by blast
  have fhull: "\<And>n. convex hull (path_image (f n)) = convex hull (path_image \<gamma>)" using f unfolding P_def by blast
  have flip: "\<And>n x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (f n x) (f n y) \<le> path_length \<gamma> * dist x y"
    using f unfolding P_def by blast
  have fUF: "\<And>n x. x \<in> U n \<Longrightarrow> f n x \<in> F" using f unfolding P_def by blast
  have foff: "\<And>n x. x \<notin> U n \<Longrightarrow> f n x = \<gamma> x" using f unfolding P_def by blast
  \<comment> \<open>The limit path @{term h} inherits the $L$-Lipschitz bound (pointwise limit of $L$-Lipschitz maps).\<close>
  have hlip: "\<And>x y::real. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> path_length \<gamma> * dist x y"
  proof -
    fix x y :: real assume xy: "x \<in> {0..1}" "y \<in> {0..1}"
    have ev: "eventually (\<lambda>n. f n x = h x \<and> f n y = h y) sequentially"
      using h[OF xy(1)] h[OF xy(2)] by eventually_elim simp
    then obtain n where n: "f n x = h x" "f n y = h y"
      unfolding eventually_sequentially by auto
    have "dist (f n x) (f n y) \<le> path_length \<gamma> * dist x y" using flip[OF xy] by blast
    then show "dist (h x) (h y) \<le> path_length \<gamma> * dist x y" using n by simp
  qed
  have hrect: "rectifiable_path h"
    by (rule lipschitz_imp_rectifiable_path[where B="path_length \<gamma>"])
       (use hlip in \<open>simp add: dist_norm\<close>)
  have hpath: "path h" using hrect by (rule rectifiable_path_imp_path)
  have hsimple: "simple_path h"
    unfolding simple_path_def
  proof (intro conjI)
    show "path h" by (rule hpath)
    show "loop_free h"
      unfolding loop_free_def
    proof (intro ballI impI)
      fix x y :: real assume xy: "x \<in> {0..1}" "y \<in> {0..1}" and eq: "h x = h y"
      have ev: "eventually (\<lambda>n. f n x = h x \<and> f n y = h y) sequentially"
        using h[OF xy(1)] h[OF xy(2)] by eventually_elim simp
      then obtain n where n: "f n x = h x" "f n y = h y"
        unfolding eventually_sequentially by auto
      have "f n x = f n y" using n eq by simp
      then show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
        using fsimple[of n] xy unfolding simple_path_def loop_free_def by blast
    qed
  qed
  have hloop: "pathfinish h = pathstart h"
  proof -
    have z01: "(0::real) \<in> {0..1}" and o01: "(1::real) \<in> {0..1}" by auto
    have ev: "eventually (\<lambda>n. f n 0 = h 0 \<and> f n 1 = h 1) sequentially"
      using h[OF z01] h[OF o01] by eventually_elim simp
    then obtain n where n: "f n 0 = h 0" "f n 1 = h 1"
      unfolding eventually_sequentially by auto
    have "f n 1 = f n 0" using fps[of n] fpf[of n] loop by (simp add: pathstart_def pathfinish_def)
    then have "h 1 = h 0" using n by simp
    then show ?thesis by (simp add: pathstart_def pathfinish_def)
  qed
  have hlen: "path_length h \<le> path_length \<gamma>"
    by (rule path_length_lipschitz[where B="path_length \<gamma>"])
       (use hlip in \<open>simp add: dist_norm\<close>)
  \<comment> \<open>The image of @{term h} lies on the frontier: each parameter either lands in an arc (so eventually
     in @{term F}) or maps via @{term \<gamma>} to a point already on the frontier.\<close>
  have notarc_notin_s: "\<And>x. (\<nexists>n. x \<in> {a n<..<b n}) \<Longrightarrow> x \<notin> s"
  proof -
    fix x assume noarc: "\<nexists>n. x \<in> {a n<..<b n}"
    show "x \<notin> s"
    proof
      assume "x \<in> s"
      then have "x \<in> \<Union>(components s)" by (simp add: Union_components)
      then obtain c where "c \<in> components s" "x \<in> c" by blast
      then obtain n where "c = {a n<..<b n}" using comps by auto
      then show False using noarc \<open>x \<in> c\<close> by blast
    qed
  qed
  have hx_in_F: "\<And>x. x \<in> {0..1} \<Longrightarrow> h x \<in> F"
  proof -
    fix x :: real assume x01: "x \<in> {0..1}"
    show "h x \<in> F"
    proof (cases "\<exists>n. x \<in> {a n<..<b n}")
      case True
      then obtain n where xn: "x \<in> {a n<..<b n}" by blast
      obtain N where N: "\<And>m. N \<le> m \<Longrightarrow> f m x = h x" using h[OF x01] unfolding eventually_sequentially by blast
      define m where "m = max N (Suc n)"
      have "N \<le> m" "n < m" by (auto simp: m_def)
      have "x \<in> U m" using xn arc_sub_U \<open>n < m\<close> by blast
      then have "f m x \<in> F" using fUF by blast
      then show "h x \<in> F" using N \<open>N \<le> m\<close> by simp
    next
      case False
      obtain n where n: "f n x = h x" using h[OF x01] unfolding eventually_sequentially by blast
      have "x \<notin> U n" using False U_mem by blast
      then have "f n x = \<gamma> x" using foff by blast
      moreover have "x \<notin> s" using False notarc_notin_s by blast
      then have "\<gamma> x \<in> F" using x01 s_def by blast
      ultimately show "h x \<in> F" using n by simp
    qed
  qed
  have hsub_F: "path_image h \<subseteq> F" using hx_in_F by (auto simp: path_image_def)
  \<comment> \<open>Off the arcs, @{term h} still agrees with @{term \<gamma>}; so @{term \<gamma>}'s image outside the deviating set @{term s} is part of
     the image of @{term h}.\<close>
  have arcs_eq_s: "\<Union> {{a n<..<b n} | n. n \<in> (UNIV::nat set)} = s"
    using comps Union_components by metis
  have hoff_s: "\<And>x. x \<in> {0..1} \<Longrightarrow> x \<notin> s \<Longrightarrow> h x = \<gamma> x"
  proof -
    fix x :: real assume x01: "x \<in> {0..1}" and xs: "x \<notin> s"
    have noarc: "\<nexists>n. x \<in> {a n<..<b n}" using xs arcs_eq_s by blast
    obtain n where n: "f n x = h x" using h[OF x01] unfolding eventually_sequentially by blast
    have "x \<notin> U n" using noarc U_mem by blast
    then have "f n x = \<gamma> x" using foff by blast
    then show "h x = \<gamma> x" using n by simp
  qed
  have gout_sub_h: "\<gamma> ` ({0..1} - s) \<subseteq> path_image h"
  proof
    fix z assume "z \<in> \<gamma> ` ({0..1} - s)"
    then obtain x where x: "x \<in> {0..1}" "x \<notin> s" "z = \<gamma> x" by auto
    then have "z = h x" using hoff_s by simp
    then show "z \<in> path_image h" using x(1) by (auto simp: path_image_def)
  qed
  \<comment> \<open>The convex hulls agree.\<close>
  have hhull: "convex hull (path_image h) = convex hull (path_image \<gamma>)"
  proof (rule subset_antisym)
    \<comment> \<open>$\subseteq$: every point $h\,x = f\,n\,x$ for some @{term n} lies in @{term "convex hull (path_image (f n))"} $=$ @{term "convex hull (path_image \<gamma>)"}.\<close>
    have ph_sub: "path_image h \<subseteq> convex hull (path_image \<gamma>)"
    proof
      fix z assume "z \<in> path_image h"
      then obtain x where x: "x \<in> {0..1}" "z = h x" by (auto simp: path_image_def)
      obtain n where n: "f n x = h x" using h[OF x(1)] unfolding eventually_sequentially by blast
      have "h x = f n x" using n by simp
      then have "h x \<in> path_image (f n)" using x(1) by (auto simp: path_image_def)
      then have "h x \<in> convex hull (path_image (f n))" using hull_subset by (meson subsetD)
      then have "h x \<in> convex hull (path_image \<gamma>)" using fhull by simp
      then show "z \<in> convex hull (path_image \<gamma>)" using x(2) by simp
    qed
    show "convex hull (path_image h) \<subseteq> convex hull (path_image \<gamma>)"
      using ph_sub convex_convex_hull by (rule hull_minimal)
  next
    \<comment> \<open>$\supseteq$: the extreme points of the hull are frontier points, hence images of parameters
       outside @{term s}, which lie in @{term "path_image h"}. (Krein--Milman + redundancy of interior points.)\<close>
    have cpt_g: "compact (convex hull path_image \<gamma>)"
      by (simp add: compact_convex_hull compact_path_image path\<gamma>)
    have km_g: "convex hull path_image \<gamma> = convex hull {x. x extreme_point_of (convex hull path_image \<gamma>)}"
      using Krein_Milman_Minkowski[OF cpt_g convex_convex_hull] by simp
    have ext_in_out: "\<And>z. z extreme_point_of (convex hull path_image \<gamma>) \<Longrightarrow> z \<in> \<gamma> ` ({0..1} - s)"
    proof -
      fix z assume e: "z extreme_point_of (convex hull path_image \<gamma>)"
      have zpig: "z \<in> path_image \<gamma>" using extreme_point_of_convex_hull[OF e] .
      then obtain x where x: "x \<in> {0..1}" "z = \<gamma> x" by (auto simp: path_image_def)
      have znotint: "z \<notin> interior (convex hull path_image \<gamma>)" using extreme_point_not_in_interior[OF e] .
      have "z \<in> F"
      proof -
        have "z \<in> convex hull path_image \<gamma>" using zpig hull_subset by (meson subsetD)
        then have "z \<in> closure (convex hull path_image \<gamma>)" using closure_subset by (meson subsetD)
        then show "z \<in> F" using znotint F_def by (simp add: frontier_def)
      qed
      then have "x \<notin> s" using x(2) s_def x(1) by auto
      then show "z \<in> \<gamma> ` ({0..1} - s)" using x by auto
    qed
    have "{x. x extreme_point_of (convex hull path_image \<gamma>)} \<subseteq> \<gamma> ` ({0..1} - s)"
      using ext_in_out by blast
    then have "convex hull {x. x extreme_point_of (convex hull path_image \<gamma>)} \<subseteq> convex hull (\<gamma> ` ({0..1} - s))"
      by (rule hull_mono)
    then have "convex hull (path_image \<gamma>) \<subseteq> convex hull (\<gamma> ` ({0..1} - s))" using km_g by simp
    also have "convex hull (\<gamma> ` ({0..1} - s)) \<subseteq> convex hull (path_image h)"
      using gout_sub_h by (rule hull_mono)
    finally show "convex hull (path_image \<gamma>) \<subseteq> convex hull (path_image h)" .
  qed
  \<comment> \<open>The image of @{term h} is exactly the frontier: $\subseteq$ is \<open>hsub_F\<close>; $\supseteq$ because @{term h} is a simple closed
     curve whose image lies on the frontier of its (now equal) convex hull.\<close>
  have hF: "frontier (convex hull (path_image h)) = F" using hhull F_eq by simp
  have h_image_F: "path_image h = F"
  proof
    show "path_image h \<subseteq> F" by (rule hsub_F)
    show "F \<subseteq> path_image h"
    proof -
      have "path_image h \<subseteq> frontier (convex hull (path_image h))" using hsub_F hF by simp
      then have "frontier (convex hull (path_image h)) \<subseteq> path_image h"
        using frontier_convex_hull_subset_path_image[OF hsimple hloop] by simp
      then show "F \<subseteq> path_image h" using hF by simp
    qed
  qed
  show ?thesis
  proof (intro exI[of _ h] conjI)
    show "rectifiable_path h" by (rule hrect)
    show "simple_path h" by (rule hsimple)
    show "pathfinish h = pathstart h" by (rule hloop)
    show "path_length h \<le> path_length \<gamma>" by (rule hlen)
    show "convex hull (path_image h) = convex hull (path_image \<gamma>)" by (rule hhull)
    show "path_image h = frontier (convex hull (path_image \<gamma>))" using h_image_F F_def by simp
  qed
qed

theorem isoperimetric_convexification:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
  obtains h where "rectifiable_path h" and "simple_path h"
    and "pathfinish h = pathstart h"
    and "path_length h \<le> path_length g"
    and "convex hull (path_image h) = convex hull (path_image g)"
    and "path_image h = frontier (convex hull (path_image g))"
proof -
  note [[quick_and_dirty]]
  \<comment> \<open>Strengthened version, assuming the loop starts on the frontier of its convex hull.
     (Here used to derive the general statement by shifting the basepoint.)\<close>
  have *: "\<And>G::real\<Rightarrow>complex. rectifiable_path G \<Longrightarrow> simple_path G \<Longrightarrow> pathfinish G = pathstart G \<Longrightarrow> pathstart G \<in> frontier (convex hull (path_image G)) \<Longrightarrow> (\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length G \<and> convex hull (path_image h) = convex hull (path_image G) \<and> path_image h = frontier (convex hull (path_image G)))"
  proof -
    fix G :: "real \<Rightarrow> complex"
    assume Grect: "rectifiable_path G" and Gsimple: "simple_path G"
      and Gloop: "pathfinish G = pathstart G"
      and Gfr: "pathstart G \<in> frontier (convex hull (path_image G))"
    \<comment> \<open>WLOG reparametrize @{term G} by arc length, so it becomes @{term "path_length G"}-Lipschitz (unit speed).
       All relevant quantities (@{term path_image}, @{term path_length}, endpoints, frontier) are preserved.\<close>
    obtain g' where g': "rectifiable_path g'" "path_image g' = path_image G"
        "pathstart g' = pathstart G" "pathfinish g' = pathfinish G"
        "path_length g' = path_length G" "arc G \<Longrightarrow> arc g'" "simple_path G \<Longrightarrow> simple_path g'"
        "\<forall>t\<in>{0..1}. path_length (subpath 0 t g') = path_length G * t"
        "\<forall>x\<in>{0..1}. \<forall>y\<in>{0..1}. dist (g' x) (g' y) \<le> path_length G * dist x y"
      using arc_length_reparametrization[OF Grect] by metis
    have g'simple: "simple_path g'" using g'(7) Gsimple by simp
    have g'rect: "rectifiable_path g'" by (rule g'(1))
    have g'loop: "pathfinish g' = pathstart g'" using g'(3,4) Gloop by simp
    have g'fr: "pathstart g' \<in> frontier (convex hull (path_image g'))"
      using g'(3) g'(2) Gfr by simp
    have g'lip: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g' x) (g' y) \<le> path_length G * dist x y"
      using g'(9) by blast
    have g'lip': "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (g' x) (g' y) \<le> path_length g' * dist x y"
      using g'lip g'(5) by simp
    \<comment> \<open>Reduced subgoal, now also assuming the unit-speed (Lipschitz) bound. This is where the
       iterated application of \<open>step_lemma\<close> goes (via \<open>convexification_unit_speed\<close>).\<close>
    have **: "\<And>\<gamma>::real\<Rightarrow>complex. rectifiable_path \<gamma> \<Longrightarrow> simple_path \<gamma> \<Longrightarrow> pathfinish \<gamma> = pathstart \<gamma> \<Longrightarrow> pathstart \<gamma> \<in> frontier (convex hull (path_image \<gamma>)) \<Longrightarrow> (\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (\<gamma> x) (\<gamma> y) \<le> path_length \<gamma> * dist x y) \<Longrightarrow> (\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length \<gamma> \<and> convex hull (path_image h) = convex hull (path_image \<gamma>) \<and> path_image h = frontier (convex hull (path_image \<gamma>)))"
      using convexification_unit_speed by blast
    have inst: "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length g' \<and> convex hull (path_image h) = convex hull (path_image g') \<and> path_image h = frontier (convex hull (path_image g'))"
      using **[OF g'rect g'simple g'loop g'fr g'lip'] .
    show "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length G \<and> convex hull (path_image h) = convex hull (path_image G) \<and> path_image h = frontier (convex hull (path_image G))"
      using inst g'(5) g'(2) by simp
  qed
  \<comment> \<open>Some point of the loop lies on the frontier (an extreme point of the convex hull).\<close>
  have pathg: "path g" using assms(2) by (rule simple_path_imp_path)
  have cpt: "compact (convex hull path_image g)"
    by (simp add: compact_convex_hull compact_path_image pathg)
  have ne: "convex hull path_image g \<noteq> {}"
    by (simp add: path_image_nonempty)
  obtain x where x_ext: "x extreme_point_of (convex hull path_image g)"
    using extreme_point_exists_convex[OF cpt convex_convex_hull ne] by blast
  have x_pig: "x \<in> path_image g" using extreme_point_of_convex_hull[OF x_ext] .
  have x_in: "x \<in> convex hull path_image g" using hull_subset x_pig by (meson subsetD)
  have x_notint: "x \<notin> interior (convex hull path_image g)" using extreme_point_not_in_interior[OF x_ext] .
  have x_clo: "x \<in> closure (convex hull path_image g)" using x_in closure_subset by (meson subsetD)
  have x_fr: "x \<in> frontier (convex hull path_image g)"
    using x_clo x_notint by (simp add: frontier_def)
  obtain t where t: "t \<in> {0..1}" "g t = x" using x_pig by (auto simp: path_image_def)
  \<comment> \<open>Shift @{term g} so that it starts at the frontier point $g\,t$; properties are preserved.\<close>
  have sp_rect: "rectifiable_path (shiftpath t g)" using assms(1,3) t(1) by (rule rectifiable_path_shiftpath)
  have sp_simple: "simple_path (shiftpath t g)" using assms(2,3) t(1) by (simp add: simple_path_shiftpath)
  have sp_loop: "pathfinish (shiftpath t g) = pathstart (shiftpath t g)" using assms(3) t(1) by (rule closed_shiftpath)
  have sp_pi: "path_image (shiftpath t g) = path_image g" using t(1) assms(3) by (rule path_image_shiftpath)
  have sp_start: "pathstart (shiftpath t g) = g t" using t(1) by (simp add: pathstart_shiftpath)
  have sp_len: "path_length (shiftpath t g) = path_length g" using assms(1,3) t(1) by (rule path_length_shiftpath)
  have sp_startfr: "pathstart (shiftpath t g) \<in> frontier (convex hull (path_image (shiftpath t g)))"
    using sp_start sp_pi x_fr t(2) by simp
  have inst: "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> path_length h \<le> path_length (shiftpath t g) \<and> convex hull (path_image h) = convex hull (path_image (shiftpath t g)) \<and> path_image h = frontier (convex hull (path_image (shiftpath t g)))"
    using *[OF sp_rect sp_simple sp_loop sp_startfr] .
  from inst obtain h where h: "rectifiable_path h" "simple_path h" "pathfinish h = pathstart h"
      "path_length h \<le> path_length (shiftpath t g)"
      "convex hull (path_image h) = convex hull (path_image (shiftpath t g))"
      "path_image h = frontier (convex hull (path_image (shiftpath t g)))" by blast
  show ?thesis
    using inst sp_len sp_pi that by force
qed

theorem isoperimetric_convexification_strict:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "\<not> convex (inside (path_image g))"
  obtains h where "rectifiable_path h" and "simple_path h"
    and "pathfinish h = pathstart h"
    and "path_length h \<le> path_length g"
    and "convex hull (path_image h) = convex hull (path_image g)"
    and "path_image h = frontier (convex hull (path_image g))"
    and "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
proof -
  obtain h where h: "rectifiable_path h" "simple_path h" "pathfinish h = pathstart h"
      "path_length h \<le> path_length g" "convex hull (path_image h) = convex hull (path_image g)"
      "path_image h = frontier (convex hull (path_image g))"
    using isoperimetric_convexification[OF assms(1,2,3)] by metis
  have pathg: "path g" using assms(2) simple_path_imp_path by blast
  have bdd_hull: "bounded (convex hull (path_image g))"
    by (simp add: bounded_convex_hull bounded_simple_path_image assms(2))
  have ins_h: "inside (path_image h) = interior (convex hull (path_image g))"
    using h(6) inside_frontier_eq_interior[OF bdd_hull convex_convex_hull] by simp
  have ins_g_sub: "inside (path_image g) \<subseteq> interior (convex hull (path_image g))"
  proof -
    let ?C = "convex hull (path_image g)"
    have pig_sub: "path_image g \<subseteq> ?C" by (rule hull_subset)
    have conn: "connected (- ?C)" using bdd_hull by (simp add: connected_complement_bounded_convex)
    have unbdd: "\<not> bounded (- ?C)"
    proof
      assume "bounded (- ?C)"
      then have "bounded (?C \<union> - ?C)" using bdd_hull bounded_Un by blast
      moreover have "?C \<union> - ?C = UNIV" by auto
      ultimately show False using not_bounded_UNIV by simp
    qed
    have un: "(?C - path_image g) \<union> (- ?C) = - path_image g" using pig_sub by auto
    have "inside (path_image g) \<subseteq> ?C - path_image g" using inside_subset[OF conn unbdd un] .
    then have "inside (path_image g) \<subseteq> ?C" by blast
    moreover have "open (inside (path_image g))" using assms(2) by (simp add: open_inside closed_simple_path_image)
    ultimately show ?thesis using interior_maximal by blast
  qed
  \<comment> \<open>Measurability: \<open>inside\<close> is bounded and open, hence Lebesgue measurable (cf. HOL Light's
      \<open>MEASURABLE_INSIDE\<close>, which is just \<open>MEASURABLE_OPEN; BOUNDED_INSIDE; OPEN_INSIDE\<close>).\<close>
  have clg: "closed (path_image g)" using assms(2) by (simp add: closed_simple_path_image)
  have bdd_ins_g: "bounded (inside (path_image g))" using Jordan_inside_outside[OF assms(2,3)] by simp
  have open_ins_g: "open (inside (path_image g))" using clg by (rule open_inside)
  have meas_ins_g: "inside (path_image g) \<in> lmeasurable"
    using bdd_ins_g open_ins_g by (rule lmeasurable_open)
  have meas_ins_h: "inside (path_image h) \<in> lmeasurable"
  proof -
    have "bounded (interior (convex hull path_image g))" using bdd_hull bounded_interior by blast
    moreover have "open (interior (convex hull path_image g))" by simp
    ultimately show ?thesis using ins_h by (simp add: lmeasurable_open)
  qed
  \<comment> \<open>The path image is not contained in the frontier of its convex hull (else \<open>inside g\<close>
      would be convex), so it meets the interior of the hull.\<close>
  have not_sub: "\<not> path_image g \<subseteq> frontier (convex hull (path_image g))"
  proof
    assume sub: "path_image g \<subseteq> frontier (convex hull (path_image g))"
    have "convex (inside (path_image g))"
    proof -
      have "frontier (convex hull (path_image g)) = path_image g"
        using frontier_convex_hull_eq_path_image[OF assms(2,3)] sub
        by (meson frontier_convex_hull_subset_path_image[OF assms(2,3)] subset_antisym)
      then have "inside (path_image g) = inside (frontier (convex hull (path_image g)))" by simp
      also have "\<dots> = interior (convex hull (path_image g))"
        using inside_frontier_eq_interior[OF bdd_hull convex_convex_hull] .
      finally show ?thesis by (simp add: convex_interior)
    qed
    then show False using assms(4) by simp
  qed
  have pig_hull: "path_image g \<subseteq> convex hull (path_image g)" by (rule hull_subset)
  have ex_int: "\<exists>x. x \<in> path_image g \<and> x \<in> interior (convex hull (path_image g))"
  proof -
    obtain x where x: "x \<in> path_image g" "x \<notin> frontier (convex hull (path_image g))"
      using not_sub by blast
    have "x \<in> convex hull (path_image g)" using x(1) pig_hull by blast
    then have "x \<in> closure (convex hull (path_image g))" using closure_subset by blast
    then have "x \<in> interior (convex hull (path_image g))" using x(2) by (simp add: frontier_def)
    then show ?thesis using x(1) by blast
  qed
  have jordan_g: "inside (path_image g) \<noteq> {} \<and> open (inside (path_image g)) \<and> connected (inside (path_image g)) \<and>
      outside (path_image g) \<noteq> {} \<and> open (outside (path_image g)) \<and> connected (outside (path_image g)) \<and>
      frontier (inside (path_image g)) = path_image g \<and> frontier (outside (path_image g)) = path_image g"
    using Jordan_inside_outside[OF assms(2,3)] by blast
  \<comment> \<open>Find a frontier point \<open>x\<close> of \<open>g\<close> in the hull interior; \<open>frontier_straddle\<close> gives a nearby
      outside point \<open>y\<close>, and a ball about \<open>y\<close> lies in \<open>outside g \<inter> interior(hull)\<close>.\<close>
  obtain x where x_pig: "x \<in> path_image g" and x_int: "x \<in> interior (convex hull (path_image g))"
    using ex_int by blast
  obtain r1 where r1: "r1 > 0" "ball x r1 \<subseteq> interior (convex hull (path_image g))"
    using x_int open_contains_ball[of "interior (convex hull (path_image g))"] by auto
  have x_fro_out: "x \<in> frontier (outside (path_image g))" using x_pig jordan_g by simp
  obtain y where y_out: "y \<in> outside (path_image g)" and y_close: "dist x y < r1"
    using x_fro_out r1(1) frontier_straddle[of x "outside (path_image g)"] by (metis dist_commute)
  have y_in_ball: "y \<in> ball x r1" using y_close by (simp add: dist_commute)
  have y_int: "y \<in> interior (convex hull (path_image g))" using y_in_ball r1(2) by blast
  have y_in_both: "y \<in> outside (path_image g) \<inter> interior (convex hull (path_image g))"
    using y_out y_int by blast
  have open_both: "open (outside (path_image g) \<inter> interior (convex hull (path_image g)))"
    using jordan_g open_Int open_interior by blast
  obtain r2 where r2: "r2 > 0" "ball y r2 \<subseteq> outside (path_image g) \<inter> interior (convex hull (path_image g))"
    using y_in_both open_both by (meson open_contains_ball)
  \<comment> \<open>This ball lies in \<open>inside h - inside g\<close>: it is in \<open>interior(hull) = inside h\<close> and in
      \<open>outside g\<close>, which is disjoint from \<open>inside g\<close>.\<close>
  have ins_g_sub_h: "inside (path_image g) \<subseteq> inside (path_image h)"
    using ins_g_sub ins_h by simp
  have io_disj: "inside (path_image g) \<inter> outside (path_image g) = {}"
    by (simp add: inside_Int_outside)
  have ball_sub: "ball y r2 \<subseteq> inside (path_image h) - inside (path_image g)"
  proof
    fix z assume z: "z \<in> ball y r2"
    have z_out: "z \<in> outside (path_image g)" using z r2(2) by blast
    have z_int: "z \<in> interior (convex hull (path_image g))" using z r2(2) by blast
    have "z \<in> inside (path_image h)" using z_int ins_h by simp
    moreover have "z \<notin> inside (path_image g)" using z_out io_disj by blast
    ultimately show "z \<in> inside (path_image h) - inside (path_image g)" by simp
  qed
  \<comment> \<open>A nonempty ball has positive measure, so the difference does too.\<close>
  have ball_pos: "measure lebesgue (ball y r2) > 0"
  proof -
    have "\<not> negligible (ball y r2)"
      using negligible_convex_interior[of "ball y r2"] r2(1) by simp
    moreover have "ball y r2 \<in> lmeasurable" by simp
    ultimately show ?thesis
      using negligible_iff_measure0[of "ball y r2"] measure_nonneg[of lebesgue "ball y r2"] by fastforce
  qed
  have diff_meas: "inside (path_image h) - inside (path_image g) \<in> lmeasurable"
    using meas_ins_h meas_ins_g by (simp add: fmeasurable.Diff)
  have diff_pos: "measure lebesgue (inside (path_image h) - inside (path_image g)) > 0"
  proof -
    have "ball y r2 \<in> sets lebesgue" by simp
    then have "measure lebesgue (ball y r2) \<le> measure lebesgue (inside (path_image h) - inside (path_image g))"
      using ball_sub diff_meas measure_mono_fmeasurable by blast
    then show ?thesis using ball_pos by linarith
  qed
  have meas_eq: "measure lebesgue (inside (path_image h) - inside (path_image g)) =
      measure lebesgue (inside (path_image h)) - measure lebesgue (inside (path_image g))"
    using measurable_measure_Diff[OF meas_ins_h _ ins_g_sub_h] meas_ins_g by (simp add: fmeasurableD)
  have strict: "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
    using diff_pos meas_eq by linarith
  show ?thesis
  proof (intro that)
    show "rectifiable_path h" by (rule h(1))
    show "simple_path h" by (rule h(2))
    show "pathfinish h = pathstart h" by (rule h(3))
    show "path_length h \<le> path_length g" by (rule h(4))
    show "convex hull path_image h = convex hull path_image g" by (rule h(5))
    show "path_image h = frontier (convex hull path_image g)" by (rule h(6))
    show "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))" by (rule strict)
  qed
qed

section \<open>Part 5: The isoperimetric theorem\<close>

theorem isoperimetric_theorem:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
proof -
  show ineq: "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
  proof (cases "convex (inside (path_image g))")
    case True
    show ?thesis
      using isoperimetric_theorem_convex(1)[OF assms(1-3) True assms(4)] .
  next
    case False
    obtain h where h: "rectifiable_path h" "simple_path h"
      "pathfinish h = pathstart h"
      "path_length h \<le> path_length g"
      "convex hull (path_image h) = convex hull (path_image g)"
      "path_image h = frontier (convex hull (path_image g))"
      "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
      by (rule isoperimetric_convexification_strict[OF assms(1-3) False])
    have bounded_hull: "bounded (convex hull (path_image g))"
      by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image assms(2))
    have eq_int: "inside (path_image h) = interior (convex hull (path_image g))"
      using inside_frontier_eq_interior[OF bounded_hull convex_convex_hull] h(6) by simp
    have convex_h: "convex (inside (path_image h))"
      using eq_int convex_interior[OF convex_convex_hull] by simp
    have ineq_h: "measure lebesgue (inside (path_image h)) \<le> (path_length h)\<^sup>2 / (4 * pi)"
      using isoperimetric_theorem_convex(1)[OF h(1-3) convex_h refl] .
    have mono: "(path_length h)\<^sup>2 / (4 * pi) \<le> L\<^sup>2 / (4 * pi)"
      by (intro divide_right_mono power_mono)
        (use h(4) assms(4) path_length_pos_le[OF h(1)] pi_gt_zero in simp_all)
    show ?thesis using h(7) ineq_h mono by linarith
  qed
  show "\<exists>a r. path_image g = sphere a r"
    if eq: "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi)"
  proof (cases "convex (inside (path_image g))")
    case True
    show ?thesis
      using isoperimetric_theorem_convex(2)[OF assms(1-3) True assms(4)] eq .
  next
    case False
    obtain h where h: "rectifiable_path h" "simple_path h"
      "pathfinish h = pathstart h"
      "path_length h \<le> path_length g"
      "convex hull (path_image h) = convex hull (path_image g)"
      "path_image h = frontier (convex hull (path_image g))"
      "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
      by (rule isoperimetric_convexification_strict[OF assms(1-3) False])
    have bounded_hull: "bounded (convex hull (path_image g))"
      by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image assms(2))
    have eq_int: "inside (path_image h) = interior (convex hull (path_image g))"
      using inside_frontier_eq_interior[OF bounded_hull convex_convex_hull] h(6) by simp
    have convex_h: "convex (inside (path_image h))"
      using eq_int convex_interior[OF convex_convex_hull] by simp
    have ineq_h: "measure lebesgue (inside (path_image h)) \<le> (path_length h)\<^sup>2 / (4 * pi)"
      using isoperimetric_theorem_convex(1)[OF h(1-3) convex_h refl] .
    have mono: "(path_length h)\<^sup>2 / (4 * pi) \<le> L\<^sup>2 / (4 * pi)"
      by (intro divide_right_mono power_mono)
        (use h(4) assms(4) path_length_pos_le[OF h(1)] pi_gt_zero in simp_all)
    have "measure lebesgue (inside (path_image g)) < L\<^sup>2 / (4 * pi)"
      using h(7) ineq_h mono by linarith
    with eq show ?thesis by simp
  qed
qed

end

