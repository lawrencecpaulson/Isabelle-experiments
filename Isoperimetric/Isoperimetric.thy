theory Isoperimetric
  imports Arc_Length_Reparametrization Wirtinger Special_Green
begin

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
  \<^item> @{text Arc_Length_Reparametrization}: arc length reparametrization

\<close>

section \<open>Isoperimetric theorem for convex curves\<close>

text \<open>The kernel lemma: the isoperimetric inequality for a convex curve that has been
  normalized to arc-length parametrization with zero-mean imaginary part and
  diameter along the real axis starting at a point with $Re = 0$.
  This is where the Wirtinger inequality is applied.\<close>

proposition isoperimetric_kernel:
  fixes g :: "real \<Rightarrow> complex" and L :: real and a b :: complex
  assumes conv_in: "convex (inside (path_image g))"
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
  have Lpos: "0 < L"
    using L g simple_path_length_pos_lt by blast
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
    "path_length g = L"
  obtains h where "rectifiable_path h" "simple_path h"
    "pathfinish h = pathstart h" "pathstart h = pathstart g"
    "convex (inside (path_image h))"
    "path_length h = L"
    "path_image h = path_image g"
    "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
  by (metis arc_length_reparametrization assms)

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
proof 
  define c where "c = integral {0..1} (Im \<circ> g)"
  define d where "d = -(\<i> * (of_real c :: complex))"
  define h where "h = (+) d \<circ> g"
  define a' where "a' = pathstart g + d"
  define b' where "b' = b + d"
  have pi_h: "path_image h = (+) d ` path_image g"
    unfolding h_def image_comp [symmetric] path_image_compose by simp
  show "rectifiable_path h"
    unfolding h_def using assms(1) rectifiable_path_translation_eq[of d g] by simp
  show "simple_path h"
    unfolding h_def using assms(2) simple_path_translation_eq[of d g] by simp
  show "pathfinish h = pathstart h"
    unfolding h_def using assms(3) by (simp add: pathstart_compose pathfinish_compose)
  show "path_length h = L"
    unfolding h_def using assms(5) path_length_translation[of d g] by simp
  show "pathstart h = a'" "pathfinish h = a'" unfolding h_def a'_def
    using assms(3) by (simp_all add: pathstart_compose pathfinish_compose)
  show "a' \<in> path_image h" "b' \<in> path_image h" "b' - a' = of_real (dist a' b')" "Re a' = 0"
    using assms pi_h path_image_def pathstart_def by (auto simp: a'_def b'_def d_def dist_norm)
  show "dist a' b' = diameter (path_image h)"
    using pi_h diameter_translation[of d "path_image g"] assms(7)
    unfolding a'_def b'_def by (simp add: dist_norm)
  show "convex (inside (path_image h))"
    using pi_h inside_translation[of d "path_image g"]
      convex_translation_eq[of d "inside (path_image g)"] assms(4) by simp
  show "\<And>t. t \<in> {0..1} \<Longrightarrow> path_length (subpath 0 t h) = L * t"
    by (simp add: assms(10) h_def path_length_translation subpath_image)
  show "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
    using assms(11) h_def comp_def by auto
  show "(Im \<circ> h has_integral 0) {0..1}"
  proof -
    have cont_g: "continuous_on {0..1} g"
      using rectifiable_path_imp_path[OF assms(1)] unfolding path_def .
    have int_Im_g: "(\<lambda>t. Im (g t)) integrable_on {0..1}"
      using integrable_continuous_real[OF continuous_on_Im[OF cont_g]] .
    have Im_h: "\<And>t. Im (h t) = Im (g t) - c"
      unfolding h_def comp_def d_def by simp
    have int_sub: "(\<lambda>t. Im (g t) - c) integrable_on {0..1}"
      by (rule integrable_diff[OF int_Im_g integrable_const_ivl])
    have int_h: "(Im \<circ> h) integrable_on {0..1}" 
      by (simp add: Im_h int_sub o_def)
    have "integral {0..1} (Im \<circ> h) = integral {0..1} (\<lambda>t. Im (g t) - c)"
      using integral_cong[of "{0..1}" "Im \<circ> h" "\<lambda>t. Im (g t) - c"] by (simp add: Im_h)
    also have "\<dots> = integral {0..1} (\<lambda>t. Im (g t)) - integral {0..1} (\<lambda>_::real. c::real)"
      using integral_diff[OF int_Im_g integrable_const_ivl] by simp
    also have "\<dots> = 0" unfolding c_def comp_def by simp
    finally show ?thesis using int_h has_integral_iff by blast
  qed
  show "measure lebesgue (inside (path_image h)) = measure lebesgue (inside (path_image g))"
    by (metis inside_translation measure_translation pi_h)
  show "\<exists>c' r'. path_image g = sphere c' r'" if "path_image h = sphere c0 r" for c0 r
  proof -
    have "(+) (- d) ` (+) d ` path_image g = (+) (- d) ` sphere c0 r"
      using pi_h that by argo
    then have "path_image g = (+) (- d) ` sphere c0 r"
      using translation_assoc[of "- d" d "path_image g"] by simp
    also have "\<dots> = sphere (c0 + (- d)) r"
      using sphere_translation[of "-d" c0 r] by simp
    finally show ?thesis by blast
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
    "convex (inside (path_image g1))" "path_length g1 = L" "path_image g1 = path_image g"
    using isoperimetric_reduce_shift[OF assms ab(1)] by metis
  have ab1: "a \<in> path_image g1" "b \<in> path_image g1" "dist a b = diameter (path_image g1)"
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
    using isoperimetric_reduce_arc_length[OF g2(1,2,3,5,6)] by metis
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
    by (metis g3(7) sphere_back2 sphere_back5)
  have ineq_h: "measure lebesgue (inside (path_image h)) \<le> L\<^sup>2 / (4 * pi)"
    using isoperimetric_kernel(1) h by blast
  show "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    using ineq_h meas_eq by simp
  show "\<exists>a r. path_image g = sphere a r"
    if "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi)"
  proof -
    have "measure lebesgue (inside (path_image h)) = L\<^sup>2 / (4 * pi)"
      using that meas_eq by simp
    then obtain c r where "path_image h = sphere c r"
    using isoperimetric_kernel(2) h by blast
    then show ?thesis using sphere_back by auto
  qed
qed

section \<open>Convexification\<close>

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
    then have "g a = g b" .
    with \<open>simple_path g\<close> ab01 have "a = b \<or> a = 0 \<and> b = 1 \<or> a = 1 \<and> b = 0"
      unfolding simple_path_def loop_free_def by auto
    with \<open>a < b\<close> have ab_eq: "a = 0" "b = 1" by auto
    have g01: "g 0 = g 1"
      using assms(2) by (simp add: pathfinish_def pathstart_def)
    have pi_eq: "path_image g = {g 0} \<union> g ` {0<..<1}"
      using g01 by (fastforce simp: path_image_def image_iff)
    have int_sub: "g ` {0<..<1} \<subseteq> interior (convex hull (path_image g))"
      using interior_subset ab_eq by simp
    have ext_sub: "{x. x extreme_point_of (convex hull (path_image g))} \<subseteq> {g 0}"
        using int_sub pi_eq extreme_point_not_in_interior 
         extreme_point_of_convex_hull by fastforce
      \<comment> \<open>By Krein--Milman, the convex hull collapses to a single point\<close>
    have compact_hull: "compact (convex hull (path_image g))"
      by (rule compact_convex_hull[OF compact_simple_path_image[OF \<open>simple_path g\<close>]])
    have "convex hull (path_image g) = convex hull {x. x extreme_point_of (convex hull (path_image g))}"
      using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull] by simp
    also have "\<dots> \<subseteq> convex hull {g 0}"
      using ext_sub by (intro hull_mono)
    also have "\<dots> = {g 0}" by (simp add: convex_hull_singleton)
    finally have "convex hull (path_image g) \<subseteq> {g 0}" .
    then have "interior (convex hull (path_image g)) = {}"
      by (simp add: subset_singleton_iff)
    with interior_ne show ?thesis by contradiction
  next
    case ga_ne_gb: False
    have hull_eq: "convex hull (g ` ({0..1} - {a<..<b})) = convex hull (path_image g)"
    proof
      show "convex hull (g ` ({0..1} - {a<..<b})) \<subseteq> convex hull (path_image g)"
        by (intro hull_mono image_mono) (auto simp: path_image_def)
          \<comment> \<open>For $\supseteq$, use extreme points: they lie in @{term "path_image g"} but not in the interior\<close>
      have compact_hull: "compact (convex hull (path_image g))"
        by (rule compact_convex_hull[OF compact_simple_path_image[OF \<open>simple_path g\<close>]])
      have ext_in_rest: "{x. x extreme_point_of (convex hull (path_image g))} \<subseteq> g ` ({0..1} - {a<..<b})"
        using path_image_def
        using extreme_point_not_in_interior interior_subset extreme_point_of_convex_hull
          by (smt (verit, del_insts) DiffI image_diff_subset mem_Collect_eq subset_iff)
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
          ab01(1) ab01(2) less_imp_le[OF \<open>a < b\<close>] ga_ne_gb] by blast

    \<comment> \<open>Step 2: the frontier of the convex hull admits a rectifiable simple loop parametrization
       (this corresponds to HOL Light's \<open>RECTIFIABLE_LOOP_RELATIVE_FRONTIER_CONVEX\<close>)\<close>
    have frontier_eq_rel: "rel_frontier (convex hull (path_image g)) = frontier (convex hull (path_image g))"
      using rel_frontier_nonempty_interior[OF interior_ne] by simp
    obtain d where d_props:
      "simple_path d" "pathfinish d = pathstart d" "rectifiable_path d"
      "path_image d = frontier (convex hull (path_image g))"
      by (meson assms(1) bounded_convex_hull bounded_simple_path_image convex_convex_hull interior_ne
          rectifiable_loop_frontier_convex)

\<comment> \<open>Step 4: double arc decomposition of the frontier loop @{term d}, with inside decomposition\<close>
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
      and rev_pi: "path_image (reversepath d1) = path_image d1"
      using da(5,6) by (simp_all)
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
        \<comment> \<open>The open part of @{term g0} lies in the interior, 
            hence @{term g0} meets the frontier only at $g\,a$, $g\,b$\<close>
    have "{a..b} = {a<..<b} \<union> {a, b}"
      using \<open>a < b\<close> by auto
    then have g0_decomp: "path_image g0 = g ` {a<..<b} \<union> {g a, g b}"
      by (simp add: arcs(7))
    have "g ` {a<..<b} \<inter> path_image d = {}"
      using assms(9) d_props(4) by simp
    then have g0_d_int: "path_image g0 \<inter> path_image d = {g a, g b}"
      by (simp add: g0_decomp ga_d gb_d)
    have d0_g0_int: "path_image d0 \<inter> path_image g0 = {g a, g b}"
      using da(7,8) g0_d_int by auto
    have d1_g0_int: "path_image d1 \<inter> path_image g0 = {g a, g b}"
      using d1_sub da(7) g0_d_int by auto
    have d_union: "path_image d0 \<union> path_image (reversepath d1) = path_image d"
      using da(8) rev_pi by simp
    have "bounded (convex hull path_image g)"
      by (intro bounded_convex_hull compact_imp_bounded compact_simple_path_image \<open>simple_path g\<close>)
    then have inside_eq: "inside (path_image d0 \<union> path_image (reversepath d1)) = interior (convex hull path_image g)"
        using inside_frontier_eq_interior convex_convex_hull d_union d_props(4) by force
    have "g ` {a<..<b} \<noteq> {}"
      using \<open>a < b\<close> by auto
    then have g0_inside_ne: "path_image g0 \<inter> inside (path_image d0 \<union> path_image (reversepath d1)) \<noteq> {}"
      using g0_decomp inside_eq interior_subset by blast
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
    qed (use da d0_g0_int g0_ends in \<open>auto simp add: arc_rev_g0\<close>)
    have J0_close: "pathfinish (d0 +++ reversepath g0) = pathstart (d0 +++ reversepath g0)"
      using da(3) g0_ends by auto
    have J0_pi: "path_image (d0 +++ reversepath g0) = path_image d0 \<union> path_image g0"
      using da(4) g0_ends by (simp add: path_image_join)
    have J1_loop: "simple_path (reversepath d1 +++ reversepath g0)"
    proof (rule simple_path_join_loop)
    qed (use da d1_g0_int g0_ends in \<open>auto simp add: arc_rev_g0 arc_reversepath\<close>)
    have J1_close: "pathfinish (reversepath d1 +++ reversepath g0) = pathstart (reversepath d1 +++ reversepath g0)"
      using da(6) g0_ends by auto
    have J1_pi: "path_image (reversepath d1 +++ reversepath g0) = path_image d1 \<union> path_image g0"
      using da(5) g0_ends by (simp add: path_image_join)
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
      using arcs(10) hull_subset by fastforce
    have hull_closed: "closed (convex hull path_image g)"
      by (simp add: compact_imp_closed compact_convex_hull compact_simple_path_image \<open>simple_path g\<close>)
    have g1_cover: "path_image g1 \<subseteq> interior (convex hull path_image g) \<union> frontier (convex hull path_image g)"
      using g1_in_hull hull_closed by (simp add: frontier_def) blast
        \<comment> \<open>@{term S} (which is @{term g1} minus its endpoints) is covered by the two \<open>inside\<close>-plus-arc regions ...\<close>
    have cover: "z \<in> (inside (path_image d1 \<union> path_image g0) \<union> path_image d1) \<union> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
      if "z \<in> S" for z
        using that S_def g1_g0_int d_props(4) da(8) g1_cover split2 by blast
    have ic0: "inside (path_image d1 \<union> path_image g0) \<inter> closure (inside (path_image d0 \<union> path_image g0)) = {}"
      by (simp add: inf_commute op_in1 open_Int_closure_eq_empty split1)
    have ic1: "inside (path_image d0 \<union> path_image g0) \<inter> closure (inside (path_image d1 \<union> path_image g0)) = {}"
      by (simp add: op_in0 open_Int_closure_eq_empty split1)
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
      using in1_d0 in1_in0 d1_in0 d1_d0_S by blast
    have "S - closure (inside (path_image d1 \<union> path_image g0)) = S - (inside (path_image d1 \<union> path_image g0) \<union> path_image d1)"
      using cl_J1 S_g0 by blast
    then have eqA: "S - closure (inside (path_image d1 \<union> path_image g0)) = S \<inter> (path_image d0 \<union> inside (path_image d0 \<union> path_image g0))"
      using cover disj by blast
    have "S - closure (inside (path_image d0 \<union> path_image g0)) = S - (inside (path_image d0 \<union> path_image g0) \<union> path_image d0)"
      using cl_J0 S_g0 by blast
    then have eqB: "S - closure (inside (path_image d0 \<union> path_image g0)) = S \<inter> (path_image d1 \<union> inside (path_image d1 \<union> path_image g0))"
      using cover disj by blast
    have opA: "openin (top_of_set S) (S - closure (inside (path_image d1 \<union> path_image g0)))"
      by (simp add: Diff_eq open_Compl openin_open_Int)
    have opB: "openin (top_of_set S) (S - closure (inside (path_image d0 \<union> path_image g0)))"
      by (simp add: Diff_eq open_Compl openin_open_Int)
    have AB_cover: "(S - closure (inside (path_image d1 \<union> path_image g0))) \<union> (S - closure (inside (path_image d0 \<union> path_image g0))) = S"
      using eqA eqB cover by blast
    have AB_disj: "(S - closure (inside (path_image d1 \<union> path_image g0))) \<inter> (S - closure (inside (path_image d0 \<union> path_image g0))) = {}"
      using eqA eqB in1_d0 in1_in0 d1_in0 d1_d0_S split1 by auto
    have one_empty: "(S - closure (inside (path_image d1 \<union> path_image g0))) = {} \<or> (S - closure (inside (path_image d0 \<union> path_image g0))) = {}"
      using S_conn opA opB AB_cover AB_disj connected_openin by blast
    have disjunction: "S \<inter> path_image d0 = {} \<or> S \<inter> path_image d1 = {}"
      using eqA eqB one_empty by auto
      \<comment> \<open>Whichever arc @{term S} avoids becomes @{term d0} (reversing the pair in the second case)\<close>
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
      have r3: "pathstart (reversepath d1) = g a" using da(6) by simp
      have r4: "pathfinish (reversepath d1) = g b" using da(5) by (simp add: )
      have r5: "pathstart (reversepath d0) = g b" using da(4) by (simp add: )
      have r6: "pathfinish (reversepath d0) = g a" using da(3) by (simp add: )
      have r7: "path_image (reversepath d1) \<inter> path_image (reversepath d0) = {g a, g b}"
        using da(7) by (simp add: Int_commute)
      have r8: "path_image (reversepath d1) \<union> path_image (reversepath d0) = path_image d"
        using da(8) by (simp add: Un_commute)
      have r9: "inside (path_image (reversepath d1) \<union> path_image g0) \<inter> inside (path_image (reversepath d0) \<union> path_image g0) = {}"
        using split1 by (simp add: Int_commute)
      have r10: "inside (path_image (reversepath d1) \<union> path_image g0) \<union> inside (path_image (reversepath d0) \<union> path_image g0) \<union> (path_image g0 - {g a, g b}) = interior (convex hull path_image g)"
        using split2 by (simp add: path_image_reversepath Un_commute Un_left_commute)
      have r11: "(path_image g1 - {g b, g a}) \<inter> path_image (reversepath d1) = {}"
        using d1e by (simp add: path_image_reversepath)
      show thesis
        by (rule that[OF r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11])
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
        by (metis Un_subset_iff convex_convex_hull d_props(4) d_split(8) frontier_subset_eq hull_closed
            hull_minimal)
      have km_ext: "convex hull path_image g = convex hull {x. x extreme_point_of (convex hull path_image g)}"
        using Krein_Milman_Minkowski[OF compact_hull convex_convex_hull] by simp
      have test_cl: "\<And>x. x \<in> path_image g \<Longrightarrow> x \<in> closure (convex hull path_image g)"
        using closure_subset hull_subset by (meson subset_iff)
      have test_front: "\<And>x. x \<in> closure (convex hull path_image g) \<Longrightarrow> x \<notin> interior (convex hull path_image g) \<Longrightarrow> x \<in> frontier (convex hull path_image g)"
        by (simp add: frontier_def)
      have ext_in_g_front: "\<And>x. x extreme_point_of (convex hull path_image g) \<Longrightarrow> x \<in> path_image g \<inter> path_image d"
        by (simp add: d_props(4) extreme_point_not_in_interior extreme_point_of_convex_hull test_cl
            test_front)
      have gab_d1: "g a \<in> path_image d1" "g b \<in> path_image d1"
        using d_split(5,6) by (metis pathstart_in_path_image pathfinish_in_path_image)+
      have g0_int_d: "path_image g0 \<inter> path_image d = {g a, g b}"
        using g0_d_int by force
      have g1_int_d: "path_image g1 \<inter> path_image d \<subseteq> path_image d1" 
        using gab_d1 d_split by blast
      have hull_d1_eq: "convex hull (path_image d1) = convex hull (path_image g)"
      proof (rule subset_antisym)
        show "convex hull (path_image d1) \<subseteq> convex hull (path_image g)" by (rule d1_sub_hull)
      next
        have "path_image g \<inter> path_image d \<subseteq> path_image d1"
          by (metis Int_Un_distrib2 Int_lower2 Un_subset_iff arcs(10) d_split(7) g0_d_int g1_int_d)
        then have "{x. x extreme_point_of (convex hull path_image g)} \<subseteq> path_image d1"
          using ext_in_g_front by blast
        then show "convex hull (path_image g) \<subseteq> convex hull (path_image d1)" 
          using km_ext hull_mono by blast
      qed
      \<comment> \<open>The straight segment between $g(a)$ and $g(b)$ lies on the frontier, via \<open>seg_frontier_aux\<close>
         applied to the arc @{term d1} (whose hull is the whole convex hull by \<open>hull_d1_eq\<close>).\<close>
      have seg_in_frontier: "closed_segment (g a) (g b) \<subseteq> frontier (convex hull path_image g)"
      proof (rule seg_frontier_aux[of _ _ _ d1])
        show "compact (convex hull path_image g)" by (rule compact_hull)
        show "interior (convex hull path_image g) \<noteq> {}" by (rule interior_ne)
        show "path_image d1 \<subseteq> frontier (convex hull path_image g)"
          using d_split(8) d_props(4) by blast
        show "connected (path_image d1 - {g a, g b})"
          using connected_simple_path_endless[OF arc_imp_simple_path[OF d_split(2)]] d_split(5,6)
          by (simp add: insert_commute)
      qed (use assms hull_d1_eq ga_ne_gb gab_d1 ga_ne_gb in auto)
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
      have not_d1: False if "path_image (reversepath d1) \<subseteq> closed_segment (g a) (g b)"
      proof -
        have "interior (convex hull (path_image g)) \<subseteq> interior (closed_segment (g a) (g b))"
          by (metis convex_closed_segment hull_d1_eq interior_mono rev_d1_pi subset_hull that)
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
      have "(\<lambda>t. (t - a)/(b - a)) ` {a..b} = (\<lambda>t. t/(b-a) - a/(b-a)) ` {a..b}"
        by (simp add: diff_divide_distrib)
      also have "\<dots> = {a/(b-a) - a/(b-a) .. b/(b-a) - a/(b-a)}"
        using \<open>a < b\<close> by (subst image_affinity_atLeastAtMost_div_diff) auto
      also have "\<dots> = {0..1}" 
        using \<open>a < b\<close> by (simp flip: diff_divide_distrib)
      finally have interval_img: "(\<lambda>t. (t - a)/(b - a)) ` {a..b} = {0..1}" .
      have lin: "(\<lambda>t. g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)) ` {a..b} = closed_segment (g a) (g b)"
      proof -
        have "(\<lambda>t. g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)) ` {a..b}
            = (\<lambda>u. g a + u *\<^sub>R (g b - g a)) ` ((\<lambda>t. (t-a)/(b-a)) ` {a..b})"
          by (simp add: image_image)
        also have "\<dots> = closed_segment (g a) (g b)"
          by (simp add: image_image interval_img closed_segment_image_interval algebra_simps cong: image_cong)
        finally show ?thesis .
      qed
      have hh_eq_lin: "\<And>t. t \<in> {a..b} \<Longrightarrow> h t = g a + ((t - a)/(b - a)) *\<^sub>R (g b - g a)"
        using \<open>a < b\<close> by (auto simp: h_def)
      have hh_seg: "h ` {a..b} = closed_segment (g a) (g b)"
        by (simp add: hh_eq_lin lin)
      have a_ge0: "0 \<le> a" and b_le1: "b \<le> 1" using ab01 by auto
      have hh_0: "h 0 = g 0" using a_ge0 by (simp add: h_def)
      have hh_1: "h 1 = g 1" using b_le1 by (simp add: h_def)
      have hh_start: "pathstart h = pathstart g" by (simp add: pathstart_def hh_0)
      have hh_finish: "pathfinish h = pathstart g"
        using assms(2) by (simp add: pathstart_def pathfinish_def hh_1)
      have hh_frontier: "h ` {a..b} \<subseteq> frontier (convex hull path_image g)"
        using hh_seg seg_in_frontier by simp
      have hh_out_img: "h ` ({0..1} - {a<..<b}) = g ` ({0..1} - {a<..<b})"
        by (meson Diff_iff h_def image_cong)
      have univ: "{0..1} = {a..b} \<union> ({0..1} - {a<..<b})"
        using ab01 \<open>a < b\<close> by auto
      have pi_h: "path_image h = closed_segment (g a) (g b) \<union> g ` ({0..1} - {a<..<b})"
        by (metis hh_out_img hh_seg image_Un path_defs(4) univ)
      have front_in_hull: "frontier (convex hull path_image g) \<subseteq> convex hull path_image g"
        using hull_closed by (simp add: frontier_def closure_closed)
      have seg_in: "closed_segment (g a) (g b) \<subseteq> convex hull path_image g"
        using seg_in_frontier front_in_hull by (rule subset_trans)
      have out_in: "g ` ({0..1} - {a<..<b}) \<subseteq> convex hull path_image g"
        using arcs(8) g1_in_hull by blast
      have hull_hh: "convex hull (path_image h) = convex hull (path_image g)"
        using hull_seg_eq pi_h by argo
      have L_nonneg: "0 \<le> L"
      proof -
        have le: "dist (g a) (g b) \<le> L * dist a b" using assms(3) ab01 by blast
        then have "0 \<le> L * dist a b" by (smt (verit) zero_le_dist) 
        with \<open>a < b\<close> show ?thesis by (simp add: zero_le_mult_iff)
      qed
      have dab: "dist (g a) (g b) \<le> L * (b - a)"
        by (smt (verit) assms(3,4,5,6) dist_real_def)
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
          using \<open>a<b\<close> dab by (simp add: dist_norm norm_minus_commute divide_simps)
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
        by (smt (verit) ab01(1) atLeastAtMost_iff hh_lo lip_g lipschitz_on_def)
      have lip_hi: "L-lipschitz_on {b..1} h"
        by (smt (verit) ab01(2) atLeastAtMost_iff hh_hi lip_g lipschitz_on_def)
      have "L-lipschitz_on {0..b} (\<lambda>x. if x \<le> a then h x else h x)"
        using lip_lo lip_mid by (rule lipschitz_on_concat) simp
      then have lip_lomid: "L-lipschitz_on {0..b} h" by simp      
      have "L-lipschitz_on {0..1} (\<lambda>x. if x \<le> b then h x else h x)"
        using lip_lomid lip_hi by (rule lipschitz_on_concat) simp
      then have lip_hh: "L-lipschitz_on {0..1} h" by simp
      have path_hh: "path h"
        using lip_hh by (simp add: path_def lipschitz_on_continuous_on)
      have g1_img: "g ` ({0..1} - {a<..<b}) = path_image g1" using arcs(8) by simp
      have opse_in_d0: "open_segment (g a) (g b) \<subseteq> path_image d0"
        using d0_eq_seg by (simp add: open_segment_def)
      have opse_g1_disj: "open_segment (g a) (g b) \<inter> path_image g1 = {}"
        by (metis Int_Diff d0_eq_seg d_split(11) inf_commute insert_commute open_segment_def)
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
        using hh_in_opse hh_out_in_g1 opse_g1_disj by fastforce
      have loopfree_hh: "loop_free h"
        unfolding loop_free_def by (metis gloopD h_def hh_inj_mid testM1)
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
          have elem: "norm (f (Sup k) - f (Inf k)) \<le> M * content k" if k: "k \<in> D" for k
          proof -
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
            by (metis D additive_content_division box_real(2))
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
        using vector_variation_combine has_bounded_variation_on_combine
        by (metis a_ge0 ab01(2) assms(4) atLeastAtMost_iff bv_hh less_eq_real_def)
      have split_g: "vector_variation {0..1} g = vector_variation {0..a} g + vector_variation {a..b} g + vector_variation {b..1} g"
        using vector_variation_combine has_bounded_variation_on_combine
        by (metis a_ge0 ab01(2) assms(4) atLeastAtMost_iff bv_g less_eq_real_def)
      have lo_eq: "vector_variation {0..a} h = vector_variation {0..a} g"
        by (rule vector_variation_cong) (simp add: hh_lo)
      have hi_eq: "vector_variation {b..1} h = vector_variation {b..1} g"
        by (rule vector_variation_cong) (simp add: hh_hi)
      have hh_a: "h a = g a" using \<open>a<b\<close> by (simp add: h_def)
      have hh_b: "h b = g b" using \<open>a<b\<close> by (simp add: h_def)
      have mid_hh_ge: "vector_variation {a..b} h \<ge> norm (g b - g a)"
        using vector_variation_ge_norm_function[OF bv_hh_ab, of b a] \<open>a<b\<close> hh_a hh_b
        by (simp add: norm_minus_commute)
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
          have content_elem: "(Sup k - Inf k) = content k" if k: "k \<in> D" for k
            using division_ofD(3,4)[OF D k] by force
          have "(\<Sum>k\<in>D. norm (h (Sup k) - h (Inf k))) =  ((\<Sum>k\<in>D. (Sup k - Inf k))/(b-a)) * norm (g b - g a)"
            using elem by (simp add: sum_distrib_right sum_divide_distrib)
          also have "(\<Sum>k\<in>D. (Sup k - Inf k)) = (\<Sum>k\<in>D. content k)"
            by (rule sum.cong[OF refl]) (rule content_elem)
          also have "(\<Sum>k\<in>D. content k) = content {a..b}"
            by (metis D additive_content_division box_real(2))
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
        using seg_in_frontier c_mem assms(9) by blast
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
        by (simp add: hi_eq lo_eq mid_g_gt mid_hh_eq path_length_def split_g split_hh)
      have lip_show: "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> dist (h x) (h y) \<le> L * dist x y"
        using lipschitz_onD[OF lip_hh] .
      have hh_agree: "\<And>x. x \<notin> {a<..<b} \<Longrightarrow> h x = g x" using hh_out_g .
      show thesis
        using that[OF simple_hh hh_start hh_finish lip_show path_length_lt hull_hh hh_agree hh_frontier] .
    qed
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
    using g0F g1F by (auto simp: s_def less_eq_real_def)
  have "openin (top_of_set {0..1}) ({0..1} \<inter> \<gamma> -` (- F))"
    using cont\<gamma> clF by (intro continuous_openin_preimage_gen) auto
  moreover have "{0..1} \<inter> \<gamma> -` (- F) = s" unfolding s_def by auto
  ultimately have s_openin: "openin (top_of_set {0..1}) s" by simp
  have "openin (top_of_set {0<..<1}) s"
    using s_openin s_sub by (metis greaterThanLessThan_subseteq_atLeastAtMost_iff openin_subset_trans order_refl)
  then have opens: "open s" by (metis open_greaterThanLessThan openin_open_trans)
  have s_ne: "s \<noteq> {}"
    using False by (auto simp: s_def F_def path_image_def)
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
    have q_interval: "q n = {Inf (q n)<..<Sup (q n)}" for n
    proof -
      have nem: "q n \<noteq> {}" using q_comp in_components_nonempty by blast
      have bd: "bounded (q n)" using qsub s_bdd bounded_subset by blast
      show "q n = {Inf (q n)<..<Sup (q n)}" using nem bd
        by (metis comp_open in_components_maximal open_bounded_connected_real_is_interval q_comp)
    qed
    define a where "a = (\<lambda>n. Inf (q n))"
    define b where "b = (\<lambda>n. Sup (q n))"
    have qab: "\<And>n. q n = {a n<..<b n}" using q_interval by (simp add: a_def b_def)
    have ablt: "\<And>n. a n < b n"
      using q_comp in_components_nonempty qab
      by (metis greaterThanLessThan_empty linorder_not_less)
    have clq: "\<And>n. closure (q n) = {a n..b n}" using qab ablt by (simp add: closure_greaterThanLessThan)
    have cls01: "closure s \<subseteq> {0..1}"
      using s_sub closure_mono[of s "{0<..<1}"] closure_greaterThanLessThan[of "0::real" 1] by simp
    have ab01: "a n \<in> {0..1} \<and> b n \<in> {0..1}" for n
    proof -
      have sub: "{a n..b n} \<subseteq> {0..1}"
        by (metis closure_mono clq cls01 qsub subset_trans) 
      then show ?thesis using sub using ablt[of n] by auto
    qed
    have a_notin: "a n \<notin> s" for n
    proof 
      assume ains: "a n \<in> s" 
      have sub: "{a n..<b n} \<subseteq> s"
      proof
        fix x assume "x \<in> {a n..<b n}"
        then have "x = a n \<or> x \<in> {a n<..<b n}" by auto
        then show "x \<in> s" using ains qab qsub by blast
      qed
      moreover have "{a n..<b n} \<noteq> {}" using ablt[of n] by auto
      moreover have "q n \<subseteq> {a n..<b n}" using qab by auto
      ultimately have "{a n..<b n} = q n"
        using connected_Ico q_comp[of n] in_components_maximal connected_Ioc by metis
      then show False using ablt[of n] qab by (metis atLeastLessThan_iff greaterThanLessThan_iff less_irrefl order_refl)
    qed
    have b_notin: "b n \<notin> s" for n
    proof
      assume bins: "b n \<in> s" 
      have sub: "{a n<..b n} \<subseteq> s"
      proof
        fix x assume "x \<in> {a n<..b n}"
        then have "x = b n \<or> x \<in> {a n<..<b n}" by auto
        then show "x \<in> s" using bins qab qsub by blast
      qed
      moreover have "{a n<..b n} \<noteq> {}" using ablt[of n] by auto
      moreover have "q n \<subseteq> {a n<..b n}" using qab by auto
      ultimately have "{a n<..b n} = q n"
        using q_comp[of n] in_components_maximal connected_Ioc by metis
      then show False using ablt[of n] qab by (metis greaterThanAtMost_iff greaterThanLessThan_iff less_irrefl order_refl)
    qed
    have gaF: "\<And>n. \<gamma> (a n) \<in> F"
      using a_notin ab01 s_def by blast
    have gbF: "\<And>n. \<gamma> (b n) \<in> F"
      using ab01 b_notin s_def by blast
    have comp_eq: "components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
      using full_SetCompr_eq q_range qab by force
    show "\<exists>a b::nat\<Rightarrow>real. (\<forall>n. a n \<in> {0..1}) \<and> (\<forall>n. b n \<in> {0..1}) \<and> (\<forall>n. a n \<le> b n) \<and> (\<forall>n. \<gamma> (a n) \<in> F) \<and> (\<forall>n. \<gamma> (b n) \<in> F) \<and> components s = {{a n<..<b n} | n. n \<in> (UNIV::nat set)}"
      using ab01 ablt gaF gbF comp_eq by (intro exI[of _ a] exI[of _ b]) (auto simp: less_imp_le)
  qed
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
    using U_def arc_in_s by blast
  have an_notin_s: "\<And>n. a n \<notin> s" using gaF s_def by blast
  have bn_notin_s: "\<And>n. b n \<notin> s" using gbF s_def by blast
  have an_notin_U: "\<And>n. a n \<notin> U n" using an_notin_s U_sub_s by blast
  have bn_notin_U: "\<And>n. b n \<notin> U n" using bn_notin_s U_sub_s by blast
  have arc_sub_U: "\<And>i j::nat. i < j \<Longrightarrow> {a i<..<b i} \<subseteq> U j"
    using U_def by blast
  have U_mem: "\<And>x n. x \<in> U n \<Longrightarrow> \<exists>i<n. x \<in> {a i<..<b i}"
    using U_def by blast
  have arc_disj: "\<And>i j. {a i<..<b i} \<noteq> {a j<..<b j} \<Longrightarrow> {a i<..<b i} \<inter> {a j<..<b j} = {}"
    using arc_comp components_nonoverlap by blast
  have arc_disj_U: "\<And>n. \<not> {a n<..<b n} \<subseteq> U n \<Longrightarrow> {a n<..<b n} \<inter> U n = {}"
    using U_mem arc_disj arc_sub_U by blast
  have F_eq: "F = frontier (convex hull (path_image \<gamma>))" by (simp add: F_def)
  \<comment> \<open>Inductive step: straighten the @{term n}-th arc with \<open>step_lemma\<close> (unless it is empty or already
     handled), preserving the invariant.\<close>
  have step: "\<exists>h'. P (Suc n) h' \<and> (\<forall>x. \<not>(x \<in> {a n<..<b n} \<and> x \<notin> U n) \<longrightarrow> h' x = h x)"
    if Ph: "P n h" for n h
  proof -
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
        using arc_off_F hF harc by auto
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
        by (metis arc_off_F h'off hUF harc)
      have h'UF: "h' x \<in> F" if "x \<in> U (Suc n)" for x
        using that USuc h'agree h'arcF hF hUF by auto
      have h'offSuc: "\<And>x. x \<notin> U (Suc n) \<Longrightarrow> h' x = \<gamma> x"
        by (simp add: USuc h'agree hoff)
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
  have "\<exists>y. eventually (\<lambda>n. f n x = y) sequentially"
    if x01: "x \<in> {0..1}" for x
      \<comment> \<open>For each parameter @{term x} the sequence @{term "f n x"} is eventually constant: either @{term x} lies in no arc
     (so $f\,n\,x = \gamma\,x$ throughout), or it lies in the arc with least index @{term N}, after which @{term f} is fixed.\<close>
  proof (cases "\<exists>n. x \<in> {a n<..<b n}")
    case False
    have stab: "f n x = f 0 x" for n
    proof (induct n)
      case 0 show ?case by simp
    next
      case (Suc n)
      then show ?case using Suc fstep False
        by presburger
    qed
    then show ?thesis
      using eventuallyI by blast
  next
    case True
    define N where "N = (LEAST n. x \<in> {a n<..<b n})"
    have xN: "x \<in> {a N<..<b N}" using True LeastI_ex N_def by (metis (mono_tags, lifting))
    have stab2: "\<And>m. N < m \<Longrightarrow> f (Suc m) x = f m x"
      using arc_sub_U fstep xN by blast
    have stab3: "\<And>d. f (Suc N + d) x = f (Suc N) x"
    proof -
      fix d show "f (Suc N + d) x = f (Suc N) x"
      by (induct d; use stab2 in force)
    qed
    have "eventually (\<lambda>n. f n x = f (Suc N) x) sequentially"
      using eventually_sequentiallyI[where c="Suc N"]
      by (metis (mono_tags, lifting) nat_le_iff_add stab3)
    then show ?thesis by blast
  qed
  then obtain h where h: "\<And>x. x \<in> {0..1} \<Longrightarrow> eventually (\<lambda>n. f n x = h x) sequentially"
    by metis
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
  have hlip: "dist (h x) (h y) \<le> path_length \<gamma> * dist x y"
    if xy: "x \<in> {0..1}" "y \<in> {0..1}" for x y
  proof -
    have ev: "eventually (\<lambda>n. f n x = h x \<and> f n y = h y) sequentially"
      using h[OF xy(1)] h[OF xy(2)] by eventually_elim simp
    then obtain n where n: "f n x = h x" "f n y = h y"
      unfolding eventually_sequentially by auto
    then show ?thesis 
      by (metis flip xy)
  qed
  have hrect: "rectifiable_path h"
    by (metis Rectifiable_Path.lipschitz_imp_rectifiable_path dist_norm hlip)
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
      then show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
        using fsimple[of n] xy unfolding simple_path_def loop_free_def eq by presburger
    qed
  qed
  have hloop: "pathfinish h = pathstart h"
  proof -
    have z01: "(0::real) \<in> {0..1}" and o01: "(1::real) \<in> {0..1}" by auto
    have ev: "eventually (\<lambda>n. f n 0 = h 0 \<and> f n 1 = h 1) sequentially"
      using h[OF z01] h[OF o01] by eventually_elim simp
    then obtain n where n: "f n 0 = h 0" "f n 1 = h 1"
      unfolding eventually_sequentially by auto
    then show ?thesis
      by (metis assms(3) fpf fps pathstart_def pathfinish_def)
  qed
  have hlen: "path_length h \<le> path_length \<gamma>"
    by (rule path_length_lipschitz[where B="path_length \<gamma>"])
       (use hlip in \<open>simp add: dist_norm\<close>)
  \<comment> \<open>The image of @{term h} lies on the frontier: each parameter either lands in an arc (so eventually
     in @{term F}) or maps via @{term \<gamma>} to a point already on the frontier.\<close>
  have notarc_notin_s: "\<And>x. (\<nexists>n. x \<in> {a n<..<b n}) \<Longrightarrow> x \<notin> s"
    by (smt (verit) Union_components Union_iff comps mem_Collect_eq)
  have hx_in_F: "h x \<in> F" if x01: "x \<in> {0..1}" for x
  proof (cases "\<exists>n. x \<in> {a n<..<b n}")
    case True
    then obtain n where xn: "x \<in> {a n<..<b n}" by blast
    obtain N where "\<And>m. N \<le> m \<Longrightarrow> f m x = h x" 
      using h[OF x01] unfolding eventually_sequentially by blast
    with xn arc_sub_U show ?thesis
      by (metis fUF less_eq_Suc_le nle_le subsetD)
  next
    case False
    obtain n where n: "f n x = h x" using h[OF x01] unfolding eventually_sequentially by blast
    have "x \<notin> U n" using False U_mem by blast
    then show "h x \<in> F" using n
      using False foff notarc_notin_s s_def that by force
  qed
  have hsub_F: "path_image h \<subseteq> F" using hx_in_F by (auto simp: path_image_def)
  \<comment> \<open>Off the arcs, @{term h} still agrees with @{term \<gamma>}; so @{term \<gamma>}'s image outside the deviating set @{term s} is part of
     the image of @{term h}.\<close>
  have arcs_eq_s: "\<Union> {{a n<..<b n} | n. n \<in> UNIV} = s"
    using comps Union_components by metis
  have hoff_s: "h x = \<gamma> x" if x01: "x \<in> {0..1}" and xs: "x \<notin> s" for x
  proof -
    obtain n where "f n x = h x" using h[OF x01] unfolding eventually_sequentially by blast
    then show "h x = \<gamma> x"
      by (metis U_sub_s subsetD foff xs)
  qed
  have gout_sub_h: "\<gamma> ` ({0..1} - s) \<subseteq> path_image h"
    using hoff_s by (force simp: path_image_def)
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
      then show "z \<in> convex hull (path_image \<gamma>)" using x(2)
        by (metis fhull hull_inc)
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
    have ext_in_out: "z \<in> \<gamma> ` ({0..1} - s)" if "z extreme_point_of (convex hull path_image \<gamma>)" for z
    proof -
      have zpig: "z \<in> path_image \<gamma>" using extreme_point_of_convex_hull[OF that] .
      then obtain x where x: "x \<in> {0..1}" "z = \<gamma> x" by (auto simp: path_image_def)
      have znotint: "z \<notin> interior (convex hull path_image \<gamma>)" 
        using extreme_point_not_in_interior[OF that] .
      have "z \<in> F"
        by (metis Diff_iff F_def closure_subset frontier_def hull_subset subsetD znotint zpig)
      then show "z \<in> \<gamma> ` ({0..1} - s)" using x s_def by blast
    qed
    have "{x. x extreme_point_of (convex hull path_image \<gamma>)} \<subseteq> \<gamma> ` ({0..1} - s)"
      using ext_in_out by blast
    then show "convex hull (path_image \<gamma>) \<subseteq> convex hull (path_image h)"
      by (metis dual_order.trans gout_sub_h hull_mono km_g) 
  qed
  \<comment> \<open>The image of @{term h} is exactly the frontier: $\subseteq$ is \<open>hsub_F\<close>; $\supseteq$ because @{term h} is a simple closed
     curve whose image lies on the frontier of its (now equal) convex hull.\<close>
  have hF: "frontier (convex hull (path_image h)) = F" using hhull F_eq by simp
  have h_image_F: "path_image h = F"
    using frontier_convex_hull_subset_path_image hF hloop hsimple hsub_F by blast
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
  \<comment> \<open>Some point of the loop lies on the frontier (an extreme point of the convex hull).\<close>
  have pathg: "path g" using assms(2) by (rule simple_path_imp_path)
  have cpt: "compact (convex hull path_image g)"
    by (simp add: compact_convex_hull compact_path_image pathg)
  obtain x where x_ext: "x extreme_point_of (convex hull path_image g)"
    using cpt extreme_point_exists_convex by fastforce
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
  \<comment> \<open>Strengthened version, assuming the loop starts on the frontier of its convex hull.
     (Here used to derive the general statement by shifting the basepoint.)\<close>
  have *: "\<exists>h. rectifiable_path h \<and> simple_path h \<and> pathfinish h = pathstart h \<and> 
               path_length h \<le> path_length \<gamma> \<and> convex hull (path_image h) = convex hull (path_image \<gamma>) \<and> path_image h = frontier (convex hull (path_image \<gamma>))"
    if Grect: "rectifiable_path \<gamma>" and Gsimple: "simple_path \<gamma>"
      and Gloop: "pathfinish \<gamma> = pathstart \<gamma>"
      and Gfr: "pathstart \<gamma> \<in> frontier (convex hull (path_image \<gamma>))" for \<gamma> :: "real \<Rightarrow> complex"
    using arc_length_reparametrization[of \<gamma>] convexification_unit_speed 
    by (smt (verit, best) that)
  show ?thesis
    using *[OF sp_rect sp_simple sp_loop sp_startfr]
    by (metis sp_len sp_pi that) 
qed

theorem isoperimetric_convexification_strict:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "rectifiable_path g" "simple_path g" "pathfinish g = pathstart g" "\<not> convex (inside (path_image g))"
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
    have conn: "connected (- ?C)" using bdd_hull by (simp add: connected_complement_bounded_convex)
    have unbdd: "\<not> bounded (- ?C)"
      by (simp add: bdd_hull cobounded_imp_unbounded)
    have "(?C - path_image g) \<union> (- ?C) = - path_image g"
      using hull_subset by force
    then have "inside (path_image g) \<subseteq> ?C" using inside_subset[OF conn unbdd] by blast
    moreover have "open (inside (path_image g))" using assms(2) 
      by (simp add: open_inside closed_simple_path_image)
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
    by (simp add: bdd_hull ins_h lmeasurable_interior)
  \<comment> \<open>The path image is not contained in the frontier of its convex hull (else \<open>inside g\<close>
      would be convex), so it meets the interior of the hull.\<close>
  have not_sub: "\<not> path_image g \<subseteq> frontier (convex hull (path_image g))"
    using assms frontier_convex_hull_subset_path_image h(6) ins_h by fastforce
  have pig_hull: "path_image g \<subseteq> convex hull (path_image g)" by (rule hull_subset)
  obtain x where x_pig: "x \<in> path_image g" and "x \<notin> frontier (convex hull (path_image g))"
    using not_sub by blast
  then have x_int: "x \<in> interior (convex hull (path_image g))"
    by (simp add: compact_path_image frontier_def hull_inc pathg)
  have jordan_g: "inside (path_image g) \<noteq> {} \<and> open (inside (path_image g)) \<and> connected (inside (path_image g)) \<and>
      outside (path_image g) \<noteq> {} \<and> open (outside (path_image g)) \<and> connected (outside (path_image g)) \<and>
      frontier (inside (path_image g)) = path_image g \<and> frontier (outside (path_image g)) = path_image g"
    using Jordan_inside_outside[OF assms(2,3)] by blast
  \<comment> \<open>Find a frontier point \<open>x\<close> of \<open>g\<close> in the hull interior; \<open>frontier_straddle\<close> gives a nearby
      outside point \<open>y\<close>, and a ball about \<open>y\<close> lies in \<open>outside g \<inter> interior(hull)\<close>.\<close>
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
    by (smt (verit) DiffI IntE disjoint_iff inf.absorb_iff2 ins_h io_disj r2(2) subsetI)
  \<comment> \<open>A nonempty ball has positive measure, so the difference does too.\<close>
  have ball_pos: "measure lebesgue (ball y r2) > 0"
    by (simp add: r2(1))
  have diff_meas: "inside (path_image h) - inside (path_image g) \<in> lmeasurable"
    using meas_ins_h meas_ins_g by (simp add: fmeasurable.Diff)
  have diff_pos: "measure lebesgue (inside (path_image h) - inside (path_image g)) > 0"
    by (metis ball_sub diff_meas ball_pos negligible_iff_measure negligible_subset zero_less_measure_iff)
  have meas_eq: "measure lebesgue (inside (path_image h) - inside (path_image g)) =
      measure lebesgue (inside (path_image h)) - measure lebesgue (inside (path_image g))"
    using measurable_measure_Diff[OF meas_ins_h _ ins_g_sub_h] meas_ins_g by (simp add: fmeasurableD)
  have strict: "measure lebesgue (inside (path_image g)) < measure lebesgue (inside (path_image h))"
    using diff_pos meas_eq by linarith
  show ?thesis
    using h strict that by blast
qed

section \<open>The isoperimetric theorem\<close>

theorem isoperimetric_theorem:
  fixes g :: "real \<Rightarrow> complex"
  assumes "rectifiable_path g" "simple_path g"
    "pathfinish g = pathstart g"
    "path_length g = L"
  shows "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow>
      \<exists>a r. path_image g = sphere a r"
proof -
  have "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi) \<and> 
        (measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<longrightarrow>
      (\<exists>a r. path_image g = sphere a r))"
  proof (cases "convex (inside (path_image g))")
    case True
    show ?thesis
      using True assms isoperimetric_theorem_convex by blast
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
  then show "measure lebesgue (inside (path_image g)) \<le> L\<^sup>2 / (4 * pi)"
    and "measure lebesgue (inside (path_image g)) = L\<^sup>2 / (4 * pi) \<Longrightarrow> \<exists>a r. path_image g = sphere a r"
    by auto
qed

end
