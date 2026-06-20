theory Arc_Length_Reparametrization
  imports "HOL-Analysis.Rectifiable_Path"
begin

text \<open>
  Arc length reparametrization for rectifiable paths, following HOL Light's
  @{text "Multivariate/integration.ml"} (lines 24391--24980).

  Given a rectifiable path @{term g}, there exists a reparametrization @{term h}
  that is Lipschitz with constant @{term "path_length g"}, preserves the path image,
  and has the property that arc length grows linearly with the parameter.
\<close>

section \<open>Reparametrization\<close>

lemma rectifiable_path_reparametrization:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "rectifiable_path g"
    "continuous_on {0..1} \<phi>" "\<phi> ` {0..1} \<subseteq> {0..1}"
    "\<phi> 0 = 0" "\<phi> 1 = 1"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> x \<le> y \<Longrightarrow> \<phi> x \<le> \<phi> y"
  shows "rectifiable_path (g \<circ> \<phi>)"
proof -
  have g_path: "path g" and g_bv: "has_bounded_variation_on g {0..1}"
    using assms(1) unfolding rectifiable_path_def by auto
  have mono: "mono_on {0..1} \<phi>"
    unfolding mono_on_def using assms(6) by auto
  show ?thesis
    unfolding rectifiable_path_def
  proof
    show "path (g \<circ> \<phi>)"
      unfolding path_def
      using continuous_on_compose[OF assms(2)] g_path
      by (meson assms(3) continuous_on_subset path_def)
  next
    have "has_bounded_variation_on g {\<phi> 0..\<phi> 1}"
      using g_bv assms(4,5) by simp
    then show "has_bounded_variation_on (g \<circ> \<phi>) {0..1}"
      using has_bounded_variation_compose_monotone(1)[OF _ mono] assms(4,5) by simp
  qed
qed

lemma path_length_reparametrization:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "rectifiable_path g"
    "continuous_on {0..1} \<phi>" "\<phi> ` {0..1} \<subseteq> {0..1}"
    "\<phi> 0 = 0" "\<phi> 1 = 1"
    "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> x \<le> y \<Longrightarrow> \<phi> x \<le> \<phi> y"
  shows "path_length (g \<circ> \<phi>) = path_length g"
proof -
  have g_bv: "has_bounded_variation_on g {0..1}"
    using assms(1) unfolding rectifiable_path_def by auto
  have mono: "mono_on {0..1} \<phi>"
    unfolding mono_on_def using assms(6) by auto
  \<comment> \<open>Upper bound: monotone composition decreases variation\<close>
  have upper: "vector_variation {0..1} (g \<circ> \<phi>) \<le> vector_variation {0..1} g"
    using has_bounded_variation_compose_monotone(2)[OF _ mono] g_bv assms(4,5) by simp
  \<comment> \<open>Lower bound: construct monotone right inverse \<psi> of \<phi>\<close>
  have \<phi>_surj: "\<phi> ` {0..1} = {0..1}"
  proof (rule antisym)
    show "\<phi> ` {0..1} \<subseteq> {0..1}" using assms(3) .
  next
    show "{0..1} \<subseteq> \<phi> ` {0..1}"
    proof
      fix s :: real assume s01: "s \<in> {0..1}"
      show "s \<in> \<phi> ` {0..1}"
        using IVT'[of \<phi> 0 s 1] assms(2,4,5) s01
        by (auto intro: continuous_on_subset[OF assms(2)])
    qed
  qed
  define \<psi> where "\<psi> s = (SOME t. t \<in> {0..1} \<and> \<phi> t = s)" for s
  have \<psi>_prop: "\<psi> s \<in> {0..1} \<and> \<phi> (\<psi> s) = s" if "s \<in> {0..1}" for s
  proof -
    from \<phi>_surj that have "s \<in> \<phi> ` {0..1}" by auto
    then obtain t where "t \<in> {0..1}" "\<phi> t = s" by auto
    then have "\<exists>t. t \<in> {0..1} \<and> \<phi> t = s" by auto
    then show ?thesis unfolding \<psi>_def by (rule someI_ex)
  qed
  have \<psi>_in: "\<psi> s \<in> {0..1}" if "s \<in> {0..1}" for s
    using \<psi>_prop[OF that] by auto
  have \<phi>\<psi>: "\<phi> (\<psi> s) = s" if "s \<in> {0..1}" for s
    using \<psi>_prop[OF that] by auto
  have \<psi>_mono: "mono_on {0..1} \<psi>"
  proof (rule mono_onI)
    fix s1 s2 :: real
    assume s1: "s1 \<in> {0..1}" and s2: "s2 \<in> {0..1}" and le: "s1 \<le> s2"
    show "\<psi> s1 \<le> \<psi> s2"
    proof (rule ccontr)
      assume "\<not> \<psi> s1 \<le> \<psi> s2"
      then have gt: "\<psi> s2 < \<psi> s1" by linarith
      then have "\<phi> (\<psi> s2) \<le> \<phi> (\<psi> s1)"
        using assms(6)[OF \<psi>_in[OF s2] \<psi>_in[OF s1]] by linarith
      then have "s2 \<le> s1" using \<phi>\<psi>[OF s1] \<phi>\<psi>[OF s2] by simp
      then have "s1 = s2" using le by linarith
      then show False using gt by simp
    qed
  qed
  have \<psi>0: "\<psi> 0 \<in> {0..1}" using \<psi>_in by auto
  have \<psi>1: "\<psi> 1 \<in> {0..1}" using \<psi>_in by auto
  have bv_comp: "has_bounded_variation_on (g \<circ> \<phi>) {0..1}"
    using has_bounded_variation_compose_monotone(1)[OF _ mono] g_bv assms(4,5) by simp
  have lower: "vector_variation {0..1} g \<le> vector_variation {0..1} (g \<circ> \<phi>)"
  proof -
    have eq: "vector_variation {0..1} g = vector_variation {0..1} ((g \<circ> \<phi>) \<circ> \<psi>)"
    proof (rule vector_variation_cong)
      fix x :: real assume "x \<in> {0..1}"
      then show "g x = ((g \<circ> \<phi>) \<circ> \<psi>) x"
        using \<phi>\<psi> by (simp add: comp_def)
    qed
    have bv_sub: "has_bounded_variation_on (g \<circ> \<phi>) {\<psi> 0..\<psi> 1}"
      using has_bounded_variation_on_subset[OF bv_comp] \<psi>0 \<psi>1 by auto
    have "vector_variation {0..1} ((g \<circ> \<phi>) \<circ> \<psi>)
          \<le> vector_variation {\<psi> 0..\<psi> 1} (g \<circ> \<phi>)"
      using has_bounded_variation_compose_monotone(2)[OF bv_sub \<psi>_mono] .
    also have "\<dots> \<le> vector_variation {0..1} (g \<circ> \<phi>)"
      using vector_variation_monotone[OF bv_comp] \<psi>0 \<psi>1 by auto
    finally show ?thesis using eq by linarith
  qed
  show ?thesis
    unfolding path_length_def using upper lower by linarith
qed

section \<open>Uniqueness and minimality\<close>


lemma continuous_injective_on_interval_mono:
  fixes \<phi> :: "real \<Rightarrow> real"
  assumes cont: "continuous_on {a..b} \<phi>" and inj: "inj_on \<phi> {a..b}" and ab: "a < b"
  shows "(\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. x \<le> y \<longrightarrow> \<phi> x \<le> \<phi> y) \<or>
         (\<forall>x\<in>{a..b}. \<forall>y\<in>{a..b}. x \<le> y \<longrightarrow> \<phi> y \<le> \<phi> x)"
proof (cases "\<phi> a \<le> \<phi> b")
  case True
  \<comment> \<open>Show \<phi> is increasing\<close>
  have "\<phi> s \<le> \<phi> t" if st: "s \<in> {a..b}" "t \<in> {a..b}" "s \<le> t" for s t
  proof (rule ccontr)
    assume "\<not> \<phi> s \<le> \<phi> t"
    then have fs_gt_ft: "\<phi> t < \<phi> s" by linarith
    then have "s \<noteq> t" by auto
    then have st_lt: "s < t" using st(3) by linarith
    show False
    proof (cases "\<phi> t < \<phi> a")
      case True
      \<comment> \<open>\<phi>(t) < \<phi>(a) \<le> \<phi>(b), by IVT' on [t,b] get c with \<phi>(c) = \<phi>(a)\<close>
      have "\<exists>c\<ge>t. c \<le> b \<and> \<phi> c = \<phi> a"
        using IVT'[of \<phi> t "\<phi> a" b] True \<open>\<phi> a \<le> \<phi> b\<close> continuous_on_subset[OF cont] st
        by auto
      then obtain c where c: "c \<ge> t" "c \<le> b" "\<phi> c = \<phi> a" by auto
      have "c \<in> {a..b}" using c st by auto
      then have "c = a" using inj_onD[OF inj \<open>\<phi> c = \<phi> a\<close>] st by auto
      then show False using c(1) st_lt st(1) by auto
    next
      case False
      \<comment> \<open>\<phi>(a) \<le> \<phi>(t) < \<phi>(s), by IVT' on [a,s] get c with \<phi>(c) = \<phi>(t)\<close>
      then have "\<phi> a \<le> \<phi> t" by linarith
      have "\<exists>c\<ge>a. c \<le> s \<and> \<phi> c = \<phi> t"
        using IVT'[of \<phi> a "\<phi> t" s] \<open>\<phi> a \<le> \<phi> t\<close> fs_gt_ft continuous_on_subset[OF cont] st
        by auto
      then obtain c where c: "c \<ge> a" "c \<le> s" "\<phi> c = \<phi> t" by auto
      have "c \<in> {a..b}" using c st by auto
      then have "c = t" using inj_onD[OF inj \<open>\<phi> c = \<phi> t\<close>] st by auto
      then show False using c(2) st_lt by auto
    qed
  qed
  then show ?thesis by auto
next
  case False
  then have "\<not> \<phi> a \<le> \<phi> b" by simp
  then have fab: "\<phi> b < \<phi> a"
  proof -
    have "\<phi> a \<noteq> \<phi> b"
    proof
      assume "\<phi> a = \<phi> b"
      then have "a = b" using inj_onD[OF inj] ab by auto
      then show False using ab by auto
    qed
    then show ?thesis using \<open>\<not> \<phi> a \<le> \<phi> b\<close> by linarith
  qed
  \<comment> \<open>Show \<phi> is decreasing: symmetric argument\<close>
  have "\<phi> t \<le> \<phi> s" if st: "s \<in> {a..b}" "t \<in> {a..b}" "s \<le> t" for s t
  proof (rule ccontr)
    assume "\<not> \<phi> t \<le> \<phi> s"
    then have ft_gt_fs: "\<phi> s < \<phi> t" by linarith
    then have "s \<noteq> t" by auto
    then have st_lt: "s < t" using st(3) by linarith
    show False
    proof (cases "\<phi> s < \<phi> b")
      case True
      \<comment> \<open>\<phi>(s) < \<phi>(b) < \<phi>(a), by IVT2' on [a,s] get c with \<phi>(c) = \<phi>(b)\<close>
      have "\<exists>c\<ge>a. c \<le> s \<and> \<phi> c = \<phi> b"
        using IVT2'[of \<phi> s "\<phi> b" a] True fab
          continuous_on_subset[OF cont] st
        by auto
      then obtain c where c: "c \<ge> a" "c \<le> s" "\<phi> c = \<phi> b" by auto
      have "c \<in> {a..b}" using c st by auto
      then have "c = b" using inj_onD[OF inj \<open>\<phi> c = \<phi> b\<close>] st by auto
      then show False using c(2) st_lt st(2) by auto
    next
      case False
      \<comment> \<open>\<phi>(b) \<le> \<phi>(s) < \<phi>(t), by IVT2' on [t,b] get c with \<phi>(c) = \<phi>(s)\<close>
      then have "\<phi> b \<le> \<phi> s" by linarith
      have "\<exists>c\<ge>t. c \<le> b \<and> \<phi> c = \<phi> s"
        using IVT2'[of \<phi> b "\<phi> s" t] ft_gt_fs \<open>\<phi> b \<le> \<phi> s\<close>
          continuous_on_subset[OF cont] st
        by auto
      then obtain c where c: "c \<ge> t" "c \<le> b" "\<phi> c = \<phi> s" by auto
      have "c \<in> {a..b}" using c st by auto
      then have "c = s" using inj_onD[OF inj \<open>\<phi> c = \<phi> s\<close>] st by auto
      then show False using c(1) st_lt by auto
    qed
  qed
  then show ?thesis by auto
qed

lemma continuous_on_path_length_subpath_right:
  assumes "rectifiable_path g" "s \<in> {0..1}"
  shows "continuous_on {0..1} (\<lambda>t. path_length (subpath s t g))"
proof -
  have g_bv: "has_bounded_variation_on g {0..1}"
    using assms(1) unfolding rectifiable_path_def by auto
  have g_cont: "continuous_on {0..1} g"
    using assms(1) unfolding rectifiable_path_def path_def by auto
  define V where "V t = vector_variation {0..t} g" for t :: real
  have V_cont: "continuous_on {0..1} V"
    unfolding V_def continuous_on_eq_continuous_within
  proof
    fix c :: real assume c01: "c \<in> {0..1}"
    have "continuous (at c within {0..1}) (\<lambda>x. vector_variation {0..x} g) \<longleftrightarrow>
          continuous (at c within {0..1}) g"
      using vector_variation_continuous[OF g_bv c01] .
    moreover have "continuous (at c within {0..1}) g"
      using g_cont c01 unfolding continuous_on_eq_continuous_within by auto
    ultimately show "continuous (at c within {0..1}) (\<lambda>t. vector_variation {0..t} g)"
      by simp
  qed
  have V_mono: "V x \<le> V y" if "x \<in> {0..1}" "y \<in> {0..1}" "x \<le> y" for x y
  proof -
    have bv_0y: "has_bounded_variation_on g {0..y}"
      using has_bounded_variation_on_subset[OF g_bv] that by auto
    have "V y = V x + vector_variation {x..y} g"
      using vector_variation_combine[OF bv_0y] that unfolding V_def by auto
    moreover have "vector_variation {x..y} g \<ge> 0"
      using vector_variation_pos_le[OF has_bounded_variation_on_subset[OF g_bv]] that by auto
    ultimately show ?thesis by linarith
  qed
  have eq: "path_length (subpath s t g) = \<bar>V t - V s\<bar>"
    if t01: "t \<in> {0..1}" for t
  proof -
    have "path_length (subpath s t g) = vector_variation (closed_segment s t) g"
      using path_length_subpath_eq[OF assms(2) t01 assms(1)] .
    also have "\<dots> = \<bar>V t - V s\<bar>"
    proof (cases "s \<le> t")
      case True
      then have cs: "closed_segment s t = {s..t}" by (simp add: closed_segment_eq_real_ivl)
      have s_in: "s \<in> {0..t}" using assms(2) True by auto
      have bv_0t: "has_bounded_variation_on g {0..t}"
        using has_bounded_variation_on_subset[OF g_bv] t01 by auto
      have split: "V t = V s + vector_variation {s..t} g"
        using vector_variation_combine[OF bv_0t s_in] unfolding V_def by simp
      then have "vector_variation {s..t} g = V t - V s" by linarith
      moreover have "V s \<le> V t" using V_mono[OF assms(2) t01 True] .
      ultimately show ?thesis using cs by simp
    next
      case False
      then have ts: "t < s" by linarith
      then have cs: "closed_segment s t = {t..s}" by (simp add: closed_segment_eq_real_ivl)
      have t_in: "t \<in> {0..s}" using t01 ts by auto
      have bv_0s: "has_bounded_variation_on g {0..s}"
        using has_bounded_variation_on_subset[OF g_bv] assms(2) by auto
      have split: "V s = V t + vector_variation {t..s} g"
        using vector_variation_combine[OF bv_0s t_in] unfolding V_def by simp
      then have "vector_variation {t..s} g = V s - V t" by linarith
      moreover have "V t \<le> V s" using V_mono[OF t01 assms(2)] ts by linarith
      ultimately show ?thesis using cs by simp
    qed
    finally show ?thesis .
  qed
  have "continuous_on {0..1} (\<lambda>t. \<bar>V t - V s\<bar>)"
    by (intro continuous_intros V_cont)
  moreover have "continuous_on {0..1} (\<lambda>t. \<bar>V t - V s\<bar>) = continuous_on {0..1} (\<lambda>t. path_length (subpath s t g))"
    by (rule continuous_on_cong[OF refl]) (use eq in auto)
  ultimately show ?thesis by simp
qed

lemma continuous_on_path_length_subpath_left:
  assumes "rectifiable_path g" "t \<in> {0..1}"
  shows "continuous_on {0..1} (\<lambda>s. path_length (subpath s t g))"
proof -
  have eq: "path_length (subpath s t g) = path_length (subpath t s g)"
    if "s \<in> {0..1}" for s
  proof -
    have "path_length (subpath s t g) = vector_variation (closed_segment s t) g"
      using path_length_subpath_eq[OF that assms(2) assms(1)] .
    also have "\<dots> = vector_variation (closed_segment t s) g"
      by (simp add: closed_segment_commute)
    also have "\<dots> = path_length (subpath t s g)"
      using path_length_subpath_eq[OF assms(2) that assms(1)] by simp
    finally show ?thesis .
  qed
  have "continuous_on {0..1} (\<lambda>s. path_length (subpath t s g))"
    using continuous_on_path_length_subpath_right[OF assms] .
  moreover have "\<And>s. s \<in> {0..1} \<Longrightarrow> path_length (subpath t s g) = path_length (subpath s t g)"
    using eq by simp
  ultimately show ?thesis
    using continuous_on_cong[OF refl, of "{0..1}" "\<lambda>s. path_length (subpath t s g)" "\<lambda>s. path_length (subpath s t g)"]
    by auto
qed

end
