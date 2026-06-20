theory Rectifiable_Path
  imports Absolute_Continuity
begin

text \<open>
  Rectifiable paths and arc length, following HOL Light's
  @{text "Multivariate/integration.ml"} (lines 23827--25750).

  A path is rectifiable iff it is continuous and has bounded variation on
  @{term "{0..1}"}. The path length is the vector variation on that interval.
\<close>

section \<open>Basic properties\<close>

lemma rectifiable_path_imp_path:
  "rectifiable_path g \<Longrightarrow> path g"
  unfolding rectifiable_path_def by simp

lemma path_length_pos_le:
  "rectifiable_path g \<Longrightarrow> 0 \<le> path_length g"
  unfolding rectifiable_path_def path_length_def
  by (auto intro: vector_variation_pos_le)

lemma path_length_eq_0:
  "rectifiable_path g \<Longrightarrow>
    (path_length g = 0 \<longleftrightarrow> (\<exists>c. \<forall>t \<in> {0..1}. g t = c))"
  unfolding rectifiable_path_def path_length_def
  by (rule vector_variation_const_eq) auto

lemma simple_path_length_pos_lt:
  "rectifiable_path g \<Longrightarrow> simple_path g \<Longrightarrow> 0 < path_length g"
 proof -
  assume rect: "rectifiable_path g" and sp: "simple_path g"
  have "path_length g \<noteq> 0"
  proof
    assume "path_length g = 0"
    then obtain c where c: "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = c"
      using path_length_eq_0[OF rect] by auto
    hence "g (1/4) = g (3/4)" by auto
    moreover from sp have "inj_on g {0<..<1}" by (rule simple_path_inj_on)
    ultimately have "(1/4::real) = 3/4"
      by (auto dest: inj_onD)
    thus False by simp
  qed
  with path_length_pos_le[OF rect] show "0 < path_length g"
    by linarith
 qed

section \<open>Invariance under transformations\<close>

lemma rectifiable_path_translation_eq:
  "rectifiable_path ((\<lambda>x. a + x) \<circ> g) \<longleftrightarrow> rectifiable_path g"
proof -
  have "path g"
    if "path (\<lambda>x. a + g x)"
      and "has_bounded_variation_on (\<lambda>x. a + g x) {0..1}"
    using that path_translation_eq[of a g] by (simp add: o_def)
  moreover have "has_bounded_variation_on g {0..1}"
    if "path (\<lambda>x. a + g x)"
      and "has_bounded_variation_on (\<lambda>x. a + g x) {0..1}"
  proof -
    have "has_bounded_variation_on (\<lambda>x. a + g x + (- a)) {0..1}"
      using that(2) has_bounded_variation_on_const[of "-a" "{0..1}"]
      by (rule has_bounded_variation_on_add)
    then show ?thesis by simp
  qed
  moreover have "path (\<lambda>x. a + g x)"
    if "path g"
      and "has_bounded_variation_on g {0..1}"
    using that path_translation_eq[of a g] by (simp add: o_def)
  moreover have "has_bounded_variation_on (\<lambda>x. a + g x) {0..1}"
    if "path g"
      and "has_bounded_variation_on g {0..1}"
    using that(2) has_bounded_variation_on_const[of a "{0..1}"]
    by (auto intro: has_bounded_variation_on_add)
  ultimately show ?thesis
    by (auto simp: o_def rectifiable_path_def)
qed

lemma path_length_translation:
  "path_length ((\<lambda>x. a + x) \<circ> g) = path_length g"
  unfolding path_length_def vector_variation_def comp_def
  by (simp add: algebra_simps)

lemma has_bounded_variation_on_linear_image:
  assumes "linear f" "has_bounded_variation_on g {0..1}"
  shows "has_bounded_variation_on (f \<circ> g) {0..1}"
proof -
  have bl: "bounded_linear f" using assms(1) linear_conv_bounded_linear by auto
  have bound: "\<And>d. d division_of {0..1} \<Longrightarrow>
    (\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))
    \<le> onorm f * vector_variation {0..1} g"
  proof -
    fix d :: "real set set" assume div: "d division_of {0..1}"
    have "(\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))
      = (\<Sum>k\<in>d. norm (f (g (Sup k) - g (Inf k))))" 
      using assms(1) by (simp add: o_def linear_diff)
    also have "\<dots> \<le> (\<Sum>k\<in>d. onorm f * norm (g (Sup k) - g (Inf k)))" 
      by (intro sum_mono onorm[OF bl])
    also have "\<dots> = onorm f * (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))" 
      by (simp add: sum_distrib_left)
    also have "\<dots> \<le> onorm f * vector_variation {0..1} g" 
      by (intro mult_left_mono has_bounded_variation_works(1)[OF assms(2) div order_refl]
          onorm_pos_le[OF bl])
    finally show "(\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))
      \<le> onorm f * vector_variation {0..1} g" .
  qed
  then show ?thesis
    unfolding has_bounded_variation_on_interval by blast
qed

lemma rectifiable_path_linear_image_eq:
  assumes "linear f" "inj f"
  shows "rectifiable_path (f \<circ> g) \<longleftrightarrow> rectifiable_path g"
proof
  assume "rectifiable_path g"
  then show "rectifiable_path (f \<circ> g)"
    unfolding rectifiable_path_def
    using path_linear_image_eq[OF assms] has_bounded_variation_on_linear_image[OF assms(1)]
    by auto
next
  assume fg: "rectifiable_path (f \<circ> g)"
  have invf: "has_bounded_variation_on g {0..1}"
  proof -
    obtain B where "B > 0" and Bbound: "\<And>x. B * norm x \<le> norm (f x)"
      using linear_inj_bounded_below_pos[OF assms(1) assms(2)] by auto
    have bv_fg: "has_bounded_variation_on (f \<circ> g) {0..1}"
      using fg unfolding rectifiable_path_def by auto
    show ?thesis unfolding has_bounded_variation_on_interval
    proof -
      obtain C where C: "\<And>d. d division_of {0..1} \<Longrightarrow>
        (\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k))) \<le> C"
        using bv_fg unfolding has_bounded_variation_on_interval by auto
      { fix d :: "real set set" assume div: "d division_of {0..1}"
        have "(\<Sum>k\<in>d. B * norm (g (Sup k) - g (Inf k)))
          \<le> (\<Sum>k\<in>d. norm (f (g (Sup k) - g (Inf k))))" 
          by (intro sum_mono Bbound)
        also have "\<dots> = (\<Sum>k\<in>d. norm ((f \<circ> g) (Sup k) - (f \<circ> g) (Inf k)))"
          using assms(1) by (simp add: o_def real_vector.linear_diff)
        also have "\<dots> \<le> C" using C[OF div] .
        finally have "B * (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> C"
          by (simp add: sum_distrib_left)
        then have "(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> C / B"
          using \<open>B > 0\<close> by (simp add: field_simps) }
      then show "\<exists>B. \<forall>d. d division_of {0..1} \<longrightarrow>
        (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> B" by blast
    qed
  qed
  moreover have "path g"
    using fg path_linear_image_eq[OF assms(1) assms(2)] unfolding rectifiable_path_def by auto
  ultimately show "rectifiable_path g"
    unfolding rectifiable_path_def by auto
qed


lemma path_length_linear_image:
  assumes "linear f" "\<And>x. norm (f x) = norm x"
  shows "path_length (f \<circ> g) = path_length g"
proof -
  have eq: "\<And>k. norm (f (g (Sup k)) - f (g (Inf k))) = norm (g (Sup k) - g (Inf k))"
    by (metis assms(1) assms(2) real_vector.linear_diff)
  then show ?thesis
    unfolding path_length_def vector_variation_def set_variation_def comp_def by presburger
qed


lemma rectifiable_path_eq:
  assumes eq: "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = h t"
    and rect: "rectifiable_path g"
  shows "rectifiable_path h"
proof -
  have "path h"
  proof -
    have "continuous_on {0..1} h = continuous_on {0..1} g"
      by (rule continuous_on_cong_simp[OF refl]) (use eq in \<open>simp add: simp_implies_def\<close>)
    then show ?thesis using rect unfolding rectifiable_path_def path_def by auto
  qed
  moreover have "has_bounded_variation_on h {0..1}"
  proof -
    from rect have bv: "has_bounded_variation_on g {0..1}"
      unfolding rectifiable_path_def by auto
    have sup_inf_in: "Sup k \<in> {0..1} \<and> Inf k \<in> {0..1}"
      if "d division_of {(0::real)..1}" "k \<in> d" for d k
    proof -
      from division_ofD(2)[OF that] have ks: "k \<subseteq> {0..1}" .
      from division_ofD(3)[OF that] have kne: "k \<noteq> {}" .
      from division_ofD(4)[OF that] obtain a b where kab: "k = cbox a b" by auto
      with kne have "a \<le> b" by auto
      then have "Sup k = b" "Inf k = a"
        using kab by (auto simp: cSup_atLeastAtMost cInf_atLeastAtMost)
      then show ?thesis using ks kab \<open>a \<le> b\<close> by auto
    qed
    have sums_eq: "(\<Sum>k\<in>d. norm (h (Sup k) - h (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
      if "d division_of {(0::real)..1}" for d
      using sup_inf_in[OF that] by (intro sum.cong refl) (auto simp: eq)
    then show ?thesis
      using bv unfolding has_bounded_variation_on_interval by auto
  qed
  ultimately show ?thesis unfolding rectifiable_path_def by auto
qed

lemma path_length_eq:
  assumes eq: "\<And>t. t \<in> {0..1} \<Longrightarrow> g t = h t"
    and rect: "rectifiable_path g"
  shows "path_length g = path_length h"
proof -
  have sup_inf_in: "Sup k \<in> {0..1} \<and> Inf k \<in> {0..1}"
    if "d division_of t" "t \<subseteq> {(0::real)..1}" "k \<in> d" for d t k
  proof -
    from division_ofD(2)[OF that(1) that(3)] that(2) have ks: "k \<subseteq> {0..1}" by auto
    from division_ofD(3)[OF that(1) that(3)] have kne: "k \<noteq> {}" .
    from division_ofD(4)[OF that(1) that(3)] obtain a b where kab: "k = cbox a b" by auto
    with kne have "a \<le> b" by auto
    then have "Sup k = b" "Inf k = a"
      using kab by (auto simp: cSup_atLeastAtMost cInf_atLeastAtMost)
    then show ?thesis using ks kab \<open>a \<le> b\<close> by auto
  qed
  have sums_eq: "(\<Sum>k\<in>d. norm (h (Sup k) - h (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
    if "d division_of t" "t \<subseteq> {(0::real)..1}" for d t
    using sup_inf_in[OF that] by (intro sum.cong refl) (auto simp: eq)
  have "{\<Sum>k\<in>d. norm (h (Sup k) - h (Inf k)) |d. \<exists>t. d division_of t \<and> t \<subseteq> {0..1}}
      = {\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)) |d. \<exists>t. d division_of t \<and> t \<subseteq> {0..1}}"
    by (metis (lifting) sums_eq)
  then show ?thesis
    unfolding path_length_def vector_variation_def set_variation_def by auto
qed


lemma path_length_reversepath:
  "rectifiable_path g \<Longrightarrow> path_length (reversepath g) = path_length g"
  unfolding path_length_def reversepath_def comp_def[symmetric]
  using vector_variation_reflect[of 0 1 g 1] by simp

lemma rectifiable_path_subpath:
  "\<lbrakk>rectifiable_path g; u \<in> {0..1}; v \<in> {0..1}\<rbrakk> \<Longrightarrow>
    rectifiable_path (subpath u v g)"
  unfolding rectifiable_path_def subpath_def
proof (intro conjI)
  assume rect: "path g \<and> has_bounded_variation_on g {0..1}" and u: "u \<in> {0..1}" and v: "v \<in> {0..1}"
  show "path (\<lambda>x. g ((v - u) * x + u))"
    using rect u v path_subpath unfolding subpath_def by auto
  have bv: "has_bounded_variation_on g {0..1}" using rect by auto
  have seg: "closed_segment u v \<subseteq> {0..1}" using u v
    by (auto simp: closed_segment_eq_real_ivl split: if_splits)
  show "has_bounded_variation_on (\<lambda>x. g ((v - u) * x + u)) {0..1}"
  proof (cases "u \<le> v")
    case True
    have mono: "mono_on {0..1} (\<lambda>x. (v - u) * x + u)"
      using True by (auto intro!: mono_onI mult_left_mono)
    have "has_bounded_variation_on g {u..v}"
      using bv seg True by (auto simp: closed_segment_eq_real_ivl
        intro: has_bounded_variation_on_subset)
    then show ?thesis
      using has_bounded_variation_compose_monotone(1)[of g "\<lambda>x. (v-u)*x+u" 0 1]
        mono True by (simp add: comp_def)
  next
    case False
    then have vu: "v \<le> u" by auto
    have mono: "mono_on {0..1} (\<lambda>x. (u - v) * x + v)"
      using vu by (auto intro!: mono_onI mult_left_mono)
    have bvvu: "has_bounded_variation_on g {v..u}"
      using bv seg vu
      by (auto simp: closed_segment_eq_real_ivl split: if_splits
        intro: has_bounded_variation_on_subset)
    have "(\<lambda>x. g ((v - u) * x + u)) = (\<lambda>x. g ((u - v) * (1 - x) + v))"
      by (auto simp: algebra_simps)
    also have "\<dots> = (g \<circ> (\<lambda>x. (u-v)*x + v)) \<circ> (\<lambda>x. 1 - x)"
      by (auto simp: comp_def)
    finally have eq: "(\<lambda>x. g ((v - u) * x + u)) = (g \<circ> (\<lambda>x. (u-v)*x + v)) \<circ> (-) 1"
      by (auto simp: comp_def)
    have "has_bounded_variation_on (g \<circ> (\<lambda>x. (u-v)*x + v)) {0..1}"
      using has_bounded_variation_compose_monotone(1)[of g "\<lambda>x. (u-v)*x+v" 0 1]
        mono bvvu by (simp add: comp_def)
    then have "has_bounded_variation_on (g \<circ> (\<lambda>x. (u-v)*x + v)) {1 - 1..1 - 0}"
      by simp
    then have "has_bounded_variation_on ((g \<circ> (\<lambda>x. (u-v)*x + v)) \<circ> (-) 1) {0..1}"
      by (rule has_bounded_variation_on_reflect)
    then show ?thesis
      using eq by simp
  qed
qed

lemma division_of_affine_image:
  fixes c d :: real
  assumes cpos: "c > 0" and div: "D division_of T" and sub: "T \<subseteq> {a..b}"
  shows "((`) (\<lambda>x. c * x + d)) ` D division_of ((\<lambda>x. c * x + d) ` T)"
    and "(\<lambda>x. c * x + d) ` T \<subseteq> {c*a+d..c*b+d}"
proof -
  let ?\<phi> = "\<lambda>x::real. c * x + d"
  have inj: "inj ?\<phi>" using cpos by (intro injI) simp
  have mono: "mono ?\<phi>" using cpos by (intro monoI) auto
  show sub': "?\<phi> ` T \<subseteq> {c*a+d..c*b+d}"
    using sub cpos by (auto simp: mult_left_mono)
  show "((`) ?\<phi>) ` D division_of (?\<phi> ` T)"
    unfolding division_of_def
  proof (intro conjI ballI impI)
    show "finite (((`) ?\<phi>) ` D)"
      using division_ofD(1)[OF div] by auto
  next
    fix K assume "K \<in> ((`) ?\<phi>) ` D"
    then obtain K0 where K0: "K0 \<in> D" "K = ?\<phi> ` K0" by auto
    from division_ofD(2)[OF div K0(1)] have K0sub: "K0 \<subseteq> T" .
    from division_ofD(3)[OF div K0(1)] have K0ne: "K0 \<noteq> {}" .
    then show "K \<subseteq> ?\<phi> ` T" "K \<noteq> {}" using K0(2) K0sub by auto
    from division_ofD(4)[OF div K0(1)] obtain \<alpha> \<beta> where ab: "K0 = cbox \<alpha> \<beta>" by auto
    then have "K0 = {\<alpha>..\<beta>}" by auto
    with K0ne have \<alpha>\<beta>: "\<alpha> \<le> \<beta>" by auto
    have "K = ?\<phi> ` {\<alpha>..\<beta>}" using K0(2) \<open>K0 = {\<alpha>..\<beta>}\<close> by auto
    also have "\<dots> = {c*\<alpha>+d..c*\<beta>+d}"
    proof -
      have "?\<phi> ` {\<alpha>..\<beta>} = {y. \<exists>x. \<alpha> \<le> x \<and> x \<le> \<beta> \<and> y = c*x+d}"
        by (auto simp: image_def)
      also have "\<dots> = {c*\<alpha>+d..c*\<beta>+d}"
      proof (auto simp: mult_left_mono[OF _ less_imp_le[OF cpos]])
        fix y assume "c * \<alpha> + d \<le> y" "y \<le> c * \<beta> + d"
        then have "\<alpha> \<le> (y - d) / c" "((y - d) / c) \<le> \<beta>"
          using cpos by (auto simp: field_simps)
        moreover have "y = c * ((y - d) / c) + d" using cpos by auto
        ultimately show "\<exists>x\<ge>\<alpha>. x \<le> \<beta> \<and> y = c * x + d" by auto
      qed
      finally show ?thesis .
    qed
    finally show "\<exists>\<alpha> \<beta>. K = cbox \<alpha> \<beta>" by (auto simp: cbox_interval)
  next
    fix K1 K2
    assume "K1 \<in> ((`) ?\<phi>) ` D" "K2 \<in> ((`) ?\<phi>) ` D" "K1 \<noteq> K2"
    then obtain K1' K2' where K1': "K1' \<in> D" "K1 = ?\<phi> ` K1'"
      and K2': "K2' \<in> D" "K2 = ?\<phi> ` K2'" by auto
    have "K1' \<noteq> K2'" using \<open>K1 \<noteq> K2\<close> K1'(2) K2'(2) inj_image_eq_iff[OF inj] by auto
    then have disj: "interior K1' \<inter> interior K2' = {}"
      using division_ofD(5)[OF div K1'(1) K2'(1)] by auto
    show "interior K1 \<inter> interior K2 = {}"
    proof (rule ccontr)
      assume "interior K1 \<inter> interior K2 \<noteq> {}"
      then obtain y where "y \<in> interior K1" "y \<in> interior K2" by auto
      from division_ofD(4)[OF div K1'(1)] obtain a1 b1 where "K1' = cbox a1 b1" by auto
      from division_ofD(4)[OF div K2'(1)] obtain a2 b2 where "K2' = cbox a2 b2" by auto
      then have K1eq: "K1' = {a1..b1}" and K2eq: "K2' = {a2..b2}"
        using \<open>K1' = cbox a1 b1\<close> by auto
      from division_ofD(3)[OF div K1'(1)] K1eq have "a1 \<le> b1" by (auto split: if_splits)
      from division_ofD(3)[OF div K2'(1)] K2eq have "a2 \<le> b2" by (auto split: if_splits)
      have K1img: "K1 = {c*a1+d..c*b1+d}" 
      proof -
        have "K1 = ?\<phi> ` {a1..b1}" using K1'(2) K1eq by auto
        also have "\<dots> = {c*a1+d..c*b1+d}"
        proof safe
          fix x assume "x \<in> {a1..b1}"
          then show "?\<phi> x \<in> {c*a1+d..c*b1+d}" using cpos
            by (auto intro: mult_left_mono)
        next
          fix y assume "y \<in> {c*a1+d..c*b1+d}"
          then have mem: "(y-d)/c \<in> {a1..b1}" using cpos by (auto simp: field_simps)
          moreover have "?\<phi> ((y-d)/c) = y" using cpos by (simp add: field_simps)
          ultimately show "y \<in> ?\<phi> ` {a1..b1}" by force
        qed
        finally show ?thesis .
      qed
      have K2img: "K2 = {c*a2+d..c*b2+d}"
      proof -
        have "K2 = ?\<phi> ` {a2..b2}" using K2'(2) K2eq by auto
        also have "\<dots> = {c*a2+d..c*b2+d}"
        proof safe
          fix x assume "x \<in> {a2..b2}"
          then show "?\<phi> x \<in> {c*a2+d..c*b2+d}" using cpos
            by (auto intro: mult_left_mono)
        next
          fix y assume "y \<in> {c*a2+d..c*b2+d}"
          then have "(y-d)/c \<in> {a2..b2}" using cpos by (auto simp: field_simps)
          moreover have "?\<phi> ((y-d)/c) = y" using cpos by (simp add: field_simps)
          ultimately show "y \<in> ?\<phi> ` {a2..b2}" by force
        qed
        finally show ?thesis .
      qed
      from \<open>y \<in> interior K1\<close> K1img have "c*a1+d < y" "y < c*b1+d"
        using \<open>a1 \<le> b1\<close> interior_atLeastAtMost_real by auto
      then have "a1 < (y-d)/c" "(y-d)/c < b1" using cpos by (auto simp: field_simps)
      then have "(y-d)/c \<in> interior K1'"
        using K1eq interior_atLeastAtMost_real by auto
      from \<open>y \<in> interior K2\<close> K2img have "c*a2+d < y" "y < c*b2+d"
        using \<open>a2 \<le> b2\<close> interior_atLeastAtMost_real by auto
      then have "a2 < (y-d)/c" "(y-d)/c < b2" using cpos by (auto simp: field_simps)
      then have "(y-d)/c \<in> interior K2'"
        using K2eq interior_atLeastAtMost_real by auto
      with \<open>(y-d)/c \<in> interior K1'\<close> disj show False by auto
    qed
  next
    have "\<Union> (((`) ?\<phi>) ` D) = ?\<phi> ` (\<Union> D)" by auto
    also have "\<Union> D = T" using division_ofD(6)[OF div] by auto
    finally show "\<Union> (((`) ?\<phi>) ` D) = ?\<phi> ` T" .
  qed
qed

lemma vector_variation_affine_eq:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space" and c d :: real
  assumes "c > 0" "a \<le> b"
  shows "vector_variation {a..b} (g \<circ> (\<lambda>x. c * x + d)) = vector_variation {c*a+d..c*b+d} g"
proof -
  let ?\<phi> = "\<lambda>x::real. c * x + d"
  let ?\<psi> = "\<lambda>x::real. (x - d) / c"
  have cne: "c \<noteq> 0" using assms(1) by auto
  have cpos: "0 < c" using assms(1) .
  have inj_\<phi>: "inj ?\<phi>" using cne by (intro injI) simp
  have \<phi>\<psi>: "\<And>x. ?\<phi> (?\<psi> x) = x" using cne by (simp add: field_simps)
  have \<psi>\<phi>: "\<And>x. ?\<psi> (?\<phi> x) = x" using cne by (simp add: field_simps)
  have ab': "c*a+d \<le> c*b+d" using assms by (auto intro: mult_left_mono)
  have img_ivl: "\<And>\<alpha> \<beta>. \<alpha> \<le> \<beta> \<Longrightarrow> ?\<phi> ` {\<alpha>..\<beta>} = {c*\<alpha>+d..c*\<beta>+d}"
  proof safe
    fix \<alpha> \<beta> x :: real assume "\<alpha> \<le> \<beta>" "x \<in> {\<alpha>..\<beta>}"
    then show "?\<phi> x \<in> {c*\<alpha>+d..c*\<beta>+d}" using cpos by (auto intro: mult_left_mono)
  next
    fix \<alpha> \<beta> y :: real assume "\<alpha> \<le> \<beta>" "y \<in> {c*\<alpha>+d..c*\<beta>+d}"
    then have "(y-d)/c \<in> {\<alpha>..\<beta>}" using cpos by (auto simp: field_simps)
    moreover have "?\<phi> ((y-d)/c) = y" using cne by (simp add: field_simps)
    ultimately show "y \<in> ?\<phi> ` {\<alpha>..\<beta>}" by force
  qed
  \<comment> \<open>Key: the variation sums over divisions of any T equal those over \<phi>(T)\<close>
  have sum_transform: "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
    = (\<Sum>k\<in>((`) ?\<phi>) ` D. norm (g (Sup k) - g (Inf k)))"
    if "D division_of T" for D :: "real set set" and T :: "real set"
  proof -
    have div: "D division_of T" using that .
    have inj_on_img: "inj_on ((`) ?\<phi>) D"
      using inj_image_eq_iff[OF inj_\<phi>] by (auto intro!: inj_onI)
    have "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>D. norm (g (?\<phi> (Sup k)) - g (?\<phi> (Inf k))))" by (simp add: o_def)
    also have "\<dots> = (\<Sum>k\<in>D. norm (g (Sup (?\<phi> ` k)) - g (Inf (?\<phi> ` k))))"
    proof (intro sum.cong refl arg_cong[where f=norm] arg_cong2[where f="(-)"])
      fix k assume "k \<in> D"
      from division_ofD(4)[OF div this] obtain \<alpha> \<beta> where kab: "k = cbox \<alpha> \<beta>" by auto
      from division_ofD(3)[OF div \<open>k \<in> D\<close>] have kne: "k \<noteq> {}" .
      with kab have le: "\<alpha> \<le> \<beta>" by auto
      have k_ivl: "k = {\<alpha>..\<beta>}" using kab by auto
      have img: "?\<phi> ` k = {c*\<alpha>+d..c*\<beta>+d}" using img_ivl[OF le] k_ivl by simp
      have le': "c*\<alpha>+d \<le> c*\<beta>+d" using le cpos by (auto intro: mult_left_mono)
      show "g (?\<phi> (Sup k)) = g (Sup (?\<phi> ` k))"
        using k_ivl le img le' by (simp add: cSup_atLeastAtMost)
      show "g (?\<phi> (Inf k)) = g (Inf (?\<phi> ` k))"
        using k_ivl le img le' by (simp add: cInf_atLeastAtMost)
    qed
    also have "\<dots> = (\<Sum>k\<in>((`) ?\<phi>) ` D. norm (g (Sup k) - g (Inf k)))"
      by (metis (no_types, lifting) inj_on_img sum.reindex_cong)
    finally show "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>((`) ?\<phi>) ` D. norm (g (Sup k) - g (Inf k)))" .
  qed
  \<comment> \<open>Now show the Sup sets in the vector_variation definition are equal\<close>
  have sets_eq: "{\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)) |D.
      \<exists>T. D division_of T \<and> T \<subseteq> {a..b}}
    = {\<Sum>k\<in>D. norm (g (Sup k) - g (Inf k)) |D.
      \<exists>T. D division_of T \<and> T \<subseteq> {c*a+d..c*b+d}}"
  proof safe
    fix D T assume div: "D division_of T" and sub: "T \<subseteq> {a..b}"
    let ?D' = "((`) ?\<phi>) ` D"
    have div': "?D' division_of (?\<phi> ` T)"
      using division_of_affine_image(1)[OF cpos div sub] .
    have sub': "?\<phi> ` T \<subseteq> {c*a+d..c*b+d}"
      using division_of_affine_image(2)[OF cpos div sub] .
    have sum_eq: "(\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>?D'. norm (g (Sup k) - g (Inf k)))"
      using sum_transform[OF div] .
    show "\<exists>Da. (\<Sum>k\<in>D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>Da. norm (g (Sup k) - g (Inf k)))
      \<and> (\<exists>T. Da division_of T \<and> T \<subseteq> {c*a+d..c*b+d})"
      using sum_eq div' sub' by blast
  next
    fix D T assume div: "D division_of T" and sub: "T \<subseteq> {c*a+d..c*b+d}"
    \<comment> \<open>Map back via the inverse affine map (1/c)*x + (-d/c)\<close>
    let ?c' = "1/c" and ?d' = "-d/c"
    have cpos': "?c' > 0" using cpos by auto
    have div': "((`) (\<lambda>x. ?c' * x + ?d')) ` D division_of ((\<lambda>x. ?c' * x + ?d') ` T)"
      using division_of_affine_image(1)[OF cpos' div sub] .
    have sub': "(\<lambda>x. ?c' * x + ?d') ` T \<subseteq> {?c'*(c*a+d)+?d'..?c'*(c*b+d)+?d'}"
      using division_of_affine_image(2)[OF cpos' div sub] .
    have endpoints: "?c'*(c*a+d)+?d' = a" "?c'*(c*b+d)+?d' = b"
      using cne by (auto simp: field_simps)
    \<comment> \<open>The inverse map equals \<psi>\<close>
    have inv_eq: "(\<lambda>x::real. ?c' * x + ?d') = ?\<psi>"
      by (rule ext) (simp add: diff_divide_distrib)
    have div'': "((`) ?\<psi>) ` D division_of (?\<psi> ` T)"
      using div' unfolding inv_eq .
    have sub'': "?\<psi> ` T \<subseteq> {a..b}"
    proof -
      have "(\<lambda>x::real. ?c' * x + ?d') ` T \<subseteq> {a..b}"
        using sub' endpoints by auto
      then show ?thesis unfolding inv_eq .
    qed
    \<comment> \<open>Show the sum over D equals the sum over \<psi>-image composed with \<phi>\<close>
    have sum_eq: "(\<Sum>k\<in>((`) ?\<psi>) ` D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>((`) ?\<phi>) ` ((`) ?\<psi>) ` D. norm (g (Sup k) - g (Inf k)))"
      using sum_transform[OF div''] .
    have \<phi>\<psi>_img: "?\<phi> ` ?\<psi> ` S = S" for S :: "real set"
    proof -
      have "?\<phi> ` ?\<psi> ` S = (?\<phi> \<circ> ?\<psi>) ` S" by (simp add: image_image)
      also have "(?\<phi> \<circ> ?\<psi>) = id"
        using cne by (auto simp: o_def field_simps)
      also have "id ` S = S" by simp
      finally show ?thesis .
    qed
    have img_back: "((`) ?\<phi>) ` ((`) ?\<psi>) ` D = D"
    proof -
      have "((`) ?\<phi>) ` ((`) ?\<psi>) ` D = ((`) ?\<phi> \<circ> (`) ?\<psi>) ` D"
        by (simp add: image_comp)
      also have "((`) ?\<phi> \<circ> (`) ?\<psi>) = id"
        by (rule ext) (simp add: \<phi>\<psi>_img)
      also have "id ` D = D" by simp
      finally show ?thesis .
    qed
    have sum_eq': "(\<Sum>k\<in>((`) ?\<psi>) ` D. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      = (\<Sum>k\<in>D. norm (g (Sup k) - g (Inf k)))"
      using sum_eq img_back by simp
    show "\<exists>E. (\<Sum>k\<in>D. norm (g (Sup k) - g (Inf k))) = (\<Sum>k\<in>E. norm ((g \<circ> ?\<phi>) (Sup k) - (g \<circ> ?\<phi>) (Inf k)))
      \<and> (\<exists>T. E division_of T \<and> T \<subseteq> {a..b})"
      using sum_eq' div'' sub'' by (metis (no_types, lifting))
  qed
  show ?thesis
    unfolding vector_variation_def set_variation_def using sets_eq by auto
qed

lemma path_length_subpath_eq:
  assumes "s \<in> {0..1}" "t \<in> {0..1}"
    and rect: "rectifiable_path g"
  shows "path_length (subpath s t g) = vector_variation (closed_segment s t) g"
  using assms
proof (cases "s \<le> t")
  case True
  then have cs: "closed_segment s t = {s..t}"
    by (simp add: closed_segment_eq_real_ivl)
  show ?thesis
  proof (cases "s = t")
    case True
    then show ?thesis
    proof -
      from \<open>s = t\<close> have cs': "closed_segment s t = {t..t}" using cs by simp
      have "path_length (subpath t t g) = 0"
        by (metis \<open>t \<in> {0..1}\<close> eq_iff_diff_eq_0 mult_zero_left path_length_eq_0 rect
            rectifiable_path_subpath subpath_def)
      moreover have "vector_variation {t..t} g = 0"
        by (rule vector_variation_on_null) (simp add: content_real_eq_0)
      ultimately show ?thesis using \<open>s = t\<close> cs' by simp
    qed
  next
    case False
    with \<open>s \<le> t\<close> have "s < t" by auto
    then have "t - s > 0" by auto
    have "path_length (subpath s t g) = vector_variation {0..1} (g \<circ> (\<lambda>x. (t-s)*x + s))"
      unfolding path_length_def subpath_def by (simp add: comp_def)
    also have "\<dots> = vector_variation {(t-s)*0+s..(t-s)*1+s} g"
      using vector_variation_affine_eq[OF \<open>t - s > 0\<close> zero_le_one, where d=s and g=g] by simp
    also have "\<dots> = vector_variation {s..t} g"
      by simp
    finally show ?thesis by (simp add: cs)
  qed
next
  case False
  then have ts: "t < s" by auto
  then have cs: "closed_segment s t = {t..s}"
    by (simp add: closed_segment_eq_real_ivl)
  have "s - t > 0" using ts by auto
  have "path_length (subpath s t g) = vector_variation {0..1} (\<lambda>x. g ((t - s) * x + s))"
    unfolding path_length_def subpath_def by simp
  also have "\<dots> = vector_variation {0..1} (g \<circ> (\<lambda>x. (s - t) * x + t) \<circ> (-) 1)"
    by (simp add: comp_def algebra_simps)
  finally
   show ?thesis
    using vector_variation_affine_eq[OF \<open>s - t > 0\<close> zero_le_one, where d=t and g=g]
    by (simp add: cs vector_variation_reflect)
qed

lemma vector_variation_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "vector_variation s f = vector_variation s g"
proof -
  have sum_eq: "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
    if "d division_of t" "t \<subseteq> s" for d t
  proof (rule sum.cong[OF refl])
    fix k assume "k \<in> d"
    then have "k \<subseteq> t" "k \<noteq> {}" "\<exists>a b. k = cbox a b"
      using division_ofD(2,3,4)[OF that(1)] by auto
    then obtain a b where "k = cbox a b" "a \<le> b" by fastforce
    then have "Inf k \<in> k" "Sup k \<in> k" by auto
    then have "Inf k \<in> s" "Sup k \<in> s" using \<open>k \<subseteq> t\<close> that(2) by auto
    then show "norm (f (Sup k) - f (Inf k)) = norm (g (Sup k) - g (Inf k))"
      using assms by auto
  qed
  have "{\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)) |d. \<exists>t. d division_of t \<and> t \<subseteq> s}
      = {\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)) |d. \<exists>t. d division_of t \<and> t \<subseteq> s}"
    (is "?L = ?R")
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> ?L"
    then obtain d t where "x = (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k)))" "d division_of t" "t \<subseteq> s"
      by auto
    then show "x \<in> ?R" using sum_eq by auto
  next
    fix x assume "x \<in> ?R"
    then obtain d t where "x = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))" "d division_of t" "t \<subseteq> s"
      by auto
    then show "x \<in> ?L" using sum_eq
      by (metis (mono_tags, lifting) mem_Collect_eq)
  qed
  then show ?thesis
    unfolding vector_variation_def set_variation_def by simp
qed

lemma has_bounded_variation_on_cong:
  assumes "\<And>x. x \<in> s \<Longrightarrow> f x = g x"
  shows "has_bounded_variation_on f s \<longleftrightarrow> has_bounded_variation_on g s"
proof -
  have "\<And>d t. d division_of t \<Longrightarrow> t \<subseteq> s \<Longrightarrow>
    (\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
  proof -
    fix d t assume dt: "d division_of t" "t \<subseteq> s"
    show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = (\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k)))"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> d"
      then have "k \<subseteq> t" "k \<noteq> {}" "\<exists>a b. k = cbox a b"
        using division_ofD(2,3,4)[OF dt(1)] by auto
      then obtain a b where "k = cbox a b" "a \<le> b" by fastforce
      then have "Inf k \<in> k" "Sup k \<in> k" by auto
      then have "Inf k \<in> s" "Sup k \<in> s" using \<open>k \<subseteq> t\<close> dt(2) by auto
      then show "norm (f (Sup k) - f (Inf k)) = norm (g (Sup k) - g (Inf k))"
        using assms by auto
    qed
  qed
  then show ?thesis
    unfolding has_bounded_variation_on_def has_bounded_setvariation_on_def by (metis (lifting))
qed

lemma has_bounded_variation_on_affine_iff:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space" and c d :: real
  assumes "c > 0" "a \<le> b"
  shows "has_bounded_variation_on (g \<circ> (\<lambda>x. c * x + d)) {a..b} \<longleftrightarrow>
    has_bounded_variation_on g {c*a+d..c*b+d}"
proof
  assume "has_bounded_variation_on g {c*a+d..c*b+d}"
  moreover have "mono_on {a..b} (\<lambda>x. c * x + d)"
    using assms(1) by (auto intro!: mono_onI mult_left_mono)
  ultimately show "has_bounded_variation_on (g \<circ> (\<lambda>x. c * x + d)) {a..b}"
    by (rule has_bounded_variation_compose_monotone(1))
next
  assume bv: "has_bounded_variation_on (g \<circ> (\<lambda>x. c * x + d)) {a..b}"
  let ?inv = "\<lambda>x. (x - d) / c"
  have inv_mono: "mono_on {c*a+d..c*b+d} ?inv"
    using assms(1) by (smt (verit, ccfv_SIG) divide_less_cancel monotone_on_def)
  have inv_a: "?inv (c*a+d) = a" and inv_b: "?inv (c*b+d) = b"
    using assms(1) by (auto simp: field_simps)
  have comp_eq: "(g \<circ> (\<lambda>x. c * x + d)) \<circ> ?inv = g"
    using assms(1) by (auto simp: comp_def field_simps)
  have "has_bounded_variation_on ((g \<circ> (\<lambda>x. c * x + d)) \<circ> ?inv) {c*a+d..c*b+d}"
    by (metis (lifting) bv has_bounded_variation_compose_monotone(1) inv_a inv_b
        inv_mono)
  then show "has_bounded_variation_on g {c*a+d..c*b+d}"
    by (simp add: comp_eq)
qed

lemma rectifiable_path_join:
  assumes "pathfinish g1 = pathstart g2"
  shows "rectifiable_path (g1 +++ g2) \<longleftrightarrow>
    rectifiable_path g1 \<and> rectifiable_path g2"
proof -
  have half: "(0::real) \<le> 1/2" "1/2 \<le> (1::real)" by auto
  \<comment> \<open>On {0..1/2}, the joinpath agrees with g1 \<circ> (\<lambda>x. 2*x)\<close>
  have eq1: "(g1 +++ g2) x = (g1 \<circ> (\<lambda>x. 2 * x)) x" if "x \<in> {0..1/2}" for x
    using that by (auto simp: joinpaths_def)
  \<comment> \<open>On {1/2..1}, the joinpath agrees with g2 \<circ> (\<lambda>x. 2*x - 1)\<close>
  have eq2: "(g1 +++ g2) x = (g2 \<circ> (\<lambda>x. 2 * x + (-1))) x" if "x \<in> {1/2..1}" for x
  proof -
    from that have "x = 1/2 \<or> x > 1/2" by auto
    then show ?thesis
    proof
      assume "x = 1/2"
      then show ?thesis
        using assms by (simp add: joinpaths_def mult.commute pathfinish_def pathstart_def)
    next
      assume "x > 1/2"
      then show ?thesis by (auto simp: joinpaths_def comp_def)
    qed
  qed
  \<comment> \<open>Bounded variation equivalences\<close>
  have bv1: "has_bounded_variation_on (g1 +++ g2) {0..1/2} \<longleftrightarrow>
    has_bounded_variation_on g1 {0..1}"
  proof -
    have "has_bounded_variation_on (g1 +++ g2) {0..1/2} \<longleftrightarrow>
      has_bounded_variation_on (g1 \<circ> (\<lambda>x. 2 * x)) {0..1/2}"
      by (rule has_bounded_variation_on_cong[OF eq1])
    also have "\<dots> \<longleftrightarrow> has_bounded_variation_on g1 {2*0+0..2*(1/2)+0}"
      using has_bounded_variation_on_affine_iff [of 2 0 \<open>1/2\<close> _ 0] by force
    also have "{2*0+(0::real)..2*(1/2)+0} = {0..1}" by auto
    finally show ?thesis .
  qed
  have bv2: "has_bounded_variation_on (g1 +++ g2) {1/2..1} \<longleftrightarrow>
    has_bounded_variation_on g2 {0..1}"
  proof -
    have "has_bounded_variation_on (g1 +++ g2) {1/2..1} \<longleftrightarrow>
      has_bounded_variation_on (g2 \<circ> (\<lambda>x. 2 * x + (-1))) {1/2..1}"
      by (rule has_bounded_variation_on_cong[OF eq2])
    also have "\<dots> \<longleftrightarrow> has_bounded_variation_on g2 {2*(1/2)+(-1)..2*1+(-1)}"
      by (rule has_bounded_variation_on_affine_iff) auto
    also have "{2*(1/2)+(-1::real)..2*1+(-1)} = {0..1}" by auto
    finally show ?thesis .
  qed
  show ?thesis
    unfolding rectifiable_path_def
    using path_join[OF assms]
      has_bounded_variation_on_combine[OF half(1) half(2), of "g1 +++ g2"]
      bv1 bv2
    by auto
qed

lemma path_length_join:
  assumes "rectifiable_path g1"
    and "rectifiable_path g2"
    and "pathfinish g1 = pathstart g2"
  shows "path_length (g1 +++ g2) = path_length g1 + path_length g2"
proof -
  have half: "(0::real) \<le> 1/2" "1/2 \<le> (1::real)" by auto
  have bvj: "has_bounded_variation_on (g1 +++ g2) {0..1}"
    using rectifiable_path_def assms rectifiable_path_join by blast
  \<comment> \<open>On {0..1/2}, the joinpath agrees with g1 \<circ> (\<lambda>x. 2*x)\<close>
  have eq1: "(g1 +++ g2) x = (g1 \<circ> (\<lambda>x. 2 * x)) x" if "x \<in> {0..1/2}" for x
    using that by (auto simp: joinpaths_def)
  \<comment> \<open>On {1/2..1}, the joinpath agrees with g2 \<circ> (\<lambda>x. 2*x - 1)\<close>
  have eq2: "(g1 +++ g2) x = (g2 \<circ> (\<lambda>x. 2 * x + (-1))) x" if "x \<in> {1/2..1}" for x
  proof -
    from that have "x = 1/2 \<or> x > 1/2" by auto
    then show ?thesis
    proof
      assume "x = 1/2"
      then show ?thesis
        using assms by (simp add: joinpaths_def mult.commute pathfinish_def pathstart_def)
    next
      assume "x > 1/2"
      then show ?thesis by (auto simp: joinpaths_def comp_def)
    qed
  qed
  \<comment> \<open>Variation on left half\<close>
  have vv1: "vector_variation {0..1/2} (g1 +++ g2) = path_length g1"
  proof -
    have "vector_variation {0..1/2} (g1 +++ g2) =
      vector_variation {0..1/2} (g1 \<circ> (\<lambda>x. 2 * x))"
      by (rule vector_variation_cong[OF eq1])
    also have "\<dots> = vector_variation {2*0+0..2*(1/2)+0} g1"
      using vector_variation_affine_eq
      by (metis (no_types, lifting) ext add.right_neutral half(1) zero_less_numeral)
    also have "{2*0+(0::real)..2*(1/2)+0} = {0..1}" by auto
    finally show ?thesis unfolding path_length_def .
  qed
  \<comment> \<open>Variation on right half\<close>
  have vv2: "vector_variation {1/2..1} (g1 +++ g2) = path_length g2"
  proof -
    have "vector_variation {1/2..1} (g1 +++ g2) =
      vector_variation {1/2..1} (g2 \<circ> (\<lambda>x. 2 * x + (-1)))"
      by (rule vector_variation_cong[OF eq2])
    also have "\<dots> = vector_variation {2*(1/2)+(-1)..2*1+(-1)} g2"
      by (rule vector_variation_affine_eq) auto
    also have "{2*(1/2)+(-1::real)..2*1+(-1)} = {0..1}" by auto
    finally show ?thesis unfolding path_length_def .
  qed
  \<comment> \<open>Combine\<close>
  show ?thesis
    unfolding path_length_def
    using vector_variation_combine[OF bvj, of "1/2"] half vv1 vv2
    unfolding path_length_def
    by auto
qed

section \<open>Shiftpath\<close>

lemma rectifiable_path_shiftpath:
  assumes "rectifiable_path g"
    and "pathfinish g = pathstart g"
    and "t \<in> {0..1}"
  shows "rectifiable_path (shiftpath t g)"
proof -
  note rg = assms(1) and loop = assms(2) and t01 = assms(3)
  from rg have pg: "path g" and bvg: "has_bounded_variation_on g {0..1}"
    unfolding rectifiable_path_def by auto
  from t01 have t0: "0 \<le> t" and t1: "t \<le> 1" and mt: "0 \<le> 1 - t" and mt1: "1 - t \<le> 1" by auto
  \<comment> \<open>On {0..1-t}, shiftpath t g agrees with g \<circ> (\<lambda>x. x + t)\<close>
  have eq1: "shiftpath t g x = (g \<circ> (\<lambda>x. 1 * x + t)) x" if "x \<in> {0..1-t}" for x
    by (metis add.commute atLeastAtMost_iff comp_def mult_1 shiftpath_alt_def that)
  \<comment> \<open>On {1-t..1}, shiftpath t g agrees with g \<circ> (\<lambda>x. x + (t-1))\<close>
  have eq2: "shiftpath t g x = (g \<circ> (\<lambda>x. 1 * x + (t - 1))) x" if "x \<in> {1-t..1}" for x
  proof -
    from that have "x = 1-t \<or> x > 1-t" by auto
    then show ?thesis
    proof
      assume "x = 1-t"
      then show ?thesis
        using loop t1 by (simp add: shiftpath_def pathfinish_def pathstart_def)
    next
      assume "x > 1-t"
      then have "t + x > 1" by auto
      then show ?thesis
        by (simp add: add.commute add_diff_eq shiftpath_def)
    qed
  qed
  \<comment> \<open>Bounded variation on each half\<close>
  have bv1: "has_bounded_variation_on (shiftpath t g) {0..1-t}"
  proof -
    have "has_bounded_variation_on (shiftpath t g) {0..1-t} \<longleftrightarrow>
      has_bounded_variation_on (g \<circ> (\<lambda>x. 1 * x + t)) {0..1-t}"
      by (rule has_bounded_variation_on_cong[OF eq1])
    also have "\<dots> \<longleftrightarrow> has_bounded_variation_on g {1*0+t..1*(1-t)+t}"
      using has_bounded_variation_on_affine_iff mt zero_less_one by blast
    also have "{1*0+t..1*(1-t)+t} = {t..1::real}" by auto
    finally show ?thesis
      using has_bounded_variation_on_subset[OF bvg, of "{t..1}"] t0 t1 by auto
  qed
  have bv2: "has_bounded_variation_on (shiftpath t g) {1-t..1}"
  proof -
    have "has_bounded_variation_on (shiftpath t g) {1-t..1} \<longleftrightarrow>
      has_bounded_variation_on (g \<circ> (\<lambda>x. 1 * x + (t - 1))) {1-t..1}"
      by (rule has_bounded_variation_on_cong[OF eq2])
    also have "\<dots> \<longleftrightarrow> has_bounded_variation_on g {1*(1-t)+(t-1)..1*1+(t-1)}"
      using has_bounded_variation_on_affine_iff mt1 zero_less_one by blast
    also have "{1*(1-t)+(t-1)..1*1+(t-1)} = {0..t::real}" by auto
    finally show ?thesis
      using has_bounded_variation_on_subset[OF bvg, of "{0..t}"] t0 t1 by auto
  qed
  \<comment> \<open>Combine\<close>
  have "has_bounded_variation_on (shiftpath t g) {0..1}"
    using has_bounded_variation_on_combine[of 0 "1-t" 1 "shiftpath t g"] mt mt1 bv1 bv2 by auto
  then show "rectifiable_path (shiftpath t g)"
    unfolding rectifiable_path_def
    using path_shiftpath[OF pg loop t01] by auto
qed

lemma path_length_shiftpath:
  assumes rg: "rectifiable_path g"
    and loop: "pathfinish g = pathstart g"
    and t01: "t \<in> {0..1}"
  shows "path_length (shiftpath t g) = path_length g"
proof -
  from rg have bvg: "has_bounded_variation_on g {0..1}"
    unfolding rectifiable_path_def by auto
  have bvs: "has_bounded_variation_on (shiftpath t g) {0..1}"
    using rectifiable_path_shiftpath[OF rg loop t01]
    unfolding rectifiable_path_def by auto
  from t01 have t0: "0 \<le> t" and t1: "t \<le> 1" and mt: "0 \<le> 1 - t" and mt1: "1 - t \<le> 1" by auto
  \<comment> \<open>Pointwise agreements (reuse from rectifiable_path_shiftpath proof)\<close>
  have eq1: "shiftpath t g x = (g \<circ> (\<lambda>x. 1 * x + t)) x" if "x \<in> {0..1-t}" for x
    using that t1 by (auto simp: shiftpath_def algebra_simps)
  have eq2: "shiftpath t g x = (g \<circ> (\<lambda>x. 1 * x + (t - 1))) x" if "x \<in> {1-t..1}" for x
  proof -
    from that have "x = 1-t \<or> x > 1-t" by auto
    then show ?thesis
    proof
      assume "x = 1-t"
      then show ?thesis
        using loop t1 by (simp add: shiftpath_def pathfinish_def pathstart_def algebra_simps)
    next
      assume "x > 1-t"
      then have "t + x > 1" by auto
      then show ?thesis by (auto simp: shiftpath_def comp_def algebra_simps)
    qed
  qed
  \<comment> \<open>Variation on {0..1-t}\<close>
  have vv1: "vector_variation {0..1-t} (shiftpath t g) = vector_variation {t..1} g"
  proof -
    have "vector_variation {0..1-t} (shiftpath t g) =
      vector_variation {0..1-t} (g \<circ> (\<lambda>x. 1 * x + t))"
      by (rule vector_variation_cong[OF eq1])
    also have "\<dots> = vector_variation {1*0+t..1*(1-t)+t} g"
      by (rule vector_variation_affine_eq) (use t1 in auto)
    also have "{1*0+t..1*(1-t)+t} = {t..1::real}" by auto
    finally show ?thesis .
  qed
  \<comment> \<open>Variation on {1-t..1}\<close>
  have vv2: "vector_variation {1-t..1} (shiftpath t g) = vector_variation {0..t} g"
  proof -
    have "vector_variation {1-t..1} (shiftpath t g) =
      vector_variation {1-t..1} (g \<circ> (\<lambda>x. 1 * x + (t - 1)))"
      by (rule vector_variation_cong[OF eq2])
    also have "\<dots> = vector_variation {1*(1-t)+(t-1)..1*1+(t-1)} g"
      by (rule vector_variation_affine_eq) (use t0 in auto)
    also have "{1*(1-t)+(t-1)..1*1+(t-1)} = {0..t::real}" by auto
    finally show ?thesis .
  qed
  \<comment> \<open>Combine\<close>
  have "path_length (shiftpath t g) = vector_variation {0..1} (shiftpath t g)"
    unfolding path_length_def ..
  also have "\<dots> = vector_variation {0..1-t} (shiftpath t g) +
    vector_variation {1-t..1} (shiftpath t g)"
    using vector_variation_combine[OF bvs, of "1-t"] mt mt1 by auto
  also have "\<dots> = vector_variation {t..1} g + vector_variation {0..t} g"
    using vv1 vv2 by simp
  also have "\<dots> = vector_variation {0..t} g + vector_variation {t..1} g"
    by (rule add.commute)
  also have "\<dots> = vector_variation {0..1} g"
    using vector_variation_combine[OF bvg, of t] t01 by auto
  also have "\<dots> = path_length g"
    unfolding path_length_def ..
  finally show "path_length (shiftpath t g) = path_length g" .
qed

section \<open>Lipschitz and distance bounds\<close>

lemma lipschitz_imp_rectifiable_path:
  assumes "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow>
    norm (g x - g y) \<le> B * norm (x - y)"
  shows "rectifiable_path g"
  unfolding rectifiable_path_def
proof
  show "path g"
    unfolding path_def
  proof (rule continuous_onI)
    fix x e :: real assume "x \<in> {0..1}" "e > 0"
    define d where "d = (if B \<le> 0 then 1 else e / B)"
    have "d > 0" using \<open>e > 0\<close> unfolding d_def by (auto simp: field_simps)
    moreover have "\<And>x'. x' \<in> {0..1} \<Longrightarrow> dist x' x < d \<Longrightarrow> dist (g x') (g x) < e"
    proof -
      fix x' assume "x' \<in> {0..1}" "dist x' x < d"
      have "dist (g x') (g x) = norm (g x' - g x)" by (simp add: dist_norm)
      also have "\<dots> \<le> B * norm (x' - x)" using assms[OF \<open>x' \<in> {0..1}\<close> \<open>x \<in> {0..1}\<close>] .
      also have "\<dots> \<le> B * dist x' x" by (simp add: dist_norm)
      also have "\<dots> < e"
      proof (cases "B \<le> 0")
        case True
        then have "B * dist x' x \<le> 0" by (simp add: mult_nonpos_nonneg)
        also have "0 < e" using \<open>e > 0\<close> .
        finally show ?thesis .
      next
        case False
        then have "B > 0" by auto
        then have "B * dist x' x < B * d"
          using \<open>dist x' x < d\<close> by auto
        also have "\<dots> = e" using \<open>B > 0\<close> unfolding d_def by auto
        finally show ?thesis .
      qed
      finally show "dist (g x') (g x) < e" .
    qed
    ultimately show "\<exists>d>0. \<forall>x'\<in>{0..1}. dist x' x < d \<longrightarrow> dist (g x') (g x) \<le> e"
      using less_le_not_le by blast 
  qed
next
  show "has_bounded_variation_on g {0..1}"
    using Lipschitz_imp_has_bounded_variation[of "{0..1}" g B] assms
    by auto
qed

lemma path_length_lipschitz:
  assumes "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> norm (g x - g y) \<le> B * norm (x - y)"
  shows "path_length g \<le> B"
  unfolding path_length_def
proof (rule has_bounded_variation_works(2)[OF Lipschitz_imp_has_bounded_variation[of "{0..1}" g B]])
  show "bounded {0..1::real}" by simp
  show "\<And>x y. x \<in> {0..1} \<Longrightarrow> y \<in> {0..1} \<Longrightarrow> norm (g x - g y) \<le> B * norm (x - y)"
    using assms by auto
next
  fix d t assume dt: "d division_of t" "t \<subseteq> {(0::real)..1}"
  have \<open>B \<ge> 0\<close>
    using assms [of 0 1] norm_ge_zero by (fastforce elim: order_trans)
  have "(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> (\<Sum>k\<in>d. B * content k)"
  proof (rule sum_mono)
    fix k assume kd: "k \<in> d"
    from division_ofD(2,3,4)[OF dt(1) kd] obtain l u where
      k_eq: "k = cbox l u" and ksub: "k \<subseteq> t" and kne: "k \<noteq> {}" by auto
    then have lu: "l \<le> u" by fastforce
    obtain ls: "l \<in> {0..1}" and us: "u \<in> {0..1}"
      using ksub dt(2) lu k_eq cbox_interval atLeastAtMost_iff by blast
    have "norm (g (Sup k) - g (Inf k)) = norm (g u - g l)"
      using lu k_eq by (simp add: cbox_interval)
    also have "\<dots> \<le> B * norm (u - l)"
      using assms[OF us ls] by (simp add: norm_minus_commute)
    also have "\<dots> = B * (u - l)" using lu by (simp add: real_norm_def)
    also have "\<dots> = B * content k"
      using lu k_eq by (simp add: cbox_interval)
    finally show "norm (g (Sup k) - g (Inf k)) \<le> B * content k" .
  qed
  also have "\<dots> = B * (\<Sum>k\<in>d. content k)" by (simp add: sum_distrib_left)
  also have "\<dots> \<le> B * 1"
  proof (intro mult_left_mono \<open>B\<ge>0\<close>)
    have "(\<Sum>k\<in>d. content k) \<le> content {0..1::real}"
      using subadditive_content_division[OF dt(1)] dt(2) by force
    then show "(\<Sum>k\<in>d. content k) \<le> 1" by simp
  qed
  finally show "(\<Sum>k\<in>d. norm (g (Sup k) - g (Inf k))) \<le> B" by simp
qed


lemma dist_points_le_path_length:
  "\<lbrakk>rectifiable_path g; a \<in> {0..1}; b \<in> {0..1}\<rbrakk> \<Longrightarrow>
    dist (g a) (g b) \<le> path_length g"
  unfolding rectifiable_path_def path_length_def dist_norm
  using vector_variation_ge_norm_function by blast

lemma dist_endpoints_le_path_length:
  "rectifiable_path g \<Longrightarrow> dist (pathstart g) (pathfinish g) \<le> path_length g"
  using dist_points_le_path_length[of g 0 1]
  by (simp add: pathstart_def pathfinish_def)

lemma path_length_eq_line_segment:
  assumes rect: "rectifiable_path g"
    and len: "path_length g = dist (pathstart g) (pathfinish g)"
  shows "path_image g = closed_segment (pathstart g) (pathfinish g)"
proof (rule equalityI)
  have pg: "path g" and bv: "has_bounded_variation_on g {0..1}"
    using rect unfolding rectifiable_path_def by auto
  have vv_eq: "vector_variation {0..1} g = norm (g 1 - g 0)"
    using len unfolding path_length_def pathstart_def pathfinish_def dist_norm
    by (simp add: norm_minus_commute)
  show sub: "path_image g \<subseteq> closed_segment (pathstart g) (pathfinish g)"
  proof
    fix x assume "x \<in> path_image g"
    then obtain t where t: "t \<in> {0..1}" "x = g t"
      unfolding path_image_def by auto
    have t01: "0 \<le> t" "t \<le> 1" using t(1) by auto
    have bv_0t: "has_bounded_variation_on g {0..t}"
      using has_bounded_variation_on_subset[OF bv] t(1) by auto
    have bv_t1: "has_bounded_variation_on g {t..1}"
      using has_bounded_variation_on_subset[OF bv] t(1) by auto
    have n1: "norm (g t - g 0) \<le> vector_variation {0..t} g"
      using vector_variation_ge_norm_function[OF bv_0t] t01 by auto
    have n2: "norm (g 1 - g t) \<le> vector_variation {t..1} g"
      using vector_variation_ge_norm_function[OF bv_t1] t01 by auto
    have split: "vector_variation {0..t} g + vector_variation {t..1} g =
      vector_variation {0..1} g"
      using vector_variation_combine[OF bv] t(1) by auto
    have tri: "norm (g 1 - g 0) \<le> norm (g t - g 0) + norm (g 1 - g t)"
      using norm_triangle_ineq[of "g t - g 0" "g 1 - g t"] by simp
    have "norm (g t - g 0) + norm (g 1 - g t) = norm (g 1 - g 0)"
      using n1 n2 split vv_eq tri by linarith
    then have "dist (g 0) (g 1) = dist (g 0) (g t) + dist (g t) (g 1)"
      by (simp add: dist_norm norm_minus_commute)
    then have "between (g 0, g 1) (g t)"
      unfolding between by simp
    then show "x \<in> closed_segment (pathstart g) (pathfinish g)"
      unfolding t(2) pathstart_def pathfinish_def between_mem_segment by simp
  qed
  show "closed_segment (pathstart g) (pathfinish g) \<subseteq> path_image g"
  proof -
    have ne: "path_image g \<noteq> {}"
      unfolding path_image_def by auto
    have compact: "compact (path_image g)"
      using compact_path_image[OF pg] .
    have conn: "connected (path_image g)"
      using connected_path_image[OF pg] .
    have col: "collinear (path_image g)"
    proof -
      from sub have "path_image g \<subseteq> closed_segment (pathstart g) (pathfinish g)" .
      moreover have "collinear (closed_segment (pathstart g) (pathfinish g))"
        by (rule collinear_closed_segment)
      ultimately show ?thesis
        unfolding collinear_def by (meson subsetD)
    qed
    obtain p q where pq: "path_image g = closed_segment p q"
      using compact_convex_collinear_segment_alt[OF ne compact conn col] by auto
    have "pathstart g \<in> path_image g"
      unfolding path_image_def pathstart_def by auto
    moreover have "pathfinish g \<in> path_image g"
      unfolding path_image_def pathfinish_def by auto
    ultimately have "pathstart g \<in> closed_segment p q" "pathfinish g \<in> closed_segment p q"
      using pq by auto
    then have "closed_segment (pathstart g) (pathfinish g) \<subseteq> closed_segment p q"
      using subset_closed_segment by blast
    then show ?thesis using pq by simp
  qed
qed

section \<open>Linepath\<close>

lemma rectifiable_path_linepath:
  "rectifiable_path (linepath a b)"
proof (rule lipschitz_imp_rectifiable_path[where B="dist a b"])
  fix x y :: real assume "x \<in> {0..1}" "y \<in> {0..1}"
  have "linepath a b x - linepath a b y = (x - y) *\<^sub>R (b - a)"
    by (simp add: linepath_def algebra_simps)
  then have "norm (linepath a b x - linepath a b y) = \<bar>x - y\<bar> * norm (b - a)"
    by simp
  also have "\<dots> = norm (b - a) * norm (x - y)"
    by (simp add: abs_real_def real_norm_def mult.commute)
  also have "\<dots> = dist a b * norm (x - y)"
    by (simp add: dist_norm norm_minus_commute)
  finally show "norm (linepath a b x - linepath a b y) \<le> dist a b * norm (x - y)"
    by simp
qed

lemma path_length_linepath:
  "path_length (linepath a b) = dist a b"
proof (rule antisym)
  show "path_length (linepath a b) \<le> dist a b"
  proof (rule path_length_lipschitz)
    fix x y :: real assume "x \<in> {0..1}" "y \<in> {0..1}"
    have "linepath a b x - linepath a b y = (x - y) *\<^sub>R (b - a)"
      by (simp add: linepath_def algebra_simps)
    then have "norm (linepath a b x - linepath a b y) = \<bar>x - y\<bar> * norm (b - a)"
      by simp
    also have "\<dots> = dist a b * norm (x - y)"
      by (simp add: dist_norm norm_minus_commute abs_real_def real_norm_def mult.commute)
    finally show "norm (linepath a b x - linepath a b y) \<le> dist a b * norm (x - y)"
      by simp
  qed
next
  have "dist a b = dist (pathstart (linepath a b)) (pathfinish (linepath a b))"
    by (simp add: pathstart_def pathfinish_def linepath_def dist_norm)
  also have "\<dots> \<le> path_length (linepath a b)"
    by (rule dist_endpoints_le_path_length[OF rectifiable_path_linepath])
  finally show "dist a b \<le> path_length (linepath a b)" .
qed

section \<open>Rectifiable path image bound\<close>

lemma rectifiable_path_image_subset_cball:
  assumes "rectifiable_path g"
  shows "path_image g \<subseteq> cball (pathstart g) (path_length g)"
proof
  fix x assume "x \<in> path_image g"
  then obtain t where t: "t \<in> {0..1}" "x = g t"
    unfolding path_image_def by auto
  have "dist (pathstart g) x = dist (g 0) (g t)"
    by (simp add: t(2) pathstart_def)
  also have "\<dots> \<le> path_length g"
    using dist_points_le_path_length[OF assms _ t(1)] by simp
  finally show "x \<in> cball (pathstart g) (path_length g)"
    by (simp add: mem_cball)
qed

section \<open>Absolutely continuous paths\<close>

lemma rectifiable_path_differentiable:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "negligible S"
    "absolutely_continuous_on {0..1} g"
    "\<And>t. t \<in> {0..1} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "rectifiable_path g"
  unfolding rectifiable_path_def
proof
  show "path g"
    unfolding path_def
    using absolutely_continuous_on_imp_continuous[OF assms(2) is_interval_cc] .
  show "has_bounded_variation_on g {0..1}"
    using absolutely_continuous_on_imp_has_bounded_variation_on[OF assms(2) bounded_closed_interval] .
qed

lemma vector_variation_integral_norm_derivative:
  fixes f :: "real \<Rightarrow> 'a::euclidean_space"
  assumes neg: "negligible S" and ab: "a \<le> b"
    and ac: "absolutely_continuous_on {a..b} f"
    and deriv: "\<And>x. x \<in> {a..b} - S \<Longrightarrow> (f has_vector_derivative f' x) (at x)"
  shows "vector_variation {a..b} f = integral {a..b} (\<lambda>t. norm (f' t))"
proof -
  \<comment> \<open>Bounded variation from absolute continuity\<close>
  have bv: "has_bounded_variation_on f {a..b}"
    using absolutely_continuous_on_imp_has_bounded_variation_on[OF ac bounded_closed_interval] .
      \<comment> \<open>FTC on subintervals\<close>
  have ftc_sub: "(f' has_integral (f v - f u)) {u..v}"
    if "u \<le> v" "{u..v} \<subseteq> {a..b}" for u v
  proof (rule fundamental_theorem_of_calculus_absolutely_continuous[OF neg that(1)])
    show "absolutely_continuous_on {u..v} f"
      using absolutely_continuous_on_subset[OF ac that(2)] .
  next
    fix x assume "x \<in> {u..v} - S"
    then show "(f has_vector_derivative f' x) (at x within {u..v})"
      using deriv[of x] that(2) has_vector_derivative_at_within by blast
  qed
  have integral_sub: "integral {u..v} f' = f v - f u"
    if "u \<le> v" "{u..v} \<subseteq> {a..b}" for u v
    using integral_unique[OF ftc_sub[OF that]] .
  have f'_int: "f' integrable_on {a..b}"
    using ftc_sub[OF ab subset_refl] by (auto simp: integrable_on_def)
      \<comment> \<open>f' is absolutely integrable: use bounded variation characterization\<close>
  have f'_abs_int: "f' absolutely_integrable_on {a..b}"
  proof (rule bounded_variation_absolutely_integrable_real_interval[OF f'_int])
    fix d assume d: "d division_of {a..b}"
    show "(\<Sum>K\<in>d. norm (integral K f')) \<le> vector_variation {a..b} f"
    proof -
      have "(\<Sum>K\<in>d. norm (integral K f')) = (\<Sum>K\<in>d. norm (f (Sup K) - f (Inf K)))"
      proof (rule sum.cong[OF refl])
        fix K assume "K \<in> d"
        then obtain u v where uv: "K = {u..v}" "u \<le> v"
          by (metis atLeastatMost_empty_iff cbox_division_memE cbox_interval d)
        have sub: "{u..v} \<subseteq> {a..b}"
          using division_ofD(2)[OF d \<open>K \<in> d\<close>] uv(1) by auto
        have "integral K f' = f v - f u"
          unfolding uv(1) using integral_sub[OF uv(2) sub] .
        moreover have "Sup K = v" "Inf K = u"
          using uv by auto
        ultimately show "norm (integral K f') = norm (f (Sup K) - f (Inf K))"
          by simp
      qed
      also have "\<dots> \<le> vector_variation {a..b} f"
        using has_bounded_variation_works(1)[OF bv d] by auto
      finally show ?thesis .
    qed
  qed
    \<comment> \<open>Norm of f' is integrable\<close>
  have norm_f'_int: "(\<lambda>t. norm (f' t)) integrable_on {a..b}"
    using f'_abs_int unfolding absolutely_integrable_on_def by simp
      \<comment> \<open>Direction \<le>: vector_variation \<le> integral of norm\<close>
  have le_dir: "vector_variation {a..b} f \<le> integral {a..b} (\<lambda>t. norm (f' t))"
    unfolding vector_variation_def
  proof (rule has_bounded_setvariation_works(2)[OF bv[unfolded has_bounded_variation_on_def]])
    fix d t assume dt: "d division_of t" "t \<subseteq> {a..b}"
    have "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) = (\<Sum>k\<in>d. norm (integral k f'))"
    proof (rule sum.cong[OF refl])
      fix k assume "k \<in> d"
      then obtain u v where k: "k = {u..v}" "u \<le> v"
        by (metis atLeastatMost_empty' box_real(2) cbox_division_memE dt(1))
      have sub: "{u..v} \<subseteq> {a..b}"
        using division_ofD(2)[OF dt(1) \<open>k \<in> d\<close>] dt(2) k(1) by blast
      have "integral k f' = f v - f u"
        unfolding k(1) using integral_sub[OF k(2) sub] .
      moreover have "Sup k = v" "Inf k = u"
        using k by auto
      ultimately show "norm (f (Sup k) - f (Inf k)) = norm (integral k f')"
        by simp
    qed
    also have "\<dots> \<le> (\<Sum>k\<in>d. integral k (\<lambda>t. norm (f' t)))"
    proof (rule sum_mono)
      fix k assume kd: "k \<in> d"
      then obtain u v where k: "k = {u..v}" "u \<le> v"
        by (metis atLeastatMost_empty_iff cbox_division_memE dt(1) interval_cbox)
      have sub: "{u..v} \<subseteq> {a..b}"
        using dt k(1) kd by blast
      show "norm (integral k f') \<le> integral k (\<lambda>t. norm (f' t))"
        unfolding k(1)
        by (rule integral_norm_bound_integral
            [OF integrable_on_subinterval[OF f'_int sub]
              integrable_on_subinterval[OF norm_f'_int sub]])
          auto
    qed
    also have "\<dots> \<le> integral {a..b} (\<lambda>t. norm (f' t))"
    proof -
      have sum_int: "((\<lambda>t. norm (f' t)) has_integral (\<Sum>k\<in>d. integral k (\<lambda>t. norm (f' t)))) (\<Union>d)"
      proof (rule has_integral_Union)
        show "finite d" using division_of_finite[OF dt(1)] .
      next
        fix S assume Sd: "S \<in> d"
        then obtain u v where uv: "S = {u..v}" "u \<le> v"
          by (metis atLeastatMost_empty_iff cbox_division_memE dt(1) interval_cbox)
        have "{u..v} \<subseteq> {a..b}"
          using division_ofD(2)[OF dt(1) Sd] dt(2) uv(1) by blast
        then show "((\<lambda>t. norm (f' t)) has_integral integral S (\<lambda>t. norm (f' t))) S"
          unfolding uv(1)
          using integrable_on_subinterval[OF norm_f'_int] has_integral_integral by blast
      next
        show "pairwise (\<lambda>S S'. negligible (S \<inter> S')) d"
          unfolding pairwise_def
        proof (intro ballI impI)
          fix K1 K2 assume "K1 \<in> d" "K2 \<in> d" "K1 \<noteq> K2"
          then have disj: "interior K1 \<inter> interior K2 = {}"
            using division_ofD(5)[OF dt(1)] by blast
          obtain a1 b1 where K1: "K1 = cbox a1 b1"
            using division_ofD(4)[OF dt(1) \<open>K1 \<in> d\<close>] by auto
          obtain a2 b2 where K2: "K2 = cbox a2 b2"
            using division_ofD(4)[OF dt(1) \<open>K2 \<in> d\<close>] by auto
          have "K1 \<inter> K2 = cbox (\<Sum>i\<in>Basis. max (a1 \<bullet> i) (a2 \<bullet> i) *\<^sub>R i)
                               (\<Sum>i\<in>Basis. min (b1 \<bullet> i) (b2 \<bullet> i) *\<^sub>R i)"
            unfolding K1 K2 by (rule Int_interval)
          moreover have "box (\<Sum>i\<in>Basis. max (a1 \<bullet> i) (a2 \<bullet> i) *\<^sub>R i)
                              (\<Sum>i\<in>Basis. min (b1 \<bullet> i) (b2 \<bullet> i) *\<^sub>R i) = {}"
            using disj unfolding K1 K2 Int_interval interior_cbox by simp
          ultimately show "negligible (K1 \<inter> K2)"
            using negligible_interval(1) by (metis (mono_tags, lifting))
        qed
      qed
      have eq: "(\<Sum>k\<in>d. integral k (\<lambda>t. norm (f' t))) = integral (\<Union>d) (\<lambda>t. norm (f' t))"
        using integral_unique[OF sum_int] by simp
      have "integral (\<Union>d) (\<lambda>t. norm (f' t)) \<le> integral {a..b} (\<lambda>t. norm (f' t))"
      proof (rule integral_subset_le)
        show "\<Union>d \<subseteq> {a..b}" using dt(2) division_ofD(6)[OF dt(1)] by auto
        show "(\<lambda>t. norm (f' t)) integrable_on \<Union>d"
          using sum_int by (auto simp: integrable_on_def)
        show "(\<lambda>t. norm (f' t)) integrable_on {a..b}" by fact
        show "\<forall>x\<in>{a..b}. 0 \<le> norm (f' x)" by simp
      qed
      then show ?thesis using eq by linarith
    qed
    finally show "(\<Sum>k\<in>d. norm (f (Sup k) - f (Inf k))) \<le> integral {a..b} (\<lambda>t. norm (f' t))" .
  qed
    \<comment> \<open>Direction \<ge>: integral of norm \<le> vector_variation\<close>
    \<comment> \<open>Key idea: use gauge characterization of the integral combined with the derivative condition\<close>
  have ge_dir: "integral {a..b} (\<lambda>t. norm (f' t)) \<le> vector_variation {a..b} f"
  proof (rule field_le_epsilon)
    fix \<epsilon> :: real assume "\<epsilon> > 0"
      \<comment> \<open>Get gauge from Henstock's lemma for f'\<close>
    define e where "e = \<epsilon> / (2 * real DIM('a) + 1)"
    have "e > 0" using \<open>\<epsilon> > 0\<close> unfolding e_def by (simp add: field_simps)
    then obtain \<gamma> where "gauge \<gamma>" and \<gamma>:
      "\<And>\<D>. \<D> tagged_division_of cbox a b \<Longrightarrow> \<gamma> fine \<D> \<Longrightarrow>
        norm ((\<Sum>(x,k)\<in>\<D>. content k *\<^sub>R f' x) - integral {a..b} f') < e"
      using has_integral_real[THEN iffD1, OF integrable_integral[OF f'_int], rule_format, of e]
      by auto
        \<comment> \<open>Get gauge for the norm integral\<close>
    obtain \<gamma>' where "gauge \<gamma>'" and \<gamma>':
      "\<And>\<D>. \<D> tagged_division_of cbox a b \<Longrightarrow> \<gamma>' fine \<D> \<Longrightarrow>
        norm ((\<Sum>(x,k)\<in>\<D>. content k *\<^sub>R (\<lambda>t. norm (f' t)) x) -
              integral {a..b} (\<lambda>t. norm (f' t))) < e"
      using has_integral_real[THEN iffD1, OF integrable_integral[OF norm_f'_int], rule_format, of e]
        \<open>e > 0\<close>
      by auto
        \<comment> \<open>Combine gauges and get a fine tagged division\<close>
    define \<Gamma> where "\<Gamma> = (\<lambda>x. \<gamma> x \<inter> \<gamma>' x)"
    have "gauge \<Gamma>" unfolding \<Gamma>_def using \<open>gauge \<gamma>\<close> \<open>gauge \<gamma>'\<close> by (rule gauge_Int)
    then obtain p where td: "p tagged_division_of {a..b}" and fine: "\<Gamma> fine p"
      using fine_division_exists_real by blast
    have \<gamma>_fine: "\<gamma> fine p" and \<gamma>'_fine: "\<gamma>' fine p"
      using fine unfolding \<Gamma>_def fine_Int by auto
        \<comment> \<open>Riemann sum for norm(f') is close to the integral\<close>
    have rs_norm: "norm ((\<Sum>(x,k)\<in>p. content k * norm (f' x)) -
                          integral {a..b} (\<lambda>t. norm (f' t))) < e"
      using \<gamma>'[OF td[unfolded interval_cbox] \<gamma>'_fine] by simp
        \<comment> \<open>Henstock bound: sum of pointwise errors is small\<close>
    have td_partial: "p tagged_partial_division_of cbox a b"
      using td unfolding interval_cbox tagged_division_of_def by simp
    have henstock: "(\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R f' x - integral k f')) \<le> 2 * real DIM('a) * e"
    proof (rule Henstock_lemma_part2)
      show "f' integrable_on cbox a b" using f'_int by force
      show "0 < e" by fact
      show "gauge \<gamma>" by fact
      show "\<And>\<D>. \<D> tagged_division_of cbox a b \<Longrightarrow> \<gamma> fine \<D> \<Longrightarrow>
              norm ((\<Sum>(x, k)\<in>\<D>. content k *\<^sub>R f' x) - integral (cbox a b) f') < e"
        using \<gamma> by force
      show "p tagged_partial_division_of cbox a b" by fact
      show "\<gamma> fine p" by fact
    qed
      \<comment> \<open>The underlying division from the tagged division\<close>
    have div_p: "snd ` p division_of {a..b}"
      using division_of_tagged_division[OF td] .
        \<comment> \<open>In 1D, snd is injective on tagged partial divisions\<close>
    have inj_snd: "inj_on snd p"
    proof (rule inj_onI)
      fix xk yk assume xk_in: "xk \<in> p" and yk_in: "yk \<in> p" and eq: "snd xk = snd yk"
      obtain x k where xk: "xk = (x, k)" by (cases xk)
      obtain y l where yk: "yk = (y, l)" by (cases yk)
      from eq have kl: "k = l" using xk yk by simp
      show "xk = yk"
      proof (rule ccontr)
        assume neq: "xk \<noteq> yk"
        then have xy: "x \<noteq> y" using xk yk kl by auto
        have x_in: "x \<in> k" using tagged_division_ofD(2)[OF td xk_in[unfolded xk]] by simp
        have y_in: "y \<in> k" using tagged_division_ofD(2)[OF td yk_in[unfolded yk]] kl by simp
        have "interior k \<inter> interior l = {}"
          using tagged_partial_division_ofD(5)[OF td_partial xk_in[unfolded xk] yk_in[unfolded yk]
                neq[unfolded xk yk]] by auto
        then have int_empty: "interior k = {}" using kl by simp
        obtain a' b' where ab': "k = cbox a' b'"
          using tagged_partial_division_ofD(4)[OF td_partial xk_in[unfolded xk]] by auto
        then have k_eq: "k = {a'..b'}" by simp
        from x_in y_in have "a' \<le> x" "x \<le> b'" "a' \<le> y" "y \<le> b'" by (simp_all add: k_eq)
        with xy have "a' < b'" by linarith
        then have "{a'<..<b'} \<noteq> {}" by auto
        moreover have "interior k = {a'<..<b'}"
          unfolding k_eq by (rule interior_atLeastAtMost_real)
        ultimately show False using int_empty by auto
      qed
    qed
      \<comment> \<open>Sum over tagged division = sum over underlying division\<close>
    have sum_eq: "(\<Sum>(x,k)\<in>p. g k) = (\<Sum>K\<in>snd ` p. g K)" for g :: "real set \<Rightarrow> real"
    proof -
      have "sum g (snd ` p) = sum (g \<circ> snd) p"
        using Groups_Big.comm_monoid_add_class.sum.reindex[OF inj_snd] by simp
      also have "\<dots> = (\<Sum>(x,k)\<in>p. g k)"
        by (simp add: case_prod_unfold comp_def)
      finally show ?thesis by simp
    qed
        \<comment> \<open>Sum of norm of integrals over subintervals \<le> vector variation\<close>
    have int_sum_le_vv: "(\<Sum>(x,k)\<in>p. norm (integral k f')) \<le> vector_variation {a..b} f"
    proof -
      have "(\<Sum>(x,k)\<in>p. norm (integral k f')) = (\<Sum>K\<in>snd ` p. norm (integral K f'))"
        using sum_eq .
      also have "\<dots> = (\<Sum>K\<in>snd ` p. norm (f (Sup K) - f (Inf K)))"
      proof (rule sum.cong[OF refl])
        fix K assume "K \<in> snd ` p"
        then obtain u v where uv: "K = {u..v}" "u \<le> v"
          by (metis atLeastatMost_empty_iff cbox_division_memE div_p interval_cbox)
        have sub: "{u..v} \<subseteq> {a..b}"
          using division_ofD(2)[OF div_p \<open>K \<in> snd ` p\<close>] uv(1) by auto
        have "integral K f' = f v - f u"
          unfolding uv(1) using integral_sub[OF uv(2) sub] .
        moreover have "Sup K = v" "Inf K = u" using uv by auto
        ultimately show "norm (integral K f') = norm (f (Sup K) - f (Inf K))" by simp
      qed
      also have "\<dots> \<le> vector_variation {a..b} f"
        using has_bounded_variation_works(1)[OF bv div_p] by auto
      finally show ?thesis .
    qed
    \<comment> \<open>Triangle inequality: Riemann sum \<le> sum of integral norms + Henstock error\<close>
    have tri: "(\<Sum>(x,k)\<in>p. content k * norm (f' x)) \<le>
              (\<Sum>(x,k)\<in>p. norm (integral k f')) + (\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R f' x - integral k f'))"
    proof -
      have "(\<Sum>(x,k)\<in>p. content k * norm (f' x)) = (\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R f' x))"
      proof (rule sum.cong[OF refl])
        fix xk assume "xk \<in> p"
        then obtain x k where xk: "xk = (x, k)" by (cases xk)
        have "content k \<ge> 0"
          using tagged_partial_division_ofD(4)[OF td_partial \<open>xk \<in> p\<close>[unfolded xk]]
          by (auto simp: xk intro: content_pos_le)
        then show "(case xk of (x, k) \<Rightarrow> content k * norm (f' x)) =
                   (case xk of (x, k) \<Rightarrow> norm (content k *\<^sub>R f' x))"
          by (simp add: xk)
      qed
      also have "\<dots> \<le> (\<Sum>(x,k)\<in>p. norm (integral k f') + norm (content k *\<^sub>R f' x - integral k f'))"
      proof (rule sum_mono)
        fix xk assume "xk \<in> p"
        obtain x k where xk: "xk = (x, k)" by (cases xk)
        show "(case xk of (x, k) \<Rightarrow> norm (content k *\<^sub>R f' x)) \<le>
              (case xk of (x, k) \<Rightarrow> norm (integral k f') + norm (content k *\<^sub>R f' x - integral k f'))"
          unfolding xk split by (rule norm_triangle_sub)
      qed
      also have "\<dots> = (\<Sum>(x,k)\<in>p. norm (integral k f')) + (\<Sum>(x,k)\<in>p. norm (content k *\<^sub>R f' x - integral k f'))"
        by (simp add: sum.distrib case_prod_unfold)
      finally show ?thesis .
    qed
    \<comment> \<open>Combine all bounds\<close>
    have "(\<Sum>(x,k)\<in>p. content k * norm (f' x)) \<le> vector_variation {a..b} f + 2 * real DIM('a) * e"
      using tri int_sum_le_vv henstock by linarith
    moreover have "integral {a..b} (\<lambda>t. norm (f' t)) - (\<Sum>(x,k)\<in>p. content k * norm (f' x)) < e"
      using rs_norm by (simp add: abs_less_iff norm_minus_commute)
    ultimately have "integral {a..b} (\<lambda>t. norm (f' t)) < vector_variation {a..b} f + 2 * real DIM('a) * e + e"
      by linarith
    then have "integral {a..b} (\<lambda>t. norm (f' t)) < vector_variation {a..b} f + (2 * real DIM('a) + 1) * e"
      by (simp add: algebra_simps)
    also have "(2 * real DIM('a) + 1) * e = \<epsilon>"
      unfolding e_def by simp
    finally show "integral {a..b} (\<lambda>t. norm (f' t)) \<le> vector_variation {a..b} f + \<epsilon>"
      by linarith
  qed
  show ?thesis using le_dir ge_dir by linarith
qed

lemma path_length_differentiable:
  fixes g :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "negligible S"
    "absolutely_continuous_on {0..1} g"
    "\<And>t. t \<in> {0..1} - S \<Longrightarrow> (g has_vector_derivative g' t) (at t)"
  shows "path_length g = integral {0..1} (\<lambda>t. norm (g' t))"
  unfolding path_length_def
  using vector_variation_integral_norm_derivative[OF assms(1) _ assms(2,3)] by simp

end
