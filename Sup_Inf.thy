theory Sup_Inf 
  imports "HOL-Analysis.Analysis"

begin


lemma lim_1_over_real_power:
  assumes "0 < Re s"
  shows "((\<lambda>x::complex. 1 / (x powr s)) \<longlongrightarrow> 0) at_top"
proof (rule Lim_null_comparison)
  have "1 \<le> ln x" if "3 \<le> x" for x::real
    using ln_272_gt_1 that by (force intro: order_trans [of _ "ln (272/100)"])
  then show "\<forall>\<^sub>F x in at_top. norm (1 / x powr s) \<le> cmod (ln x / x powr s)"
    apply (auto simp: norm_divide field_split_simps eventually_sequentially)
    sorry
  show "((\<lambda>x. cmod (Ln x / x powr s)) \<longlongrightarrow> 0) at_top"
    using lim_Ln_over_power [OF assms]
qed

  apply (rule Lim_null_comparison)

  sorry
  using lim_1_over_complex_power [of "of_real s", THEN filterlim_sequentially_Suc [THEN iffD2]] assms
  apply (subst filterlim_sequentially_Suc [symmetric])
  by (simp add: lim_sequentially dist_norm Ln_Reals_eq norm_powr_real_powr norm_divide)

thm Lim_null_comparison lim_1_over_complex_power
lemma lim_1_over_real_power:
  fixes s :: real
  assumes "0 < s"
  shows "((\<lambda>n. 1 / (of_nat n powr s)) \<longlongrightarrow> 0) sequentially"
  using lim_1_over_complex_power [of "of_real s", THEN filterlim_sequentially_Suc [THEN iffD2]] assms
  apply (subst filterlim_sequentially_Suc [symmetric])
  by (simp add: lim_sequentially dist_norm Ln_Reals_eq norm_powr_real_powr norm_divide)

thm has_integral_powr_to_inf

lemma has_integral_to_inf:
  fixes h ::"real \<Rightarrow> real"
  assumes int: "\<And>y::real. h integrable_on {a..y}"
    and lim: "((\<lambda>y. integral {a..y} h) \<longlongrightarrow> l) at_top"
    and nonneg: "\<And>y. y \<ge> a \<Longrightarrow> h y \<ge> 0"
  shows "(h has_integral l) {a..}"
proof -
  have ge: "integral {a..y} h \<ge> 0" for y
    by (meson Henstock_Kurzweil_Integration.integral_nonneg atLeastAtMost_iff int nonneg)
  then have "l \<ge> 0"
    using tendsto_lowerbound [OF lim] eventuallyI trivial_limit_at_top_linorder by blast 
  have moni: "mono (\<lambda>y. integral {a..y} h)"
    by (simp add: int integral_subset_le monoI nonneg)
  then have int_le_l: "integral {a..y} h \<le> l" for y
    using order_topology_class.order_tendstoD [OF lim, of "integral {a..y} h"]
    by (smt (verit) eventually_at_top_linorder monotoneD nle_le)
  define f where "f = (\<lambda>n x. if x \<in> {a..of_nat n} then h x else 0)"
  have has_integral_f: "(f n has_integral (integral {a..of_nat n} h)) {a..}"
    if n: "n \<ge> a" for n :: nat
  proof -
    have "(f n has_integral (integral {a..of_nat n} h)) {a..n}"
      by (metis f_def has_integral_eq int integrable_integral)
    thus "(f n has_integral (integral {a..of_nat n} h)) {a..}"
      by (rule has_integral_on_superset) (auto simp: f_def)
  qed
  have integral_f: "integral {a..} (f n) = (if n \<ge> a then integral {a..of_nat n} h else 0)" for n :: nat
    by (meson atLeastAtMost_iff f_def has_integral_f has_integral_iff has_integral_is_0 order_trans)
  have *: "h integrable_on {a..} \<and> (\<lambda>n. integral {a..} (f n)) \<longlonglongrightarrow> integral {a..} h"
  proof (intro monotone_convergence_increasing allI ballI)
    fix n
    show "f n integrable_on {a..}"
      by (metis atLeastatMost_empty' empty_iff f_def has_integral_f has_integral_iff has_integral_is_0)
  next
    fix n x
    show "f n x \<le> f (Suc n) x" using nonneg by (auto simp: f_def)
  next
    fix x :: real assume x: "x \<in> {a..}" 
    from filterlim_real_sequentially have "eventually (\<lambda>n. real n \<ge> x) at_top"
      by (simp add: filterlim_at_top)
    with x have "eventually (\<lambda>n. f n x = h x) at_top"
      by (auto elim!: eventually_mono simp: f_def)
    thus "(\<lambda>n. f n x) \<longlonglongrightarrow> h x" by (simp add: tendsto_eventually)
  next
    have "integral {a..} (f n) \<le> l" for n :: nat
      using int_le_l \<open>0 \<le> l\<close> integral_f by presburger
    then have "norm (integral {a..} (f n)) \<le> l" for n :: nat
      by (simp add: \<open>\<And>y. 0 \<le> integral {a..y} h\<close> integral_f)
    thus "bounded (range(\<lambda>k. integral {a..} (f k)))"
      by (smt (verit, del_insts) boundedI rangeE)
  qed
  from filterlim_real_sequentially
    have "eventually (\<lambda>n. real n \<ge> a) at_top"
    by (simp add: filterlim_at_top)
  hence "eventually (\<lambda>n. integral {a..n} h = integral {a..} (f n)) at_top"
    by eventually_elim (simp add: integral_f)
  moreover have "((\<lambda>y. integral {a..y} h) \<circ> real) \<longlonglongrightarrow> l"
    unfolding tendsto_compose_filtermap
    using filterlim_def filterlim_real_sequentially lim tendsto_mono by blast
  ultimately have "(\<lambda>n. integral {a..} (f n)) \<longlonglongrightarrow> l" 
    by (force intro: Lim_transform_eventually)
  then show ?thesis
    using "*" LIMSEQ_unique by blast
qed

lemma has_integral_powr_to_inf:
  fixes a e :: real
  assumes "e < -1" "a > 0"
  shows   "((\<lambda>x. x powr e) has_integral -(a powr (e + 1)) / (e + 1)) {a..}"
proof (rule has_integral_to_inf)
  define F where "F \<equiv> (\<lambda>x. x powr (e + 1) / (e + 1))"
  have der: "(F has_real_derivative (x powr e)) (at x within {a..y})" if "x\<ge>a" for x y
    using that assms unfolding F_def by (intro derivative_eq_intros | force)+
  then show "\<And>y. (\<lambda>x. x powr e) integrable_on {a..y}"
    by (metis Icc_subset_Ici_iff assms dual_order.refl has_integral_powr_to_inf integrable_on_def integrable_on_subinterval)
  moreover have "((\<lambda>x. x powr e) has_integral (F y - F a)) {a..y}" if "y \<ge> a" for y
    by (meson der atLeastAtMost_iff fundamental_theorem_of_calculus has_real_derivative_iff_has_vector_derivative that)
  moreover have "(F \<longlongrightarrow> 0) at_top"
    using assms
    apply (simp add: F_def)
    apply (clarsimp simp add: tendsto_iff dist_norm norm_divide field_split_simps)

    sorry
  ultimately
  show "((\<lambda>y. integral {a..y} (\<lambda>x. x powr e)) \<longlongrightarrow> - (a powr (e + 1)) / (e + 1)) at_top"
    sorry
qed auto



context
  fixes f::"'a \<Rightarrow> 'b::{conditionally_complete_linorder,linordered_field}"
begin

lemma Sup_mult_eq:
  assumes "bdd_above (f ` A)" "A \<noteq> {}" "a \<ge> 0"
  shows  "(SUP x\<in>A. a * f x) = a * (SUP x\<in>A. f x)"
proof (cases "a=0")
  case False
  have bdd: "bdd_above ((\<lambda>x. a * f x) ` A)"
    using assms by (metis bdd_above.I2 bdd_above.unfold imageI mult_left_mono)
  show ?thesis 
  proof (rule antisym)
    show "(SUP x\<in>A. a * f x) \<le> a * Sup (f ` A)"
      using assms bdd by (auto simp add: cSup_le_iff cSup_upper mult_left_mono)
    have "\<And>x. x \<in> A \<Longrightarrow> f x \<le> (SUP x\<in>A. a * f x) / a"
      by (simp add: False assms bdd cSup_upper less_le mult_imp_le_div_pos)
    then have "Sup (f ` A) \<le> (SUP x\<in>A. a * f x) / a"
      using assms by (auto simp add: cSup_le_iff)
    with False assms show "a * Sup (f ` A) \<le> (SUP x\<in>A. a * f x)"
      by (auto simp: field_simps)
  qed 
qed (use assms in auto)

lemma Inf_mult_eq:
  assumes "bdd_below (f ` A)" "A \<noteq> {}" "a \<ge> 0"
  shows  "(INF x\<in>A. a * f x) = a * (INF x\<in>A. f x)"
proof (cases "a=0")
  case False
  have bdd: "bdd_below ((\<lambda>x. a * f x) ` A)"
    by (metis assms bdd_below.unfold bdd_belowI2 imageI mult_left_mono)
  show ?thesis 
  proof (rule antisym)
    show "a * Inf (f ` A) \<le> (INF x\<in>A. a * f x)"
      by (simp add: assms cINF_greatest cINF_lower2 ordered_comm_semiring_class.comm_mult_left_mono)
    have "\<And>x. x\<in>A \<Longrightarrow> (INF x\<in>A. a * f x) / a \<le> f x"
      by (metis (full_types) False \<open>a \<ge> 0\<close> bdd cINF_lower divide_le_eq less_le mult.commute)
    then have "(INF x\<in>A. a * f x)/a \<le> Inf (f ` A)"
      using assms by (auto simp add: le_cInf_iff)
    with False assms show "(INF x\<in>A. a * f x) \<le> a * Inf (f ` A)"
      by (auto simp: field_simps)
  qed 
qed (use assms in auto)

end

end
