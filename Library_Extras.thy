section \<open>Library Extras\<close>
text \<open>Already added to the repository\<close>

theory Library_Extras imports
  "HOL-Analysis.Analysis" 
  "HOL-ex.Sketch_and_Explore"
   
begin

text \<open>In fact, strict inequality is required only at a single point within the box.\<close>
lemma integral_less:
  fixes f :: "'n::euclidean_space \<Rightarrow> real"
  assumes cont: "continuous_on (cbox a b) f" "continuous_on (cbox a b) g" and "box a b \<noteq> {}"
    and fg: "\<And>x. x \<in> box a b \<Longrightarrow> f x < g x"
  shows "integral (cbox a b) f < integral (cbox a b) g"
proof -
  obtain int: "f integrable_on (cbox a b)" "g integrable_on (cbox a b)"
    using cont integrable_continuous by blast
  then have "integral (cbox a b) f \<le> integral (cbox a b) g"
    by (metis fg integrable_on_open_interval integral_le integral_open_interval less_eq_real_def)
  moreover have "integral (cbox a b) f \<noteq> integral (cbox a b) g"
  proof (rule ccontr)
    assume "\<not> integral (cbox a b) f \<noteq> integral (cbox a b) g"
    then have 0: "((\<lambda>x. g x - f x) has_integral 0) (cbox a b)"
      by (metis (full_types) cancel_comm_monoid_add_class.diff_cancel has_integral_diff int integrable_integral)
    have cgf: "continuous_on (cbox a b) (\<lambda>x. g x - f x)"
      using cont continuous_on_diff by blast
    show False
      using has_integral_0_cbox_imp_0 [OF cgf _ 0] assms(3) box_subset_cbox fg less_eq_real_def by fastforce
  qed
  ultimately show ?thesis
    by linarith
qed

lemma integral_less_real:
  fixes f :: "real \<Rightarrow> real"
  assumes "continuous_on {a..b} f" "continuous_on {a..b} g" and "{a<..<b} \<noteq> {}"
    and "\<And>x. x \<in> {a<..<b} \<Longrightarrow> f x < g x"
  shows "integral {a..b} f < integral {a..b} g"
  by (metis assms box_real integral_less)

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


lemma fact_eq_fact_times:
  assumes "m \<ge> n"
  shows "fact m = fact n * \<Prod>{Suc n..m}"
  unfolding fact_prod
  by (metis add.commute assms le_add1 le_add_diff_inverse of_nat_id plus_1_eq_Suc prod.ub_add_nat)

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
