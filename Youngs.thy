section \<open>Misc experiments\<close>

theory Youngs imports
  "HOL-Library.Sum_of_Squares" "HOL-Analysis.Analysis" "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
  "Stirling_Formula.Stirling_Formula"
  "HOL-ex.Sketch_and_Explore"
   
begin

subsection \<open>Possible library additions\<close>

thm sum.atLeast_Suc_lessThan_Suc_shift
context comm_monoid_set
begin

lemma atLeast_atMost_pred_shift:
  "F (g \<circ> (\<lambda>n. n - Suc 0)) {Suc m..Suc n} = F g {m..n}"
  unfolding atLeast_Suc_atMost_Suc_shift by simp

lemma atLeast_lessThan_pred_shift:
  "F (g \<circ> (\<lambda>n. n - Suc 0)) {Suc m..<Suc n} = F g {m..<n}"
  unfolding atLeast_Suc_lessThan_Suc_shift by simp

end


thm of_int_less_iff
context linordered_idom
begin

lemma of_nat_nat_eq_iff: "of_nat (nat i) = of_int i \<longleftrightarrow> 0 \<le> i"
  using local.of_int_le_iff by fastforce

end



thm fact_div_fact
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

lemma field_differentiable_diff_const [simp,derivative_intros]:
  "(-)c field_differentiable F"
  unfolding field_differentiable_def
  by (rule derivative_eq_intros exI | force)+

thm deriv_add
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

subsection \<open>Some irrational numbers\<close>
text \<open>From Aigner and Ziegler, Proofs from THE BOOK (Springer, 2018), Chapter 8, pp. 50--51.\<close>

definition hf where "hf \<equiv> \<lambda>n. \<lambda>x::real. (x^n * (1-x)^n) / fact n"

definition cf where "cf \<equiv> \<lambda>n i. if i < n then 0 else (n choose (i-n)) * (-1)^(i-n)"

text \<open>Mere knowledge that the coefficients are integers is not enough later on.\<close>
lemma hf_int_poly:
  fixes x::real
  shows "hf n = (\<lambda>x. (1 / fact n) * (\<Sum>i=0..2*n. real_of_int (cf n i) * x^i))"
proof 
  fix x
  have inj: "inj_on ((+)n) {..n}" 
    by (auto simp: inj_on_def)
  have [simp]: "((+)n) ` {..n} = {n..2*n}"
    using nat_le_iff_add by fastforce
  have "(x^n * (-x + 1)^n) = x ^ n * (\<Sum>k\<le>n. real (n choose k) * (- x) ^ k)"
    unfolding binomial_ring by simp
  also have "... = x ^ n * (\<Sum>k\<le>n. real_of_int ((n choose k) * (-1)^k) * x ^ k)"
    by (simp add: mult.assoc flip: power_minus)
  also have "... = (\<Sum>k\<le>n. real_of_int ((n choose k) * (-1)^k) * x ^ (n+k))"
    by (simp add: sum_distrib_left mult_ac power_add)
  also have "... = (\<Sum>i=n..2*n. real_of_int (cf n i) * x^i)"
    by (simp add: sum.reindex [OF inj, simplified] cf_def)
  finally have "hf n x = (1 / fact n) * (\<Sum>i = n..2 * n. real_of_int (cf n i) * x^i)"
    by (simp add: hf_def)
  moreover have "(\<Sum>i = 0..<n. real_of_int (cf n i) * x^i) = 0"
    by (simp add: cf_def)
  ultimately show "hf n x = (1 / fact n) * (\<Sum>i = 0..2 * n. real_of_int (cf n i) * x^i)"
    using sum.union_disjoint [of "{0..<n}" "{n..2*n}" "\<lambda>i. real_of_int (cf n i) * x^i"]
    by (simp add: ivl_disj_int_two(7) ivl_disj_un_two(7) mult_2)
qed

text \<open>Lemma (ii) with strict inequalities is more work and less useful.\<close>
lemma hf_nonneg:
  assumes "0 \<le> x" "x \<le> 1" shows "0 \<le> hf n x" 
    using assms by (simp add: hf_def)

lemma hf_le_inverse_fact:
  assumes "0 \<le> x" "x \<le> 1" shows "hf n x \<le> 1/fact n"
  using assms by (auto simp: hf_def divide_simps mult_le_one power_le_one)

lemma hf_differt [iff]: "hf n differentiable at x"
  unfolding hf_int_poly differentiable_def
  by (intro derivative_eq_intros exI | simp)+

lemma deriv_sum_int:
  "deriv (\<lambda>x. \<Sum>i=0..n. real_of_int (c i) * x^i) x 
     = (if n=0 then 0 else (\<Sum>i=0..n - Suc 0. real_of_int ((int i + 1) * c (Suc i)) * x^i))"
  (is "deriv ?f x = (if n=0 then 0 else ?g)")
proof -
  have "(?f has_real_derivative ?g) (at x)" if "n > 0"
  proof -
    have "(\<Sum>i = 0..n. i * x ^ (i - Suc 0) * (c i))
        = (\<Sum>i = Suc 0..n. (real (i - Suc 0) + 1) * real_of_int (c i) * x ^ (i - Suc 0))"
      using that by (auto simp add: sum.atLeast_Suc_atMost intro!: sum.cong)
    also have "... = sum ((\<lambda>i. (real i + 1) * real_of_int (c (Suc i)) * x^i) \<circ> (\<lambda>n. n - Suc 0)) {Suc 0..Suc (n - Suc 0)}"
      using that by simp
    also have "... = ?g"
      by (simp flip: sum.atLeast_atMost_pred_shift [where m=0])
    finally have \<section>: "(\<Sum>a = 0..n. a * x ^ (a - Suc 0) * (c a)) = ?g" .
    show ?thesis
      by (rule derivative_eq_intros \<section> | simp)+
  qed
  then show ?thesis
    by (force intro: DERIV_imp_deriv)
qed

text \<open>We calculate the coefficients of the $k$th derivative precisely.\<close>
lemma hf_deriv_int_poly:
   "(deriv^^k) (hf n) = (\<lambda>x. (1 / fact n) * (\<Sum>i=0..2*n-k. real_of_int (int(\<Prod>{i<..i+k}) * cf n (i+k)) * x^i))"
proof (induction k)
  case 0
  show ?case 
    by (simp add: hf_int_poly)
next
  case (Suc k)
  define F where "F \<equiv> \<lambda>x. (\<Sum>i = 0..2*n - k. real_of_int (int(\<Prod>{i<..i+k}) * cf n (i+k)) * x^i)"
  have Fd: "F field_differentiable at x" for x
    unfolding field_differentiable_def F_def
    by (rule derivative_eq_intros exI | force)+
  have "deriv (\<lambda>x. F x / fact n) x 
      = (\<Sum>i = 0..2 * n - Suc k. real_of_int (int(\<Prod>{i<..i+ Suc k}) * cf n (Suc (i+k))) * x^i) / fact n" for x
    unfolding deriv_cdivide_right [OF Fd]
    apply (simp add: F_def deriv_sum_int cf_def add.commute flip: of_int_mult)
    apply (auto intro!: sum.cong)
    by (metis Suc_le_mono atLeastSucAtMost_greaterThanAtMost le_add1 of_nat_Suc prod.head)+
  then show ?case
    by (simp add: Suc F_def)
qed

lemma hf_deriv_0: "(deriv^^k) (hf n) 0 \<in> \<int>"
proof (cases "n \<le> k")
  case True
  then obtain j where "(fact k::real) = real_of_int j * fact n"
    using fact_dvd 
    by (metis dvd_def fact_nonzero mult.commute nonzero_mult_div_cancel_left of_int_fact real_of_int_div) 
  moreover have "prod real {0<..k} = fact k"
    by (simp add: fact_prod atLeastSucAtMost_greaterThanAtMost)
  ultimately show ?thesis
    by (simp add: hf_deriv_int_poly dvd_def)
next
  case False
  then show ?thesis
    by (simp add: hf_deriv_int_poly cf_def)
qed

lemma deriv_hf_minus: "deriv (hf n) = (\<lambda>x. - deriv (hf n) (1-x))"
proof 
  fix x
  have "hf n = hf n \<circ> (\<lambda>x. (1-x))"
    by (simp add: fun_eq_iff hf_def mult.commute)
  then have "deriv (hf n) x = deriv (hf n \<circ> (\<lambda>x. (1-x))) x"
    by fastforce
  also have "... = deriv (hf n) (1-x) * deriv ((-) 1) x"
    by (intro real_derivative_chain) auto
  finally show "deriv (hf n) x = - deriv (hf n) (1-x)"
    by simp
qed

lemma deriv_n_hf_diffr [iff]: "(deriv^^k) (hf n) field_differentiable at x"
  unfolding field_differentiable_def hf_deriv_int_poly
  by (rule derivative_eq_intros exI | force)+

lemma deriv_n_hf_minus: "(deriv^^k) (hf n) = (\<lambda>x. (-1)^k * (deriv^^k) (hf n) (1-x))"
proof (induction k)
  case 0
  then show ?case
    by (simp add: fun_eq_iff hf_def)
next
  case (Suc k)
  have o: "(\<lambda>x. (deriv ^^ k) (hf n) (1-x)) = (deriv ^^ k) (hf n) \<circ> (-) 1"
    by auto
  show ?case
  proof
    fix x
    have [simp]: "((deriv^^k) (hf n) \<circ> (-) 1) field_differentiable at x"
      by (force intro: field_differentiable_compose)
    have "(deriv ^^ Suc k) (hf n) x = deriv (\<lambda>x. (-1) ^ k * (deriv ^^ k) (hf n) (1-x)) x"
      by simp (metis Suc)
    also have "... = (-1) ^ k * deriv (\<lambda>x. (deriv ^^ k) (hf n) (1-x)) x"
      using o by fastforce
    also have "... = (-1) ^ Suc k * (deriv ^^ Suc k) (hf n) (1-x)"
      by (subst o, subst deriv_chain, auto)
    finally show "(deriv ^^ Suc k) (hf n) x = (-1) ^ Suc k * (deriv ^^ Suc k) (hf n) (1-x)" .
  qed
qed

lemma hf_deriv_1: "(deriv^^k) (hf n) 1 \<in> \<int>"
  by (smt (verit, best) Ints_1 Ints_minus Ints_mult Ints_power deriv_n_hf_minus hf_deriv_0)

lemma hf_deriv_eq_0: "k > 2*n \<Longrightarrow> (deriv^^k) (hf n) = (\<lambda>x. 0)"
  by (force simp add: cf_def hf_deriv_int_poly)

lemma hf_Suc: "hf (Suc n) x = hf n x * x * (1-x) / Suc n"
  by (simp add: hf_def algebra_simps)

lemma exp_hf_lowerbound:
  assumes x: "1/3 \<le> x" "x \<le> 2/3" and "s \<ge> 0"
  shows "exp (of_int s * (1/3)) * hf n (1/3) \<le> exp (of_int s * x) * hf n x"
proof -
  have hf: "hf n (1/3) \<le> hf n x"
  proof (induction n)
    case (Suc n)
    have "2 \<le> 9 * x * (1 - x)"
      using x by sos
    then have "2 * (1 + real n) * hf n x \<le> (9 * x * (1 - x)) * (1 + real n) * hf n x"
      using assms by (intro mult_mono hf_nonneg) auto
    then show ?case 
      apply (simp add: Suc hf_Suc field_simps)
      by (smt (verit, best) Suc mult_left_mono of_nat_0_le_iff)
  qed (auto simp: hf_def)
  show ?thesis
    using assms by (intro mult_mono exp_le_cancel_iff [THEN iffD2] hf hf_nonneg) auto
qed 

lemma exp_nat_irrational:
  assumes "s > 0"
  shows "exp (real_of_int s) \<notin> \<rat>"
proof
  assume "exp (real_of_int s) \<in> \<rat>"
  then obtain a b where ab: "a > 0" "b > 0" "coprime a b" and exp_s: "exp s = of_int a / of_int b"
    using Rats_cases' div_0 exp_not_eq_zero of_int_0
    by (smt (verit, best) exp_gt_zero of_int_0_less_iff zero_less_divide_iff)
  define n where "n \<equiv> nat (max (a^2) (3 * s^3))"
  then have ns3: "s^3 \<le> real n / 3"
    by linarith
  have "n > 0"
    using \<open>a > 0\<close> n_def by (smt (verit, best) zero_less_nat_eq zero_less_power)
  then have "s ^ (2*n+1) \<le> s ^ (3*n)"
    using \<open>a > 0\<close> assms by (intro power_increasing) auto
  also have "... = real_of_int(s^3) ^ n"
    by (simp add: power_mult)
  also have "... \<le> (n / 3) ^ n"
    using assms ns3 by (simp add: power_mono)
  also have "... \<le> (n / exp 1) ^ n"
    using exp_le \<open>n > 0\<close>
    by (auto simp add: divide_simps)
  finally have s_le: "s ^ (2*n+1) \<le> (n / exp 1) ^ n"
    by presburger 
  have a_less: "a < sqrt (2*pi*n)"
  proof -
    have "a = sqrt (a^2)"
      by (simp add: ab(1) order_less_imp_le)
    also have "... \<le> sqrt n"
      unfolding n_def
      by (smt (verit, ccfv_SIG) int_nat_eq of_nat_less_of_int_iff real_sqrt_le_mono)
    also have "... < sqrt (2*pi*n)"
      by (smt (verit, ccfv_SIG) \<open>0 < n\<close> divide_le_eq_1_pos mult.commute nonzero_mult_div_cancel_left of_nat_0_less_iff pi_gt_zero real_sqrt_less_mono sin_gt_zero_02 sin_le_zero)
    finally show ?thesis .
  qed
  have "sqrt (2*pi*n) * (n / exp 1) ^ n > a * s ^ (2*n+1)"
    using mult_strict_right_mono [OF a_less] mult_left_mono [OF s_le]
    by (smt (verit, best) s_le ab(1) assms of_int_1 of_int_le_iff of_int_mult zero_less_power)
  then have n: "fact n > a * s ^ (2*n+1)"
    using fact_bounds(1) by (smt (verit, best) \<open>0 < n\<close> of_int_fact of_int_less_iff)
  define F where "F \<equiv> \<lambda>x. \<Sum>i\<le>2*n. (-1)^i * s^(2*n-i) * (deriv^^i) (hf n) x"
  have Fder [derivative_intros]: "(F has_real_derivative -s * F x + s ^ (2*n+1) * hf n x) (at x)" for x
  proof -
    have *: "sum f {..n+n} = sum f {..<n+n}" if "f (n+n) = 0" for f::"nat \<Rightarrow> real"
      by (smt (verit, best) lessThan_Suc_atMost sum.lessThan_Suc that)
    have [simp]: "(deriv ((deriv ^^ (n+n)) (hf n)) x) = 0"
      using hf_deriv_eq_0 [where k= "Suc(n+n)"] by simp
    have \<section>: "(\<Sum>k\<le>n+n. (-1) ^ k * ((deriv ^^ Suc k) (hf n) x * of_int s ^ (n+n - k))) 
           + s * (\<Sum>j=0..n+n. (-1) ^ j * ((deriv ^^ j) (hf n) x * of_int s ^ (n+n - j))) 
           = s * (hf n x * of_int s ^ (n+n))" 
      using \<open>n>0\<close>
      apply (subst sum_Suc_reindex)
      apply (simp add: algebra_simps atLeast0AtMost)
      apply (force simp add: * mult.left_commute [of "of_int s"] minus_nat.diff_Suc sum_distrib_left 
                   simp flip: sum.distrib intro!: comm_monoid_add_class.sum.neutral split: nat.split_asm)
      done
    show ?thesis
      unfolding F_def 
      apply (rule derivative_eq_intros field_differentiable_derivI | simp)+
      using \<section> by (simp add: algebra_simps atLeast0AtMost eval_nat_numeral)
  qed

  have F01_Ints: "F 0 \<in> \<int>" "F 1 \<in> \<int>"
    by (simp_all add: F_def hf_deriv_0 hf_deriv_1 Ints_sum)
  define sF where "sF \<equiv> \<lambda>x. exp (of_int s * x) * F x"
  define sF' where "sF' \<equiv> \<lambda>x. of_int s ^ Suc(2*n) * (exp (of_int s * x) * hf n x)"
  have sF_der: "(sF has_real_derivative sF' x) (at x)" for x
    unfolding sF_def sF'_def
    by (rule refl derivative_eq_intros | force simp: algebra_simps)+
  let ?N = "b * integral {0..1} sF'"
  have sF'_integral: "(sF' has_integral sF 1 - sF 0) {0..1}"
    by (smt (verit) fundamental_theorem_of_calculus has_field_derivative_iff_has_vector_derivative has_vector_derivative_at_within sF_der)
  then have "?N = a * F 1 - b * F 0"
    using \<open>b > 0\<close> by (simp add: integral_unique exp_s sF_def algebra_simps)
  also have "... \<in> \<int>"
    using hf_deriv_1 by (simp add: F01_Ints)
  finally have N_Ints: "?N \<in> \<int>" .

  define l13 where "l13 \<equiv> of_int s ^ Suc (2*n) * exp (of_int s * (1/3)) * hf n (1/3)"
  have subset01: "{1/3..2/3} \<subseteq> {0..1::real}"
    by auto
  have integ_13_23: "sF' integrable_on {1/3..2/3}"
    by (meson subset01 integrable_on_def integrable_on_subinterval sF'_integral)
  have "0 < integral {1/3..2/3} (\<lambda>x::real. l13)"
    by (simp add: hf_def l13_def assms)
  also have "\<dots> \<le> integral {1/3..2/3} sF'"
  proof (rule integral_le)
    fix x::real assume "x \<in> {1/3..2/3}"
    with exp_hf_lowerbound assms show "l13 \<le> sF' x"
      by (auto simp: l13_def sF'_def)
  qed (use integ_13_23 in auto)
  also have "... \<le> integral {0..1} sF'"
    using integral_subset_le [OF subset01 integ_13_23] sF'_integral assms hf_nonneg sF'_def by auto
  finally have "integral {0..1} sF' > 0" .
  then have "0 < ?N"
    by (simp add: \<open>b > 0\<close>)
  have "integral {0..1} sF' = of_int s ^ Suc(2*n) * integral {0..1} (\<lambda>x. exp (s*x) * hf n x)"
    unfolding sF'_def by force 
  also have "... \<le> of_int s ^ Suc(2*n) * (exp s * (1 / fact n))"
  proof (rule mult_left_mono)
    have "integral {0..1} (\<lambda>x. exp (s*x) * hf n x)  \<le> integral {0..1} (\<lambda>x::real. exp s * (1 / fact n))"
    proof (intro mult_mono integral_le)
      show "(\<lambda>x. exp (s*x) * hf n x) integrable_on {0..1}"
        using \<open>0 < ?N\<close> not_integrable_integral sF'_def by fastforce
    qed (use assms hf_nonneg hf_le_inverse_fact in auto)
    also have "... = exp s * (1 / fact n)"
      by simp
    finally show "integral {0..1} (\<lambda>x. exp (s*x) * hf n x) \<le> exp s * (1 / fact n)" .
  qed (use assms in auto)
  finally have "?N \<le> b * of_int s ^ Suc(2*n) * exp s * (1 / fact n)"
    using \<open>b > 0\<close> by (simp add: sF'_def mult_ac divide_simps)
  also have "... < 1"
    using n apply (simp add: field_simps exp_s)
    by (metis of_int_fact of_int_less_iff of_int_mult of_int_power)
  finally show False
    using \<open>0 < ?N\<close> Ints_cases N_Ints by force
qed

theorem exp_irrational:
  fixes q::real
  assumes "q \<in> \<rat>" "q \<noteq> 0"
  shows "exp q \<notin> \<rat>"
proof 
  assume q: "exp q \<in> \<rat>"
  obtain s t where "s \<noteq> 0" "t > 0" "q = of_int s / of_int t"
    by (metis Rats_cases' assms div_0 of_int_0)
  then have "(exp q) ^ (nat t) = exp s"
    by (smt (verit, best) exp_divide_power_eq of_nat_nat zero_less_nat_eq)
  moreover have "exp q ^ (nat t) \<in> \<rat>"
    by (simp add: q)
  ultimately show False
    by (smt (verit, del_insts) Rats_inverse \<open>s \<noteq> 0\<close> exp_minus exp_nat_irrational of_int_of_nat)
qed


subsection \<open>Experiments involving Young's Inequality\<close>

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


lemma D:
  fixes f :: "real \<Rightarrow> real"
  assumes sm: "strict_mono_on f {0..}" and cont: "continuous_on {0..} f" and "0 \<le> a" "0 \<le> b" "f 0 = 0" "f a = b"
  shows "a*b = integral {0..a} f + integral {0..b} (inv_into {0..a} f)"
proof (cases "a=0")
  case False
  then have "a > 0"
    using assms(3) by linarith
  have "continuous_on {0..a} f"
    using cont continuous_on_subset by fastforce
  with sm have "continuous_on {0..b} (inv_into {0..a} f)"
    apply (simp add: strict_mono_on_def)
    by (metis assms(3) assms(5) assms(6) atLeastAtMost_iff strict_mono_continuous_inv strict_mono_onI)
  obtain S where S: "(f has_integral S) {0..a}"
    using \<open>continuous_on {0..a} f\<close> integrable_continuous_real by blast
  { fix \<epsilon> :: real
    assume "\<epsilon> > 0"
    with \<open>a > 0\<close> have "\<epsilon> / (2 * a) > 0"
      by simp
    with S \<open>a > 0\<close> has_integral_factor_content_real [of f S 0 a] 
    obtain \<gamma> where "gauge \<gamma>"
    and \<gamma>: "\<And>p. p tagged_division_of {0..a} \<and> \<gamma> fine p \<longrightarrow>
            norm ((\<Sum>(x,K)\<in>p. content K *\<^sub>R f x) - S) \<le> (\<epsilon> / (2*a)) * content {0..a}"
      by auto
    obtain \<D> where \<D>: "\<D> tagged_division_of {0..a} \<and> \<gamma> fine \<D>"
      by (meson \<open>gauge \<gamma>\<close> fine_division_exists_real)
    then have "norm ((\<Sum>(x,K)\<in>\<D>. content K *\<^sub>R f x) - S) \<le> \<epsilon>/2"
      using False \<gamma> assms(3) by auto

(*This can't work. Riemann integrability is a stronger property. The fineness condition can't be satisfied.*)

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




(*ALL THIS APPARENTLY USELESS*)
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
