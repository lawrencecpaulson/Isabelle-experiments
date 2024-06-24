section \<open>The Proof of Theorem 1.1\<close>

theory The_Proof
  imports From_Diagonal

begin

definition "H \<equiv> \<lambda>p. -p * log 2 p - (1-p) * log 2 (1-p)"

lemma H_reflect: "H (1-p) = H p"
  by (simp add: H_def)

lemma H_ge0:
  assumes "0 \<le> p" "p \<le> 1"
  shows "0 \<le> H p"
  unfolding H_def
  by (smt (verit, best) assms mult_minus_left mult_le_0_iff zero_less_log_cancel_iff)

lemma H_half_mono:
  assumes "0<p'" "p'\<le>p" "p \<le> 1/2"
  shows "H p' \<le> H p"
proof -
  have "(H has_real_derivative 0) (at (1/2))" 
    unfolding H_def by (rule derivative_eq_intros | force)+
  define dH where "dH \<equiv> \<lambda>x::real. -ln(x)/ln(2) + ln(1 - x)/ln(2)"
  have dH: "(H has_real_derivative dH x) (at x)"
    if "0<x" "x<1" for x
    unfolding H_def dH_def log_def
    by (rule derivative_eq_intros | use that in force)+
  have "dH(1/2) = 0"
    by (simp add: dH_def)
  moreover
  have "dH x \<ge> 0" if "0<x" "x\<le>1/2" for x
    using that by (simp add: dH_def divide_right_mono)
  ultimately show ?thesis
    by (smt (verit) dH DERIV_nonneg_imp_nondecreasing assms le_divide_eq_1_pos)
qed

lemma H_half_mono':
  assumes "1/2 \<le> p'" "p'\<le>p" "p < 1"
  shows "H p' \<ge> H p"
  using H_half_mono [of "1-p" "1-p'"] H_reflect assms by auto

text \<open>Many thanks to Fedor Petrov on mathoverflow\<close>
lemma H_12_1:
  fixes a b::nat
  assumes "a \<ge> b"
  shows "log 2 (a choose b) \<le> a * H(b/a)"
proof (cases "a=b \<or> b=0")
  case True
  with assms show ?thesis
    by (auto simp: H_def)
next
  let ?p = "b/a"
  case False
  then have p01: "0 < ?p" "?p < 1"
    using assms by auto
  then have "(a choose b) * ?p ^ b * (1-?p) ^ (a-b) \<le> (?p + (1-?p)) ^ a"
    by (subst binomial_ring) (force intro!: member_le_sum assms)
  also have "\<dots> = 1"
    by simp
  finally have \<section>: "(a choose b) * ?p ^ b * (1-?p) ^ (a-b) \<le> 1" .
  have "log 2 (a choose b) + b * log 2 ?p + (a-b) * log 2 (1-?p) \<le> 0"
    using Transcendental.log_mono [OF _ _ \<section>]
    by (simp add: p01 assms log_mult log_nat_power)
  then show ?thesis
    using p01 False assms unfolding H_def by (simp add: field_simps)
qed 

definition "g \<equiv> GG (2/5)"

definition "f1 \<equiv> \<lambda>x y. x + y + (2-x) * H(1/(2-x))"

lemma FF_le_f1:
  fixes k::nat and x y::real
  assumes x: "0 \<le> x" "x \<le> 1" and y: "0 \<le> y" "y \<le> 1" and "k>0"
  shows "FF k x y \<le> f1 x y"
proof -
  let ?kkm = "k + k - nat \<lceil>x*k\<rceil>"
  have le: "nat\<lfloor>k - x*k\<rfloor> \<le> k - nat\<lceil>x*k\<rceil>"
    using floor_ceiling_diff_le x
    by (meson mult_left_le_one_le mult_nonneg_nonneg of_nat_0_le_iff)
  have gt0: "nat\<lfloor>k - x*k\<rfloor> > 0"
    sorry
  then have RN_gt0: "RN k (nat\<lfloor>k - x*k\<rfloor>) > 0"
    by (metis RN_eq_0_iff \<open>k>0\<close> gr0I)
  then have \<section>: "RN k (nat\<lfloor>k - x*k\<rfloor>) \<le> k + nat\<lfloor>k - x*k\<rfloor> choose k"
    using RN_le_choose by force
  also have "... \<le> k + k - nat\<lceil>x*k\<rceil> choose k"
  proof (intro Binomial.binomial_mono)
    show "k + nat \<lfloor>k - x*k\<rfloor> \<le> ?kkm"
      using RN_gt0 le linorder_not_le by fastforce
  qed
  finally have "RN k (nat \<lfloor>real k - x*k\<rfloor>) \<le> ?kkm choose k" .
  with RN_gt0 have "FF k x y \<le> log 2 (?kkm choose k) / k + x + y"
    by (simp add: FF_def divide_right_mono nat_less_real_le)
  also have "\<dots> \<le> (?kkm * H(k/?kkm)) / k + x + y"
  proof -
    have "k \<le> k + k - nat\<lceil>x*k\<rceil>"
      using gt0 by linarith
    then show ?thesis
      by (simp add: H_12_1 divide_right_mono)
  qed
  also have "... \<le> f1 x y"
  proof -
    have 1: "?kkm / k \<le> 2-x"
        using x by (simp add: field_split_simps)
    have 2: "H (real k / ?kkm) \<le> H (1 / (2-x))"
    proof (intro H_half_mono')
      show "1 / 2 \<le> 1 / (2-x)"
        using x by auto
    next
      show "1 / (2-x) \<le> k / ?kkm"
        using x gt0 by (simp add: field_split_simps) linarith
    next
      show "real k / ?kkm < 1"
        by (smt (verit, best) Multiseries_Expansion.intyness_0 Num.of_nat_simps(4) approximation_preproc_nat(4) divide_less_eq_1 gt0 le less_imp_of_nat_less of_nat_mono)
    qed
    have "?kkm / k * H (k / ?kkm) \<le> (2-x) * H (1 / (2-x))"
    proof (intro mult_mono [OF 1 2] H_ge0)
      show "real k / ?kkm \<le> 1"
        using x gt0 by (simp add: divide_simps) linarith
    qed (use x in auto)
    then show ?thesis
      by (simp add: f1_def)
  qed
  finally show ?thesis .
qed

lemma g_eq: "g x y = log 2 (5/2) + x * log 2 (5/3) + y * log 2 ((2 * (x+y)) / (5*y))"
  by (simp add: g_def GG_def)

