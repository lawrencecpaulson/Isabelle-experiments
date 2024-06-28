section \<open>The Proof of Theorem 1.1\<close>

theory The_Proof
  imports From_Diagonal

begin

definition "H \<equiv> \<lambda>p. -p * log 2 p - (1-p) * log 2 (1-p)"

lemma H0 [simp]: "H 0 = 0" and H1 [simp]: "H 1 = 0"
  by (auto simp: H_def)

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

lemma g_eq: "g x y = log 2 (5/2) + x * log 2 (5/3) + y * log 2 ((2 * (x+y)) / (5*y))"
  by (simp add: g_def GG_def)

definition "f1 \<equiv> \<lambda>x y. x + y + (2-x) * H(1/(2-x))"

(*A singularity of x=1. Okay if we put ln(0) = 0! *)
text \<open>Claim (62)\<close>
lemma FF_le_f1:
  fixes k::nat and x y::real
  assumes x: "0 \<le> x" "x \<le> 1" and y: "0 \<le> y" "y \<le> 1" and "k>0"
  shows "FF k x y \<le> f1 x y"
proof -
  let ?kl = "k + k - nat \<lceil>x*k\<rceil>"
  have gt0: "nat\<lfloor>k - x*k\<rfloor> > 0"
    sorry
  have kk_less_1: "k / ?kl < 1"
    using x gt0 by (simp add: field_split_simps, linarith)
  have le: "nat\<lfloor>k - x*k\<rfloor> \<le> k - nat\<lceil>x*k\<rceil>"
    using floor_ceiling_diff_le x
    by (meson mult_left_le_one_le mult_nonneg_nonneg of_nat_0_le_iff)
  have RN_gt0: "RN k (nat\<lfloor>k - x*k\<rfloor>) > 0"
    by (metis gt0 RN_eq_0_iff \<open>k>0\<close> gr0I)
  then have \<section>: "RN k (nat\<lfloor>k - x*k\<rfloor>) \<le> k + nat\<lfloor>k - x*k\<rfloor> choose k"
    using RN_le_choose by force
  also have "\<dots> \<le> k + k - nat\<lceil>x*k\<rceil> choose k"
  proof (intro Binomial.binomial_mono)
    show "k + nat \<lfloor>k - x*k\<rfloor> \<le> ?kl"
      using RN_gt0 le linorder_not_le by fastforce
  qed
  finally have "RN k (nat \<lfloor>real k - x*k\<rfloor>) \<le> ?kl choose k" .
  with RN_gt0 have "FF k x y \<le> log 2 (?kl choose k) / k + x + y"
    by (simp add: FF_def divide_right_mono nat_less_real_le)
  also have "\<dots> \<le> (?kl * H(k/?kl)) / k + x + y"
  proof -
    have "k \<le> k + k - nat\<lceil>x*k\<rceil>"
      using gt0 by linarith
    then show ?thesis
      by (simp add: H_12_1 divide_right_mono)
  qed
  also have "\<dots> \<le> f1 x y"
  proof -
    have 1: "?kl / k \<le> 2-x"
        using x by (simp add: field_split_simps)
    have 2: "H (k / ?kl) \<le> H (1 / (2-x))"
    proof (intro H_half_mono')
      show "1 / (2-x) \<le> k / ?kl"
        using x gt0 by (simp add: field_split_simps, linarith)
    qed (use x kk_less_1 in auto)
    have "?kl / k * H (k / ?kl) \<le> (2-x) * H (1 / (2-x))"
      using x mult_mono [OF 1 2 _ H_ge0] kk_less_1 by fastforce
    then show ?thesis
      by (simp add: f1_def)
  qed
  finally show ?thesis .
qed


definition "f2 \<equiv> \<lambda>x y. f1 x y - (log 2 (exp 1) / 40) * (1-x) / (2-x)"

text \<open>Claim (63) IN WEAKENED FORM\<close>
lemma (in P0_min) FF_le_f2_aux:
  fixes k::nat and x y::real
  assumes x: "3/4 \<le> x" "x \<le> 1" and y: "0 \<le> y" "y \<le> 1"
  and l: "real l = k - x*k"
  assumes p0_min_101: "p0_min \<le> 1 - 1/5"
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  defines "\<gamma>0 \<equiv> min \<gamma> (0.07)" 
  assumes big: "Big_Closer_10_1 \<gamma>0 l"
  shows "FF k x y \<le> f2 x y + 3 / (real k * ln 2)"
proof -
  have "l>0"
    using big by (simp add: Big_Closer_10_1_def)
  have "x>0"
    using x by linarith
  with l have "k\<ge>l"
    by (smt (verit, del_insts) of_nat_0_le_iff of_nat_le_iff pos_prod_lt)
  with \<open>0 < l\<close> have "k>0" by force
  have RN_gt0: "RN k l > 0"
    by (metis RN_eq_0_iff \<open>0 < k\<close> \<open>0 < l\<close> gr0I)
  define \<delta> where "\<delta> \<equiv> \<gamma>/40"
  have A: "l / real(k+l) = (1-x)/(2-x)"
    using x \<open>k>0\<close> by (simp add: l field_simps)
  have B: "real(k+l) / k = 2-x"
    using \<open>0 < k\<close> l by auto
  have \<gamma>: "\<gamma> \<le> 1/5" 
    using x A by (simp add: \<gamma>_def)
  have "1 - 1 / (2-x) = (1-x) / (2-x)"
    using x by (simp add: divide_simps)
  then have Heq: "H (1 / (2-x)) = H ((1-x) / (2-x))"
    by (metis H_reflect)
  have "RN k l \<le> exp (-\<delta>*k + 3) * (k+l choose l)"
    unfolding \<delta>_def \<gamma>_def
  proof (rule Closer_10_1)
    show "real l / (real k + real l) \<le> 1/5"
      using \<gamma> \<gamma>_def by blast
    have "min (l / (k + real l)) 0.07 > 0"
      using \<open>l>0\<close> by force 
    then show "Big_Closer_10_1 (min (l / (k + real l)) 0.07) l"
      using big \<gamma>0_def \<gamma>_def by blast
  qed (use p0_min_101 in auto)
  with RN_gt0 have "FF k x y \<le> log 2 (exp (-\<delta>*k + 3) * (k+l choose l)) / k + x + y"
    unfolding FF_def
    by (intro add_mono divide_right_mono Transcendental.log_mono; simp flip: l)
  also have "\<dots> = (log 2 (exp (-\<delta>*k + 3)) + log 2 (k+l choose l)) / k + x + y"
    by (simp add: log_mult)
  also have "\<dots> \<le> ((-\<delta>*k + 3) / ln 2 + (k+l) * H(l/(k+l))) / k + x + y"
    using H_12_1
    by (smt (verit, ccfv_SIG) General_Extras.log_exp divide_right_mono le_add2 of_nat_0_le_iff)
  also have "\<dots> = (-\<delta>*k + 3) / k / ln 2 + (k+l) / k * H(l/(k+l)) + x + y"
    by argo
  also have "\<dots> = -\<delta> / ln 2 + 3 / (k * ln 2) + (2-x) * H((1-x)/(2-x)) + x + y"
  proof -
    have "(-\<delta>*k + 3) / k / ln 2 = -\<delta> / ln 2 + 3 / (k * ln 2)"
      using \<open>0 < k\<close> by (simp add: divide_simps)
    moreover have "(k+l) / k * H(l/(k+l)) = (2-x) * H((1-x)/(2-x))"
      using A B by presburger
    ultimately show ?thesis
      by argo
  qed
  also have "\<dots> = - (log 2 (exp 1) / 40) * (1-x) / (2-x) + 3 / (k * ln 2) + (2-x) * H((1-x)/(2-x)) + x + y"
    using A by (force simp: \<delta>_def \<gamma>_def field_simps)
  also have "\<dots> \<le> f2 x y + 3 / (real k * ln 2)"
    by (simp add: Heq f1_def f2_def)
  finally show ?thesis .
qed

text \<open>probably we are able to assume that the variables are rational\<close>
lemma (in P0_min) FF_le_f2:
  fixes x y::real
  assumes x: "3/4 \<le> x" "x \<le> 1" and y: "0 \<le> y" "y \<le> 1"
  assumes p0_min_101: "p0_min \<le> 1 - 1/5"
  defines "\<gamma> \<equiv> (1-x) / (2-x)"
  shows "FF k x y \<le> f2 x y + 3 / (real k * ln 2)"
proof (cases "x=1")
  case True
  then show ?thesis 
    by (simp add: FF_def f2_def f1_def)
next
  case False
  with x have "x<1"
    by linarith
  define \<gamma>0 where "\<gamma>0 \<equiv> min \<gamma> (0.07)" 
  have \<gamma>: "0<\<gamma>" "\<gamma> \<le> 1/5"
    using x \<open>x<1\<close> y by (auto simp add: \<gamma>_def divide_simps)
  then have "\<gamma>0>0"
    by (simp add: \<gamma>0_def)
  then obtain l where big: "Big_Closer_10_1 \<gamma>0 l"
    by (meson Big_Closer_10_1 eventually_sequentially order.refl)
  have "l>0"
    using big by (simp add: Big_Closer_10_1_def)
  have "x>0"
    using x by linarith
  define k where "k = nat\<lceil>l/(1-x)\<rceil>"
  have "k\<ge>l"
    using x False by (simp add: k_def divide_simps mult_left_le le_natceiling_iff)
  with \<open>0 < l\<close> have "k>0" by force

  have lle: "l \<le> (1-x) * k"
    unfolding k_def
    by (metis \<open>x < 1\<close> diff_gt_0_iff_gt mult.commute pos_divide_le_eq real_nat_ceiling_ge)

  have RN_gt0: "RN k l > 0"
    by (metis RN_eq_0_iff \<open>0 < k\<close> \<open>0 < l\<close> gr0I)
  define \<delta> where "\<delta> \<equiv> \<gamma>/40"
  have "1 - 1 / (2-x) = (1-x) / (2-x)"
    using x by (simp add: divide_simps)
  then have Heq: "H (1 / (2-x)) = H ((1-x) / (2-x))"
    by (metis H_reflect)
  have "RN k l \<le> exp (- (l / (k + real l) / 40) * k + 3) * (k+l choose l)"
    unfolding \<delta>_def \<gamma>_def
  proof (rule Closer_10_1)
    have "1-x \<le> 1/4"
      using x by linarith
    then have "4 * real l \<le> k"
      using mult_left_mono [OF lle, of 4] mult_ac
      by (metis (no_types, opaque_lifting) le_divide_eq_numeral1(1) mult_left_le of_nat_0_le_iff order.trans zero_le_numeral)
    then show "l / (k + real l) \<le> 1/5"
      by (simp add: divide_simps)
    have "min (l / (k + real l)) 0.07 > 0"
      using \<open>l>0\<close> by force 
    then show "Big_Closer_10_1 (min (l / (k + real l)) 0.07) l"
      using big \<gamma>0_def \<gamma>_def by blast
  qed (use p0_min_101 in auto)





  oops

lemma DD:
  fixes \<delta>::real
  assumes "0 < \<delta>" "\<delta> \<le> 1 / 2^11"
  shows "\<forall>\<^sup>\<infinity>k. log 2 (RN k k) / k \<le> 2-\<delta>"
  sorry

text \<open>Main theorem 1.1: the exponent is approximately 3.9987\<close>
theorem 
  obtains \<epsilon>::real where "\<epsilon>>0" "\<forall>\<^sup>\<infinity>k. RN k k \<le> (4-\<epsilon>)^k"
proof
  let ?\<epsilon> = "0.00135::real"
  let ?\<delta> = "1 / 2^11::real"
  have "?\<delta> > 0"
    by simp
  then have "\<forall>\<^sup>\<infinity>k. k>0 \<and> log 2 (RN k k) / k \<le> 2-?\<delta>"
    unfolding eventually_conj_iff using DD eventually_gt_at_top by blast
  then have A: "\<forall>\<^sup>\<infinity>k. RN k k \<le> (2 powr (2-?\<delta>)) ^ k"
  proof (eventually_elim)
    case (elim k)
    then have "log 2 (RN k k) \<le> (2-?\<delta>) * k"
      by (meson of_nat_0_less_iff pos_divide_le_eq)
    then have "RN k k \<le> 2 powr ((2-?\<delta>) * k)"
      by (smt (verit, best) Transcendental.log_le_iff powr_ge_pzero)
    then show "RN k k \<le> (2 powr (2-?\<delta>)) ^ k"
      by (simp add: mult.commute powr_power)
  qed
  moreover have "2 powr (2-?\<delta>) \<le> 4 - ?\<epsilon>"
    by (approximation 50)
  ultimately show "\<forall>\<^sup>\<infinity>k. real (RN k k) \<le> (4-?\<epsilon>) ^ k"
    by (smt (verit) power_mono powr_ge_pzero eventually_mono)
qed auto

end
