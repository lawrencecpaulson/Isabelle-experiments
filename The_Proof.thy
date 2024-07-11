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

lemma H_bounded:
  assumes "0 \<le> p" "p \<le> 1"
  shows "H p \<le> H(1/2)"
  by (smt (verit, best) H0 H1 H_ge0 H_half_mono H_half_mono' assms)

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

definition "f2 \<equiv> \<lambda>x y. f1 x y - (log 2 (exp 1) / 40) * (1-x) / (2-x)"

definition "ff \<equiv> \<lambda>x y. if x < 3/4 then f1 x y else f2 x y"

definition "ff_bound \<equiv> 2 + 2 * H(1/2)"

text \<open>The proofs involving @{term Sup} are needlessly difficult because ultimately 
the sets involved are finite, eliminating the need to demonstrate boundedness.
Simpler might be to use the extended reals.\<close>

lemma le_ff_bound:
  assumes "x \<in> {0..1}" and "y \<in> {0..1}" 
  shows "ff x y \<le> ff_bound"
proof -
  have H: "H(1 / (2-x)) \<le> H(1/2)"
    using assms by (intro H_bounded) auto
  have "ff x y \<le> f1 x y"
    using assms by (simp add: ff_def f2_def)
  also have "... \<le> 1 + 1 + 2 * H(1/2)"
    unfolding f1_def
    using assms H by (intro add_mono mult_mono H_ge0) auto
  also have "... \<le> ff_bound"
    by (simp add: ff_bound_def)
  finally show ?thesis .
qed

lemma ff_GG_bound:
  assumes x: "x \<in> {0..1}" and y: "y \<in> {0..1}" 
  shows "min (ff x y) (GG \<mu> x y) \<le> ff_bound"
proof -
  have "ff x y \<le> ff_bound"
    using assms by (intro le_ff_bound) auto
  then show ?thesis
    by auto
qed

lemma bdd_above_ff_GG:
  assumes "x \<in> {0..1}" "u\<le>1"
  shows "bdd_above ((\<lambda>y. min (ff x y) (GG \<mu> x y) + \<eta>) ` {0..u})"
  using ff_GG_bound assms
  by (intro bdd_above.I2 [where M = "ff_bound+\<eta>"]) force

lemma bdd_above_SUP_ff_GG:
  assumes "u \<in> {0..1} \<rightarrow> {0..1}"
  shows "bdd_above ((\<lambda>x. \<Squnion>y\<in>{0..u x}. min (ff x y) (GG \<mu> x y) + \<eta>) ` {0..1})"
  using bdd_above_ff_GG assms
  by (intro bdd_aboveI [where M = "ff_bound + \<eta>"]) (auto simp: cSup_le_iff ff_GG_bound Pi_iff)



(*A singularity if x=1. Okay if we put ln(0) = 0! *)
text \<open>Claim (62)\<close>
lemma FF_le_f1:
  fixes k::nat and x y::real
  assumes x: "0 \<le> x" "x \<le> 1" and y: "0 \<le> y" "y \<le> 1"
  shows "FF k x y \<le> f1 x y"
proof (cases "nat\<lfloor>k - x*k\<rfloor> = 0")
  case True
  with x show ?thesis
    by (simp add: FF_def f1_def H_ge0)
next
  case False
  let ?kl = "k + k - nat \<lceil>x*k\<rceil>"
  have kk_less_1: "k / ?kl < 1"
    using x False by (simp add: field_split_simps, linarith)
  have le: "nat\<lfloor>k - x*k\<rfloor> \<le> k - nat\<lceil>x*k\<rceil>"
    using floor_ceiling_diff_le x
    by (meson mult_left_le_one_le mult_nonneg_nonneg of_nat_0_le_iff)
  have "k>0"
    using False zero_less_iff_neq_zero by fastforce
  have RN_gt0: "RN k (nat\<lfloor>k - x*k\<rfloor>) > 0"
    by (metis False RN_eq_0_iff \<open>k>0\<close> gr0I)
  then have \<section>: "RN k (nat\<lfloor>k - x*k\<rfloor>) \<le> k + nat\<lfloor>k - x*k\<rfloor> choose k"
    using RN_le_choose by force
  also have "\<dots> \<le> k + k - nat\<lceil>x*k\<rceil> choose k"
  proof (intro Binomial.binomial_mono)
    show "k + nat \<lfloor>k - x*k\<rfloor> \<le> ?kl"
      using False le by linarith
  qed
  finally have "RN k (nat \<lfloor>real k - x*k\<rfloor>) \<le> ?kl choose k" .
  with RN_gt0 have "FF k x y \<le> log 2 (?kl choose k) / k + x + y"
    by (simp add: FF_def divide_right_mono nat_less_real_le)
  also have "\<dots> \<le> (?kl * H(k/?kl)) / k + x + y"
  proof -
    have "k \<le> k + k - nat\<lceil>x*k\<rceil>"
      using False by linarith
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
        using x False by (simp add: field_split_simps, linarith)
    qed (use x kk_less_1 in auto)
    have "?kl / k * H (k / ?kl) \<le> (2-x) * H (1 / (2-x))"
      using x mult_mono [OF 1 2 _ H_ge0] kk_less_1 by fastforce
    then show ?thesis
      by (simp add: f1_def)
  qed
  finally show ?thesis .
qed



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



text \<open>The body of the proof has been extracted to allow the symmetry argument\<close>
lemma (in Book_Basis) From_11_1_Body:
  fixes V :: "'a set"
  assumes \<mu>: "0 < \<mu>" "\<mu> < 1" and "\<eta> > 0" and le1: "\<mu>/(1-\<mu>) + \<eta> \<le> 1"
    and ge_RN: "Suc nV \<ge> RN k k"
    and Red: "graph_density Red \<ge> 1/2" 
    and p0_min12: "p0_min \<le> 1/2"
    and Red_E: "Red \<subseteq> E" and Blue_def: "Blue = E\<setminus>Red" 
    and no_Red_K: "\<not> (\<exists>K. size_clique k K Red)"
    and no_Blue_K: "\<not> (\<exists>K. size_clique k K Blue)"
    and big: "Big_From_11_1 \<eta> \<mu> k"
  shows "log 2 (RN k k) / k \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..\<mu>*x/(1-\<mu>)+\<eta>}. min (ff x y) (GG \<mu> x y) + \<eta>)"
proof -  
  have big41: "Big_Blue_4_1 \<mu> k" and big61: "Big_Y_6_1 \<mu> k" 
    and big85: "Big_ZZ_8_5 \<mu> k" and big11_2: "Big_From_11_2 \<mu> k"
    and ok111_le_\<eta>: "ok_fun_11_1 \<mu> k / k \<le> \<eta>"
    and powr_le_\<eta>: "(2 / (1-\<mu>)) * k powr (-1/20) \<le> \<eta>" and "k>0"
    using big by (auto simp: Big_From_11_1_def Big_Y_6_1_def Big_Y_6_2_def)
  then have big53: "Big_Red_5_3 \<mu> k"
    by (meson Big_From_11_2_def)

  obtain X0 Y0 where card_X0: "card X0 \<ge> nV/2" and card_Y0: "card Y0 = gorder div 2"
    and "X0 = V \<setminus> Y0" "Y0\<subseteq>V"
    and p0_half: "1/2 \<le> gen_density Red X0 Y0"
    and "Book V E p0_min Red Blue X0 Y0" 
  proof (rule Basis_imp_Book [OF _ Red_E])
    show "E = all_edges V"
      using complete by auto
    show "p0_min \<le> graph_density Red"
      using p0_min12 Red by linarith
    show "\<not> ((\<exists>K. size_clique k K Red) \<or> (\<exists>K. size_clique k K Blue))"
      using no_Blue_K no_Red_K by blast
  qed (use infinite_UNIV p0_min Blue_def Red in auto)
  then interpret Book V E p0_min Red Blue X0 Y0
    by meson
  have "Colours k k"
    using Colours_def no_Blue_K no_Red_K by auto
  define \<R> where "\<R> \<equiv> Step_class \<mu> k k {red_step}"
  define \<S> where "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  define t where "t \<equiv> card \<R>" 
  define s where "s \<equiv> card \<S>"
  define m where "m \<equiv> halted_point \<mu> k k"
  define x where "x \<equiv> t/k"
  define y where "y \<equiv> s/k"
  define v where "v \<equiv> min (ff x y) (GG \<mu> x y) + \<eta>"
  have sts: "(s + real t) / s = (x+y) / y"
    using \<open>k>0\<close> by (simp add: x_def y_def field_simps)
  have "t<k"
    by (simp add: \<R>_def \<mu> t_def \<open>Colours k k\<close> red_step_limit)
  then obtain x01: "0\<le>x" "x<1"
    by (auto simp: x_def)
  have "s<k"
    unfolding s_def \<S>_def
    by (meson \<mu> \<open>Colours k k\<close> le_less_trans bblue_dboost_step_limit big41 le_add2)
  then obtain y01: "0\<le>y" "y<1"
    by (auto simp: y_def)
  define w where "w \<equiv> (\<Squnion>y\<in>{0..\<mu>*x/(1-\<mu>)+\<eta>}. min (ff x y) (GG \<mu> x y) + \<eta>)"
  show ?thesis
  proof (intro cSup_upper2 cSUP_least imageI)
    show "w \<in> (\<lambda>x. \<Squnion>y\<in>{0..\<mu>*x/(1-\<mu>)+\<eta>}. min (ff x y) (GG \<mu> x y) + \<eta>) ` {0..1}"
      using x01 by (force simp: w_def intro!: image_eqI [where x=x])
  next
    have beta_le: "bigbeta \<mu> k k \<le> \<mu>"
      using \<open>Colours k k\<close> \<mu> big53 bigbeta_le by blast
    have "s \<le> (bigbeta \<mu> k k / (1 - bigbeta \<mu> k k)) * t + (2 / (1-\<mu>)) * k powr (19/20)"
      using ZZ_8_5 [OF \<mu> \<open>Colours k k\<close> big85] by (auto simp: \<R>_def \<S>_def s_def t_def)
    also have "\<dots> \<le> (\<mu> / (1-\<mu>)) * t + (2 / (1-\<mu>)) * k powr (19/20)"
      by (smt (verit, ccfv_SIG) \<mu> beta_le frac_le mult_right_mono of_nat_0_le_iff)
    also have "\<dots> \<le> (\<mu> / (1-\<mu>)) * t + (2 / (1-\<mu>)) * (k powr (-1/20) * k powr 1)"
      unfolding powr_add [symmetric] by simp
    finally have "s \<le> (\<mu> / (1-\<mu>)) * t + (2 / (1-\<mu>)) * k powr (-1/20) * k" 
      by simp
    with powr_le_\<eta> have \<dagger>: "s \<le> (\<mu> / (1-\<mu>)) * t + \<eta> * k"
      by (smt (verit, ccfv_SIG) mult_right_mono of_nat_0_le_iff)

    have k_minus_t: "nat \<lfloor>real k - real t\<rfloor> = k-t"
      by linarith
    have "nV div 2 \<le> card Y0"
      by (simp add: card_Y0)
    then have \<section>: "log 2 (Suc nV) \<le> log 2 (RN k (k-t)) + s + t + 2 - ok_fun_61 k"
      using From_11_3 [OF \<mu> \<open>Colours k k\<close> big61] p0_half by (auto simp: \<R>_def \<S>_def p0_def s_def t_def)

    have 122: "FF k x y \<le> ff x y"
    proof -
      have "FF k x y \<le> f1 x y"
        using x01 y01
        by (intro FF_le_f1) auto
      moreover
      have "FF k x y \<le> f2 x y + 3 / (real k * ln 2)" if "x \<ge> 3/4"
      proof (intro FF_le_f2_aux that)
        define l where "l \<equiv> k-t"
        define \<gamma> where "\<gamma> \<equiv> real l / (real k + real l)"
        have "\<gamma> = (1-x) / (2-x)"
          using \<open>0 < k\<close> \<open>t < k\<close> by (simp add: l_def \<gamma>_def x_def divide_simps)
        then have "\<gamma> \<le> 1/5"
          using that \<open>x<1\<close> by simp
        show "real l = real k - x * real k"
          using \<open>t < k\<close> by (simp add: l_def x_def)
        show "Big_Closer_10_1 (min (real l / (real k + real l)) (0.07)) l"
          sorry
      qed (use x01 y01 p0_min12 in auto)
      have "FF k x y \<le> f2 x y" if "x \<ge> 3/4"
        sorry
      ultimately
      show ?thesis
        by (auto simp: ff_def) 
    qed
    have "log 2 (Suc nV) / k \<le> log 2 (RN k (k-t)) / k + x + y + (2 - ok_fun_61 k) / k"
      using \<open>k>0\<close> divide_right_mono [OF \<section>, of k] add_divide_distrib x_def y_def
      by (smt (verit) add_uminus_conv_diff of_nat_0_le_iff)
    also have "... = FF k x y + (2 - ok_fun_61 k) / k"
      by (simp add: FF_def x_def k_minus_t)
    also have "... \<le> ff x y + (2 - ok_fun_61 k) / k"
      by (simp add: 122)
    also have "... \<le> ff x y + ok_fun_11_1 \<mu> k / k"
      by (simp add: ok_fun_11_1_def divide_right_mono)
    finally have le_FF: "log 2 (Suc nV) / k \<le> ff x y + ok_fun_11_1 \<mu> k / k" .

    have "nV div 2 \<le> card X0"
      using card_X0 by linarith
    then have 112: "log 2 (Suc nV) \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (ratio \<mu> s t)
                + ok_fun_11_2 \<mu> k"
      using From_11_2 [OF \<mu> \<open>Colours k k\<close> big11_2] p0_half
      unfolding s_def t_def p0_def \<R>_def \<S>_def by blast
    have "log 2 (Suc nV) / k \<le> log 2 (1/\<mu>) + x * log 2 (1 / (1-\<mu>)) + y * log 2 (ratio \<mu> s t)
                          + ok_fun_11_2 \<mu> k / k"
      using \<open>k>0\<close> divide_right_mono [OF 112, of k]
      by (simp add: add_divide_distrib x_def y_def)
    also have "... = GG \<mu> x y + ok_fun_11_2 \<mu> k / k"
      by (metis GG_def sts times_divide_eq_right)
    also have "... \<le> GG \<mu> x y + ok_fun_11_1 \<mu> k / k"
      by (simp add: ok_fun_11_1_def divide_right_mono)
    finally have le_GG: "log 2 (Suc nV) / k \<le> GG \<mu> x y + ok_fun_11_1 \<mu> k / k" .
    have "RN k k > 0"
      by (metis RN_eq_0_iff \<open>k>0\<close> gr0I)
    moreover have "log 2 (Suc nV) / k \<le> v"
      unfolding v_def using ok111_le_\<eta> le_FF le_GG by linarith
    ultimately have "log 2 (RN k k) / k \<le> v"
      using ge_RN \<open>k>0\<close>
      by (smt (verit, best) Transcendental.log_mono divide_right_mono of_nat_0_less_iff of_nat_mono)
    also have "... \<le> w"
      unfolding w_def v_def
    proof (intro cSup_upper2)
      have "y \<in> {0..\<mu>*x/(1-\<mu>)+\<eta>}"
        using divide_right_mono [OF \<dagger>, of k] \<open>k>0\<close> by (simp add: x_def y_def) argo
      then show "min (ff x y) (GG \<mu> x y) + \<eta> \<in> (\<lambda>y. min (ff x y) (GG \<mu> x y) + \<eta>) ` {0..\<mu>*x/(1-\<mu>)+\<eta>}"
        by blast
    next
      have "\<mu>*x/(1-\<mu>)+\<eta> \<le> 1"
        by (smt (verit, best) \<mu>(2) assms(1) assms(4) frac_le mult_left_le x01(2))
      then show "bdd_above ((\<lambda>y. min (ff x y) (GG \<mu> x y) + \<eta>) ` {0..\<mu>*x/(1-\<mu>)+\<eta>})"
        by (simp add: bdd_above_ff_GG less_imp_le x01)
    qed auto
    finally show "log 2 (real (RN k k)) / k \<le> w" .
  next
    show "bdd_above ((\<lambda>x. \<Squnion>y\<in>{0..\<mu> * x / (1 - \<mu>) + \<eta>}. min (ff x y) (GG \<mu> x y) + \<eta>) ` {0..1})"
    proof (rule bdd_above_SUP_ff_GG)
      show "(\<lambda>x. \<mu>*x/(1-\<mu>)+\<eta>) \<in> {0..1} \<rightarrow> {0..1}"
        using \<mu> \<open>\<eta>>0\<close> le1
        apply clarsimp
        by (smt (verit, best) frac_le mult_left_le)
    qed
  qed 
qed

theorem (in P0_min) From_11_1:
  assumes \<mu>: "0 < \<mu>" "\<mu> < 1" and "\<eta> > 0" and le1: "\<mu>/(1-\<mu>) + \<eta> \<le> 1" 
    and p0_min12: "p0_min \<le> 1/2" and big: "Big_From_11_1 \<eta> \<mu> k"
  shows "log 2 (RN k k) / k \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..\<mu>*x/(1-\<mu>)+\<eta>}. min (ff x y) (GG \<mu> x y) + \<eta>)"
proof -
  have "k\<ge>3"
    using big by (auto simp: Big_From_11_1_def)
  define n where "n \<equiv> RN k k - 1"
  define V where "V \<equiv> {..<n}"
  define E where "E \<equiv> all_edges V" 
  interpret Book_Basis V E
  proof
    show "\<And>e. e \<in> E \<Longrightarrow> e \<subseteq> V"
      by (simp add: E_def comp_sgraph.wellformed)
    show "\<And>e. e \<in> E \<Longrightarrow> card e = 2"
      by (simp add: E_def comp_sgraph.two_edges)
  qed (use V_def E_def in auto)

  have "RN k k \<ge> 3"
    using \<open>k\<ge>3\<close> RN_3plus le_trans by blast 
  then have "n < RN k k"
    by (simp add: n_def)
  moreover have [simp]: "nV = n"
    by (simp add: V_def)
  ultimately obtain Red Blue
    where Red_E: "Red \<subseteq> E" and Blue_def: "Blue = E\<setminus>Red" 
      and no_Red_K: "\<not> (\<exists>K. size_clique k K Red)"
      and no_Blue_K: "\<not> (\<exists>K. size_clique k K Blue)"
    by (metis \<open>n < RN k k\<close> less_RN_Red_Blue)
  have Blue_E: "Blue \<subseteq> E" and disjnt_Red_Blue: "disjnt Red Blue" and Blue_eq: "Blue = all_edges V \<setminus> Red"
    using complete by (auto simp: Blue_def disjnt_iff E_def) 
  have "nV > 1"
    using \<open>RN k k \<ge> 3\<close> \<open>nV=n\<close> n_def by linarith
  with graph_size have "graph_size > 0"
    by simp
  then have "graph_density E = 1"
    by (simp add: graph_density_def)
  then have "graph_density Red + graph_density Blue = 1"
    using graph_density_Un [OF disjnt_Red_Blue] by (simp add: Blue_def Red_E Un_absorb1)
  then consider (Red) "graph_density Red \<ge> 1/2" | (Blue) "graph_density Blue \<ge> 1/2"
    by force
  then show ?thesis
  proof cases
    case Red
    show ?thesis
    proof (intro From_11_1_Body)
    next
      show "RN k k \<le> Suc nV"
        by (simp add: n_def)
      show "\<nexists>K. size_clique k K Red"
        using no_Red_K by blast
      show "\<nexists>K. size_clique k K Blue"
        using no_Blue_K by blast
    qed (use Red Red_E Blue_def assms in auto)
  next
    case Blue
    show ?thesis
    proof (intro From_11_1_Body)
      show "RN k k \<le> Suc nV"
        by (simp add: n_def)
      show "Blue \<subseteq> E"
        by (simp add: Blue_E)
      show "Red = E \<setminus> Blue"
        by (simp add: Blue_def Red_E double_diff)
      show "\<nexists>K. size_clique k K Red"
        using no_Red_K by blast
      show "\<nexists>K. size_clique k K Blue"
        using no_Blue_K by blast
    qed (use Blue Red_E Blue_def assms in auto)
  qed
qed


(*THEOREM 10.1 NEEDS TO BE UNCONDITIONAL RE BIGNESS. AND THIS IS STILL WEAK*)
text \<open>probably we are able to assume that x is rational\<close>
lemma (in P0_min) FF_le_f2:
  fixes x y::real
  assumes x: "3/4 \<le> x" "x \<le> 1" and xeq: "x = real t / real k" 
      and y: "0 \<le> y" "y \<le> 1"
  assumes p0_min_101: "p0_min \<le> 1 - 1/5"
  defines "\<gamma> \<equiv> (1-x) / (2-x)"
  shows "FF k x y \<le> f2 x y + 3 / (real k * ln 2)"
proof (cases "x=1")
  case True
  then show ?thesis 
    by (simp add: FF_def f2_def f1_def)
next
  case False
  with x have "0<x" "x<1"
    by linarith+
  with xeq \<open>x<1\<close> obtain "k>0" "t<k"
    by (smt (verit, del_insts) Multiseries_Expansion.intyness_0 assms(1) divide_le_0_iff divide_less_eq_1 of_nat_less_iff zero_order(4))
  define \<gamma>0 where "\<gamma>0 \<equiv> min \<gamma> (0.07)" 
  have \<gamma>: "0<\<gamma>" "\<gamma> \<le> 1/5"
    using x \<open>x<1\<close> y by (auto simp add: \<gamma>_def divide_simps)
  then have "\<gamma>0>0"
    by (simp add: \<gamma>0_def)
(*
  then have big: "\<forall>\<^sup>\<infinity>l. Big_Closer_10_1 \<gamma>0 l"
    by (meson Big_Closer_10_1)
  moreover have "frequently (\<lambda>l. (k-t) dvd l) sequentially"
    apply (simp add: frequently_sequentially)
    by (metis Suc_diff_Suc \<open>t < k\<close> dvd_triv_left less_one more_arith_simps(5) mult_le_cancel2 nat.simps(3) not_le)
  ultimately obtain l where big: "(k-t) dvd l \<and> Big_Closer_10_1 \<gamma>0 l"
    by (smt (verit, del_insts) frequently_cong not_frequently_False)
  then obtain c where leq: "l = (k-t)*c"
    by blast
*)
  define l where "l = k-t"
  have "l>0"
    by (simp add: \<open>t < k\<close> l_def)
  have \<gamma>eq: "\<gamma> = real l / (real k + real l)"
    using \<open>0 < k\<close> \<open>t < k\<close>
    by (simp add: \<gamma>_def l_def xeq divide_simps)
  show ?thesis
  proof (intro FF_le_f2_aux x y)
    show "real l = real k - x * real k"
      using \<open>t < k\<close> by (simp add: l_def xeq)
  next
    show "p0_min \<le> 1 - 1 / 5"
      using p0_min_101 by blast
  next
    show "Big_Closer_10_1 (min (real l / (real k + real l)) (7 / 10\<^sup>2)) l"
      sorry
  qed
qed

text \<open>this result closes the gap between the different ranges of the suprema,
          And it could be folded into the proof below\<close>
lemma C:
  assumes \<mu>: "\<mu>=2/5" and "0 < \<eta>" "\<eta> \<le> 3/4 - 2/3" 
  shows "(SUP x \<in> {0..1}. SUP y \<in> {0..\<mu>*x/(1-\<mu>)+\<eta>}. min (ff x y) (GG \<mu> x y) + \<eta>)
        \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..3/4}. min (ff x y) (GG \<mu> x y) + \<eta>)"
proof (intro cSUP_subset_mono order.refl bdd_above_SUP_ff_GG)
  fix x :: real
  assume x: "x \<in> {0..1}"
  show "{0..\<mu> * x / (1 - \<mu>) + \<eta>} \<subseteq> {0..3/4}"
    using x assms unfolding \<mu> by auto
  show "{0..\<mu> * x / (1 - \<mu>) + \<eta>} \<noteq> {}"
    using x assms unfolding \<mu> by auto
  show "bdd_above ((\<lambda>y. min (ff x y) (GG \<mu> x y) + \<eta>) ` {0..3/4})"
    using ff_GG_bound [OF x]
    by (intro bdd_above.I2 [where M = "ff_bound+\<eta>"]) force
qed auto

context P0_min
begin 

theorem From_11_1_fixed:
  assumes \<mu>: "\<mu>=2/5" and \<eta>: "0 < \<eta>" "\<eta> \<le> 3/4 - 2/3" and p0_min12: "p0_min \<le> 1/2"
  and big: "Big_From_11_1 \<eta> \<mu> k"
shows "log 2 (RN k k) / k \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..3/4}. min (ff x y) (GG \<mu> x y) + \<eta>)"
      (is "?L\<le>?R")
proof -
  define u where "u \<equiv> \<lambda>x. \<mu>*x/(1-\<mu>)+\<eta>"
  have u01: "u \<in> {0..1} \<rightarrow> {0..1}"
    unfolding u_def \<mu> using \<eta> by (auto simp: Pi_iff)
  then have ux1: "u x \<le> 1" if "x \<in> {0..1}" for x
    using that by fastforce
  have 1: "\<mu> / (1 - \<mu>) + \<eta> \<le> 1"
    unfolding \<mu> using \<eta> by simp
  then have "?L \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..u x}. min (ff x y) (GG \<mu> x y) + \<eta>)"
    using assms unfolding u_def 
    by (intro From_11_1 1) auto
  also have "... \<le> ?R"
    unfolding u_def using assms by (intro C) auto
  finally show ?thesis .
qed

lemma 123:
  fixes \<delta>::real
  assumes "0 < \<delta>" "\<delta> \<le> 1 / 2^11"
  shows "(SUP x \<in> {0..1}. SUP y \<in> {0..3/4}. min (ff x y) (gg x y)) \<le> 2-\<delta>"
  sorry

end (*P0_min*)

text \<open>we subtract a tiny bit, as we seem to need this gap\<close>
definition delta'::real where "delta' \<equiv> 1 / 2^11 - 1 / 2^18"

lemma Aux_1_1:
  assumes p0_min12: "p0_min \<le> 1/2"
  shows "\<forall>\<^sup>\<infinity>k. log 2 (RN k k) / k \<le> 2 - delta'"
proof -
  define p0_min::real where "p0_min \<equiv> 1/2"
  interpret P0_min p0_min
  proof qed (auto simp: p0_min_def)
  define \<delta>::real where "\<delta> \<equiv> 1 / 2^11"
  define \<eta>::real where "\<eta> \<equiv> 1 / 2^18"
  have \<eta>: "0 < \<eta>" "\<eta> \<le> 1/12"
    by (auto simp: \<eta>_def)
  define \<mu>::real where "\<mu> \<equiv> 2/5"
  have "\<forall>\<^sup>\<infinity>k. Big_From_11_1 \<eta> \<mu> k"
    unfolding \<mu>_def using \<eta> by (intro Big_From_11_1) auto
  moreover have "log 2 (real (RN k k)) / k \<le> 2-\<delta> + \<eta>" if "Big_From_11_1 \<eta> \<mu> k" for k
  proof -
    have *: "(\<Squnion>y\<in>{0..3/4}. min (ff x y) (GG \<mu> x y) + \<eta>) = (\<Squnion>y\<in>{0..3/4}. min (ff x y) (GG \<mu> x y)) + \<eta>"
      if "x \<in> {0..1}" for x
      using bdd_above_ff_GG [OF that, of "3/4" \<mu> 0]
      by (simp add: add.commute [of _ \<eta>] Sup_add_eq)
    have "log 2 (RN k k) / k \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..3/4}. min (ff x y) (GG \<mu> x y) + \<eta>)"
      using that p0_min12 \<eta> \<mu>_def
      by (intro From_11_1_fixed) (auto simp: p0_min_def)
    also have "... \<le> (SUP x \<in> {0..1}. (SUP y \<in> {0..3/4}. min (ff x y) (GG \<mu> x y)) + \<eta>)"
    proof (intro cSUP_subset_mono bdd_above.I2 [where M = "ff_bound+\<eta>"])
      fix x :: real
      assume x: "x \<in> {0..1}"
      have "(\<Squnion>y\<in>{0..3/4}. min (ff x y) (GG \<mu> x y) + \<eta>) \<le> ff_bound + \<eta>"
        using bdd_above_ff_GG [OF x] ff_GG_bound [OF x] by (simp add: cSup_le_iff)
      with * [OF x] show "(\<Squnion>y\<in>{0..3/4}. min (ff x y) (GG \<mu> x y)) + \<eta> \<le> ff_bound + \<eta>" 
        by simp
    qed (use * in auto)
    also have "... = (SUP x \<in> {0..1}. SUP y \<in> {0..3/4}. min (ff x y) (GG \<mu> x y)) + \<eta>"
      using bdd_above_SUP_ff_GG [of "\<lambda>_. 3/4"  \<mu> 0]
      by (simp add: add.commute [of _ \<eta>] Sup_add_eq)
    also have "... \<le> 2-\<delta> + \<eta>"
      using 123 [of "1 / 2^11"] by (auto simp: \<delta>_def)
    finally show ?thesis .
  qed
  ultimately have "\<forall>\<^sup>\<infinity>k. log 2 (RN k k) / k \<le> 2-\<delta> + \<eta>"
    by (meson eventually_mono)
  then show ?thesis
    by (simp add: \<delta>_def \<eta>_def delta'_def)
qed

text \<open>Main theorem 1.1: the exponent is approximately 3.9987\<close>
theorem Main_1_1:
  obtains \<epsilon>::real where "\<epsilon>>0" "\<forall>\<^sup>\<infinity>k. RN k k \<le> (4-\<epsilon>)^k"
proof
  let ?\<epsilon> = "0.00134::real"
  have "\<forall>\<^sup>\<infinity>k. k>0 \<and> log 2 (RN k k) / k \<le> 2 - delta'"
    unfolding eventually_conj_iff using Aux_1_1 eventually_gt_at_top by blast 
  then have A: "\<forall>\<^sup>\<infinity>k. RN k k \<le> (2 powr (2-delta')) ^ k"
  proof (eventually_elim)
    case (elim k)
    then have "log 2 (RN k k) \<le> (2-delta') * k"
      by (meson of_nat_0_less_iff pos_divide_le_eq)
    then have "RN k k \<le> 2 powr ((2-delta') * k)"
      by (smt (verit, best) Transcendental.log_le_iff powr_ge_pzero)
    then show "RN k k \<le> (2 powr (2-delta')) ^ k"
      by (simp add: mult.commute powr_power)
  qed
  moreover have "2 powr (2-delta') \<le> 4 - ?\<epsilon>"
    unfolding delta'_def by (approximation 50)
  ultimately show "\<forall>\<^sup>\<infinity>k. real (RN k k) \<le> (4-?\<epsilon>) ^ k"
    by (smt (verit) power_mono powr_ge_pzero eventually_mono)
qed auto

end
