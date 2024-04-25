section \<open>An exponential improvement far from the diagonal\<close>

theory Far_From_Diagonal 
  imports Zigzag "Stirling_Formula.Stirling_Formula"

begin

subsection \<open>Fact D.3 from the Appendix\<close>

text \<open>And hence, Fact 9.4\<close>

definition "stir \<equiv> \<lambda>n. fact n / (sqrt (2*pi*n) * (n / exp 1) ^ n) - 1"

text \<open>Generalised to the reals to allow derivatives\<close>
definition "stirG \<equiv> \<lambda>n. Gamma (n+1) / (sqrt (2*pi*n) * (n / exp 1) powr n) - 1"

lemma stir_eq_stirG: "n>0 \<Longrightarrow> stir n = stirG (real n)"
  by (simp add: stirG_def stir_def add.commute powr_realpow Gamma_fact)

lemma stir_ge0: "n>0 \<Longrightarrow> stir n \<ge> 0"
  using fact_bounds[of n] by (simp add: stir_def)

lemma stir_to_0: "stir \<longlonglongrightarrow> 0"
  using fact_asymp_equiv by (simp add: asymp_equiv_def stir_def LIM_zero)

lemma stir_o1: "stir \<in> o(1)"
  using stir_to_0 tendsto_zero_imp_o1 by presburger

lemma fact_eq_stir_times: "n \<noteq> 0 \<Longrightarrow> fact n = (1 + stir n) * (sqrt (2*pi*n) * (n / exp 1) ^ n)"
  by (simp add: stir_def)

definition "logstir \<equiv> \<lambda>n. if n=0 then 0 else log 2 ((1 + stir n) * sqrt (2*pi*n))"

lemma logstir_o_real: "logstir \<in> o(real)"
proof -
  have "\<forall>\<^sup>\<infinity>n. 0 < n \<longrightarrow> \<bar>log 2 ((1 + stir n) * sqrt (2*pi*n))\<bar> \<le> c * real n" if "c>0" for c
  proof -
    have "\<forall>\<^sup>\<infinity>n. 2 powr (c*n) / sqrt (2*pi*n) \<ge> c+1"
      using that by real_asymp
    moreover have "\<forall>\<^sup>\<infinity>n. \<bar>stir n\<bar> \<le> c"
      using stir_o1 that by (auto simp: smallo_def)
    ultimately have "\<forall>\<^sup>\<infinity>n. ((1 + stir n) * sqrt (2*pi*n)) \<le> 2 powr (c * n)"
    proof eventually_elim
      fix n
      assume c1: "c+1 \<le> 2 powr (c * n) / sqrt (2*pi*n)" and lec: "\<bar>stir n\<bar> \<le> c"
      then have "stir n \<le> c"
        by auto
      then show "(1 + stir n) * sqrt (2*pi*n) \<le> 2 powr (c*n)"
        using mult_right_mono [OF c1, of "sqrt (2*pi*n)"] lec
        by (smt (verit, ccfv_SIG) c1 mult_right_mono nonzero_eq_divide_eq pos_prod_le powr_gt_zero)
    qed
    then show ?thesis
    proof (eventually_elim, clarify)
      fix n
      assume n: "(1 + stir n) * sqrt (2 * pi * real n) \<le> 2 powr (c * real n)"
        and "n>0"
      have "(1 + stir n) * sqrt (2 * pi * real n) \<ge> 1"
        using stir_ge0
        by (smt (verit) of_nat_0 \<open>0 < n\<close> mult_less_cancel_left2 nat_less_real_le pi_ge_two real_sqrt_ge_1_iff)
      with n show "\<bar>log 2 ((1 + stir n) * sqrt (2 * pi * real n))\<bar> \<le> c * real n"
        by (simp add: abs_if le_powr_iff)
    qed
  qed
  then show ?thesis
    by (auto simp: smallo_def logstir_def)
qed

lemma logfact_eq_stir_times:
   "fact n = 2 powr (logstir n) * (n / exp 1) ^ n"
proof-
  have "1 + stir n > 0" if "n\<noteq>0"
    using that by (simp add: stir_def)
  then show ?thesis
    by (simp add: logstir_def fact_eq_stir_times)
qed

lemma mono_G:
  defines "G \<equiv> (\<lambda>x::real. Gamma (x + 1) / (x / exp 1) powr x)"
  shows "mono_on {0<..} G"
proof (clarsimp simp: monotone_on_def)
  fix x y::real
  assume x: "0 < x" "x \<le> y"
  define GD where "GD \<equiv> \<lambda>u::real. Gamma(u+1) * (Digamma(u+1) - ln(u)) / (u / exp 1) powr u"
  have *: "\<exists>D. (G has_real_derivative D) (at u) \<and> D > 0" if "0 < u" for u 
  proof (intro exI conjI)
    show "(G has_real_derivative GD u) (at u)"
      using that
      unfolding G_def GD_def
      apply-
      apply (rule derivative_eq_intros has_real_derivative_powr' | force)+
      apply (auto simp: ln_div pos_prod_lt field_simps)
      done
    show "GD u > 0"
      using that by (auto simp: GD_def Digamma_plus_1_gt_ln) \<comment> \<open>Thank you, Manuel!\<close>
  qed
  show "G x \<le> G y"
    using x DERIV_pos_imp_increasing [OF _ *] by (force simp: less_eq_real_def)
qed

lemma mono_logstir: "mono logstir"
proof (clarsimp simp: monotone_def)
  fix i j::nat
  assume "i\<le>j"
  show "logstir i \<le> logstir j"
  proof (cases "j=0")
    case True
    with \<open>i\<le>j\<close> show ?thesis
      by auto
  next
    case False
    with pi_ge_two have "1 * 1 \<le> 2 * pi * j"
      by (intro mult_mono) auto
    with False stir_ge0 [of j] have *: "1 * 1 \<le> (1 + stir j) * sqrt (2 * pi * real j)"
      by (intro mult_mono) auto
    with \<open>i \<le> j\<close> mono_G show ?thesis
      by (auto simp add: logstir_def stir_eq_stirG stirG_def monotone_on_def)
  qed
qed

definition "ok_fun_94 \<equiv> \<lambda>k. - logstir k"

lemma ok_fun_94: "ok_fun_94 \<in> o(real)"
  unfolding ok_fun_94_def
  using logstir_o_real by simp 

lemma fact_9_4:
  assumes l: "0 < l" "l \<le> k"
  defines "\<gamma> \<equiv> l / (real k + real l)"
  shows "k+l choose l \<ge> 2 powr ok_fun_94 k * \<gamma> powr (-l) * (1-\<gamma>) powr (-k)" 
proof -
  have *: "ok_fun_94 k \<le> logstir (k + l) - (logstir k + logstir l)"
    using mono_logstir by (auto simp: ok_fun_94_def monotone_def)
  have "2 powr ok_fun_94 k * \<gamma> powr (- real l) * (1-\<gamma>) powr (- real k)
      = (2 powr ok_fun_94 k) * (k+l) powr(k+l) / (k powr k * l powr l)"
    by (simp add: \<gamma>_def powr_minus powr_add powr_divide divide_simps)
  also have "\<dots> \<le> (2 powr (logstir (k+l)) / (2 powr (logstir k)  * 2 powr (logstir l)))
                 * (k+l) powr (k+l) / (k powr k * l powr l)"
    by (metis "*" divide_nonneg_nonneg mult_right_mono powr_add powr_diff powr_ge_pzero powr_mono semiring_norm(92) times_divide_eq_right zero_compare_simps(4))
  also have "\<dots> = fact(k+l) / (fact k * fact l)"
    using l by (simp add: logfact_eq_stir_times powr_add divide_simps flip: powr_realpow)
  also have "\<dots> = real (k+l choose l)"
    by (simp add: binomial_fact)
  finally show ?thesis .
qed

subsection \<open>Fact D.2\<close>

text \<open>For Fact 9.6\<close>

lemma D2:
  fixes k l
  assumes t: "0<t" "t \<le> k"
  defines "\<gamma> \<equiv> l / (real k + real l)"
  shows "(k+l-t choose l) \<le> exp (- \<gamma> * (t-1)^2 / (2*k)) * (k / (k+l))^t * (k+l choose l)"
proof -
  have "(k+l-t choose l) * inverse (k+l choose l) = (\<Prod>i<t. (k-i) / (k+l-i))"
    using \<open>t \<le> k\<close>
  proof (induction t)
    case (Suc t)
    then have "t \<le> k"
      by simp
    with Suc.IH [symmetric] Suc(2) show ?case 
      apply (simp add: field_simps flip: of_nat_mult)
      by (metis binomial_absorb_comp diff_Suc_eq_diff_pred diff_add_inverse2 diff_commute)
  qed auto
  also have "\<dots> = (real k / (k+l))^t * (\<Prod>i<t. 1 - real i * real l / (real k * (k+l-i)))"
  proof -
    have "1 - real i * real l / (real k * (k+l-i)) = ((k-i)/(k+l-i)) * ((k+l) / k)" if "i<t" for i
      using that \<open>t \<le> k\<close> by (simp add: divide_simps of_nat_diff) argo
    then have *: "(\<Prod>i<t. 1 - real i * real l / (real k * (k+l-i))) = (\<Prod>i<t. ((k-i)/(k+l-i)) * ((k+l) / k))"
      by auto
    show ?thesis
      unfolding * prod.distrib by (simp add: power_divide)
  qed
  also have "\<dots> \<le> (real k / (k+l))^t * exp (- (\<Sum>i<t. real i * real l / (real k * (k+l))))"
  proof (intro mult_left_mono)
    have "real i * real l / (real k * real (k + l - i)) \<le> 1"
      if "i < t" for i
      using that \<open>t \<le> k\<close> by (simp add: divide_simps mult_mono)
    moreover have "1 - i * l / (k * real (k + l - i)) \<le> exp (- (i * real l / (k * (k + real l))))" (is "_ \<le> ?R")
      if "i < t" for i 
    proof -
      have "exp (- (i*l / (k * real (k + l - i)))) \<le> ?R"
        using that \<open>t \<le> k\<close> by (simp add: frac_le_eq divide_le_0_iff mult_mono)
      with exp_minus_ge show ?thesis
        by (smt (verit, best)) 
    qed
    ultimately show "(\<Prod>i<t. 1 - i * real l / (k * real (k + l - i))) \<le> exp (- (\<Sum>i<t. i * real l / (k * real (k + l))))"
      by (force simp add: exp_sum simp flip: sum_negf intro!: prod_mono)
  qed auto
  finally have 1: "(k+l-t choose l) * inverse (k+l choose l) \<le> (real k / (k+l))^t * exp (- (\<Sum>i<t. i * \<gamma> / k))"
    by (simp add: \<gamma>_def mult.commute)
  have **: "\<gamma> * (t - 1)^2 / (2*k) \<le> (\<Sum>i<t. i * \<gamma> / k)"
  proof -
    have g: "(\<Sum>i<t. real i) = real (t*(t-1)) / 2"
      by (induction t) (auto simp: algebra_simps eval_nat_numeral of_nat_diff)
    have "\<gamma> * (t-1)^2 / (2*k) \<le> real(t*(t-1)) / 2 * \<gamma>/k"
      by (simp add: field_simps eval_nat_numeral divide_right_mono mult_mono \<gamma>_def)
    also have "\<dots> = (\<Sum>i<t. i * \<gamma> / k)" 
      unfolding g [symmetric] by (simp add: sum_distrib_right sum_divide_distrib)
    finally show ?thesis .
  qed
  have 0: "0 \<le> real (k + l choose l)"
    by simp
  have *: "(k+l-t choose l) \<le> (real k / (k+l))^t * exp (- (\<Sum>i<t. i * \<gamma> / k)) * (k+l choose l)"
    using order_trans [OF _  mult_right_mono [OF 1 0]]
    by (simp add: less_eq_real_def)
  also have "\<dots> \<le>  (k / (k+l))^t * exp (- \<gamma> * (t-1)^2 / (2*k)) *(k+l choose l)"
    using ** by (intro mult_mono) auto
  also have "\<dots> \<le> exp (- \<gamma> * (t-1)^2 / (2 * real k)) * (k / (k+l))^t * (k+l choose l)"
    by (simp add: mult_ac)
  finally show ?thesis 
    using t by (simp add: of_nat_diff)
qed

text \<open>Statement borrowed from Bhavik; no o(k) function\<close>
corollary Far_9_6:
  fixes k l
  assumes t: "0<t" "t \<le> k"
  defines "\<gamma> \<equiv> l / (real k + real l)"
  shows "exp (-1) * (1-\<gamma>) powr (- real t) * exp (\<gamma> * (real t)\<^sup>2 / real(2*k)) * (k-t+l choose l) \<le> (k+l choose l)"
proof -
  have kkl: "k / (real k + real l) = 1 - \<gamma>" "k+l-t = k-t+l"
    using t by (auto simp add: \<gamma>_def divide_simps)
  have [simp]: "t + t \<le> Suc (t * t)"
    using t
    by (metis One_nat_def Suc_leI mult_2 mult_right_mono nle_le not_less_eq_eq numeral_2_eq_2 mult_1_right)
  have "0 \<le> \<gamma>" "\<gamma> < 1"
    using t by (auto simp: \<gamma>_def)
  then have "\<gamma> * (real t * 2) \<le> \<gamma> + real k * 2"
    using t by (smt (verit, best) mult_less_cancel_right2 of_nat_0_less_iff of_nat_mono)
  then have *: "\<gamma> * t^2 / (2*k) - 1 \<le> \<gamma> * (t-1)^2 / (2*k)"
    using t 
    apply (simp add: power2_eq_square of_nat_diff pos_divide_le_eq divide_simps)
    apply (simp add: algebra_simps)
    done
  then have *: "exp (-1) * exp (\<gamma> * t^2 / (2*k)) \<le> exp (\<gamma> * (t-1)^2 / (2*k))"
    by (metis exp_add exp_le_cancel_iff uminus_add_conv_diff)
  have 1: "exp (\<gamma> * (t-1)^2 / (2*k)) * (k+l-t choose l) \<le> (k / (k+l))^t * (k+l choose l)"
    using mult_right_mono [OF D2 [OF t], of "exp (\<gamma> * (t-1)^2 / (2*k))" l] t
    by (simp add: \<gamma>_def exp_minus of_nat_diff field_simps)
  have 2: "(k / (k+l)) powr (- real t) * exp (\<gamma> * (t-1)^2 / (2*k)) * (k+l-t choose l) \<le> (k+l choose l)"
    using mult_right_mono [OF 1, of "(1-\<gamma>) powr (- real t)"] t
    by (simp add: powr_minus \<gamma>_def powr_realpow mult_ac divide_simps)
  then have 3: "(1-\<gamma>) powr (- real t) * exp (\<gamma> * (t-1)^2 / (2*k)) * (k-t+l choose l) \<le> (k+l choose l)"
    by (simp add: kkl)
  show ?thesis
    apply (rule order_trans [OF _ 3])
    using "*" less_eq_real_def by fastforce
qed


subsection \<open>Lemma 9.3\<close>

definition "ok_fun_93g \<equiv> \<lambda>\<gamma> k. (nat \<lceil>k powr (3/4)\<rceil>) * log 2 k - (ok_fun_71 \<gamma> k + ok_fun_94 k) + 1"

lemma ok_fun_93g: 
  assumes "0 < \<gamma>" "\<gamma> < 1"
  shows "ok_fun_93g \<gamma> \<in> o(real)"
proof -
  have "(\<lambda>k. (nat \<lceil>k powr (3/4)\<rceil>) * log 2 k) \<in> o(real)"
    by real_asymp
  then show ?thesis
    unfolding ok_fun_93g_def
    by (intro ok_fun_71 [OF assms] ok_fun_94 sum_in_smallo const_smallo_real)
qed

definition "ok_fun_93h \<equiv> \<lambda>\<gamma> k. (2 / (1-\<gamma>)) * k powr (19/20) * (ln \<gamma> + 2 * ln k)
                                 + ok_fun_93g \<gamma> k * ln 2"

lemma ok_fun_93h:
  assumes "0 < \<gamma>" "\<gamma> < 1"
  shows  "ok_fun_93h \<gamma> \<in> o(real)"
proof -
  have "(\<lambda>k. (2 / (1-\<gamma>)) * k powr (19/20) * (ln \<gamma> + 2 * ln k)) \<in> o(real)"
    by real_asymp
  then show ?thesis
    unfolding ok_fun_93h_def by (metis (mono_tags) ok_fun_93g assms sum_in_smallo(1) cmult_in_smallo_iff')
qed

lemma big_ok_fun_93h:
  assumes "0 < \<gamma>" "\<gamma> < 1" "e>0" "C > 0"
  shows  "\<forall>\<^sup>\<infinity>k. \<bar>ok_fun_93h \<gamma> k\<bar> / real k \<le> e"
proof -
  have \<section>: "(\<lambda>k. ok_fun_93h \<gamma> k / real k) \<in> o(1)"
    using ok_fun_93h tendsto_zero_imp_o1 smalloD_tendsto assms by blast
  show ?thesis
    using landau_o.smallD [OF \<section>, of e] \<open>e>0\<close> by (auto simp: smallo_def)
qed

context Book_Basis
begin

definition "Big_Far_9_3 \<equiv>     
   \<lambda>\<mu> l. Big_ZZ_8_5 \<mu> l \<and> Big_X_7_1 \<mu> l \<and> Big_Y_6_2 \<mu> l \<and> Big_Red_5_3 \<mu> l
      \<and> (\<forall>k\<ge>l. p0_min - 3 * eps k > 1/k \<and> k\<ge>2
             \<and> \<bar>ok_fun_93h \<mu> k / (\<mu> * (1 + 1 / (exp 1 * (1-\<mu>))))\<bar> / k \<le> 0.667 - 2/3)"

lemma Big_Far_9_3:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_Far_9_3 \<mu> l"
proof -
  define d where "d \<equiv> \<mu> * (1 + 1 / (exp 1 * (1-\<mu>)))"
  have "d > 0"
    using assms by (auto simp: d_def divide_simps add_pos_pos)
  define e::real where "e \<equiv> 0.667 - 2/3"
  have "e>0"
    by (simp add: e_def)
  have *: "\<forall>\<^sup>\<infinity>l. \<forall>k\<ge>l. \<bar>ok_fun_93h \<mu> k / d\<bar> / k \<le> e" 
  proof -
    have "\<forall>\<^sup>\<infinity>l. \<forall>k\<ge>l. \<bar>ok_fun_93h \<mu> k\<bar> / real k \<le> d*e" 
      using \<open>0 < d\<close> \<open>0 < e\<close> assms big_ok_fun_93h[OF assms] mult_pos_pos[of d e]
      using eventually_all_ge_at_top by blast
    then show ?thesis
      apply eventually_elim 
      by (metis \<open>0 < d\<close> abs_div_pos divide_divide_eq_left' divide_le_eq mult.commute)
  qed
  with p0_min show ?thesis
    unfolding Big_Far_9_3_def eventually_conj_iff all_imp_conj_distrib eps_def d_def e_def
    apply (simp add: Big_ZZ_8_5 Big_X_7_1 Big_Y_6_2 Big_Red_5_3 assms)
    apply (intro conjI eventually_all_ge_at_top; real_asymp)
    done
qed

end

text \<open>Here @{term n} really refers to the cardinality of @{term V}, 
   so actually @{term nV}\<close>
lemma (in Book) Far_9_3:
  fixes l k
  assumes "Colours l k"  \<comment> \<open>Not mentioned in paper but presumably needed\<close>
  defines "\<gamma> \<equiv> l / (real k + real l)"
  defines "\<delta> \<equiv> min (1/200) (\<gamma>/20)"
  defines "\<R> \<equiv> Step_class \<gamma> l k {red_step}"
  defines "t \<equiv> card \<R>"
  assumes \<gamma>15: "\<gamma> \<le> 1/5" and p0: "p0 \<ge> 1/4" 
    and nge: "n \<ge> exp (-\<delta>*k) * (k+l choose l)" 
    and X0ge: "real (card X0) \<ge> n/2"  (*card X0 \<ge> n div 2 makes a harder proof*)
  assumes big: "Big_Far_9_3 \<gamma> l"
  shows "t \<ge> 2*k / 3"
proof -
  define m where "m \<equiv> halted_point \<gamma> l k"
  define \<S> where "\<S> \<equiv> Step_class \<gamma> l k {dboost_step}"
  define \<beta> where "\<beta> \<equiv> bigbeta \<gamma> l k"
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  then have "k\<ge>2" and big85: "Big_ZZ_8_5 \<gamma> l" and big71: "Big_X_7_1 \<gamma> l" and big62: "Big_Y_6_2 \<gamma> l" 
    and big53: "Big_Red_5_3 \<gamma> l"
    using big by (auto simp: Big_Far_9_3_def)
  define l34 where "l34 \<equiv> nat \<lceil>real l powr (3/4)\<rceil>"
  have "l34 > 0"
    using l34_def \<open>l>0\<close> by fastforce
  have \<gamma>01: "0 < \<gamma>" "\<gamma> < 1"
    using lk by (auto simp: \<gamma>_def)
  then have \<beta>01: "0 < \<beta>" "\<beta> < 1"
    using big53 assms bigbeta_gt0 bigbeta_less1 by (auto simp add: \<beta>_def)
  have one_minus: "1-\<gamma> = real k / (real k + real l)"
    using \<open>0<l\<close> by (simp add: \<gamma>_def divide_simps)
  have "t < k"
    using red_step_limit \<gamma>01 \<open>Colours l k\<close> by (auto simp: \<R>_def t_def)
  have f: "2 powr ok_fun_94 k * \<gamma> powr (- real l) * (1-\<gamma>) powr (- real k)
          \<le> k+l choose l" 
    unfolding \<gamma>_def using fact_9_4 lk by blast

  have powr_combine_right: "x powr a * (x powr b * y) = x powr (a+b) * y" for x y a b::real
    by (simp add: powr_add)
  have "(2 powr ok_fun_71 \<gamma> k * 2 powr ok_fun_94 k) * (\<beta>/\<gamma>) ^ card \<S> * (exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) / 2)
      \<le> 2 powr ok_fun_71 \<gamma> k * \<gamma>^l * (1-\<gamma>) ^ t * (\<beta>/\<gamma>) ^ card \<S> * (exp (-\<delta>*k) * (k+l choose l) / 2)"
    using \<gamma>01 \<open>0<\<beta>\<close> mult_right_mono [OF f, of "2 powr ok_fun_71 \<gamma> k * \<gamma>^l * (1-\<gamma>) ^ t * (\<beta>/\<gamma>) ^ card \<S> * (exp (-\<delta>*k)) / 2"]
    by (simp add: mult_ac zero_le_mult_iff powr_minus powr_diff divide_simps powr_realpow)
  also have "\<dots> \<le> 2 powr ok_fun_71 \<gamma> k * \<gamma>^l * (1-\<gamma>) ^ t * (\<beta>/\<gamma>) ^ card \<S> * card X0"
  proof (intro mult_left_mono order_refl)
    show "exp (-\<delta> * k) * real (k+l choose l) / 2 \<le> real (card X0)"
      using X0ge nge by force
    show "0 \<le> 2 powr ok_fun_71 \<gamma> k * \<gamma> ^ l * (1-\<gamma>) ^ t * (\<beta>/\<gamma>) ^ card \<S>"
      using \<gamma>01 bigbeta_ge0 by (force simp: \<beta>_def)
  qed
  also have "\<dots> \<le> card (Xseq \<gamma> l k m)"
    unfolding \<R>_def \<S>_def m_def t_def \<beta>_def
    using \<gamma>01 \<open>Colours l k\<close> big by (intro X_7_1) (auto simp: Big_Far_9_3_def)
  also have "\<dots> \<le> RN k l34"
  proof -
    have "p0 - 3 * eps k > 1/k" and "pee \<gamma> l k m \<ge> p0 - 3 * eps k"
      using lk big \<open>Colours l k\<close> p0_ge by (auto simp: Big_Far_9_3_def Y_6_2_halted \<gamma>_def m_def)
    then show ?thesis
      using halted_point_halted \<open>Colours l k\<close> \<gamma>01
      by (fastforce simp: step_terminating_iff termination_condition_def pee_def m_def l34_def)
  qed
  also have "\<dots> \<le> k powr (l34-1)"   \<comment> \<open>Bhavik's off-diagonal upper bound; can't use @{term "2^(k+l34)"}\<close>
    using lk \<open>l34>0\<close> RN_le_argpower' of_nat_mono by (simp add: powr_realpow)
  also have "\<dots> \<le> k powr l34"
    using \<open>k>0\<close> powr_mono by force
  also have "\<dots> \<le> 2 powr (l34 * log 2 k)"
    by (smt (verit, best) mult.commute \<open>k>0\<close> of_nat_0_less_iff powr_log_cancel powr_powr)
  also have "\<dots> \<le> 2 powr ((nat \<lceil>real k powr (3/4)\<rceil>) * log 2 k)"
    unfolding l34_def 
  proof (intro powr_mono powr_mono2 mult_mono ceiling_mono of_nat_mono nat_mono lk)
    show "0 \<le> real (nat \<lceil>k powr (3/4)\<rceil>)"
      by linarith
  qed (use lk in auto)
  finally have "2 powr (ok_fun_71 \<gamma> k + ok_fun_94 k) * (\<beta>/\<gamma>) ^ card \<S>
               * exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) / 2
              \<le> 2 powr ((nat \<lceil>real k powr (3/4)\<rceil>) * log 2 k)"
    by (simp add: powr_add)
  then have le_2_powr_g: "exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) * (\<beta>/\<gamma>) ^ card \<S>
             \<le> 2 powr ok_fun_93g \<gamma> k"
    using \<gamma>01 \<open>k\<ge>2\<close> by (simp add: ok_fun_93g_def field_simps powr_add powr_diff of_nat_diff flip: powr_realpow)

  let ?\<xi> = "\<beta> * t / (1-\<gamma>) + (2 / (1-\<gamma>)) * k powr (19/20)"
  have \<beta>_le: "\<beta> \<le> \<gamma>" and \<beta>_ge: "\<beta> \<ge> 1 / (real k)\<^sup>2"
    using \<beta>_def \<gamma>01 \<open>Colours l k\<close> big53 bigbeta_le bigbeta_ge_square by blast+
  
  define \<phi> where "\<phi> \<equiv> \<lambda>u. (u / (1-\<gamma>)) * ln (\<gamma>/u)"  \<comment> \<open>finding the maximum via derivatives\<close>
  have ln_eq: "ln (\<gamma> / (\<gamma> / exp 1)) / (1-\<gamma>) = 1/(1-\<gamma>)"
    using \<gamma>01 by simp
  have \<phi>: "\<phi> (\<gamma> / exp 1) \<ge> \<phi> \<beta>"
  proof (cases "\<gamma> / exp 1 \<le> \<beta>")    \<comment> \<open>Could perhaps avoid case analysis via 2nd derivatives\<close>
    case True
    show ?thesis 
    proof (intro DERIV_nonpos_imp_nonincreasing [where f = \<phi>])
      fix x
      assume x: "\<gamma> / exp 1 \<le> x" "x \<le> \<beta>"
      with \<gamma>01 have "x>0"
        by (smt (verit, best) divide_pos_pos exp_gt_zero)
      with \<gamma>01 x have "ln (\<gamma>/x) / (1-\<gamma>) - 1 / (1-\<gamma>) \<le> 0"
        by (smt (verit, ccfv_SIG) divide_pos_pos exp_gt_zero frac_le ln_eq ln_mono)
      with x \<open>x>0\<close> \<gamma>01 show "\<exists>D. (\<phi> has_real_derivative D) (at x) \<and> D \<le> 0"
        unfolding \<phi>_def by (intro exI conjI derivative_eq_intros | force)+
    qed (simp add: True)
  next
    case False
    show ?thesis
    proof (intro DERIV_nonneg_imp_nondecreasing [where f = \<phi>])
      fix x
      assume x: "\<beta> \<le> x" "x \<le> \<gamma> / exp 1"
      with \<beta>01 \<gamma>01 have "x>0" by linarith
      with \<gamma>01 x have "ln (\<gamma>/x) / (1-\<gamma>) - 1 / (1-\<gamma>) \<ge> 0"
        by (smt (verit, best) frac_le ln_eq ln_mono zero_less_divide_iff)
      with x \<open>x>0\<close> \<gamma>01 show "\<exists>D. (\<phi> has_real_derivative D) (at x) \<and> D \<ge> 0"
        unfolding \<phi>_def by (intro exI conjI derivative_eq_intros | force)+
    qed (use False in force)
  qed

  define c where "c \<equiv> \<lambda>x::real. 1 + 1 / (exp 1 * (1-x))" 
  have mono_c: "mono_on {0<..<1} c"
    by (auto simp: monotone_on_def c_def field_simps)
  have cgt0: "c x > 0" if "x<1" for x
    using that by (simp add: add_pos_nonneg c_def)

  have "card \<S> \<le> \<beta> * t / (1-\<beta>) + (2 / (1-\<gamma>)) * k powr (19/20)" 
    using ZZ_8_5 [OF \<gamma>01 \<open>Colours l k\<close> big85] \<gamma>01 by (auto simp: \<R>_def \<S>_def t_def \<beta>_def)
  also have "\<dots> \<le> ?\<xi>" 
    using \<beta>_le by (simp add: \<gamma>01 bigbeta_ge0 frac_le \<beta>_def)
  finally have "card \<S> \<le> ?\<xi>" .
  with \<beta>_le \<beta>01 have "?\<xi> * ln (\<beta>/\<gamma>) \<le> card \<S> * ln (\<beta>/\<gamma>)"
    by (simp add: mult_right_mono_neg)
  then have "-?\<xi> * ln (\<gamma>/\<beta>) \<le> card \<S> * ln (\<beta>/\<gamma>)"
    using \<beta>01 \<gamma>01 by (smt (verit) ln_div minus_mult_minus)
  then have "\<gamma> * (real k - t) - \<delta>*k - ?\<xi> * ln (\<gamma>/\<beta>) \<le> \<gamma> * (real k - t) - \<delta>*k + card \<S> * ln (\<beta>/\<gamma>)"
    by linarith
  also have "\<dots> \<le> (t - real k) * ln (1-\<gamma>) - \<delta>*k + card \<S> * ln (\<beta>/\<gamma>)"
    using mult_right_mono [OF ln_add_one_self_le_self2 [of "-\<gamma>"], of "real k - t"] 
    using \<open>t < k\<close> \<gamma>01 
    by (simp add: algebra_simps)
  also have "\<dots> = ln (exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) * (\<beta>/\<gamma>) ^ card \<S>)"
    using \<gamma>01 \<beta>01 \<open>Colours l k\<close> by (simp add: ln_mult ln_div ln_realpow ln_powr)
  also have "\<dots> \<le> ln (2 powr ok_fun_93g \<gamma> k)"
    using le_2_powr_g \<gamma>01 \<beta>01 by simp
  also have "\<dots> = ok_fun_93g \<gamma> k * ln 2"
    by (auto simp: ln_powr)
  finally have "\<gamma> * (real k - t) - \<delta>*k - ?\<xi> * ln (\<gamma>/\<beta>) \<le> ok_fun_93g \<gamma> k * ln 2" .
  then have "\<gamma> * (real k - t) \<le> ?\<xi> * ln (\<gamma>/\<beta>) + \<delta>*k + ok_fun_93g \<gamma> k * ln 2"
    by simp
  also have "\<dots> \<le> (\<beta> * t / (1-\<gamma>)) * ln (\<gamma>/\<beta>) + \<delta>*k + ok_fun_93h \<gamma> k"
  proof -
    have "\<gamma>/\<beta> \<le> \<gamma> * (real k)\<^sup>2"
      using \<open>k>0\<close> \<beta>_le \<beta>_ge \<open>\<beta>>0\<close> by (simp add: field_simps)
    then have X: "ln (\<gamma>/\<beta>) \<le> ln \<gamma> + 2 * ln k"
      using \<open>\<beta>>0\<close> \<open>\<gamma>>0\<close> \<open>k>0\<close>
      by (metis divide_pos_pos ln_le_cancel_iff ln_mult mult_2 mult_pos_pos of_nat_0_less_iff power2_eq_square)
    show ?thesis
      using mult_right_mono [OF X, of "2 * k powr (19/20) / (1-\<gamma>)"] \<open>\<gamma><1\<close>
      by (simp add: ok_fun_93h_def algebra_simps)
  qed
  also have "\<dots> \<le> ((\<gamma> / exp 1) * t / (1-\<gamma>)) + \<delta>*k + ok_fun_93h \<gamma> k"
    using \<gamma>01 mult_right_mono [OF \<phi>, of t] by (simp add: \<phi>_def mult_ac)
  finally have "\<gamma> * (real k - t) \<le> ((\<gamma> / exp 1) * t / (1-\<gamma>)) + \<delta>*k + ok_fun_93h \<gamma> k" .
  then have "(\<gamma>-\<delta>) * k - ok_fun_93h \<gamma> k \<le> t * \<gamma> * c \<gamma>"
    by (simp add: c_def algebra_simps)
  then have "((\<gamma>-\<delta>) * k - ok_fun_93h \<gamma> k) / (\<gamma> * c \<gamma>) \<le> t"
    using \<gamma>01 cgt0 by (simp add: pos_divide_le_eq)
  then have *: "t \<ge> (1-\<delta> / \<gamma>) * inverse (c \<gamma>) * k - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>)"  
    using \<gamma>01 cgt0[of \<gamma>] by (simp add: field_simps)

  define f47 where "f47 \<equiv> \<lambda>x. (1 - 1/(200*x)) * inverse (c x)"
  have "concave_on {1/10..1/5} f47"
    unfolding f47_def
  proof (intro concave_on_mul)
    show "concave_on {1/10..1/5} (\<lambda>x. 1 - 1/(200*x))"
    proof (intro f''_le0_imp_concave)
      fix x::real
      assume "x \<in> {1/10..1/5}"
      then have x01: "0<x" "x<1"
        by auto
      show "((\<lambda>x. (1 - 1/(200*x))) has_real_derivative 1/(200*x^2)) (at x)"
        using x01 by (intro derivative_eq_intros | force simp: eval_nat_numeral)+
      show "((\<lambda>x. 1/(200*x^2)) has_real_derivative -1/(100*x^3)) (at x)"
        using x01 by (intro derivative_eq_intros | force simp: eval_nat_numeral)+
      show "-1/(100*x^3) \<le> 0"
        using x01 by (simp add: divide_simps)
    qed auto
    show "concave_on {1/10..1/5} (\<lambda>x. inverse (c x))"
    proof (intro f''_le0_imp_concave)
      fix x::real
      assume "x \<in> {1/10..1/5}"
      then have x01: "0<x" "x<1"
        by auto
      have swap: "u * (x-1) = (-u) * (1-x)" for u
        by (metis minus_diff_eq minus_mult_commute)
      have \<section>: "exp 1 * (x - 1) < 0"
        using x01
        by (meson exp_gt_zero less_iff_diff_less_0 mult_less_0_iff)
      then have non0: "1 + 1 / (exp 1 * (1-x)) \<noteq> 0"
        using x01 by (smt (verit) exp_gt_zero mult_pos_pos zero_less_divide_iff)
      let ?f1 = "\<lambda>x. -exp 1 /(- 1 + exp 1 * (- 1 + x))\<^sup>2"
      let ?f2 = "\<lambda>x. 2*exp(1)^2/(-1 + exp(1)*(-1 + x))^3"
      show "((\<lambda>x. inverse (c x)) has_real_derivative ?f1 x) (at x)"
        unfolding c_def power2_eq_square
        using x01 \<section> non0
        apply (intro exI conjI derivative_eq_intros | force)+
        apply (simp add: divide_simps square_eq_iff swap)
        done
      show "(?f1 has_real_derivative ?f2 x) (at x)"
        using x01 \<section>
        by (intro derivative_eq_intros | force simp: divide_simps eval_nat_numeral)+
      show "?f2 (x::real) \<le> 0"
        using x01 \<section> by (simp add: divide_simps)
    qed auto
    show "mono_on {(1::real)/10..1/5} (\<lambda>x. 1 - 1 / (200 * x))"
      by (auto simp: monotone_on_def frac_le)
    show "monotone_on {1/10..1/5} (\<le>) (\<lambda>x y. y \<le> x) (\<lambda>x. inverse (c x))"
      using mono_c cgt0 by (auto simp: monotone_on_def divide_simps)
  qed (auto simp: c_def)
  moreover have "f47(1/10) > 0.667"
    unfolding f47_def c_def by (approximation 15)
  moreover have "f47(1/5) > 0.667"
    unfolding f47_def c_def by (approximation 15)
  ultimately have 47: "f47 x > 0.667" if "x \<in> {1/10..1/5}" for x
    using concave_on_ge_min that by fastforce

  define f48 where "f48 \<equiv> \<lambda>x. (1 - 1/20) * inverse (c x)"
  have 48: "f48 x > 0.667" if "x \<in> {0<..<1/10}" for x
  proof -
    have "(0.667::real) < (1 - 1/20) * inverse(c(1/10))"
      unfolding c_def by (approximation 15)
    also have "\<dots> \<le> f48 x"
      using that unfolding f48_def c_def
      by (intro mult_mono le_imp_inverse_le add_mono divide_left_mono) (auto simp: add_pos_pos)
    finally show ?thesis .
  qed
  define e::real where "e \<equiv> 0.667 - 2/3"
  have BIGH: "abs (ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>)) / k \<le> e"
    using big \<open>l\<le>k\<close> unfolding Big_Far_9_3_def all_imp_conj_distrib e_def [symmetric] c_def 
    by auto
  consider "\<gamma> \<in> {0<..<1/10}" | "\<gamma> \<in> {1/10..1/5}"
    using \<delta>_def \<open>\<gamma> \<le> 1/5\<close> \<gamma>01 by fastforce
  then show ?thesis
  proof cases
    case 1
    then have \<delta>\<gamma>: "\<delta> / \<gamma> = 1/20"
      by (auto simp: \<delta>_def)
    have "(2/3::real) \<le> f48 \<gamma> - e"
      using 48[OF 1] e_def by force
    also have "\<dots> \<le> (1-\<delta> / \<gamma>) * inverse (c \<gamma>) - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>) / k"
      unfolding f48_def \<delta>\<gamma> using BIGH
      by (smt (verit, best) divide_nonneg_nonneg of_nat_0_le_iff zero_less_divide_iff)
    finally
    have A: "2/3 \<le> (1-\<delta> / \<gamma>) * inverse (c \<gamma>) - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>) / k" .
    have "real (2 * k) / 3 \<le> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) * k - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>)"
      using mult_left_mono [OF A, of k] cgt0 [of \<gamma>] \<gamma>01 \<open>k>0\<close>
      by (simp add: divide_simps mult_ac)
    with * show ?thesis
      by linarith
  next
    case 2
    then have \<delta>\<gamma>: "\<delta> / \<gamma> = 1/(200*\<gamma>)"
      by (auto simp: \<delta>_def)
    have "(2/3::real) \<le> f47 \<gamma> - e"
      using 47[OF 2] e_def by force
    also have "\<dots> \<le> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>) / k"
      unfolding f47_def \<delta>\<gamma> using BIGH
      by (smt (verit, best) divide_right_mono of_nat_0_le_iff)
    finally
    have \<section>: "2/3 \<le> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>) / k" .
    have "real (2 * k) / 3 \<le> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) * k - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>)"
      using mult_left_mono [OF \<section>, of k] cgt0 [of \<gamma>] \<gamma>01 \<open>k>0\<close>
      by (simp add: divide_simps mult_ac)
    with * show ?thesis
      by linarith
  qed
qed

subsection \<open>Lemma 9.5\<close>

context Book_Basis
begin

definition "ok_fun_95a \<equiv> \<lambda>\<mu> k. ok_fun_61 k - (2 + (2 / (1-\<mu>)) * k powr (19/20))"

definition "ok_fun_95b \<equiv> \<lambda>\<mu> k. ln 2 * ok_fun_95a \<mu> k - 1"

lemma ok_fun_95a: "ok_fun_95a \<mu> \<in> o(real)"
proof -
  have "(\<lambda>k. 2 + (2 / (1-\<mu>)) * k powr (19/20)) \<in> o(real)"
    by real_asymp
  then show ?thesis
    unfolding ok_fun_95a_def using ok_fun_61 sum_in_smallo by blast
qed

lemma ok_fun_95b: "ok_fun_95b \<mu> \<in> o(real)"
  using ok_fun_95a by (auto simp: ok_fun_95b_def sum_in_smallo const_smallo_real)

definition "Big_Far_9_5 \<equiv> \<lambda>\<mu> l. Big_Red_5_3 \<mu> l \<and> Big_Y_6_1 \<mu> l \<and> Big_ZZ_8_5 \<mu> l"

lemma Big_Far_9_5:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_Far_9_5 \<mu> l"
  unfolding Big_Far_9_5_def eventually_conj_iff all_imp_conj_distrib eps_def
  by (simp add: Big_Red_5_3 Big_Y_6_1 Big_ZZ_8_5 assms)

end

text \<open>Y0 is an additional assumption found Bhavik's version. (He had a couple of others).
 The first $o(k)$ function adjusts for the error in $n/2$\<close>
lemma (in Book) Far_9_5:
  fixes l k
  fixes \<delta> \<gamma> \<eta>::real
  defines "\<gamma> \<equiv> l / (real k + real l)"
  defines "\<R> \<equiv> Step_class \<gamma> l k {red_step}"
  defines "t \<equiv> card \<R>"
  defines "m \<equiv> halted_point \<gamma> l k"
  assumes "Colours l k" 
  assumes nV: "real nV \<ge> exp (-\<delta> * k) * (k+l choose l)" and Y0: "card Y0 \<ge> nV div 2"
  assumes p0: "1/2 \<le> 1-\<gamma>-\<eta>" "1-\<gamma>-\<eta> \<le> p0" and "0\<le>\<eta>"
  assumes big: "Big_Far_9_5 \<gamma> l"
  shows "card (Yseq \<gamma> l k m) \<ge> 
     exp (-\<delta> * k + ok_fun_95b \<gamma> k) * (1-\<gamma>-\<eta>) powr (\<gamma>*t / (1-\<gamma>)) * ((1-\<gamma>-\<eta>)/(1-\<gamma>))^t 
   * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) * (k-t+l choose l)"   (is "_ \<ge> ?rhs")
proof -
  define \<S> where "\<S> \<equiv> Step_class \<gamma> l k {dboost_step}"
  define s where "s \<equiv> card \<S>"
  define \<beta> where "\<beta> \<equiv> bigbeta \<gamma> l k"
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  have \<gamma>01: "0 < \<gamma>" "\<gamma> < 1"
    using lk by (auto simp: \<gamma>_def)
  have big85: "Big_ZZ_8_5 \<gamma> l" and big61: "Big_Y_6_1 \<gamma> l" and big53: "Big_Red_5_3 \<gamma> l"
    using big by (auto simp: Big_Far_9_5_def)
  have "\<beta> \<le> \<gamma>" 
    using \<beta>_def \<gamma>01 \<open>Colours l k\<close> big53 bigbeta_le by blast 
  have 85: "s \<le> (\<beta> / (1-\<beta>)) * t + (2 / (1-\<gamma>)) * k powr (19/20)"
    unfolding s_def t_def \<R>_def \<S>_def \<beta>_def using ZZ_8_5 \<gamma>01 \<open>Colours l k\<close> big85 by blast
  also have "\<dots> \<le> (\<gamma> / (1-\<gamma>)) * t + (2 / (1-\<gamma>)) * k powr (19/20)"
    using \<gamma>01 \<open>\<beta> \<le> \<gamma>\<close> by (intro add_mono mult_right_mono frac_le) auto
  finally have D85: "s \<le> \<gamma>*t / (1-\<gamma>) + (2 / (1-\<gamma>)) * k powr (19/20)"
    by auto

  have "t<k"
    unfolding t_def \<R>_def using \<gamma>01 \<open>Colours l k\<close> red_step_limit by blast
  have st: "card (Step_class \<gamma> l k {red_step,dboost_step}) = t + s"
    using \<gamma>01 \<open>Colours l k\<close>
    by (simp add: s_def t_def \<R>_def \<S>_def Step_class_insert_NO_MATCH card_Un_disjnt disjnt_Step_class)
  then have 61: "2 powr (ok_fun_61 k) * p0 ^ (t+s) * card Y0 \<le> card (Yseq \<gamma> l k m)"
    using Y_6_1[OF \<gamma>01 big61 \<open>Colours l k\<close>] card_XY0 \<gamma>01 by (simp add: m_def divide_simps)

  have "(1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * nV \<le> (1-\<gamma>-\<eta>) powr (t+s - (2 / (1-\<gamma>)) * k powr (19/20)) * (4 * card Y0)"
  proof (intro mult_mono)
    show "(1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) \<le> (1-\<gamma>-\<eta>) powr (t+s - (2 / (1-\<gamma>)) * k powr (19/20))"
      using D85 \<gamma>01 add_divide_distrib p0 \<open>\<eta>\<ge>0\<close> powr_mono' by fastforce
    have "nV \<ge> 2"
      by (metis nontriv wellformed two_edges card_mono ex_in_conv finV)
    then have "nV \<le> 4 * (nV div 2)" by linarith
    also have "\<dots> \<le> 4 * card Y0"
      using Y0 mult_le_mono2 by presburger 
    finally show "real nV \<le> real (4 * card Y0)"      
      by force
  qed (use Y0 in auto)
  also have "\<dots> \<le> (1-\<gamma>-\<eta>) powr (t+s) / (1-\<gamma>-\<eta>) powr ((2 / (1-\<gamma>)) * k powr (19/20)) * (4 * card Y0)"
    by (simp add: divide_powr_uminus powr_diff)
  also have "\<dots> \<le> (1-\<gamma>-\<eta>) powr (t+s) / (1/2) powr ((2 / (1-\<gamma>)) * k powr (19/20)) * (4 * card Y0)"
  proof (intro mult_mono divide_left_mono)
    show "(1/2) powr ((2 / (1-\<gamma>)) * k powr (19/20)) \<le> (1-\<gamma>-\<eta>) powr ((2 / (1-\<gamma>)) * k powr (19/20))"
      using \<gamma>01 p0 \<open>0\<le>\<eta>\<close> by (intro powr_mono_both') auto
  qed (use p0 in auto)
  also have "\<dots> \<le> p0 powr (t+s) / (1/2) powr ((2 / (1-\<gamma>)) * k powr (19/20)) * (4 * card Y0)"
    using p0 powr_mono2 by (intro mult_mono divide_right_mono) auto
  also have "\<dots> = (2 powr (2 + (2 / (1-\<gamma>)) * k powr (19/20))) * p0 ^ (t+s) * card Y0"
    using p0_01 by (simp add: powr_divide powr_add power_add powr_realpow)
  finally have "2 powr (ok_fun_95a \<gamma> k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * nV \<le> 2 powr (ok_fun_61 k) * p0 ^ (t+s) * card Y0"
    by (simp add: ok_fun_95a_def powr_diff field_simps)
  with 61 have *: "card (Yseq \<gamma> l k m) \<ge> 2 powr (ok_fun_95a \<gamma> k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * nV"
    by linarith

  have F: "exp (ok_fun_95b \<gamma> k) = 2 powr ok_fun_95a \<gamma> k * exp (- 1)"
    by (simp add: ok_fun_95b_def exp_diff exp_minus powr_def field_simps)
  have "?rhs
   \<le> exp (-\<delta> * k) * 2 powr (ok_fun_95a \<gamma> k) * exp (-1) * (1-\<gamma>-\<eta>) powr (\<gamma>*t / (1-\<gamma>))
         * (((1-\<gamma>-\<eta>)/(1-\<gamma>)) ^t * exp (\<gamma> * (real t)\<^sup>2 / real(2*k)) * (k-t+l choose l))"
    unfolding exp_add F by simp
  also have "\<dots> \<le>  exp (-\<delta> * k) * 2 powr (ok_fun_95a \<gamma> k) * (1-\<gamma>-\<eta>) powr (\<gamma>*t / (1-\<gamma>))
         * (exp (-1) * ((1-\<gamma>-\<eta>)/(1-\<gamma>)) ^t * exp (\<gamma> * (real t)\<^sup>2 / real(2*k)) * (k-t+l choose l))"
    by (simp add: mult.assoc)
  also have "\<dots> \<le> 2 powr (ok_fun_95a \<gamma> k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * exp (-\<delta> * k)
                * (exp (-1) * (1-\<gamma>) powr (- real t) * exp (\<gamma> * (real t)\<^sup>2 / real(2*k)) * (k-t+l choose l))"
    using p0 \<gamma>01
    unfolding powr_add powr_minus by (simp add: mult_ac divide_simps flip: powr_realpow)
  also have "\<dots> \<le> 2 powr (ok_fun_95a \<gamma> k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * exp (-\<delta> * k) * (k+l choose l)"
  proof (cases "t=0")
    case False
    then show ?thesis
      unfolding \<gamma>_def using \<open>t<k\<close> by (intro mult_mono order_refl Far_9_6) auto
  qed auto
  also have "\<dots> \<le> 2 powr (ok_fun_95a \<gamma> k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * nV"
    using nV mult_left_mono by fastforce
  also have "\<dots> \<le> card (Yseq \<gamma> l k m)"
    by (rule *)
  finally show ?thesis .
qed

subsection \<open>Lemma 9.2 actual proof\<close>

context Book_Basis
begin

lemma error_9_2:
  assumes "0<\<mu>" "\<mu><1" 
  shows "\<forall>\<^sup>\<infinity>k. ok_fun_95b \<mu> k + \<mu>*k/60 \<ge> 0"
  using assms p0_min
  unfolding ok_fun_95b_def ok_fun_95a_def ok_fun_61_def eps_def
  by real_asymp

definition "Big_Far_9_2 \<equiv> \<lambda>\<mu> l. Big_Far_9_3 \<mu> l \<and> Big_Far_9_5 \<mu> l
                \<and> (\<forall>k\<ge>l. ok_fun_95b \<mu> k + \<mu>*k/60 \<ge> 0)"

lemma Big_Far_9_2:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_Far_9_2 \<mu> l"
  unfolding Big_Far_9_2_def eventually_conj_iff all_imp_conj_distrib eps_def
  apply (simp add: Big_Far_9_3 Big_Far_9_5 assms)
    apply (intro conjI eventually_all_ge_at_top error_9_2 [OF assms])
  done

text \<open>A little tricky for me to express since my "Colours" assumption includes the allowed 
    assumption that there are no cliques in the original graph (page 9). So it's a contrapositive\<close>
lemma (in Book) Far_9_2_aux:
  fixes l k
  fixes \<delta> \<gamma> \<eta>::real
  defines "\<gamma> \<equiv> l / (real k + real l)"
  defines "\<delta> \<equiv> \<gamma>/20"
  assumes 0: "real (card X0) \<ge> nV/2" "card Y0 \<ge> nV div 2" "p0 \<ge> 1-\<gamma>-\<eta>"
     \<comment>\<open>These are the assumptions about the red density of the graph\<close>
  assumes "Colours l k" and \<gamma>: "\<gamma> \<le> 1/10" and \<eta>: "0\<le>\<eta>" "\<eta> \<le> \<gamma>/15"
  assumes nV: "real nV \<ge> exp (-\<delta> * k) * (k+l choose l)" 
  assumes big: "Big_Far_9_2 \<gamma> l"
  shows False
proof -
  define \<R> where "\<R> \<equiv> Step_class \<gamma> l k {red_step}"
  define t where "t \<equiv> card \<R>"
  define m where "m \<equiv> halted_point \<gamma> l k"
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  have \<gamma>01: "0 < \<gamma>" "\<gamma> < 1"
    using lk by (auto simp: \<gamma>_def)
  have big93: "Big_Far_9_3 \<gamma> l" 
    using big by (auto simp: Big_Far_9_2_def)
  have t23: "t \<ge> 2*k / 3"
    unfolding t_def \<R>_def \<gamma>_def
  proof (rule Far_9_3)
    show "l / (real k + real l) \<le> 1/5"
      using \<gamma> unfolding \<gamma>_def by linarith
    have "min (1/200) (l / (real k + real l) / 20) \<ge> \<delta>"
      unfolding \<delta>_def using \<gamma> \<open>0<l\<close> by (simp add: \<gamma>_def)
    then show "exp (- min (1/200) (l / (real k + real l) / 20) * real k) * real (k + l choose l) \<le> nV"
      using \<delta>_def \<gamma>_def nV by force
    show "1/4 \<le> p0"
      using \<eta> \<gamma> 0 by linarith
    show "Big_Far_9_3 (l / (real k + real l)) l"
      using \<gamma>_def big93 by blast
  qed (use assms in auto)
  have "t<k"
    unfolding t_def \<R>_def using \<gamma>01 \<open>Colours l k\<close> red_step_limit by blast

  have ge_half: "1/2 \<le> 1-\<gamma>-\<eta>"
    using \<gamma> \<eta> by linarith
  have "ln((134/150) powr (10/9)) \<ge> -1/3 + (1/5::real)"
    by (approximation 10)
  then have "exp (-1/3 + (1/5::real)) \<le> exp (10/9 * ln (134/150))"
    by (simp add: ln_powr)
  also have "\<dots> \<le> exp (1 / (1-\<gamma>) * ln (134/150))"
    using \<gamma> by (auto simp: divide_simps)
  also have "\<dots> \<le> exp (1 / (1-\<gamma>) * ln (1-\<gamma>-\<eta>))"
    using \<gamma> \<eta> by (auto simp: divide_simps)
  also have "\<dots> = (1-\<gamma>-\<eta>) powr (1 / (1-\<gamma>))"
    using ge_half by (simp add: powr_def)
  finally have A: "exp (-1/3 + 1/5) \<le> (1-\<gamma>-\<eta>) powr (1 / (1-\<gamma>))" .

  have \<section>: "3*t / (10*k) \<le> (-1/3 + 1/5) + t/(2*k)"
    using t23 \<open>k>0\<close> by (simp add: divide_simps)
  have "3*\<gamma>*t\<^sup>2 / (10*k) \<le> \<gamma>*t*(-1/3 + 1/5) + \<gamma>*t\<^sup>2/(2*k)"
    using mult_right_mono [OF \<section>, of "\<gamma>*t"] \<gamma>01
    by (simp add: eval_nat_numeral algebra_simps) 
  then have "exp (3*\<gamma>*t\<^sup>2 / (10*k)) \<le> exp (\<gamma>*t*(-1/3 + 1/5)) * exp (\<gamma>*t\<^sup>2/(2*k))"
    by (simp add: mult_exp_exp)
  also have "\<dots> = exp (-1/3 + 1/5) powr (\<gamma>*t) * exp (\<gamma>*t\<^sup>2/(2*k))"
    by (simp add: exp_powr_real)
  also have "\<dots> \<le> (1-\<gamma>-\<eta>) powr ((\<gamma>*t) / (1-\<gamma>)) * exp (\<gamma>*t\<^sup>2/(2*k))"
    using \<gamma>01 powr_powr powr_mono2 [of "\<gamma>*t" "exp (-1/3 + 1/5)", OF _ _ A]
    by (intro mult_right_mono) auto
  finally have B: "exp (3*\<gamma>*t\<^sup>2 / (10*k)) \<le> (1-\<gamma>-\<eta>) powr ((\<gamma>*t) / (1-\<gamma>)) * exp (\<gamma>*t\<^sup>2/(2*k))" .

  have \<section>: "(2*k / 3)^2 \<le> t\<^sup>2"
    using t23 by auto
  have C: "\<delta>*k + \<gamma>*k/60 \<le> 3*\<gamma>*t\<^sup>2 / (20*k)"
    using \<open>k>0\<close> \<gamma>01 mult_right_mono [OF \<section>, of "\<gamma>/(80*k)"]
    by (simp add: field_simps \<delta>_def eval_nat_numeral)

  have "exp (- 3*\<gamma>*t / (20*k)) \<le> exp (-3 * \<eta>/2)"
  proof -
    have \<section>: "1 \<le> 3/2 * real t / (real k)"
      using t23 \<open>k>0\<close> by (auto simp: divide_simps)
    have "\<gamma> / 15 \<le> \<gamma> * real t / (10 * real k)"
      using mult_right_mono [OF \<section>, of "\<gamma>/15"] \<gamma>01 by auto
    with \<eta> show ?thesis
      by simp
  qed
  also have "\<dots> \<le> 1 - \<eta> / (1-\<gamma>)"
  proof -
    have \<section>: "2/3 \<le> (1 - \<gamma> - \<eta>)"
      using \<gamma> \<eta> by linarith
    have "1 / (1 - \<eta> / (1-\<gamma>)) = 1 + \<eta> / (1-\<gamma>-\<eta>)"
      using ge_half \<eta> by (simp add: divide_simps split: if_split_asm)
    also have "\<dots> \<le> 1 + 3 * \<eta> / 2"
      using mult_right_mono [OF \<section>, of \<eta>] \<eta> ge_half
      by (simp add: divide_simps algebra_simps)
    also have "\<dots> \<le> exp (3 * \<eta> / 2)"
      using exp_minus_ge [of "-3*\<eta>/2"] by simp
    finally show ?thesis
      using \<gamma>01 ge_half 
      by (simp add: exp_minus divide_simps mult.commute split: if_split_asm)
  qed
  also have "\<dots> = (1-\<gamma>-\<eta>) / (1-\<gamma>)"
    using \<gamma>01 by (simp add: divide_simps)
  finally have \<section>: "exp (- 3*\<gamma>*t / (20*k)) \<le> (1-\<gamma>-\<eta>) / (1-\<gamma>)" .
  have D: "exp (- 3*\<gamma>*t\<^sup>2 / (20*k)) \<le> ((1-\<gamma>-\<eta>) / (1-\<gamma>))^t"
    using powr_mono2 [of t, OF _ _ \<section>] ge_half \<gamma>01
    by (simp add: eval_nat_numeral powr_powr exp_powr_real mult_ac flip: powr_realpow)

  have "RN (k-t) l \<le> (k-t+l choose l)"
    by (simp add: add.commute RN_commute RN_le_choose)
  also have "\<dots> \<le> card (Yseq \<gamma> l k m)"
  proof -
    have "1 * real(k-t+l choose l) 
            \<le> exp (ok_fun_95b \<gamma> k + \<gamma>*k/60) * (k-t+l choose l)"
      using big  \<open>k\<ge>l\<close> unfolding Big_Far_9_2_def
      by (intro mult_right_mono mult_le_1_iff) auto
    also have "\<dots> \<le> exp (3*\<gamma>*t\<^sup>2 / (20*k) + -\<delta> * k + ok_fun_95b \<gamma> k) * (k-t+l choose l)"
      using C by simp
    also have "\<dots> = exp (3*\<gamma>*t\<^sup>2 / (10*k)) * exp (-\<delta> * k + ok_fun_95b \<gamma> k) * exp (- 3*\<gamma>*t\<^sup>2 / (20*k))
            * (k-t+l choose l)"
      by (simp flip: exp_add)
    also have "\<dots> \<le> exp (3*\<gamma>*t\<^sup>2 / (10*k)) * exp (-\<delta> * k + ok_fun_95b \<gamma> k) * ((1-\<gamma>-\<eta>)/(1-\<gamma>))^t 
            * (k-t+l choose l)"
      using \<gamma>01 ge_half D by (intro mult_right_mono) auto
    also have "\<dots> \<le> (1-\<gamma>-\<eta>) powr (\<gamma>*t / (1-\<gamma>)) * exp (\<gamma> * t\<^sup>2 / (2 * k)) * exp (-\<delta> * k + ok_fun_95b \<gamma> k) * ((1-\<gamma>-\<eta>)/(1-\<gamma>))^t 
            * (k-t+l choose l)"
      using \<gamma>01 ge_half by (intro mult_right_mono B) auto
    also have "\<dots> = exp (-\<delta> * k + ok_fun_95b \<gamma> k) * (1-\<gamma>-\<eta>) powr (\<gamma>*t / (1-\<gamma>)) * ((1-\<gamma>-\<eta>)/(1-\<gamma>))^t 
                   * exp (\<gamma> * (real t)\<^sup>2 / (2 * real k)) * (k-t+l choose l)"
      by (simp add: mult_ac)
    also have 95: "\<dots> \<le> real (card (Yseq \<gamma> l k m))"
      unfolding \<gamma>_def t_def \<R>_def m_def
    proof (rule Far_9_5)
      show "1/2 \<le> 1 - l / (real k + real l) - \<eta>"
        using ge_half \<gamma>_def by blast
      show "Big_Far_9_5 (l / (real k + real l)) l"
        using Big_Far_9_2_def big unfolding \<gamma>_def by presburger
    qed (use assms in auto)
    finally have "(k-t+l choose l) \<le> real (card (Yseq \<gamma> l k m))" by simp
    then show ?thesis
      by fastforce
  qed
  finally obtain K 
      where Ksub: "K \<subseteq> Yseq \<gamma> l k m" 
      and K: "card K = k-t \<and> clique K Red \<or> card K = l \<and> clique K Blue"
    by (meson Red_Blue_RN Yseq_subset_V size_clique_def)
  show False
    using K
  proof
    assume K: "card K = k - t \<and> clique K Red"
    have "clique (K \<union> Aseq \<gamma> l k m) Red"
    proof (intro clique_Un)
      show "clique (Aseq \<gamma> l k m) Red"
        by (meson A_Red_clique valid_state_seq)
      have "all_edges_betw_un (Aseq \<gamma> l k m) (Yseq \<gamma> l k m) \<subseteq> Red"
        using valid_state_seq Ksub
        by (auto simp: valid_state_def RB_state_def all_edges_betw_un_Un2)
      then show "all_edges_betw_un K (Aseq \<gamma> l k m) \<subseteq> Red"
        using Ksub all_edges_betw_un_commute all_edges_betw_un_mono2 by blast
      show "K \<subseteq> V"
        using Ksub Yseq_subset_V by blast
    qed (use K Aseq_subset_V in auto)
    moreover have "card (K \<union> Aseq \<gamma> l k m) = k"
    proof -
      have eqt: "card (Aseq \<gamma> l k m) = t"
        using red_step_eq_Aseq
        using \<R>_def \<gamma>01 \<open>Colours l k\<close> m_def t_def by presburger
      have "card (K \<union> Aseq \<gamma> l k m) = card K + card (Aseq \<gamma> l k m) "
      proof (intro card_Un_disjoint)
        show "finite K"
          by (meson Ksub Yseq_subset_V finV finite_subset)
        have "disjnt (Yseq \<gamma> l k m) (Aseq \<gamma> l k m)"
          using valid_state_seq by (auto simp: valid_state_def disjoint_state_def)
        with Ksub show "K \<inter> Aseq \<gamma> l k m = {}"
          by (auto simp: disjnt_def)
      qed (simp add: finite_Aseq)
      also have "\<dots> = k"
        using eqt K \<open>t < k\<close> by simp
      finally show ?thesis .
    qed
    moreover have "K \<union> Aseq \<gamma> l k m \<subseteq> V"
      using Aseq_subset_V Ksub Yseq_subset_V by blast
    ultimately show False
      using \<open>Colours l k\<close> 
      unfolding Colours_def size_clique_def by blast
  next
    assume "card K = l \<and> clique K Blue"
    then show False
      using \<open>Colours l k\<close> Ksub Yseq_subset_V
      unfolding Colours_def size_clique_def by blast
  qed
qed

text \<open>Needs to be proved OUTSIDE THE BOOK LOCALE\<close>
lemma (in Book_Basis) Far_9_2:
  fixes Red Blue :: "'a set set"
  fixes l k
  fixes \<delta> \<gamma> \<eta>::real
  defines "\<gamma> \<equiv> l / (real k + real l)"
  defines "\<delta> \<equiv> \<gamma>/20"
  assumes complete: "E = all_edges V"
  assumes Red_not_Blue: "Red \<noteq> Blue"
  assumes part_RB: "partition_on E {Red,Blue}"
  assumes infinite_UNIV: "infinite (UNIV::'a set)"
  assumes n: "real gorder \<ge> exp (-\<delta> * k) * (k+l choose l)" 
  assumes gd: "graph_density Red \<ge> 1-\<gamma>-\<eta>" 
    and p0_min_OK: "p0_min \<le> 1-\<gamma>-\<eta>"  (*NEEDED TO INTERPRET BOOK LOCALE*)
  assumes big: "Big_Far_9_2 \<gamma> l" and "l\<le>k"
  assumes "\<gamma> \<le> 1/10" and \<epsilon>: "0\<le>\<eta>" "\<eta> \<le> \<gamma>/15"
  shows "(\<exists>K. size_clique k K Red) \<or> (\<exists>K. size_clique l K Blue)"
proof (rule ccontr)
  assume neg: "\<not> ((\<exists>K. size_clique k K Red) \<or> (\<exists>K. size_clique l K Blue))"
  have "Red \<subseteq> E" "Red \<noteq> {}" "E \<noteq> {}"
    using part_RB by (auto simp: partition_on_def)
  then have "gorder\<ge>2"
    by (metis card_mono ex_in_conv finV two_edges wellformed)
  then have "0 < gorder div 2" "gorder div 2 < gorder"
    by auto
  then obtain Y0 where card_Y0: "card Y0 = gorder div 2" and "Y0\<subseteq>V" 
          and Y0: "graph_density Red \<le> gen_density Red Y0 (V\<setminus>Y0)"
    using exists_density_edge_density \<open>Red \<subseteq> E\<close> complete by blast
  define X0 where "X0 \<equiv> V \<setminus> Y0"
  interpret Book V E p0_min Red Blue X0 Y0
  proof
    show "X0\<subseteq>V" "disjnt X0 Y0"
      by (auto simp: X0_def disjnt_iff)
    show "p0_min \<le> gen_density Red X0 Y0"
      using X0_def Y0 gd gen_density_commute p0_min_OK by auto
  qed (use assms \<open>Y0\<subseteq>V\<close> in auto)
  have card_X0: "card X0 \<ge> nV/2"
    using card_Y0 \<open>Y0\<subseteq>V\<close> unfolding X0_def
    by (simp add: card_Diff_subset finite_Y0)
  have False if "l<2"
    using neg that Red_Blue_RN [of 2 gorder V] \<open>gorder\<ge>2\<close> 
    apply (simp add: size_clique_def )
    by (metis One_nat_def RN_1' Red_Blue_RN bot_least  card.empty ex_card less_2_cases neg null_clique one_le_numeral neq0_conv)
  with \<open>k\<ge>l\<close> have "l\<ge>2" "k\<ge>2"
    by force+
  have "Colours l k"
    using neg \<open>l\<le>k\<close> by (auto simp: Colours_def)
  show False
  proof (intro Far_9_2_aux [of l k \<eta>])
    show "1 - real l / (real k + real l) - \<eta> \<le> p0"
      using X0_def Y0 \<gamma>_def gd gen_density_commute p0_def by force
  qed (use assms card_X0 card_Y0 \<open>Colours l k\<close> in auto)
qed

subsection \<open>Lemma 9.1\<close>

definition "Big_Far_0_1 \<equiv> \<lambda>\<mu> l. True"

lemma Big_Far_0_1:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_Far_0_1 \<mu> l"
  unfolding Big_Far_0_1_def eventually_conj_iff all_imp_conj_distrib eps_def
  apply (simp add: Big_Far_9_3  assms)
  done

lemma (in Book) Far_9_1:
  fixes l k
  fixes \<delta> \<gamma>::real
  defines "gamma \<equiv> \<lambda>m. (l - real m) / (k + real l - real m)"
  defines "\<gamma> \<equiv> gamma 0"
  defines "\<delta> \<equiv> \<gamma>/20"
  assumes "Colours l k" and \<gamma>: "\<gamma> \<le> 1/10" 
  assumes big: "Big_Far_0_1 \<gamma> l"
  shows "RN k l \<le> exp (-\<delta>*k + 1) * (k+l choose l)"
proof (rule ccontr)
  assume non: "\<not> RN k l \<le> exp (-\<delta> * k + 1) * (k+l choose l)"
  obtain ln0: "l>0" and kn0: "k>0" and "l\<le>k"
    using \<open>Colours l k\<close> Colours_kn0 Colours_ln0  by (auto simp: Colours_def)
  define \<xi>::real where "\<xi> \<equiv> 1/15"
     \<comment>\<open>Bhavik's terminology below\<close>
  define U_lower_bound_ratio where 
        "U_lower_bound_ratio \<equiv> \<lambda>m. (1+\<xi>)^m * (\<Prod>i<m. (l - real i) / (k + l - real i))"
  define is_good_clique where  
        "is_good_clique \<equiv> \<lambda>n K. clique K Blue \<and> K \<subseteq> V \<and>
                                 card (V \<inter> (\<Inter>w\<in>K. Neighbours Blue w))
                                 \<ge> real n * U_lower_bound_ratio (card K) - card K"
  have \<gamma>_eq: "\<gamma> = l / (k + real l)"
    by (simp add: \<gamma>_def gamma_def)
  have l9k: "l \<le> 9*k"
    using \<gamma> \<open>l \<le> k\<close> by (auto simp: \<gamma>_def divide_simps)
  have U_lower_bound_ratio_ge0: "0 \<le> U_lower_bound_ratio m" if "m < l" for m
    using that by (auto simp: U_lower_bound_ratio_def \<xi>_def zero_le_mult_iff intro!: prod_nonneg)
  have "U_lower_bound_ratio (Suc m) \<le> U_lower_bound_ratio m" if "m < l" for m
  proof -
    have \<section>: "1+\<xi> \<le> (k + l - real m) / (l - real m)"
      using l9k that by (auto simp: divide_simps \<xi>_def)
    have [simp]: "U_lower_bound_ratio (Suc m)
               = ((1+\<xi>) * (l - real m) / (k + real l - real m)) * U_lower_bound_ratio m"
      by (simp add: U_lower_bound_ratio_def)
    show ?thesis
      using mult_left_mono [OF \<section>, of "U_lower_bound_ratio m"]  that
      by (simp add: U_lower_bound_ratio_ge0 field_simps)
  qed
  then have Ulb_decreasing: "antimono_on {..<l} U_lower_bound_ratio"
    by (auto simp: monotone_on_def intro: lift_Suc_antimono_le [of "{..<l}"])

  define mstar where "mstar \<equiv> LEAST m. gamma m < \<gamma>\<^sup>2"
  have "gamma l < \<gamma>\<^sup>2"
    using \<open>l>0\<close> by (simp add: gamma_def \<gamma>_def of_nat_diff)
  then obtain mstar_works: "gamma mstar < \<gamma>\<^sup>2" and mstar_le: "\<And>m. gamma m < \<gamma>\<^sup>2 \<Longrightarrow> mstar \<le> m"
    by (metis mstar_def wellorder_Least_lemma)

  have is_good_empty: "is_good_clique n {}" if "n \<le> nV" for n
    using that by (simp add: is_good_clique_def U_lower_bound_ratio_def)

  have is_good_card: "card K < l" if "is_good_clique n K" for n K
    using \<open>Colours l k\<close> that
    unfolding Colours_def is_good_clique_def
    by (metis nat_neq_iff size_clique_def size_clique_smaller)

  have ln1: "l \<noteq> Suc 0"
    using \<open>Colours l k\<close> unfolding Colours_def
    by (metis RN_1 RN_commute Red_Blue_RN XY0(2) card_XY0(1) less_eq_Suc_le)
  with ln0 have "l\<ge>2"
    by linarith


  { fix W
    assume "W\<subseteq>V"
    assume nV_eq: "nV = nat\<lceil>RN k l / exp 1\<rceil>"
    assume 49: "is_good_clique nV W"
    assume max49: "\<And>x. x\<in>V\<setminus>W \<Longrightarrow> \<not> is_good_clique nV (insert x W)"
    assume "W \<noteq> {}"
    define m where "m \<equiv> card W"
    define \<gamma>' where "\<gamma>' \<equiv> (l - real m) / (k + l - real m)"
    define \<eta> where "\<eta> \<equiv> \<xi> * \<gamma>'"
    define U where "U \<equiv> (\<Inter>w\<in>W. Neighbours Blue w)"
    define EU where "EU \<equiv> E \<inter> Pow U"
    define RedU where "RedU \<equiv> Red \<inter> Pow U"
    define BlueU where "BlueU \<equiv> Blue \<inter> Pow U"
    assume "card U > 1"

  \<comment> \<open>Following Bhavik in dividing by @{term "exp 1"}\<close>
    have "nV < RN k l"
    proof -
      have "RN k l \<ge> 2"
        using \<open>l\<ge>2\<close> \<open>k\<ge>l\<close> by (metis RN_2' RN_mono le_trans)
      then have "3 + real (RN k l) \<le> (5/2) * real (RN k l)"
        by linarith
      moreover have "(5/2::real) < exp 1"
        by (approximation 5)
      ultimately have "exp 1 + real (RN k l) \<le> exp 1 * real (RN k l)"
        by (smt (verit, best) exp_le mult_right_mono of_nat_0_le_iff)
      moreover have "0 \<le> \<lceil>real (RN k l) / exp 1\<rceil>"
        by (metis ceiling_mono ceiling_zero exp_ge_zero of_nat_0_le_iff zero_le_divide_iff)
      ultimately show ?thesis
        by (simp add: nV_eq nat_less_iff ceiling_less_iff field_simps)
    qed
    have "real nV \<ge> RN k l / exp 1"
      using nV_eq real_nat_ceiling_ge by presburger
    moreover have "exp (- \<delta> * real k) * real (k + l choose l) < real (RN k l) / exp 1"
      using non by (simp add: exp_diff exp_minus not_le field_simps)
    ultimately have nV_gt: "nV > exp (-\<delta> * k) * (k+l choose l)"
      by argo

    have "RN k l > 0"
      by (metis RN_eq_0_iff gr0I kn0 ln0)
    with \<open>nV < RN k l\<close> have nV_less: "nV < (k+l choose l)"
      by (metis add.commute RN_commute RN_le_choose le_trans linorder_not_less)

    have "\<gamma>' > 0"
      using is_good_card [OF 49] by (simp add: \<gamma>'_def m_def)
    then have "\<eta> > 0"
      by (simp add: \<eta>_def \<xi>_def)
    have "finite W"
      using \<open>W \<subseteq> V\<close> finV finite_subset by blast
    have "U \<subseteq> V"
      using \<open>W \<noteq> {}\<close> Blue_E by (force simp: U_def in_Neighbours_iff)
    then have VUU: "V \<inter> U = U"
      by blast
    have "0<m"
      using \<open>W \<noteq> {}\<close> \<open>finite W\<close> m_def by fastforce
    have "m<l"
      using "49" is_good_card m_def by blast
    then have \<gamma>1516: "\<gamma>' \<le> 15/16"
      using \<gamma>_def \<gamma> by (simp add: \<gamma>'_def gamma_def divide_simps)
    then have \<gamma>'_le1: "(1+\<xi>) * \<gamma>' \<le> 1"
      by (simp add: \<xi>_def)
    have "\<gamma>' < \<gamma>"
      using \<open>m<l\<close> \<open>0 < m\<close> kn0 by (simp add: \<gamma>_def \<gamma>'_def gamma_def field_simps)

    obtain [iff]: "finite RedU" "finite BlueU" "RedU \<subseteq> EU"
      using BlueU_def EU_def RedU_def Red_E by auto
    have card_RedU_le: "card RedU \<le> card EU"
      by (metis EU_def \<open>RedU \<subseteq> EU\<close> card_mono fin_edges finite_Int)
    interpret UBB: Book_Basis U "E \<inter> Pow U" p0_min 
    proof
      fix e :: "'a set"
      assume "e \<in> E \<inter> Pow U"
      with two_edges show "e \<subseteq> U" "card e = 2" by auto
    next
      show "finite U"
        using \<open>U \<subseteq> V\<close> by (simp add: finV finite_subset)
      show "0 < p0_min" "p0_min < 1"
        by (auto simp add: p0_min)
      have "x \<in> E" if "x \<in> all_edges U" for x 
        using \<open>U \<subseteq> V\<close> all_edges_mono that complete by blast
      then show "E \<inter> Pow U = all_edges U"
        using comp_sgraph.wellformed \<open>U \<subseteq> V\<close>
        using e_in_all_edges_ss by auto
      show "infinite (UNIV::'a set)"
        by (simp add: local.infinite_UNIV)
    qed

    have clique_W: "size_clique m W Blue"
      using "49" is_good_clique_def m_def size_clique_def by blast

    have card_EU: "card EU > 0"
      using \<open>card U > 1\<close> UBB.complete by (simp add: EU_def UBB.finV card_all_edges)
    then have "card U > 1"
      by (simp add: EU_def UBB.complete UBB.finV card_all_edges)
    have BlueU_eq: "BlueU = EU \<setminus> RedU" 
      using Blue_eq complete by (fastforce simp add: BlueU_def RedU_def EU_def)
    have [simp]: "UBB.graph_size = card EU"
      using EU_def by blast
    have False if "UBB.graph_density RedU < 1 - \<gamma>' - \<eta>"
    proof -    \<comment>\<open>by maximality, etc.\<close>
      have \<section>: "UBB.graph_density BlueU \<ge> \<gamma>' + \<eta>" 
      using that card_EU card_RedU_le 
        by (simp add: BlueU_eq UBB.graph_density_def diff_divide_distrib card_Diff_subset of_nat_diff)

      have Nx: "Neighbours BlueU x \<inter> (U \<setminus> {x}) = Neighbours BlueU x" for x 
        using that by (auto simp: BlueU_eq EU_def Neighbours_def)

      have "BlueU \<subseteq> E \<inter> Pow U"
        using BlueU_eq EU_def by blast
      with UBB.exists_density_edge_density [of 1 BlueU]
      obtain x where "x\<in>U" and x: "UBB.graph_density BlueU \<le> UBB.gen_density BlueU {x} (U\<setminus>{x})"
        by (metis UBB.complete \<open>1 < UBB.gorder\<close> card_1_singletonE insertI1 zero_less_one subsetD)
      with \<section> have "\<gamma>' + \<eta> \<le> UBB.gen_density BlueU (U\<setminus>{x}) {x}"
        using UBB.gen_density_commute by auto
      then have *: "(\<gamma>' + \<eta>) * (card U - 1) \<le> card (Neighbours BlueU x)"
        using \<open>BlueU \<subseteq> E \<inter> Pow U\<close> \<open>card U > 1\<close> \<open>x \<in> U\<close>
        by (simp add: UBB.gen_density_def UBB.edge_card_eq_sum_Neighbours UBB.finV divide_simps Nx)

      have x: "x \<in> V\<setminus>W"
        using U_def \<open>x \<in> U\<close> \<open>U \<subseteq> V\<close> by auto
      moreover
      have "is_good_clique nV (insert x W)"
        unfolding is_good_clique_def
      proof (intro conjI)
        show "clique (insert x W) Blue"
        proof (intro clique_insert)
          show "clique W Blue"
            using "49" is_good_clique_def by blast
          show "all_edges_betw_un {x} W \<subseteq> Blue"
            using \<open>x\<in>U\<close> by (auto simp: U_def all_edges_betw_un_def insert_commute in_Neighbours_iff )
        qed (use \<open>W \<subseteq> V\<close> \<open>x \<in> V\<setminus>W\<close> in auto)
      next
        show "insert x W \<subseteq> V"
          using \<open>W \<subseteq> V\<close> \<open>x \<in> V\<setminus>W\<close> by auto
      next
        have \<section>: "nV * U_lower_bound_ratio m \<le> m + card U"
          using 49 VUU unfolding is_good_clique_def m_def U_def by force
        have NB_Int_U: "Neighbours Blue x \<inter> U = Neighbours BlueU x"
          using \<open>x \<in> U\<close> by (auto simp: BlueU_def U_def Neighbours_def)
        have ulb_ins: "U_lower_bound_ratio (card (insert x W)) = U_lower_bound_ratio m * (1+\<xi>) * \<gamma>'"
          using \<open>x \<in> V\<setminus>W\<close> \<open>finite W\<close> by (simp add: m_def U_lower_bound_ratio_def \<gamma>'_def)
        have "nV * U_lower_bound_ratio (card (insert x W))  = nV * U_lower_bound_ratio m * (1+\<xi>) * \<gamma>'"
          by (simp add: ulb_ins)
        also have "\<dots> \<le> real (m + card U) * (1+\<xi>) * \<gamma>'"
          using mult_right_mono [OF \<section>, of "(1+\<xi>) * \<gamma>'"] \<open>0 < \<eta>\<close> \<open>0 < \<gamma>'\<close> \<eta>_def by argo
        also have "\<dots> \<le> m + card U * (1+\<xi>) * \<gamma>'"
          using mult_left_mono [OF \<gamma>'_le1, of m] by (simp add: algebra_simps)
        also have "\<dots> \<le> Suc m + (\<gamma>' + \<eta>) * (UBB.gorder - Suc 0)"
          using * \<open>x \<in> V\<setminus>W\<close> \<open>finite W\<close> \<open>1 < UBB.gorder\<close> \<gamma>1516
          apply (simp add: U_lower_bound_ratio_def \<xi>_def \<eta>_def)
          by (simp add: of_nat_diff algebra_simps)
        also have "\<dots> \<le> Suc m + card (\<Inter> (Neighbours Blue ` insert x W))"
          using \<open>1 < UBB.gorder\<close> \<gamma>1516 * \<open>W \<subseteq> V\<close> \<open>x \<in> V\<setminus>W\<close> \<open>finite W\<close>
          by (smt (verit) INT_insert U_def NB_Int_U One_nat_def of_nat_add)
        also have "\<dots> = real (card (insert x W) + card (V \<inter> \<Inter> (Neighbours Blue ` insert x W)))"
          using x \<open>finite W\<close> VUU unfolding m_def U_def
          by (metis DiffE INT_insert Int_left_commute card.insert)
        finally show "nV * U_lower_bound_ratio (card(insert x W)) - card(insert x W)
                   \<le> card (V \<inter> \<Inter> (Neighbours Blue ` insert x W))" 
          by simp
      qed
      ultimately show False
        using max49 by blast
    qed
    then have *: "UBB.graph_density RedU \<ge> 1 - \<gamma>' - \<eta>" by force



    \<comment> \<open>Bhavik's gamma'_le_gamma_iff\<close>
    have "\<gamma>' < \<gamma>\<^sup>2 \<longleftrightarrow> (real k * real l) + (real l * real l) < (real k * real m) + (real l * (real m * 2))"
      using \<open>m < l\<close>
      apply (simp add: \<gamma>'_def \<gamma>_eq eval_nat_numeral divide_simps; simp add: algebra_simps)
      by (metis kn0 mult_less_cancel_left_pos of_nat_0_less_iff distrib_left)
    also have "\<dots>  \<longleftrightarrow> (l * (k + l)) / (k + 2 * l) < m"
      using \<open>m < l\<close> by (simp add: field_simps)
    finally have gamma'_le_gamma_iff: "\<gamma>' < \<gamma>\<^sup>2 \<longleftrightarrow> (l * (k + l)) / (k + 2 * l) < m" .



    have ?thesis
    proof (cases "\<gamma>' < \<gamma>\<^sup>2")
      case True
      have YKK: "\<gamma>*k \<le> m" 
        unfolding \<gamma>_eq
        using \<open>0<k\<close> \<open>0<m\<close> \<open>m < l\<close> True
        apply (simp add: gamma'_le_gamma_iff divide_simps distrib_left)
        by (smt (verit, best) less_imp_of_nat_less mult_right_mono distrib_left of_nat_0_le_iff)

      define PM where "PM \<equiv> \<Prod>i<m. (l - real i) / (k + l - real i)"
      have prod_gt0: "PM > 0"
        unfolding PM_def using \<open>m<l\<close> by (intro prod_pos) auto

      have inj: "inj_on (\<lambda>i. i-m) {m..<l}"
        by (auto simp: inj_on_def)
      have "(\<Prod>i<l. real (k + l - i) / real (l - i)) / (\<Prod>i<m. real (k + l - i) / real (l - i))
          = (\<Prod>i = m..<l. real (k + l - i) / real (l - i))"
        using prod_divide_nat_ivl [of 0 m l "\<lambda>i. real (k+l-i) / real (l-i)"] \<open>0<m\<close> \<open>m < l\<close>
        by (simp add: atLeast0LessThan)
      also have "... = (\<Prod>i<l - m. (k + l - m - i) / (l - m - i))"
        apply (rule prod.reindex_cong [OF inj, symmetric])
        by (auto simp add: image_minus_const_atLeastLessThan_nat)
      finally
      have "(\<Prod>i<l - m. (k + l - m - i) / (l - m - i)) 
          = (\<Prod>i<l. real (k + l - i) / real (l - i)) / (\<Prod>i<m. real (k + l - i) / real (l - i))" 
        by linarith
      also have "... = (k+l choose l) * inverse (\<Prod>i<m. real (k + l - i) / real (l - i))"
        by (simp add: field_simps atLeast0LessThan binomial_altdef_of_nat) 
      also have "... = (k+l choose l) * PM"
        unfolding PM_def using \<open>m>0\<close> \<open>m < l\<close> kn0
        by (simp add: atLeast0LessThan of_nat_diff flip: prod_inversef)
      finally have "(\<Prod>i<l-m. (k + l - m - i) / (l - m - i)) = (k+l choose l) * PM" .
      then have DD: "real(k+l choose l) = (\<Prod>i<l-m. (k + l - (m+i)) / (l - (m+i))) / PM"
        using prod_gt0 by (simp add: field_simps)

      have "ln (1 + \<xi>) * 20 \<ge> 1"
        unfolding \<xi>_def by (approximation 10)
      with YKK have \<section>: "m * ln (1+\<xi>) \<ge> \<delta> * k"
        unfolding \<delta>_def using zero_le_one mult_mono by fastforce
      have powerm: "(1+\<xi>)^m \<ge> exp (\<delta> * k)"
        using exp_mono [OF \<section>]
        by (smt (verit) \<eta>_def \<open>0 < \<eta>\<close> \<open>0 < \<gamma>'\<close> exp_ln_iff exp_of_nat_mult zero_le_mult_iff)
      have "nV * (1+\<xi>)^m \<ge> (k+l choose l)"
        using mult_mono [OF less_imp_le [OF nV_gt] powerm]
        by (simp add: exp_minus field_simps)
      then have "nV * (1+\<xi>)^m * PM \<ge> (\<Prod>i<l-m. (k + l - (m+i)) / (l - (m+i)))"
        using \<open>m<l\<close> prod_gt0 by (force simp add: DD divide_simps split: if_split_asm)
      then have "nV * U_lower_bound_ratio m \<ge> (k+l-m choose (l-m))"
        by (simp add: PM_def U_lower_bound_ratio_def binomial_altdef_of_nat atLeast0LessThan)

      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
    have "False"
    sorry
  }
  then show ?thesis
    sorry
qed

end
