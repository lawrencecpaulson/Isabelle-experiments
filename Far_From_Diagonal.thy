section \<open>An exponential improvement far from the diagonal\<close>

theory Far_From_Diagonal 
  imports Zigzag "Stirling_Formula.Stirling_Formula"

begin



subsection \<open>Fact D.3 from the Appendix\<close>

text \<open>And hence, Fact 9.4\<close>

definition "stir \<equiv> \<lambda>n. fact n / (sqrt (2 * pi * n) * (n / exp 1) ^ n) - 1"

text \<open>Generalised to the reals to allow derivatives\<close>
definition "stirG \<equiv> \<lambda>n. Gamma (n+1) / (sqrt (2 * pi * n) * (n / exp 1) powr n) - 1"

lemma stir_eq_stirG: "n>0 \<Longrightarrow> stir n = stirG (real n)"
  by (simp add: stirG_def stir_def add.commute powr_realpow Gamma_fact)

lemma stir_ge0: "n>0 \<Longrightarrow> stir n \<ge> 0"
  using fact_bounds[of n] by (simp add: stir_def)

lemma stir_to_0: "stir \<longlonglongrightarrow> 0"
  using fact_asymp_equiv by (simp add: asymp_equiv_def stir_def LIM_zero)

lemma stir_o1: "stir \<in> o(1)"
  using stir_to_0 tendsto_zero_imp_o1 by presburger

lemma fact_eq_stir_times: "n \<noteq> 0 \<Longrightarrow> fact n = (1 + stir n) * (sqrt (2 * pi * n) * (n / exp 1) ^ n)"
  by (simp add: stir_def)

definition "logstir \<equiv> \<lambda>n. if n=0 then 0 else log 2 ((1 + stir n) * sqrt (2 * pi * n))"

lemma logstir_o_real: "logstir \<in> o(real)"
proof -
  have "\<forall>\<^sup>\<infinity>n. 0 < n \<longrightarrow> \<bar>log 2 ((1 + stir n) * sqrt (2 * pi * n))\<bar> \<le> c * real n" if "c>0" for c
  proof -
    have "\<forall>\<^sup>\<infinity>n. 2 powr (c*n) / sqrt (2 * pi * n) \<ge> c+1"
      using that by real_asymp
    moreover have "\<forall>\<^sup>\<infinity>n. \<bar>stir n\<bar> \<le> c"
      using stir_o1 that by (auto simp: smallo_def)
    ultimately have "\<forall>\<^sup>\<infinity>n. ((1 + stir n) * sqrt (2 * pi * n)) \<le> 2 powr (c * n)"
      apply eventually_elim
      apply (simp add: divide_simps mult_less_0_iff split: if_split_asm)
      by (smt (verit, best) mult_mono real_sqrt_ge_zero zero_le_mult_iff)
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
  defines "\<gamma> \<equiv> real l / (real k + real l)"
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
      apply (simp add: field_simps)
      by (metis (no_types, lifting) binomial_absorb_comp diff_Suc_eq_diff_pred diff_add_inverse2 diff_commute of_nat_mult)
  qed auto
  also have "... = (real k / (k+l))^t * (\<Prod>i<t. 1 - real i * real l / (real k * (k+l-i)))"
  proof -
    have "1 - real i * real l / (real k * (k+l-i)) = ((k-i)/(k+l-i)) * ((k+l) / k)" if "i<t" for i
      using that \<open>t \<le> k\<close> by (simp add: divide_simps of_nat_diff) argo
    then have *: "(\<Prod>i<t. 1 - real i * real l / (real k * (k+l-i))) = (\<Prod>i<t. ((k-i)/(k+l-i)) * ((k+l) / k))"
      by auto
    show ?thesis
      unfolding * prod.distrib by (simp add: power_divide)
  qed
  also have "... \<le> (real k / (k+l))^t * exp (- (\<Sum>i<t. real i * real l / (real k * (k+l))))"
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
    also have "... = (\<Sum>i<t. i * \<gamma> / k)" 
      unfolding g [symmetric] by (simp add: sum_distrib_right sum_divide_distrib)
    finally show ?thesis .
  qed
  have 0: "0 \<le> real (k + l choose l)"
    by simp
  have *: "(k+l-t choose l) \<le> (real k / (k+l))^t * exp (- (\<Sum>i<t. i * \<gamma> / k)) * (k+l choose l)"
    using order_trans [OF _  mult_right_mono [OF 1 0]]
    by (simp add: less_eq_real_def)
  also have "... \<le>  (k / (k+l))^t * exp (- \<gamma> * (t-1)^2 / (2*k)) *(k+l choose l)"
    using ** by (intro mult_mono) auto
  also have "... \<le> exp (- \<gamma> * (t-1)^2 / (2 * real k)) * (k / (k+l))^t * (k+l choose l)"
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
    apply (simp add: of_nat_diff pos_divide_le_eq algebra_simps)
    apply (simp add: algebra_simps eval_nat_numeral)
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

context Book
begin

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

definition "Big_Far_9_3 \<equiv>     
   \<lambda>\<mu> l. Big_ZZ_8_5 \<mu> l \<and> Big_X_7_1 \<mu> l \<and> Big_Y_6_2 \<mu> l \<and> Big_Red_5_3 \<mu> l
      \<and> (\<forall>k\<ge>l. p0 - 3 * eps k > 1/k \<and> k\<ge>2
             \<and> \<bar>ok_fun_93h \<mu> k / (\<mu> * (1 + 1 / (exp 1 * (1 - \<mu>))))\<bar> / k \<le> 0.667 - 2/3)"


lemma Big_Far_9_3:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_Far_9_3 \<mu> l"
proof -
  define d where "d \<equiv> \<mu> * (1 + 1 / (exp 1 * (1 - \<mu>)))"
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
  with p0_01 show ?thesis
    unfolding Big_Far_9_3_def eventually_conj_iff all_imp_conj_distrib eps_def d_def e_def
    apply (simp add: Big_ZZ_8_5 Big_X_7_1 Big_Y_6_2 Big_Red_5_3 assms)
    apply (intro conjI eventually_all_ge_at_top; real_asymp)
    done
qed

lemma Far_9_3:
  fixes l k
  assumes "Colours l k"  \<comment> \<open>Not mentioned in paper but presumably needed\<close>
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  defines "\<delta> \<equiv> min (1/200) (\<gamma>/20)"
  defines "\<R> \<equiv> Step_class \<gamma> l k {red_step}"
  defines "t \<equiv> card \<R>"
  assumes \<gamma>15: "\<gamma> \<le> 1/5" and p0: "p0 \<ge> 1/4" and nge: "n \<ge> exp (-\<delta>*k) * (k+l choose l)"
    and X0ge: "card X0 \<ge> n/2"
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
    show "exp (- \<delta> * real k) * real (k + l choose l) / 2 \<le> real (card X0)"
      using X0ge nge by force
    show "0 \<le> 2 powr ok_fun_71 \<gamma> k * \<gamma> ^ l * (1-\<gamma>) ^ t * (\<beta>/\<gamma>) ^ card \<S>"
      using \<gamma>01 bigbeta_ge0 by (force simp: \<beta>_def)
  qed
  also have "\<dots> \<le> card (Xseq \<gamma> l k m)"
    unfolding \<R>_def \<S>_def m_def t_def \<beta>_def
    using \<gamma>01 X_7_1 \<open>Colours l k\<close> big by (intro X_7_1) (auto simp: Big_Far_9_3_def)
  also have "\<dots> \<le> RN k l34"
  proof -
    have "p0 - 3 * eps k > 1/k" and "pee \<gamma> l k m \<ge> p0 - 3 * eps k"
      using lk big \<open>Colours l k\<close> by (auto simp: Big_Far_9_3_def Y_6_2_halted \<gamma>_def m_def)
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

  have "card \<S> \<le> \<beta> * t / (1 - \<beta>) + (2 / (1-\<gamma>)) * k powr (19/20)" 
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
      using mult_right_mono [OF X, of "2 * k powr (19 / 20) / (1 - \<gamma>)"] \<open>\<gamma><1\<close>
      by (simp add: ok_fun_93h_def algebra_simps)
  qed
  also have "\<dots> \<le> ((\<gamma> / exp 1) * t / (1-\<gamma>)) + \<delta>*k + ok_fun_93h \<gamma> k"
    using \<gamma>01 mult_right_mono [OF \<phi>, of t] by (simp add: \<phi>_def mult_ac)
  finally have "\<gamma> * (real k - t) \<le> ((\<gamma> / exp 1) * t / (1-\<gamma>)) + \<delta>*k + ok_fun_93h \<gamma> k" .
  then have "(\<gamma>-\<delta>) * k - ok_fun_93h \<gamma> k \<le> t * \<gamma> * c \<gamma>"
    by (simp add: c_def algebra_simps)
  then have "((\<gamma>-\<delta>) * k - ok_fun_93h \<gamma> k) / (\<gamma> * c \<gamma>) \<le> t"
    using \<gamma>01 cgt0 by (simp add: pos_divide_le_eq)
  then have *: "t \<ge> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) * k - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>)"  
    using \<gamma>01 cgt0[of \<gamma>] by (simp add: field_simps)

  define f47 where "f47 \<equiv> \<lambda>x. (1 - 1/(200*x)) * inverse (c x)"
  have "concave_on {1/10..1/5} f47"
    unfolding f47_def
  proof (intro concave_on_mul)
    show "concave_on {1 / 10..1 / 5} (\<lambda>x. 1 - 1/(200*x))"
    proof (intro f''_le0_imp_concave)
      fix x::real
      assume "x \<in> {1 / 10..1 / 5}"
      then have x01: "0<x" "x<1"
        by auto
      show "((\<lambda>x. (1 - 1/(200*x))) has_real_derivative 1/(200*x^2)) (at x)"
        using x01 by (intro derivative_eq_intros | force simp: eval_nat_numeral)+
      show "((\<lambda>x. 1/(200*x^2)) has_real_derivative -1/(100*x^3)) (at x)"
        using x01 by (intro derivative_eq_intros | force simp: eval_nat_numeral)+
      show "-1/(100*x^3) \<le> 0"
        using x01 by (simp add: divide_simps)
    qed auto
    show "concave_on {1 / 10..1 / 5} (\<lambda>x. inverse (c x))"
    proof (intro f''_le0_imp_concave)
      fix x::real
      assume "x \<in> {1 / 10..1 / 5}"
      then have x01: "0<x" "x<1"
        by auto
      have swap: "u * (x-1) = (-u) * (1-x)" for u
        by (metis minus_diff_eq minus_mult_commute)
      have \<section>: "exp 1 * (x - 1) < 0"
        using x01
        by (meson exp_gt_zero less_iff_diff_less_0 mult_less_0_iff)
      then have non0: "1 + 1 / (exp 1 * (1 - x)) \<noteq> 0"
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
    show "mono_on {(1::real) / 10..1 / 5} (\<lambda>x. 1 - 1 / (200 * x))"
      by (auto simp: monotone_on_def frac_le)
    show "monotone_on {1 / 10..1 / 5} (\<le>) (\<lambda>x y. y \<le> x) (\<lambda>x. inverse (c x))"
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
    also have "\<dots> \<le> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>) / k"
      unfolding f48_def \<delta>\<gamma> using BIGH
      by (smt (verit, best) divide_nonneg_nonneg of_nat_0_le_iff zero_less_divide_iff)
    finally
    have A: "2/3 \<le> (1 - \<delta> / \<gamma>) * inverse (c \<gamma>) - ok_fun_93h \<gamma> k / (\<gamma> * c \<gamma>) / k" .
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

definition "ok_fun_95a \<equiv> \<lambda>\<mu> k. ok_fun_61 k - (1 + (2 / (1-\<mu>)) * k powr (19/20))"

definition "ok_fun_95b \<equiv> \<lambda>\<mu> k. ln 2 * ok_fun_95a \<mu> k - 1"

lemma ok_fun_95a: "ok_fun_95a \<mu> \<in> o(real)"
proof -
  have "(\<lambda>k. 1 + (2 / (1-\<mu>)) * k powr (19/20)) \<in> o(real)"
    by real_asymp
  then show ?thesis
    unfolding ok_fun_95a_def
    using ok_fun_61 sum_in_smallo by blast
qed

lemma ok_fun_95b: "ok_fun_95b \<mu> \<in> o(real)"
  using ok_fun_95a by (auto simp: ok_fun_95b_def sum_in_smallo const_smallo_real)

definition "Big_Far_9_5 \<equiv> \<lambda>\<mu> l. Big_Red_5_3 \<mu> l \<and> Big_Y_6_1 \<mu> l \<and> Big_ZZ_8_5 \<mu> l"

lemma Big_Far_9_5:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_Far_9_5 \<mu> l"
  unfolding Big_Far_9_5_def eventually_conj_iff all_imp_conj_distrib eps_def
  by (simp add: Big_Red_5_3 Big_Y_6_1 Big_ZZ_8_5 assms)

text \<open>Y0 is an additional assumption found Bhavik's version. (He had a couple of others)\<close>
lemma Far_9_5:
  fixes l k
  fixes \<delta> \<gamma> \<eta>::real
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  defines "\<R> \<equiv> Step_class \<gamma> l k {red_step}"
  defines "t \<equiv> card \<R>"
  defines "m \<equiv> halted_point \<gamma> l k"
  assumes "Colours l k" 
  assumes n: "real n \<ge> exp (-\<delta> * k) * (k+l choose l)" and Y0: "card Y0 \<ge> real n / 2"
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
  have 85: "s \<le> (\<beta> / (1 - \<beta>)) * t + (2 / (1-\<gamma>)) * k powr (19/20)"
    unfolding s_def t_def \<R>_def \<S>_def \<beta>_def using ZZ_8_5 \<gamma>01 \<open>Colours l k\<close> big85 by blast
  also have "... \<le> (\<gamma> / (1-\<gamma>)) * t + (2 / (1-\<gamma>)) * k powr (19/20)"
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

  have "(1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * n \<le> (1-\<gamma>-\<eta>) powr (t+s - (2 / (1-\<gamma>)) * k powr (19/20)) * (2 * card Y0)"
  proof (intro mult_mono)
    show "(1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) \<le> (1-\<gamma>-\<eta>) powr (t+s - (2 / (1-\<gamma>)) * k powr (19/20))"
      using D85 \<gamma>01 add_divide_distrib p0 \<open>\<eta>\<ge>0\<close> powr_mono' by fastforce
  qed (use Y0 in auto)
  also have "... \<le> (1-\<gamma>-\<eta>) powr (t+s) / (1-\<gamma>-\<eta>) powr ((2 / (1-\<gamma>)) * k powr (19/20)) * (2 * card Y0)"
    by (simp add: divide_powr_uminus powr_diff)
  also have "... \<le> (1-\<gamma>-\<eta>) powr (t+s) / (1/2) powr ((2 / (1-\<gamma>)) * k powr (19/20)) * (2 * card Y0)"
  proof (intro mult_mono divide_left_mono)
    show "(1/2) powr ((2 / (1-\<gamma>)) * k powr (19/20)) \<le> (1-\<gamma>-\<eta>) powr ((2 / (1-\<gamma>)) * k powr (19/20))"
      using \<gamma>01 p0 \<open>0\<le>\<eta>\<close> by (intro powr_mono_both') auto
  qed (use p0 in auto)
  also have "... \<le> p0 powr (t+s) / (1/2) powr ((2 / (1-\<gamma>)) * k powr (19/20)) * (2 * card Y0)"
    using p0 powr_mono2 by (intro mult_mono divide_right_mono) auto
  also have "... = (2 powr (1 + (2 / (1-\<gamma>)) * k powr (19/20))) * p0 ^ (t+s) * card Y0"
    using p0_01 by (simp add: powr_divide powr_add power_add powr_realpow)
  finally have "2 powr (ok_fun_95a \<gamma> k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * n \<le> 2 powr (ok_fun_61 k) * p0 ^ (t+s) * card Y0"
    by (simp add: ok_fun_95a_def powr_diff field_simps)
  with 61 have *: "card (Yseq \<gamma> l k m) \<ge> 2 powr (ok_fun_95a \<gamma> k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * n"
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
  also have "\<dots> \<le> 2 powr (ok_fun_95a \<gamma> k) * (1-\<gamma>-\<eta>) powr (t + \<gamma>*t / (1-\<gamma>)) * n"
    using n mult_left_mono by fastforce
  also have "\<dots> \<le> card (Yseq \<gamma> l k m)"
    by (rule *)
  finally show ?thesis .
qed

subsection \<open>Lemma 9.2\<close>

definition "red_graph_density \<equiv> card Red / card E"

lemma density_eq_average:
  "red_graph_density =
    real (\<Sum> x \<in> V. \<Sum> y \<in> V\<setminus>{x}. if {x,y} \<in> Red then 1 else 0) / (card V * (card V - 1))"
proof -
  have cardE: "card E = card V choose 2"
    using card_all_edges complete finV by blast
  have *: "(\<Sum>x\<in>V. \<Sum>y\<in>V \<setminus> {x}. if {x, y} \<in> Red then 1 else 0) = card Red * 2"
    using Red_E by (simp add: sum_eq_card_Neighbours Red_E sum_Neighbours_eq_card)
  show ?thesis
    by (auto simp add: red_graph_density_def divide_simps cardE choose_two_real *)
qed

lemma density_eq_average_partition:
  assumes k: "0 < k" "k < card V"
  shows "red_graph_density = (\<Sum>U \<in> nsets V k. red_density U (V\<setminus>U)) / (card V choose k)"
proof -
  have cardE: "card E = card V choose 2"
    using card_all_edges complete finV by blast

  have "(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card Red U (V\<setminus>U) / (real (card U) * card (V\<setminus>U)))
     = (\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card Red U (V\<setminus>U) / (real k * (card V - k)))"
    using card_Diff_subset by (intro sum.cong) (auto simp: nsets_def)
  also have "\<dots> = (\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card Red U (V\<setminus>U)) / (k * (card V - k))"
    by (simp add: sum_divide_distrib)
  finally have *: "(\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card Red U (V\<setminus>U) / (real (card U) * card (V\<setminus>U)))
              = (\<Sum>U\<in>[V]\<^bsup>k\<^esup>. edge_card Red U (V\<setminus>U)) / (k * (card V - k))" .


  have "nV choose k \<noteq> 0"
    using assms(2) by force
  with k show ?thesis
    apply (simp add: red_graph_density_def gen_density_def cardE * divide_simps)
    apply (simp add: *)

apply (simp add: cong: sum.cong)

    apply (auto simp: )





proof -

    sorry

definition "Big_Far_9_2 \<equiv> \<lambda>\<mu> l. Big_Far_9_3 \<mu> l"

text \<open>A little tricky for me to express since my "Colours" assumption includes the allowed 
    assumption that there are no cliques in the original graph (page 9). So it's a contrapositive\<close>
lemma Far_9_2:
  fixes l k
  fixes \<delta> \<gamma> \<eta>::real
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  defines "\<delta> \<equiv> \<gamma>/20"
  assumes "Colours l k" and "\<gamma> \<le> 1/10" and \<epsilon>: "0\<le>\<eta>" "\<eta> \<le> \<gamma>/15"
  assumes n: "real nV \<ge> exp (-\<delta> * k) * (k+l choose l)" 
  assumes big: "Big_Far_9_2 \<gamma> l"
  shows "\<not> red_graph_density \<ge> 1-\<gamma>-\<epsilon>" 
proof
  assume "red_graph_density \<ge> 1-\<gamma>-\<epsilon>"
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
    apply (rule Far_9_3)
         apply (rule assms)
    using assms(1) assms(4) apply linarith

    sorry
  have "t<k"
    unfolding t_def \<R>_def using \<gamma>01 \<open>Colours l k\<close> red_step_limit by blast

  have "RN (k-t) l \<le> (k-t+l choose l)"
    by (simp add: add.commute RN_commute RN_le_choose)
  also have "\<dots> \<le> card (Yseq \<gamma> l k m)"
    sorry
  finally
  show False
    sorry
qed

end (*context Book*)

end
