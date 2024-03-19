section \<open>An exponential improvement far from the diagonal\<close>

theory Far_From_Diagonal 
  imports Zigzag "Stirling_Formula.Stirling_Formula"

begin

subsection \<open>An asymptotic form for binomial coefficients via Stirling's formula\<close>

text \<open>From Appendix D.3, page 56\<close>

lemma const_smallo_real: "(\<lambda>n. x) \<in> o(real)"
  by real_asymp

lemma o_real_shift:
  assumes "f \<in> o(real)"
  shows "(\<lambda>i. f(i+j)) \<in> o(real)"
  unfolding smallo_def
proof clarify
  fix c :: real
  assume "(0::real) < c"
  then have *: "\<forall>\<^sup>\<infinity>i. norm (f i) \<le> c/2 * norm i"
    using assms half_gt_zero landau_o.smallD by blast
  have "\<forall>\<^sup>\<infinity>i. norm (f (i + j)) \<le> c/2 * norm (i + j)"
    using eventually_all_ge_at_top [OF *]
    by (metis (mono_tags, lifting) eventually_sequentially le_add1)
  then have "\<forall>\<^sup>\<infinity>i. i\<ge>j \<longrightarrow> norm (f (i + j)) \<le> c * norm i"
    apply eventually_elim
    apply clarsimp
    by (smt (verit, best) \<open>0 < c\<close> mult_left_mono nat_distrib(2) of_nat_mono)
  then show "\<forall>\<^sup>\<infinity>i. norm (f (i + j)) \<le> c * norm i"
    using eventually_mp by fastforce
qed

lemma tendsto_zero_imp_o1:
  fixes a :: "nat \<Rightarrow> real"
  assumes "a \<longlonglongrightarrow> 0"
  shows "a \<in> o(1)"
proof -
  have "\<forall>\<^sup>\<infinity>n. \<bar>a n\<bar> \<le> c" if "c>0" for c
  proof -
    have "\<forall>\<^sup>\<infinity>n. \<bar>a n\<bar> < c"
      by (metis assms order_tendstoD(2) tendsto_rabs_zero_iff that)
    then show ?thesis
      by (meson eventually_sequentially less_eq_real_def)
  qed
  then show ?thesis
    by (auto simp: smallo_def)
qed

lemma tendsto_imp_o1:
  assumes "a \<longlonglongrightarrow> x"
  shows "(\<lambda>n. norm (a n - x)) \<in> o(1)"
  by (simp add: LIM_zero assms tendsto_zero_imp_o1 tendsto_norm_zero)

definition "stir \<equiv> \<lambda>n. fact n / (sqrt (2 * pi * n) * (n / exp 1) ^ n) - 1"

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

definition "ok_fun_94 \<equiv> \<lambda>l k. logstir (k+l) - (logstir k + logstir l)"

lemma ok_fun_94: 
  fixes l::nat shows "ok_fun_94 l \<in> o(real)"
proof -
  have "(\<lambda>k. logstir (k+l)) \<in> o(real)"
    using logstir_o_real o_real_shift by blast
  then show ?thesis
    unfolding ok_fun_94_def by (intro sum_in_smallo logstir_o_real const_smallo_real)
qed

lemma fact_9_4:
  assumes l: "0 < l" "l \<le> k"
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  shows "k+l choose l = 2 powr ok_fun_94 l k * \<gamma> powr (-l) * (1-\<gamma>) powr (-k)" 
proof -
  have "real (k+l choose l) = fact(k+l) / (fact k * fact l)"
    by (simp add: binomial_fact)
  also have "... = (2 powr (logstir (k+l)) / (2 powr (logstir k) * 2 powr (logstir l))) * (k+l) powr(k+l) / (k powr k * l powr l)"
    using l by (simp add: logfact_eq_stir_times powr_add divide_simps flip: powr_realpow)
  also have "... = (2 powr ok_fun_94 l k) * (k+l) powr(k+l) / (k powr k * l powr l)"
    by (simp add: ok_fun_94_def powr_add powr_diff)
  also have "... = 2 powr ok_fun_94 l k * \<gamma> powr (- real l) * (1-\<gamma>) powr (- real k)"
    by (simp add: \<gamma>_def powr_minus powr_add powr_divide divide_simps)
  finally show ?thesis .
qed

context Book
begin

definition "Big_Far_9_3 \<equiv>     
   \<lambda>\<mu> l. Big_ZZ_8_5 \<mu> l \<and> Big_X_7_1 \<mu> l \<and> Big_Y_6_2 \<mu> l \<and> Big_Red_5_3 \<mu> l
      \<and> (\<forall>k\<ge>l. p0 - 3 * eps k > 1/k \<and> k\<ge>2)"

lemma Big_Far_9_3:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_Far_9_3 \<mu> l"
  unfolding Big_Far_9_3_def eventually_conj_iff all_imp_conj_distrib eps_def
  apply (simp add: Big_ZZ_8_5 Big_X_7_1 Big_Y_6_2 Big_Red_5_3 assms)
  using p0_01
  apply (intro conjI eventually_all_ge_at_top; real_asymp)
  done

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
  have f: "k+l choose l = 2 powr ok_fun_94 l k * \<gamma> powr (- real l) * (1-\<gamma>) powr (- real k)" 
    unfolding \<gamma>_def using fact_9_4 lk by blast
  define g where "g \<equiv> \<lambda>k. (nat \<lceil>k powr (3/4)\<rceil>) * log 2 k - (ok_fun_X_7_1 \<gamma> l k + ok_fun_94 l k) + 1"
  have "g \<in> o(real)"
  proof -
    have "(\<lambda>k. (nat \<lceil>k powr (3/4)\<rceil>) * log 2 k) \<in> o(real)"
      by real_asymp
    then show ?thesis
      unfolding g_def
      by (intro ok_fun_X_7_1 [OF \<gamma>01] ok_fun_94 [of l] sum_in_smallo const_smallo_real)
  qed
  define h where "h \<equiv> \<lambda>k. (2 / (1-\<gamma>)) * k powr (19/20) * ln (\<gamma>/\<beta>) + g k * ln 2"
  have "h \<in> o(real)"
  proof -
    have "(\<lambda>k. (2 / (1-\<gamma>)) * k powr (19/20) * ln (\<gamma>/\<beta>)) \<in> o(real)"
      by real_asymp
    then show ?thesis
      unfolding h_def by (metis (mono_tags) \<open>g \<in> o(real)\<close> sum_in_smallo(1) cmult_in_smallo_iff')
  qed
  have \<section>: "x powr a * (x powr b * y) = x powr (a+b) * y" for x y a b::real
    by (simp add: powr_add)
  have "(2 powr ok_fun_X_7_1 \<gamma> l k * 2 powr ok_fun_94 l k) * (\<beta>/\<gamma>) ^ card \<S> * (exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) / 2)
      \<le> 2 powr ok_fun_X_7_1 \<gamma> l k * \<gamma>^l * (1-\<gamma>) ^ t * (\<beta>/\<gamma>) ^ card \<S> * (exp (-\<delta>*k) * (k+l choose l) / 2)"
    using \<gamma>01 by (simp add: f mult_ac \<section> t_def flip: powr_realpow)
  also have "\<dots> \<le> 2 powr ok_fun_X_7_1 \<gamma> l k * \<gamma>^l * (1-\<gamma>) ^ t * (\<beta>/\<gamma>) ^ card \<S> * card X0"
  proof (intro mult_left_mono order_refl)
    show "exp (- \<delta> * real k) * real (k + l choose l) / 2 \<le> real (card X0)"
      using X0ge nge by force
    show "0 \<le> 2 powr ok_fun_X_7_1 \<gamma> l k * \<gamma> ^ l * (1-\<gamma>) ^ t * (\<beta>/\<gamma>) ^ card \<S>"
      using \<gamma>01 bigbeta_ge0 by (force simp: \<beta>_def)
  qed
  also have "\<dots> \<le> card (Xseq \<gamma> l k m)"
    unfolding \<R>_def \<S>_def m_def t_def \<beta>_def
    using \<gamma>01 X_7_1 \<open>Colours l k\<close> big by (intro X_7_1) (auto simp: Big_Far_9_3_def)
  also have "... \<le> RN k l34"
  proof -
    have "p0 - 3 * eps k > 1/k" and "pee \<gamma> l k m \<ge> p0 - 3 * eps k"
      using lk big \<open>Colours l k\<close> by (auto simp: Big_Far_9_3_def Y_6_2_halted \<gamma>_def m_def)
    then show ?thesis
      using halted_point_halted \<open>Colours l k\<close> \<gamma>01
      by (fastforce simp add: step_terminating_iff termination_condition_def pee_def m_def l34_def)
  qed
  also have "... \<le> k powr (l34-1)"   \<comment> \<open>Bhavik's off-diagonal upper bound; can't use @{term "2^(k+l34)"}\<close>
    using lk \<open>l34>0\<close> RN_le_argpower' of_nat_mono by (simp add: powr_realpow)
  also have "... \<le> k powr l34"
    using \<open>k>0\<close> powr_mono by force
  also have "... \<le> 2 powr (l34 * log 2 k)"
    by (smt (verit, best) mult.commute \<open>k>0\<close> of_nat_0_less_iff powr_log_cancel powr_powr)
  also have "... \<le> 2 powr ((nat \<lceil>real k powr (3/4)\<rceil>) * log 2 k)"
    unfolding l34_def 
  proof (intro powr_mono powr_mono2 mult_mono ceiling_mono of_nat_mono nat_mono lk)
    show "0 \<le> real (nat \<lceil>k powr (3/4)\<rceil>)"
      by linarith
  qed (use lk in auto)
  finally have "2 powr (ok_fun_X_7_1 \<gamma> l k + ok_fun_94 l k) * (\<beta>/\<gamma>) ^ card \<S>
               * exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) / 2
              \<le> 2 powr ((nat \<lceil>real k powr (3/4)\<rceil>) * log 2 k)"
    by (simp add: powr_add)
  then have A: "exp (-\<delta>*k) * (1-\<gamma>) powr (- real k + t) * (\<beta>/\<gamma>) ^ card \<S>
             \<le> 2 powr g k"
    using \<gamma>01 \<open>k\<ge>2\<close> by (simp add: g_def field_simps powr_add powr_diff of_nat_diff flip: powr_realpow)

  let ?\<xi> = "\<beta> * t / (1-\<gamma>) + (2 / (1-\<gamma>)) * k powr (19/20)"
  have \<beta>_le: "\<beta> \<le> \<gamma>" and \<beta>_ge: "\<beta> \<ge> 1 / (real k)\<^sup>2"
    using \<beta>_def \<gamma>01 \<open>Colours l k\<close> big53 bigbeta_le bigbeta_ge_square by blast+

  have "card \<S> \<le> \<beta> * t / (1 - \<beta>) + (2 / (1-\<gamma>)) * k powr (19/20)" 
    using ZZ_8_5 [OF \<gamma>01 \<open>Colours l k\<close> big85] \<gamma>01 by (auto simp: \<R>_def \<S>_def t_def \<beta>_def)
  also have "... \<le> ?\<xi>" 
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
  also have "\<dots> \<le> ln (2 powr g k)"
    using A \<gamma>01 \<beta>01 by simp
  also have "... = g k * ln 2"
    by (auto simp: ln_powr)
  finally have "\<gamma> * (real k - t) - \<delta>*k - ?\<xi> * ln (\<gamma>/\<beta>) \<le> g k * ln 2" .
  then have "\<gamma> * (real k - t) \<le> ?\<xi> * ln (\<gamma>/\<beta>) + \<delta>*k + g k * ln 2"
    by simp
  also have "... \<le> (\<beta> * t / (1-\<gamma>)) * ln (\<gamma>/\<beta>) + \<delta>*k + h k"
  proof -
    have \<section>: "\<gamma>/\<beta> \<le> \<gamma> * (real k)\<^sup>2"
      using \<open>k>0\<close> \<beta>_le \<beta>_ge \<open>\<beta>>0\<close> by (simp add: field_simps)
    then show ?thesis
      by (simp add: algebra_simps h_def)
  qed
  finally have 46: "\<gamma> * (real k - t) \<le> (\<beta> * t / (1-\<gamma>)) * ln (\<gamma>/\<beta>) + \<delta>*k + h k" .

  show ?thesis
    sorry
qed

end (*context Book*)

end
