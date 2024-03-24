section \<open>An exponential improvement far from the diagonal\<close>

theory Far_From_Diagonal 
  imports Zigzag "Stirling_Formula.Stirling_Formula"

begin

lemma smallo_multiples:
  assumes f: "f \<in> o(real)" and "k>0"
  shows "(\<lambda>n. f (k * n)) \<in> o(real)"
proof (clarsimp simp: smallo_def)
  fix c::real
  assume "c>0"
  then have "c/k > 0"
    by (simp add: assms)
  with assms have "\<forall>\<^sup>\<infinity>n. \<bar>f n\<bar> \<le> c/k * real n"
    by (force simp: smallo_def del: divide_const_simps)
  then obtain N where "\<And>n. n\<ge>N \<Longrightarrow> \<bar>f n\<bar> \<le> c/k * real n"
    by (meson eventually_at_top_linorder)
  then have "\<And>m. (k*m)\<ge>N \<Longrightarrow> \<bar>f (k*m)\<bar> \<le> c/k * real (k*m)"
    by blast
  with \<open>k>0\<close> have "\<forall>\<^sup>\<infinity>m. \<bar>f (k*m)\<bar> \<le> c/k * real (k*m)"
    by (smt (verit, del_insts) One_nat_def Suc_leI eventually_at_top_linorderI mult_1_left mult_le_mono)
  then show "\<forall>\<^sup>\<infinity>n. \<bar>f (k * n)\<bar> \<le> c * real n"
    by eventually_elim (use \<open>k>0\<close> in auto)
qed

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

end (*context Book*)

end
