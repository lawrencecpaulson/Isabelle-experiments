section \<open>From diagonal to off-diagonal\<close>

theory From_Diagonal
  imports Closer_To_Diagonal

begin


lemma "\<forall>\<^sup>\<infinity>k. 1/4 \<le> 1/2 - 3 * eps k"
  unfolding eps_def by real_asymp

context Book
begin

lemma (in Book) From_11_2:
  fixes k
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours k k"  
  assumes big71: "Big_X_7_1 \<mu> k" and big62: "Big_Y_6_2 \<mu> k" and big86: "Big_ZZ_8_6 \<mu> k" and big\<mu>1: "1 \<le> \<mu> * real k"
  defines "X \<equiv> Xseq \<mu> k k" and "\<D> \<equiv> Step_class \<mu> k k {dreg_step}"
  defines "\<R> \<equiv> Step_class \<mu> k k {red_step}" and "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  defines "t \<equiv> card \<R>" and "s \<equiv> card \<S>"
  defines "m \<equiv> halted_point \<mu> k k"
  assumes X0ge: "real (card X0) \<ge> real nV / 2" and "p0 \<ge> 1/2"
  obtains f::"nat\<Rightarrow>real" where "f \<in> o(real)"
                 "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (\<mu> * real(s+t) / s) + f(k)"
proof -
  have big\<mu>2: "1 \<le> \<mu> * (real k)\<^sup>2"
    unfolding power2_eq_square by (smt (verit, ccfv_SIG) big\<mu>1 \<mu> mult_less_cancel_left1 mult_mono')
  define g where "g \<equiv> \<lambda>k. ((nat \<lceil>real k powr (3/4)\<rceil>) * log 2 k)"
  have g: "g \<in> o(real)"
    unfolding g_def by real_asymp
  have "k>0"
    using Colours_kn0 \<open>Colours k k\<close> by auto
  have big53: "Big_Red_5_3 \<mu> k"
    using Big_Y_6_2_def assms(5) by presburger
  then have bb_gt0: "bigbeta \<mu> k k > 0"
    using \<mu> \<open>Colours k k\<close> bigbeta_gt0 by blast
  have "t < k"
    by (simp add: \<R>_def \<mu> t_def \<open>Colours k k\<close> red_step_limit)

  have k34: "k powr (3/4) \<le> k powr 1"
    using \<open>k>0\<close> by (intro powr_mono) auto

  have "2 powr (ok_fun_71 \<mu> k - 1) * \<mu>^k * (1-\<mu>) ^ t * (bigbeta \<mu> k k / \<mu>) ^ s * nV
      \<le> 2 powr ok_fun_71 \<mu> k * \<mu>^k * (1-\<mu>) ^ t * (bigbeta \<mu> k k / \<mu>) ^ s * card X0"
    using X0ge \<mu> by (simp add: powr_diff mult.assoc bigbeta_ge0 mult_left_mono)
  also have "\<dots> \<le> card (X m)"
    using X_7_1 assms by blast
  also have "\<dots> \<le> 2 powr (g k)"
  proof -
    have "1/k < 1/4"
      sorry
    also have "\<dots> \<le> p0 - 3 * eps k"
      sorry
    also have "\<dots> \<le> pee \<mu> k k m"
      using Y_6_2_halted assms by blast
    finally have "pee \<mu> k k m > 1/k" .
    moreover have "termination_condition k k (X m) (Yseq \<mu> k k m)"
      unfolding m_def X_def
      using \<mu> \<open>Colours k k\<close> halted_point_halted step_terminating_iff by blast
    ultimately have "card (X m) \<le> RN k (nat \<lceil>real k powr (3/4)\<rceil>)"
      by (simp add: pee_def termination_condition_def X_def)
    then show ?thesis
      unfolding g_def by (meson RN34_le_2powr_ok \<open>0 < k\<close> of_nat_le_iff order.refl order.trans)
  qed
  finally have 58: "2 powr (g k) \<ge> 2 powr (ok_fun_71 \<mu> k - 1) * \<mu>^k * (1-\<mu>) ^ t * (bigbeta \<mu> k k / \<mu>) ^ s * nV" .
  then have 59: "nV \<le> 2 powr (1 - ok_fun_71 \<mu> k + g k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t * (\<mu> / bigbeta \<mu> k k) ^ s"
    using \<mu> bb_gt0 by (simp add: powr_diff powr_add mult.commute divide_simps) argo

  define a where "a \<equiv> 2 / (1-\<mu>)"
  consider "s < k powr (39/40)" | "bigbeta \<mu> k k \<ge> (1 - a * k powr (-1/40)) * (s / (s + t))"
    using ZZ_8_6 big86 \<open>Colours k k\<close> \<mu> a_def by (force simp: s_def t_def \<S>_def \<R>_def)
  then show ?thesis
  proof cases
    case 1
    define h where "h \<equiv> \<lambda>k. real k powr (39/40) * (log 2 \<mu> + 2 * log 2 (real k))"
    have h: "h \<in> o(real)"
      unfolding h_def by real_asymp

    have \<beta>: "bigbeta \<mu> k k \<ge> 1 / (real k)\<^sup>2"
      using \<open>Colours k k\<close> \<mu> big53 bigbeta_ge_square by blast
    then have "(\<mu> / bigbeta \<mu> k k) ^ s \<le> (\<mu> * (real k)\<^sup>2) ^ s"
      using bb_gt0 \<open>k>0\<close> \<mu> by (intro power_mono) (auto simp add: divide_simps mult.commute)
    also have "\<dots> \<le> (\<mu> * (real k)\<^sup>2) powr (k powr (39/40))"
      using \<mu> big\<mu>2 1 by (smt (verit) powr_less_mono powr_one_eq_one powr_realpow)
    also have "\<dots> = 2 powr (log 2 ((\<mu> * (real k)\<^sup>2) powr (k powr (39/40))))"
      by (smt (verit, best) big\<mu>2 powr_gt_zero powr_log_cancel)
    also have "\<dots> = 2 powr h k"
      using \<mu> big\<mu>2 \<open>k>0\<close> by (simp add: log_powr log_nat_power log_mult h_def)
    finally have \<section>: "(\<mu> / bigbeta \<mu> k k) ^ s \<le> 2 powr h k" .
    have \<section>: "nV \<le> 2 powr (1 - ok_fun_71 \<mu> k + g k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t * 2 powr h k"
      using 59 mult_left_mono [OF \<section>, of "2 powr (1 - ok_fun_71 \<mu> k + g k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t"]
      by (smt (verit) \<mu> pos_prod_le powr_nonneg_iff zero_less_divide_iff zero_less_power)
    have *: "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + (1 - ok_fun_71 \<mu> k + g k + h k)"
      using \<mu> gorder_ge2
      by (simp add: log_mult log_nat_power order.trans [OF Transcendental.log_mono [OF _ _ \<section>]])

    define sl where "sl \<equiv> \<lambda>k. \<bar>k powr (39/40) * (log 2 \<mu> + log 2 k)\<bar>"
    have sl: "sl \<in> o(real)"
      unfolding sl_def by real_asymp
    have le_sl: "\<bar>s * log 2 (\<mu> * real(s+t) / s)\<bar> \<le> sl k"
    proof (cases "s>0")
      case True
      with \<open>s>0\<close> have \<mu>eq: "\<mu> * (s + real t) / s = \<mu> * (1 + t/s)"
        by (auto simp: distrib_left)
      show ?thesis 
      proof (cases "log 2 (\<mu> * real(s+t) / s) \<le> 0")
        case True
        have "s * (- log 2 (\<mu> * (1 + t/s))) \<le> real k powr (39/40) * (log 2 \<mu> + log 2 (real k))"
        proof (intro mult_mono)
          show "s \<le> k powr (39 / 40)"
            using "1" by linarith
        next
          have "0 < \<mu> * (1 + real t / real s)"
            using \<mu> \<open>0 < s\<close> by (simp add: zero_less_mult_iff add_num_frac)
          moreover have "inverse (\<mu> * (1 + real t / real s)) \<le> \<mu> * k"
            sorry
          ultimately show "- log 2 (\<mu> * (1 + real t / real s)) \<le> log 2 \<mu> + log 2 (real k)"
            using \<mu> \<open>0 < k\<close> by (simp add: zero_less_mult_iff flip: log_inverse log_mult)
        qed (use True \<mu>eq in auto)
        with \<mu> \<open>s>0\<close> big\<mu>1 True show ?thesis
          by (simp add: \<mu>eq sl_def mult_le_0_iff)
      next
        case False
        then have "\<bar>s * log 2 (\<mu> * real (s+t) / s)\<bar> \<le> k powr (39/40) * log 2 (\<mu> * real (s+t) / s)"
          using "1" by auto
        also have "... = k powr (39/40) * (log 2 (\<mu> * (1 + t/s)))"
          by (simp add: \<mu>eq)
        also have "... = k powr (39/40) * (log 2 \<mu> + log 2 (1 + t/s))"
          using \<mu> by (smt (verit, best) divide_nonneg_nonneg log_mult of_nat_0_le_iff) 
        also have "... \<le> k powr (39/40) * (log 2 \<mu> + log 2 k)"
        proof -
          have \<dagger>: "0 < 1 + t/s"
            by (smt (verit) divide_nonneg_nonneg of_nat_0_le_iff)
          have "real t \<le> real t * real s"
            using True mult_le_cancel_left1 by fastforce
          then have "1 + t/s \<le> 1 + t"
            by (simp add: True pos_divide_le_eq)
          also have "... \<le> k"
            using \<open>t < k\<close> by linarith
          finally show ?thesis
            using \<mu> \<dagger> by (intro mult_left_mono add_mono Transcendental.log_mono) auto
        qed
        also have "... \<le> sl k"
          unfolding sl_def by linarith
        finally show ?thesis .
      qed 
    qed (auto simp: sl_def)
    show ?thesis
    proof
      let ?f = "\<lambda>k. 1 - ok_fun_71 \<mu> k + g k + h k + sl k"
      show "?f \<in> o(real)"
        using g h sl \<mu> by (simp add: const_smallo_real ok_fun_71 sum_in_smallo)
      show "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (\<mu> * real(s+t) / s) + ?f(k)"
        using le_sl by (intro order.trans [OF *]) auto
    qed
  next
    case 2
    then show ?thesis sorry
  qed
qed


end (*context P0_min*)

end
