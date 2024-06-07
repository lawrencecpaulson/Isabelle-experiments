section \<open>From diagonal to off-diagonal\<close>

theory From_Diagonal
  imports Closer_To_Diagonal

begin

lemma "\<forall>\<^sup>\<infinity>k. 1/4 \<le> 1/2 - 3 * eps k"
  unfolding eps_def by real_asymp

(* this will need to cover a closed interval, as usual; do I need a single k?*)
lemma 
  assumes "0<\<mu>0" "\<mu>0 \<le> \<mu>" "\<mu> \<le> \<mu>1" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>k. 2 / (1-\<mu>) * real k powr (-1/40) < 1"
  using assms by real_asymp


context Book
begin

lemma (in Book) From_11_2:
  fixes k
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours k k"  
  assumes big71: "Big_X_7_1 \<mu> k" and big62: "Big_Y_6_2 \<mu> k" and big86: "Big_ZZ_8_6 \<mu> k" and big\<mu>: "1 \<le> \<mu>^2 * real k"
   and big_le1: "2 / (1-\<mu>) * real k powr (-1/40) < 1"
  defines "X \<equiv> Xseq \<mu> k k" and "\<D> \<equiv> Step_class \<mu> k k {dreg_step}"
  defines "\<R> \<equiv> Step_class \<mu> k k {red_step}" and "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  defines "t \<equiv> card \<R>" and "s \<equiv> card \<S>"
  defines "m \<equiv> halted_point \<mu> k k"
  assumes X0ge: "real (card X0) \<ge> real nV / 2" and "p0 \<ge> 1/2"
  obtains f::"nat\<Rightarrow>real" where "f \<in> o(real)"
                 "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (\<mu> * real(s+t) / s) + f(k)"
proof -
  have big41: "Big_Blue_4_1 \<mu> k"
    using Big_X_7_1_def big71 by presburger
  have big\<mu>1: "1 \<le> \<mu> * real k"
    using big\<mu> \<mu>
    by (smt (verit, best) mult_less_cancel_right2 mult_right_mono of_nat_less_0_iff power2_eq_square)
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
  have "s < k"
    unfolding \<S>_def \<mu> s_def
    using \<open>Colours k k\<close> bblue_dboost_step_limit big41 \<mu>  
    by (meson le_add2 le_less_trans)

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
  have ok_less1: "a * real k powr (-1/40) < 1"
    unfolding a_def using big_le1 by blast
  consider "s < k powr (39/40)" | "s \<ge> k powr (39/40)" "bigbeta \<mu> k k \<ge> (1 - a * k powr (-1/40)) * (s / (s + t))"
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
    finally have \<dagger>: "(\<mu> / bigbeta \<mu> k k) ^ s \<le> 2 powr h k" .
    have \<ddagger>: "nV \<le> 2 powr (1 - ok_fun_71 \<mu> k + g k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t * 2 powr h k"
      using 59 mult_left_mono [OF \<dagger>, of "2 powr (1 - ok_fun_71 \<mu> k + g k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t"]
      by (smt (verit) \<mu> pos_prod_le powr_nonneg_iff zero_less_divide_iff zero_less_power)
    have *: "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + (1 - ok_fun_71 \<mu> k + g k + h k)"
      using \<mu> gorder_ge2 by (simp add: log_mult log_nat_power order.trans [OF Transcendental.log_mono [OF _ _ \<ddagger>]])

    define sl where "sl \<equiv> \<lambda>k. \<bar>k powr (39/40) * (log 2 \<mu> + log 2 k)\<bar>"
    have sl: "sl \<in> o(real)"
      unfolding sl_def by real_asymp
    have le_sl: "\<bar>s * log 2 (\<mu> * real(s+t) / s)\<bar> \<le> sl k"
    proof (cases "s>0")
      case True
      with \<open>s>0\<close> have \<mu>eq: "\<mu> * (s + real t) / s = \<mu> * (1 + t/s)"
        by (auto simp: distrib_left)
      have lek: "1 + t/s \<le> k" (* used only once, so move down?*)
      proof -
        have "real t \<le> real t * real s"
          using True mult_le_cancel_left1 by fastforce
        then have "1 + t/s \<le> 1 + t"
          by (simp add: True pos_divide_le_eq)
        also have "... \<le> k"
          using \<open>t < k\<close> by linarith
        finally show ?thesis .
      qed
      show ?thesis 
      proof (cases "log 2 (\<mu> * real(s+t) / s) \<le> 0")
        case True
        have "s * (- log 2 (\<mu> * (1 + t/s))) \<le> real k powr (39/40) * (log 2 \<mu> + log 2 (real k))"
        proof (intro mult_mono)
          show "s \<le> k powr (39 / 40)"
            using "1" by linarith
        next
          have "inverse (\<mu> * (1 + t/s)) \<le> inverse \<mu>"
            using \<mu> inverse_le_1_iff by fastforce
          also have "\<dots> \<le> \<mu> * k"
            using big\<mu> \<mu> by (metis neq_iff mult.assoc mult_le_cancel_left_pos power2_eq_square right_inverse)
          finally have "inverse (\<mu> * (1 + t/s)) \<le> \<mu> * k" .
          moreover have "0 < \<mu> * (1 + real t / real s)"
            using \<mu> \<open>0 < s\<close> by (simp add: zero_less_mult_iff add_num_frac)
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
          have "0 < 1 + t/s"
            by (smt (verit) divide_nonneg_nonneg of_nat_0_le_iff)
          then show ?thesis
            using \<mu> lek by (intro mult_left_mono add_mono Transcendental.log_mono) auto
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
    then have "s > 0"
      using \<open>0 < k\<close> powr_gt_zero by fastforce
    define h where "h \<equiv> \<lambda>k. real k * log 2 (1 - a * k powr (-1/40))"
    have h: "h \<in> o(real)"
      using \<mu> unfolding a_def h_def by real_asymp

    have "s * log 2 (\<mu> / bigbeta \<mu> k k) = s * log 2 \<mu> - s * log 2 (bigbeta \<mu> k k)"
      using \<mu> bb_gt0 2 by (simp add: log_divide algebra_simps)
    also have "... \<le> s * log 2 \<mu> - s * log 2 ((1 - a * k powr (-1/40)) * (s / (s + t)))"
      using 2 \<open>s>0\<close> ok_less1 by (intro diff_mono order_refl mult_left_mono Transcendental.log_mono) auto
    also have "... = s * log 2 \<mu> - s * (log 2 (1 - a * k powr (-1/40)) + log 2 (s / (s + t)))"
      using \<open>0 < s\<close> a_def add_log_eq_powr big_le1 by auto
    also have "... = s * log 2 (\<mu> * (real(s+t) / s)) - s * log 2 (1 - a * k powr (-1/40))"
      using \<mu> \<open>s>0\<close> by (simp add: log_divide log_mult ring_distribs flip: times_divide_eq_right)
    also have "... < s * log 2 (\<mu> * (real(s+t) / s)) - h k"
    proof -
      have "log 2 (1 - a * real k powr (-1/40)) < 0"
        using \<mu> \<open>0 < k\<close> a_def ok_less1 by auto
      with \<open>s<k\<close> show ?thesis
        by (simp add: h_def)
    qed
    finally have \<dagger>: "s * log 2 (\<mu> / bigbeta \<mu> k k) < s * log 2 (\<mu> * (real(s+t) / s)) - h k" .
    show ?thesis
    proof
      let ?f = "\<lambda>k. 1 - ok_fun_71 \<mu> k + g k - h k"
      show "?f \<in> o(real)"
        using g h \<mu> by (simp add: const_smallo_real ok_fun_71 sum_in_smallo)
      have *: "log 2 nV \<le> s * log 2 (\<mu> / bigbeta \<mu> k k) + k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + (1 - ok_fun_71 \<mu> k + g k)"
        using \<mu> gorder_ge2 
        by (simp add: bb_gt0 log_mult log_nat_power order.trans [OF Transcendental.log_mono [OF _ _ 59]])
      with \<dagger> show "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (\<mu> * real(s+t) / s) + ?f k"
        by simp
    qed
  qed
qed


end (*context P0_min*)

end
