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
  assumes big71: "Big_X_7_1 \<mu> k" and big62: "Big_Y_6_2 \<mu> k" and big86: "Big_ZZ_8_6 \<mu> k" and big\<mu>: "1 \<le> \<mu> * (real k)\<^sup>2"
  defines "X \<equiv> Xseq \<mu> k k" and "\<D> \<equiv> Step_class \<mu> k k {dreg_step}"
  defines "\<R> \<equiv> Step_class \<mu> k k {red_step}" and "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  defines "t \<equiv> card \<R>" and "s \<equiv> card \<S>"
  defines "m \<equiv> halted_point \<mu> k k"
  assumes X0ge: "real (card X0) \<ge> real nV / 2" and "p0 \<ge> 1/2"
  obtains f::"nat\<Rightarrow>real" where "f \<in> o(real)"
                 "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (\<mu> * real(s+t) / s) + f(k)"
proof -
  define g where "g \<equiv> \<lambda>k. ((nat \<lceil>real k powr (3/4)\<rceil>) * log 2 k)"
  have g: "g \<in> o(real)"
    unfolding g_def by real_asymp
  have "k>0"
    using Colours_kn0 \<open>Colours k k\<close> by auto
  have big53: "Big_Red_5_3 \<mu> k"
    using Big_Y_6_2_def assms(5) by presburger
  then have bb_gt0: "bigbeta \<mu> k k > 0"
    using \<mu> \<open>Colours k k\<close> bigbeta_gt0 by blast

  have k34: "k powr (3/4) \<le> k powr 1"
    using \<open>k>0\<close> by (intro powr_mono) auto

  have "2 powr (ok_fun_71 \<mu> k - 1) * \<mu>^k * (1-\<mu>) ^ t * (bigbeta \<mu> k k / \<mu>) ^ s * nV
      \<le> 2 powr ok_fun_71 \<mu> k * \<mu>^k * (1-\<mu>) ^ t * (bigbeta \<mu> k k / \<mu>) ^ s * card X0"
    using X0ge \<mu> by (simp add: powr_diff mult.assoc bigbeta_ge0 mult_left_mono)
  also have "... \<le> card (X m)"
    using X_7_1 assms by blast
  also have "... \<le> 2 powr (g k)"
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
  then have 59: "nV \<le> 2 powr (1 - ok_fun_71 \<mu> k + g k) * inverse \<mu> ^ k * inverse(1-\<mu>) ^ t * (\<mu> / bigbeta \<mu> k k) ^ s"
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

    have DD: "(\<mu> / bigbeta \<mu> k k) ^ s \<ge> 0"
      using \<mu> bb_gt0 by fastforce

    have \<beta>: "bigbeta \<mu> k k \<ge> 1 / (real k)\<^sup>2"
      using \<open>Colours k k\<close> \<mu> big53 bigbeta_ge_square by blast
    then have "(\<mu> / bigbeta \<mu> k k) ^ s \<le> (\<mu> * (real k)\<^sup>2) ^ s"
      using bb_gt0 \<open>k>0\<close> \<mu> by (intro power_mono) (auto simp add: divide_simps mult.commute)
    also have "... \<le> (\<mu> * (real k)\<^sup>2) powr (k powr (39/40))"
      using \<mu> big\<mu> 1 by (smt (verit) powr_less_mono powr_one_eq_one powr_realpow)
    also have "... = 2 powr (log 2 ((\<mu> * (real k)\<^sup>2) powr (k powr (39/40))))"
      by (smt (verit, best) big\<mu> powr_gt_zero powr_log_cancel)
    also have "... = 2 powr h k"
      using \<mu> big\<mu> \<open>k>0\<close> by (simp add: log_powr log_nat_power log_mult h_def)
    finally have \<section>: "(\<mu> / bigbeta \<mu> k k) ^ s \<le> 2 powr h k" .
    have *: "nV \<le> 2 powr (1 - ok_fun_71 \<mu> k + g k) * inverse \<mu> ^ k * inverse(1-\<mu>) ^ t * 2 powr h k"
      using 59 mult_left_mono [OF \<section>, of "2 powr (1 - ok_fun_71 \<mu> k + g k) * inverse \<mu> ^ k * inverse(1-\<mu>) ^ t"]
      apply (simp add: mult_ac)
      by (smt (verit) \<mu> plus_inverse_ge_2 pos_prod_lt powr_ge_pzero zero_less_power)
    show ?thesis
    proof
      let ?f = "\<lambda>k. 1 - ok_fun_71 \<mu> k + g k + h k"
      show "?f \<in> o(real)"
        using g h \<mu> by (simp add: const_smallo_real ok_fun_71 sum_in_smallo)
      show "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (\<mu> * real(s+t) / s) + ?f(k)"
        using * apply (simp add: powr_add powr_diff mult_ac)
        sorry
    qed
  next
    case 2
    then show ?thesis sorry
  qed
qed


end (*context P0_min*)

end
