section \<open>From diagonal to off-diagonal\<close>

theory From_Diagonal
  imports Closer_To_Diagonal

begin


lemma "\<forall>\<^sup>\<infinity>k. 1/4 \<le> 1/2 - 3 * eps k"
  unfolding eps_def by real_asymp

context Book
begin


lemma (in Book) DDG:
  fixes k
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours k k"  
  assumes big71: "Big_X_7_1 \<mu> k" and big62: "Big_Y_6_2 \<mu> k"
  defines "X \<equiv> Xseq \<mu> k k" and "\<D> \<equiv> Step_class \<mu> k k {dreg_step}"
  defines "\<R> \<equiv> Step_class \<mu> k k {red_step}" and "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  defines "t \<equiv> card \<R>" and "s \<equiv> card \<S>"
  defines "m \<equiv> halted_point \<mu> k k"
  assumes X0ge: "real (card X0) \<ge> nV/2" and "p0 \<ge> 1/2"
  shows "nV \<le> 2 ^ f k * inverse \<mu> ^ k * (1 / (1-\<mu>)) ^ t * (\<mu> / bigbeta \<mu> k k) ^ s"
proof -
  define g where "g \<equiv> \<lambda>k. ((nat \<lceil>real k powr (3/4)\<rceil>) * log 2 k)"
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
  then have "nV \<le> 2 powr (1 - ok_fun_71 \<mu> k + g k) * (1/\<mu>)^k * (1 / (1-\<mu>)) ^ t * (\<mu> / bigbeta \<mu> k k) ^ s"
    using \<mu> bb_gt0 by (simp add: powr_diff powr_add mult.commute divide_simps) argo

  moreover have "RN k k \<le> nV / card (X m)"
      sorry

lemma From_11_2:
  fixes k::nat and \<mu>::real
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours k k"
  defines "\<R> \<equiv> Step_class \<mu> k k {red_step}"
  defines "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  shows "log 2 (RN k k) \<le> k * log 2 (1 / (1-\<mu>)) + card \<R> * (1 / (1-\<mu>)) + card \<S> * (\<mu> * (card \<S> + card \<R>) / card \<S>) + f(k)"
proof -
  have "card X0 \<ge> nV / 2"

    sorry


end (*context P0_min*)

end
