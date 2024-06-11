section \<open>From diagonal to off-diagonal\<close>

theory From_Diagonal
  imports Closer_To_Diagonal

begin

subsection \<open>Lemma 2.2\<close>

definition "Big_From_11_2 \<equiv>     
   \<lambda>\<mu> k. Big_ZZ_8_6 \<mu> k \<and> Big_X_7_1 \<mu> k \<and> Big_Y_6_2 \<mu> k \<and> Big_Red_5_3 \<mu> k \<and> Big_Blue_4_1 \<mu> k 
       \<and> 1 \<le> \<mu>^2 * real k \<and> 2 / (1-\<mu>) * real k powr (-1/40) < 1 \<and> 1/k < 1/2 - 3 * eps k"

lemma Big_From_11_2:
  assumes "0<\<mu>0" "\<mu>0 \<le> \<mu>1" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_From_11_2 \<mu> k"
proof -
  have A: "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> 1 \<le> \<mu>\<^sup>2 * k"
    using assms
    apply (intro eventually_all_geI0)
     apply real_asymp
    by (smt (verit, ccfv_SIG) mult_le_cancel_right of_nat_less_0_iff power_mono)
  have B: "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> 2 / (1-\<mu>) * k powr (-1/40) < 1"
  proof (intro eventually_all_geI1)
    show "\<forall>\<^sup>\<infinity>k. 2 / (1-\<mu>1) * k powr (-1/40) < 1"
      by real_asymp
  qed (use assms in auto)
  have C: "\<forall>\<^sup>\<infinity>k. 1/k < 1/2 - 3 * eps k"
    unfolding eps_def by real_asymp
  show ?thesis
    unfolding Big_From_11_2_def
    using assms Big_ZZ_8_6 Big_X_7_1 Big_Y_6_2 Big_Red_5_3 Big_Blue_4_1 A B C
    by (simp add: eventually_conj_iff all_imp_conj_distrib)  
qed

lemma (in Book) From_11_2:
  fixes k
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours k k"  
  assumes big: "Big_From_11_2 \<mu> k"
  defines "\<R> \<equiv> Step_class \<mu> k k {red_step}" and "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  defines "t \<equiv> card \<R>" and "s \<equiv> card \<S>"
  defines "m \<equiv> halted_point \<mu> k k"
  assumes 0: "card X0 \<ge> nV div 2" and "p0 \<ge> 1/2"
  obtains f::"nat\<Rightarrow>real" where "f \<in> o(real)"
                 "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (\<mu> * real(s+t) / s) + f(k)"
proof -
  have big71: "Big_X_7_1 \<mu> k" and big62: "Big_Y_6_2 \<mu> k" and big86: "Big_ZZ_8_6 \<mu> k" and big53: "Big_Red_5_3 \<mu> k"
    and big41: "Big_Blue_4_1 \<mu> k" and big\<mu>: "1 \<le> \<mu>^2 * real k"
    and big_le1: "2 / (1-\<mu>) * real k powr (-1/40) < 1"
    using big by (auto simp: Big_From_11_2_def)
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
  have bb_gt0: "bigbeta \<mu> k k > 0"
    using big53 \<mu> \<open>Colours k k\<close> bigbeta_gt0 by blast
  have "t < k"
    by (simp add: \<R>_def \<mu> t_def \<open>Colours k k\<close> red_step_limit)
  have "s < k"
    unfolding \<S>_def \<mu> s_def
    using \<open>Colours k k\<close> bblue_dboost_step_limit big41 \<mu>  
    by (meson le_add2 le_less_trans)

  have k34: "k powr (3/4) \<le> k powr 1"
    using \<open>k>0\<close> by (intro powr_mono) auto

  define g712 where "g712 \<equiv> \<lambda>k. 2 - ok_fun_71 \<mu> k + g k"
  have "nV \<le> 4 * card X0"
    using 0 card_XY0 by (auto simp: odd_iff_mod_2_eq_one)
  with \<mu> have "2 powr (ok_fun_71 \<mu> k - 2) * \<mu>^k * (1-\<mu>) ^ t * (bigbeta \<mu> k k / \<mu>) ^ s * nV
      \<le> 2 powr ok_fun_71 \<mu> k * \<mu>^k * (1-\<mu>) ^ t * (bigbeta \<mu> k k / \<mu>) ^ s * card X0"
    using \<mu> by (simp add: powr_diff mult.assoc bigbeta_ge0 mult_left_mono)
  also have "\<dots> \<le> card (Xseq \<mu> k k m)"
    using X_7_1 assms big71 by blast
  also have "\<dots> \<le> 2 powr (g k)"
  proof -
    have "1/k < p0 - 3 * eps k"
    using big \<open>p0 \<ge> 1/2\<close> by (auto simp: Big_From_11_2_def)
    also have "\<dots> \<le> pee \<mu> k k m"
      using Y_6_2_halted big62 assms by blast
    finally have "pee \<mu> k k m > 1/k" .
    moreover have "termination_condition k k (Xseq \<mu> k k m) (Yseq \<mu> k k m)"
      unfolding m_def 
      using \<mu> \<open>Colours k k\<close> halted_point_halted step_terminating_iff by blast
    ultimately have "card (Xseq \<mu> k k m) \<le> RN k (nat \<lceil>real k powr (3/4)\<rceil>)"
      by (simp add: pee_def termination_condition_def)
    then show ?thesis
      unfolding g_def by (meson RN34_le_2powr_ok \<open>0 < k\<close> of_nat_le_iff order.refl order.trans)
  qed
  finally have 58: "2 powr (g k) \<ge> 2 powr (ok_fun_71 \<mu> k - 2) * \<mu>^k * (1-\<mu>) ^ t * (bigbeta \<mu> k k / \<mu>) ^ s * nV" .
  then have 59: "nV \<le> 2 powr (g712 k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t * (\<mu> / bigbeta \<mu> k k) ^ s"
    using \<mu> bb_gt0 by (simp add: g712_def powr_diff powr_add mult.commute divide_simps) argo

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
    have \<ddagger>: "nV \<le> 2 powr (g712 k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t * 2 powr h k"
      using 59 mult_left_mono [OF \<dagger>, of "2 powr (g712 k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t"]
      by (smt (verit) \<mu> pos_prod_le powr_nonneg_iff zero_less_divide_iff zero_less_power)
    have *: "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + (g712 k + h k)"
      using \<mu> gorder_ge2 by (simp add: log_mult log_nat_power order.trans [OF Transcendental.log_mono [OF _ _ \<ddagger>]])

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
        have lek: "1 + t/s \<le> k"
        proof -
          have "real t \<le> real t * real s"
            using True mult_le_cancel_left1 by fastforce
          then have "1 + t/s \<le> 1 + t"
            by (simp add: True pos_divide_le_eq)
          also have "\<dots> \<le> k"
            using \<open>t < k\<close> by linarith
          finally show ?thesis .
        qed
        have "\<bar>s * log 2 (\<mu> * real (s+t) / s)\<bar> \<le> k powr (39/40) * log 2 (\<mu> * real (s+t) / s)"
          using False "1" by auto
        also have "\<dots> = k powr (39/40) * (log 2 (\<mu> * (1 + t/s)))"
          by (simp add: \<mu>eq)
        also have "\<dots> = k powr (39/40) * (log 2 \<mu> + log 2 (1 + t/s))"
          using \<mu> by (smt (verit, best) divide_nonneg_nonneg log_mult of_nat_0_le_iff) 
        also have "\<dots> \<le> k powr (39/40) * (log 2 \<mu> + log 2 k)"
          by (smt (verit, best) "1" Transcendental.log_mono divide_nonneg_nonneg lek 
              mult_le_cancel_left_pos of_nat_0_le_iff)
        also have "\<dots> \<le> sl k"
          unfolding sl_def by linarith
        finally show ?thesis .
      qed 
    qed (auto simp: sl_def)
    show ?thesis
    proof
      let ?f = "\<lambda>k. g712 k + h k + sl k"
      show "?f \<in> o(real)"
        using g h sl \<mu> by (simp add: g712_def const_smallo_real ok_fun_71 sum_in_smallo)
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
    also have "\<dots> \<le> s * log 2 \<mu> - s * log 2 ((1 - a * k powr (-1/40)) * (s / (s + t)))"
      using 2 \<open>s>0\<close> ok_less1 by (intro diff_mono order_refl mult_left_mono Transcendental.log_mono) auto
    also have "\<dots> = s * log 2 \<mu> - s * (log 2 (1 - a * k powr (-1/40)) + log 2 (s / (s + t)))"
      using \<open>0 < s\<close> a_def add_log_eq_powr big_le1 by auto
    also have "\<dots> = s * log 2 (\<mu> * (real(s+t) / s)) - s * log 2 (1 - a * k powr (-1/40))"
      using \<mu> \<open>s>0\<close> by (simp add: log_divide log_mult ring_distribs flip: times_divide_eq_right)
    also have "\<dots> < s * log 2 (\<mu> * (real(s+t) / s)) - h k"
    proof -
      have "log 2 (1 - a * real k powr (-1/40)) < 0"
        using \<mu> \<open>0 < k\<close> a_def ok_less1 by auto
      with \<open>s<k\<close> show ?thesis
        by (simp add: h_def)
    qed
    finally have \<dagger>: "s * log 2 (\<mu> / bigbeta \<mu> k k) < s * log 2 (\<mu> * (real(s+t) / s)) - h k" .
    show ?thesis
    proof
      let ?f = "\<lambda>k. g712 k - h k"
      show "?f \<in> o(real)"
        using g h \<mu> by (simp add: g712_def const_smallo_real ok_fun_71 sum_in_smallo)
      have "log 2 nV \<le> s * log 2 (\<mu> / bigbeta \<mu> k k) + k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + (g712 k)"
        using \<mu> gorder_ge2 
        by (simp add: bb_gt0 log_mult log_nat_power order.trans [OF Transcendental.log_mono [OF _ _ 59]])
      with \<dagger> show "log 2 nV \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (\<mu> * real(s+t) / s) + ?f k"
        by simp
    qed
  qed
qed

subsection \<open>Lemma 2.3\<close>

lemma (in Book) From_11_3:
  fixes k
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours k k"  
  assumes big: "Big_Y_6_1 \<mu> k"
  defines "\<R> \<equiv> Step_class \<mu> k k {red_step}" and "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  defines "t \<equiv> card \<R>" and "s \<equiv> card \<S>"
  defines "m \<equiv> halted_point \<mu> k k"
  assumes 0: "card Y0 \<ge> nV div 2" and "p0 \<ge> 1/2"
  shows "log 2 nV \<le> log 2 (RN k (k-t)) + s + t + 2 - ok_fun_61 k"
proof -
  define RS where "RS \<equiv> Step_class \<mu> k k {red_step,dboost_step}"
  have "RS = \<R> \<union> \<S>"
    using Step_class_insert \<R>_def \<S>_def RS_def by blast
  moreover obtain "finite \<R>" "finite \<S>"
    by (simp add: \<R>_def \<S>_def \<open>0<\<mu>\<close> \<open>Colours k k\<close>)
  moreover have "disjnt \<R> \<S>"
    using \<R>_def \<S>_def disjnt_Step_class by auto
  ultimately have card_RS: "card RS = t+s"
    by (simp add: t_def s_def card_Un_disjnt)
  have 4: "nV/4 \<le> card Y0"
    using 0 card_XY0 by (auto simp: odd_iff_mod_2_eq_one)
  have ge0: "0 \<le> 2 powr ok_fun_61 k * p0 ^ card RS"
    using p0_01 by fastforce
  have "2 powr (- real s - real t + ok_fun_61 k - 2) * nV = 2 powr (ok_fun_61 k - 2) * (1/2) ^ card RS * nV"
    by (simp add: powr_add powr_diff powr_minus power_add powr_realpow divide_simps card_RS)
  also have "\<dots> \<le> 2 powr (ok_fun_61 k - 2) * p0 ^ card RS * nV"
    using power_mono [OF \<open>p0 \<ge> 1/2\<close>] gorder_ge2 by auto
  also have "\<dots> \<le> 2 powr (ok_fun_61 k) * p0 ^ card RS * (nV/4)"
    by (simp add: divide_simps powr_diff split: if_split_asm)
  also have "... \<le> 2 powr (ok_fun_61 k) * p0 ^ card RS * card Y0"
    using   mult_left_mono [OF 4 ge0 ] by simp
  also have "... \<le> card (Yseq \<mu> k k m)"
    using Y_6_1 [OF \<mu> big \<open>Colours k k\<close>] by (simp add: m_def RS_def divide_simps split: if_split_asm)
  finally have "2 powr (- real s - real t + ok_fun_61 k - 2) * nV \<le> card (Yseq \<mu> k k m)" .
  moreover
  { assume "card (Yseq \<mu> k k m) \<ge> RN k (k-t)"
    then obtain K where K: "K \<subseteq> Yseq \<mu> k k m" and "size_clique (k-t) K Red \<or> size_clique k K Blue"
      by (metis RN_commute Red_Blue_RN Yseq_subset_V)
    then have KRed: "size_clique (k-t) K Red"
      by (meson Colours_def \<open>Colours k k\<close>)
    have "card (K \<union> Aseq \<mu> k k m) = k"
    proof (subst card_Un_disjnt)
      show "finite K" "finite (Aseq \<mu> k k m)"
        using K finite_Aseq finite_Yseq infinite_super by blast+
      show "disjnt K (Aseq \<mu> k k m)"
        using valid_state_seq[of \<mu> k k m] K disjnt_subset1
        by (auto simp: valid_state_def disjoint_state_def)
      have "card (Aseq \<mu> k k m) = t"
        using \<open>\<mu>>0\<close> \<open>Colours k k\<close> red_step_eq_Aseq \<R>_def t_def m_def by presburger
      then show "card K + card (Aseq \<mu> k k m) = k"
        using Aseq_less_k[OF \<open>Colours k k\<close>] nat_less_le KRed size_clique_def by force
    qed
    moreover have "clique (K \<union> Aseq \<mu> k k m) Red"
    proof -
      obtain "K \<subseteq> V" "Aseq \<mu> k k m \<subseteq> V"
        by (meson Aseq_subset_V KRed size_clique_def)
      moreover have "clique K Red"
        using KRed size_clique_def by blast
      moreover have "clique (Aseq \<mu> k k m) Red"
        by (meson A_Red_clique valid_state_seq)
      moreover have "all_edges_betw_un (Aseq \<mu> k k m) (Yseq \<mu> k k m) \<subseteq> Red"
        using valid_state_seq[of \<mu> k k m] K
        by (auto simp: valid_state_def RB_state_def all_edges_betw_un_Un2)
      then have "all_edges_betw_un K (Aseq \<mu> k k m) \<subseteq> Red"
        using K all_edges_betw_un_mono2 all_edges_betw_un_commute by blast
      ultimately show ?thesis
        by (simp add: local.clique_Un)
    qed
    ultimately have "size_clique k (K \<union> Aseq \<mu> k k m) Red"
      using KRed Aseq_subset_V by (auto simp: size_clique_def)
    with \<open>Colours k k\<close> have False
      by (simp add: Colours_def)
  } 
  ultimately have *: "2 powr (- real s - real t + ok_fun_61 k - 2) * nV < RN k (k-t)"
    by fastforce
  have "- real s - real t + ok_fun_61 k - 2 + log 2 nV = log 2 (2 powr (- real s - real t + ok_fun_61 k - 2) * nV)"
    using add_log_eq_powr gorder_ge2 by auto
  also have "... \<le> log 2 (RN k (k-t))"
    using "*" Transcendental.log_mono gorder_ge2 less_eq_real_def by auto
  finally show "log 2 nV \<le> log 2 (RN k (k - t)) + real s + real t + 2 - ok_fun_61 k"
    by linarith
qed

subsection \<open>Lemma 2.1\<close>

end
