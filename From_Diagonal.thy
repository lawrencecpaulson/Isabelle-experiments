section \<open>From diagonal to off-diagonal\<close>

theory From_Diagonal
  imports Closer_To_Diagonal

begin

subsection \<open>Lemma 2.2\<close>

definition "ok_fun_11_2a \<equiv> \<lambda>k. \<lceil>real k powr (3/4)\<rceil> * log 2 k"

definition "ok_fun_11_2b \<equiv> \<lambda>\<mu> k. k powr (39/40) * (log 2 \<mu> + 3 * log 2 k)"

definition "ok_fun_11_2c \<equiv> \<lambda>\<mu> k. - k * log 2 (1 - (2 / (1-\<mu>)) * k powr (-1/40))"

definition "ok_fun_11_2 \<equiv> \<lambda>\<mu> k. 2 - ok_fun_71 \<mu> k + ok_fun_11_2a k
      + max (ok_fun_11_2b \<mu> k) (ok_fun_11_2c \<mu> k)"

lemma ok_fun_11_2a: "ok_fun_11_2a \<in> o(real)"
  unfolding ok_fun_11_2a_def
  by real_asymp

text \<open>possibly, the functions that depend upon @{term \<mu>} need a more refined analysis to cover 
a closed interval of possible values. But possibly not, as the text implies @{term "\<mu>=2/5"}.\<close>

lemma ok_fun_11_2b: "ok_fun_11_2b \<mu> \<in> o(real)"
  unfolding ok_fun_11_2b_def by real_asymp

lemma ok_fun_11_2c: "ok_fun_11_2c \<mu> \<in> o(real)"
unfolding ok_fun_11_2c_def
  by real_asymp

lemma ok_fun_11_2:
  assumes "0<\<mu>" "\<mu><1" 
  shows "ok_fun_11_2 \<mu> \<in> o(real)"
  unfolding ok_fun_11_2_def
  by (simp add: assms const_smallo_real maxmin_in_smallo ok_fun_11_2a ok_fun_11_2b ok_fun_11_2c ok_fun_71 sum_in_smallo)


definition "Big_From_11_2 \<equiv>     
   \<lambda>\<mu> k. Big_ZZ_8_6 \<mu> k \<and> Big_X_7_1 \<mu> k \<and> Big_Y_6_2 \<mu> k \<and> Big_Red_5_3 \<mu> k \<and> Big_Blue_4_1 \<mu> k 
       \<and> 1 \<le> \<mu>^2 * real k \<and> 2 / (1-\<mu>) * real k powr (-1/40) < 1 \<and> 1/k < 1/2 - 3 * eps k"

lemma Big_From_11_2:
  assumes "0<\<mu>0" "\<mu>0 \<le> \<mu>1" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_From_11_2 \<mu> k"
proof -
  have A: "\<forall>\<^sup>\<infinity>k. \<forall>\<mu>. \<mu>0 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> 1 \<le> \<mu>\<^sup>2 * k"
  proof (intro eventually_all_geI0)
    show *: "\<forall>\<^sup>\<infinity>x. 1 \<le> \<mu>0\<^sup>2 * real x"
      using \<open>0<\<mu>0\<close> by real_asymp
  next
    fix k \<mu>
    assume "1 \<le> \<mu>0\<^sup>2 * real k" and "\<mu>0 \<le> \<mu>" "\<mu> \<le> \<mu>1"
    with \<open>0<\<mu>0\<close> show "1 \<le> \<mu>\<^sup>2 * k"
      by (smt (verit, ccfv_SIG) mult_le_cancel_right of_nat_less_0_iff power_mono)
  qed
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

text \<open>Simply to prevent issues about the positioning of the function @{term real}}\<close>
abbreviation "H \<equiv> \<lambda>\<mu> s t. \<mu> * (real s + real t) / real s"

text \<open>the text refers to the actual Ramsey number but I don't see how that could work.
Theorem 11.1 will define @{term n} to be one less than the Ramsay number, hence we add that one back here.\<close>
lemma (in Book) From_11_2:
  fixes k
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours k k"  
  assumes big: "Big_From_11_2 \<mu> k"
  defines "\<R> \<equiv> Step_class \<mu> k k {red_step}" and "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  defines "t \<equiv> card \<R>" and "s \<equiv> card \<S>"
  defines "m \<equiv> halted_point \<mu> k k"
  defines "nV' \<equiv> Suc nV"
  assumes 0: "card X0 \<ge> nV div 2" and "p0 \<ge> 1/2"
  shows "log 2 nV' \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (H \<mu> s t) + ok_fun_11_2 \<mu> k"
proof -
  have "k>0"
    using Colours_kn0 \<open>Colours k k\<close> by auto
  have big71: "Big_X_7_1 \<mu> k" and big62: "Big_Y_6_2 \<mu> k" and big86: "Big_ZZ_8_6 \<mu> k" and big53: "Big_Red_5_3 \<mu> k"
    and big41: "Big_Blue_4_1 \<mu> k" and big\<mu>: "1 \<le> \<mu>^2 * real k"
    and big_le1: "2 / (1-\<mu>) * real k powr (-1/40) < 1"
    using big by (auto simp: Big_From_11_2_def)
  have big\<mu>1: "1 \<le> \<mu> * real k"
    using big\<mu> \<mu>
    by (smt (verit, best) mult_less_cancel_right2 mult_right_mono of_nat_less_0_iff power2_eq_square)
  then have log2\<mu>k: "log 2 \<mu> + log 2 k \<ge> 0"
    using \<open>k>0\<close> \<open>\<mu>>0\<close> add_log_eq_powr by auto
  have big\<mu>2: "1 \<le> \<mu> * (real k)\<^sup>2"
    unfolding power2_eq_square by (smt (verit, ccfv_SIG) big\<mu>1 \<mu> mult_less_cancel_left1 mult_mono')
  define g where "g \<equiv> \<lambda>k. \<lceil>real k powr (3/4)\<rceil> * log 2 k"
  have g: "g \<in> o(real)"
    unfolding g_def by real_asymp
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
  have "nV' \<ge> 2"
    using gorder_ge2 nV'_def by linarith
  have "nV' \<le> 4 * card X0"
    using 0 card_XY0 by (auto simp: nV'_def odd_iff_mod_2_eq_one)
  with \<mu> have "2 powr (ok_fun_71 \<mu> k - 2) * \<mu>^k * (1-\<mu>) ^ t * (bigbeta \<mu> k k / \<mu>) ^ s * nV'
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
      unfolding g_def
      by (smt (verit) RN34_le_2powr_ok \<open>0 < k\<close> of_nat_le_iff)
  qed
  finally have 58: "2 powr (g k) \<ge> 2 powr (ok_fun_71 \<mu> k - 2) * \<mu>^k * (1-\<mu>) ^ t * (bigbeta \<mu> k k / \<mu>) ^ s * nV'" .
  then have 59: "nV' \<le> 2 powr (g712 k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t * (\<mu> / bigbeta \<mu> k k) ^ s"
    using \<mu> bb_gt0 by (simp add: g712_def powr_diff powr_add mult.commute divide_simps) argo

  define a where "a \<equiv> 2 / (1-\<mu>)"
  have ok_less1: "a * real k powr (-1/40) < 1"
    unfolding a_def using big_le1 by blast
  consider "s < k powr (39/40)" | "s \<ge> k powr (39/40)" "bigbeta \<mu> k k \<ge> (1 - a * k powr (-1/40)) * (s / (s + t))"
    using ZZ_8_6 big86 \<open>Colours k k\<close> \<mu> a_def by (force simp: s_def t_def \<S>_def \<R>_def)
  then show ?thesis
  proof cases
    case 1
    define h where "h \<equiv> \<lambda>c k. real k powr (39/40) * (log 2 \<mu> + real c * log 2 (real k))"
    have h: "h c \<in> o(real)" for c
      unfolding h_def by real_asymp

    have le_h: "\<bar>s * log 2 (H \<mu> s t)\<bar> \<le> h 1 k"
    proof (cases "s>0")
      case True
      with \<open>s>0\<close> have \<mu>eq: "H \<mu> s t = \<mu> * (1 + t/s)"
        by (auto simp: distrib_left)
      show ?thesis 
      proof (cases "log 2 (H \<mu> s t) \<le> 0")
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
          by (simp add: \<mu>eq h_def mult_le_0_iff)
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
        have "\<bar>s * log 2 (H \<mu> s t)\<bar> \<le> k powr (39/40) * log 2 (H \<mu> s t)"
          using False "1" by auto
        also have "\<dots> = k powr (39/40) * (log 2 (\<mu> * (1 + t/s)))"
          by (simp add: \<mu>eq)
        also have "\<dots> = k powr (39/40) * (log 2 \<mu> + log 2 (1 + t/s))"
          using \<mu> by (smt (verit, best) divide_nonneg_nonneg log_mult of_nat_0_le_iff) 
        also have "\<dots> \<le> k powr (39/40) * (log 2 \<mu> + log 2 k)"
          by (smt (verit, best) "1" Transcendental.log_mono divide_nonneg_nonneg lek 
              mult_le_cancel_left_pos of_nat_0_le_iff)
        also have "\<dots> \<le> h 1 k"
          unfolding h_def using \<open>0 < k\<close> by force
        finally show ?thesis .
      qed 
    qed (use log2\<mu>k h_def in auto)

    have \<beta>: "bigbeta \<mu> k k \<ge> 1 / (real k)\<^sup>2"
      using \<open>Colours k k\<close> \<mu> big53 bigbeta_ge_square by blast
    then have "(\<mu> / bigbeta \<mu> k k) ^ s \<le> (\<mu> * (real k)\<^sup>2) ^ s"
      using bb_gt0 \<open>k>0\<close> \<mu> by (intro power_mono) (auto simp add: divide_simps mult.commute)
    also have "\<dots> \<le> (\<mu> * (real k)\<^sup>2) powr (k powr (39/40))"
      using \<mu> big\<mu>2 1 by (smt (verit) powr_less_mono powr_one_eq_one powr_realpow)
    also have "\<dots> = 2 powr (log 2 ((\<mu> * (real k)\<^sup>2) powr (k powr (39/40))))"
      by (smt (verit, best) big\<mu>2 powr_gt_zero powr_log_cancel)
    also have "\<dots> = 2 powr h 2 k"
      using \<mu> big\<mu>2 \<open>k>0\<close> by (simp add: log_powr log_nat_power log_mult h_def)
    finally have \<dagger>: "(\<mu> / bigbeta \<mu> k k) ^ s \<le> 2 powr h 2 k" .
    have \<ddagger>: "nV' \<le> 2 powr (g712 k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t * 2 powr h 2 k"
      using 59 mult_left_mono [OF \<dagger>, of "2 powr (g712 k) * (1/\<mu>) ^ k * (1 / (1-\<mu>)) ^ t"]
      by (smt (verit) \<mu> pos_prod_le powr_nonneg_iff zero_less_divide_iff zero_less_power)
    have *: "log 2 nV' \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + (g712 k + h 2 k)"
      using \<mu> \<open>nV' \<ge> 2\<close> by (simp add: log_mult log_nat_power order.trans [OF Transcendental.log_mono [OF _ _ \<ddagger>]])

    show ?thesis
    proof -
      have le_ok_fun: "g712 k + h 3 k \<le> ok_fun_11_2 \<mu> k"
        by (simp add: g712_def h_def ok_fun_11_2_def g_def ok_fun_11_2a_def ok_fun_11_2b_def)
      have h3: "h 3 k = h 1 k + h 2 k - real k powr (39/40) * log 2 \<mu>"
        by (simp add: h_def algebra_simps)
      have "0 \<le> h 1 k + s * log 2 ((\<mu> * real s + \<mu> * real t) / s)"
        by (smt (verit, del_insts) of_nat_add distrib_left le_h)
      moreover have "log 2 \<mu> < 0"
        using \<mu> by simp
      ultimately have "g712 k + h 2 k \<le> s * log 2 (H \<mu> s t) + ok_fun_11_2 \<mu> k"
        by (smt (verit, best) \<open>0 < k\<close> distrib_left h3 le_ok_fun nat_neq_iff of_nat_eq_0_iff pos_prod_lt powr_gt_zero)
      then show "log 2 nV' \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (H \<mu> s t) + ok_fun_11_2 \<mu> k"
        using "*" by linarith
    qed
  next
    case 2
    then have "s > 0"
      using \<open>0 < k\<close> powr_gt_zero by fastforce
    define h where "h \<equiv> \<lambda>k. real k * log 2 (1 - a * k powr (-1/40))"
    have "s * log 2 (\<mu> / bigbeta \<mu> k k) = s * log 2 \<mu> - s * log 2 (bigbeta \<mu> k k)"
      using \<mu> bb_gt0 2 by (simp add: log_divide algebra_simps)
    also have "\<dots> \<le> s * log 2 \<mu> - s * log 2 ((1 - a * k powr (-1/40)) * (s / (s + t)))"
      using 2 \<open>s>0\<close> ok_less1 by (intro diff_mono order_refl mult_left_mono Transcendental.log_mono) auto
    also have "\<dots> = s * log 2 \<mu> - s * (log 2 (1 - a * k powr (-1/40)) + log 2 (s / (s + t)))"
      using \<open>0 < s\<close> a_def add_log_eq_powr big_le1 by auto
    also have "\<dots> = s * log 2 (H \<mu> s t) - s * log 2 (1 - a * k powr (-1/40))"
      using \<open>0 < \<mu>\<close> \<open>0 < s\<close> minus_log_eq_powr by (auto simp flip: right_diff_distrib')
    also have "\<dots> < s * log 2 (H \<mu> s t) - h k"
    proof -
      have "log 2 (1 - a * real k powr (-1/40)) < 0"
        using \<mu> \<open>0 < k\<close> a_def ok_less1 by auto
      with \<open>s<k\<close> show ?thesis
        by (simp add: h_def)
    qed
    finally have \<dagger>: "s * log 2 (\<mu> / bigbeta \<mu> k k) < s * log 2 (H \<mu> s t) - h k" .
    show ?thesis
    proof -
      have le_ok_fun: "g712 k - h k \<le> ok_fun_11_2 \<mu> k"
        by (simp add: g712_def h_def ok_fun_11_2_def g_def ok_fun_11_2a_def a_def ok_fun_11_2c_def)
      have "log 2 nV' \<le> s * log 2 (\<mu> / bigbeta \<mu> k k) + k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + (g712 k)"
        using \<mu> \<open>nV' \<ge> 2\<close> 
        by (simp add: bb_gt0 log_mult log_nat_power order.trans [OF Transcendental.log_mono [OF _ _ 59]])
      with \<dagger> le_ok_fun show "log 2 nV' \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (H \<mu> s t) + ok_fun_11_2 \<mu> k"
        by simp
    qed
  qed
qed

subsection \<open>Lemma 2.3\<close>

text \<open>same remark as in Lemma 11.2 about the use of the Ramsey number in the conclusion\<close>
lemma (in Book) From_11_3:
  fixes k
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours k k"  
  assumes big: "Big_Y_6_1 \<mu> k"
  defines "\<R> \<equiv> Step_class \<mu> k k {red_step}" and "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  defines "t \<equiv> card \<R>" and "s \<equiv> card \<S>"
  defines "m \<equiv> halted_point \<mu> k k"
  defines "nV' \<equiv> Suc nV"
  assumes 0: "card Y0 \<ge> nV div 2" and "p0 \<ge> 1/2"
  shows "log 2 nV' \<le> log 2 (RN k (k-t)) + s + t + 2 - ok_fun_61 k"
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
  have 4: "nV'/4 \<le> card Y0"
    using 0 card_XY0 by (auto simp: nV'_def odd_iff_mod_2_eq_one)
  have ge0: "0 \<le> 2 powr ok_fun_61 k * p0 ^ card RS"
    using p0_01 by fastforce
  have "nV' \<ge> 2"
    using gorder_ge2 nV'_def by linarith
  have "2 powr (- real s - real t + ok_fun_61 k - 2) * nV' = 2 powr (ok_fun_61 k - 2) * (1/2) ^ card RS * nV'"
    by (simp add: powr_add powr_diff powr_minus power_add powr_realpow divide_simps card_RS)
  also have "\<dots> \<le> 2 powr (ok_fun_61 k - 2) * p0 ^ card RS * nV'"
    using power_mono [OF \<open>p0 \<ge> 1/2\<close>] \<open>nV' \<ge> 2\<close> by auto
  also have "\<dots> \<le> 2 powr (ok_fun_61 k) * p0 ^ card RS * (nV'/4)"
    by (simp add: divide_simps powr_diff split: if_split_asm)
  also have "... \<le> 2 powr (ok_fun_61 k) * p0 ^ card RS * card Y0"
    using   mult_left_mono [OF 4 ge0 ] by simp
  also have "... \<le> card (Yseq \<mu> k k m)"
    using Y_6_1 [OF \<mu> big \<open>Colours k k\<close>] by (simp add: m_def RS_def divide_simps split: if_split_asm)
  finally have "2 powr (- real s - real t + ok_fun_61 k - 2) * nV' \<le> card (Yseq \<mu> k k m)" .
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
  ultimately have *: "2 powr (- real s - real t + ok_fun_61 k - 2) * nV' < RN k (k-t)"
    by fastforce
  have "- real s - real t + ok_fun_61 k - 2 + log 2 nV' = log 2 (2 powr (- real s - real t + ok_fun_61 k - 2) * nV')"
    using add_log_eq_powr \<open>nV' \<ge> 2\<close> by auto
  also have "... \<le> log 2 (RN k (k-t))"
    using "*" Transcendental.log_mono \<open>nV' \<ge> 2\<close> less_eq_real_def by auto
  finally show "log 2 nV' \<le> log 2 (RN k (k - t)) + real s + real t + 2 - ok_fun_61 k"
    by linarith
qed

subsection \<open>Theorem 2.1\<close>

(* actually it is undefined when k=0 or x=1; could we use 1+R(k,k') in the definition?*)
definition FF :: "nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
 "FF \<equiv> \<lambda>k x y. log 2 (RN k (nat\<lfloor>real k - x * real k\<rfloor>)) / real k + x + y"

definition GG :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "GG \<equiv> \<lambda>\<mu> x y. log 2 (1/\<mu>) + x * log 2 (1/(1-\<mu>)) + y * log 2 (\<mu> * (x+y) / y)"

definition FF_bound :: "nat \<Rightarrow> real \<Rightarrow> real" where
  "FF_bound \<equiv> \<lambda>k u. FF k 0 u + \<bar>FF k 1 u\<bar> + 1"


(* the ugly mess here fixes the singularity when x=1. We just add in \<bar>FF k 1 u\<bar>, whatever it may be!*)
lemma FF:
  assumes x: "x \<in> {0..1}" and "y \<in> {0..u}" "k>0"
  shows "FF k x y \<le> FF_bound k u"
proof (cases "\<lfloor>k - x*k\<rfloor> = 0")
  case True  \<comment>\<open>all this nonsense just to handle the singularity\<close>
  have "u \<ge> 0"
    using assms by simp
  have "0 \<le> log 2 (RN k k) / k"
  proof (cases "k=0")
    case False
    then have "RN k k \<ge> 1"
      by (simp add: RN_eq_0_iff leI)
    then show ?thesis
      by simp
  qed auto
  with \<open>u \<ge> 0\<close> have "FF k 0 u \<ge> 0"
    by (simp add: FF_def)
  with assms show ?thesis
    by (simp add: True FF_def abs_if FF_bound_def)
next
  case False
  with \<open>k>0\<close> assms have *: "0 < \<lfloor>k - x*k\<rfloor>"
    using linorder_neqE_linordered_idom by fastforce
  have le_k: "k - x*k \<le> k"
    using x by auto
  then have le_k: "nat \<lfloor>k - x*k\<rfloor> \<le> k"
    by linarith
  have "log 2 (RN k (nat \<lfloor>k - x*k\<rfloor>)) / k \<le> log 2 (RN k k) / k"
  proof (intro divide_right_mono Transcendental.log_mono)
    show "0 < real (RN k (nat \<lfloor>k - x*k\<rfloor>))"
      by (metis RN_eq_0_iff \<open>k>0\<close> gr_zeroI * of_nat_0_less_iff zero_less_nat_eq) 
  qed (auto simp: RN_mono le_k)
  then show ?thesis
    using assms False le_SucE by (fastforce simp: FF_def FF_bound_def)
qed

lemma FF2: "y' \<le> y \<Longrightarrow> FF k x y' \<le> FF k x y"
  by (simp add: FF_def)

context P0_min
begin 


definition "ok_fun_11_1 \<equiv> \<lambda>\<mu> k. max (ok_fun_11_2 \<mu> k) (2 - ok_fun_61 k)"

lemma ok_fun_11_1:
  assumes "0<\<mu>" "\<mu><1" 
  shows "ok_fun_11_1 \<mu> \<in> o(real)"
  unfolding ok_fun_11_1_def
  by (simp add: assms const_smallo_real maxmin_in_smallo ok_fun_11_2 ok_fun_61 sum_in_smallo)

lemma eventually_ok111_le_\<eta>:
  assumes "\<eta> > 0" and \<mu>: "0<\<mu>" "\<mu><1" 
  shows "\<forall>\<^sup>\<infinity>k. ok_fun_11_1 \<mu> k / k \<le> \<eta>"
proof -
  have "(\<lambda>k. ok_fun_11_1 \<mu> k / k) \<in> o(\<lambda>k. 1)"
    using eventually_mono ok_fun_11_1 [OF \<mu>] by (fastforce simp: smallo_def divide_simps)
  with assms have "\<forall>\<^sup>\<infinity>k. \<bar>ok_fun_11_1 \<mu> k\<bar> / k \<le> \<eta>"
    by (auto simp: smallo_def)
  then show ?thesis
    by (metis (mono_tags, lifting) eventually_mono abs_divide abs_le_D1 abs_of_nat)
qed

lemma eventually_powr_le_\<eta>:
  assumes "\<eta> > 0" 
  shows "\<forall>\<^sup>\<infinity>k. (2 / (1-\<mu>)) * k powr (-1/20) \<le> \<eta>"
  using assms by real_asymp

definition "Big_From_11_1 \<equiv> 
   \<lambda>\<eta> \<mu> k. Big_From_11_2 \<mu> k \<and> Big_ZZ_8_5 \<mu> k \<and> Big_Y_6_1 \<mu> k \<and> ok_fun_11_1 \<mu> k / k \<le> \<eta>
         \<and> (2 / (1-\<mu>)) * k powr (-1/20) \<le> \<eta>"

text \<open>in sections 9 and 10 (and by implication all proceeding sections), we needed to consider 
  a closed interval of possible values of @{term \<mu>}. Let's hope, maybe not here. }\<close>
lemma Big_From_11_1:
  assumes "\<eta> > 0" "0<\<mu>" "\<mu><1" 
  shows "\<forall>\<^sup>\<infinity>k. Big_From_11_1 \<eta> \<mu> k"
  unfolding Big_From_11_1_def
  using assms Big_From_11_2 Big_ZZ_8_5 Big_Y_6_1 eventually_ok111_le_\<eta> eventually_powr_le_\<eta> 
  apply (simp add: eventually_conj_iff all_imp_conj_distrib eventually_sequentially)
  by (metis (mono_tags, lifting) order.refl)  


text \<open>The body of the proof has been extracted to allow the symmetry argument\<close>
lemma (in Book_Basis) From_11_1_Body:
  fixes V :: "'a set"
  assumes \<mu>: "0 < \<mu>" "\<mu> < 1" and "\<eta> > 0" and "k>0" and ge_RN: "Suc nV \<ge> RN k k"
    and Red: "graph_density Red \<ge> 1/2" 
    and p0_min12: "p0_min \<le> 1/2"
    and Red_E: "Red \<subseteq> E" and Blue_def: "Blue = E\<setminus>Red" 
    and no_Red_K: "\<not> (\<exists>K. size_clique k K Red)"
    and no_Blue_K: "\<not> (\<exists>K. size_clique k K Blue)"
    and big: "Big_From_11_1 \<eta> \<mu> k"
  shows "log 2 (RN k k) / k \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..\<mu>*x/(1-\<mu>)+\<eta>}. min (FF k x y) (GG \<mu> x y) + \<eta>)"
proof -  
  have big41: "Big_Blue_4_1 \<mu> k" and big61: "Big_Y_6_1 \<mu> k" 
    and big85: "Big_ZZ_8_5 \<mu> k" and big11_2: "Big_From_11_2 \<mu> k"
    and ok111_le_\<eta>: "ok_fun_11_1 \<mu> k / k \<le> \<eta>"
    and powr_le_\<eta>: "(2 / (1-\<mu>)) * k powr (-1/20) \<le> \<eta>"
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
  have FF_GG_bound: "min (FF k x y) (GG \<mu> x y) + \<eta> \<le> FF_bound k (\<mu> / (1-\<mu>) + \<eta>) + \<eta>"
    if x: "x \<in> {0..1}" and y: "y \<in> {0..\<mu> * x / (1-\<mu>) + \<eta>}" for x y
  proof -
    have FF_ub: "FF k x y \<le> FF_bound k (\<mu> / (1-\<mu>) + \<eta>)"
    proof (rule order.trans)
      show "FF k x y \<le> FF_bound k y"
        using x y \<open>0 < k\<close> by (simp add: FF)
    next
      have "y \<le> \<mu> / (1-\<mu>) + \<eta>"
        using x y \<mu> by simp (smt (verit, best) frac_le mult_left_le)
      then show "FF_bound k y \<le> FF_bound k (\<mu> / (1-\<mu>) + \<eta>)"
        by (simp add: FF_bound_def FF_def)
    qed
    show ?thesis
      using FF_ub by auto
  qed
  define \<R> where "\<R> \<equiv> Step_class \<mu> k k {red_step}"
  define \<S> where "\<S> \<equiv> Step_class \<mu> k k {dboost_step}"
  define t where "t \<equiv> card \<R>" 
  define s where "s \<equiv> card \<S>"
  define m where "m \<equiv> halted_point \<mu> k k"
  define x where "x \<equiv> t/k"
  define y where "y \<equiv> s/k"
  define v where "v \<equiv> min (FF k x y) (GG \<mu> x y) + \<eta>"
  have sts: "(s + real t) / s = (x+y) / y"
    using \<open>k>0\<close> by (simp add: x_def y_def field_simps)
  have "t < k"
    by (simp add: \<R>_def \<mu> t_def \<open>Colours k k\<close> red_step_limit)
  then obtain x01: "0\<le>x" "x\<le>1"
    by (auto simp: x_def)

  define w where "w \<equiv> (\<Squnion>y\<in>{0..\<mu> * x / (1-\<mu>) + \<eta>}. min (FF k x y) (GG \<mu> x y) + \<eta>)"
  show ?thesis
  proof (intro cSup_upper2 cSUP_least imageI bdd_aboveI2)
    show "w \<in> (\<lambda>x. \<Squnion>y\<in>{0..\<mu> * x / (1-\<mu>) + \<eta>}. min (FF k x y) (GG \<mu> x y) + \<eta>) ` {0..1}"
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
    have "log 2 (Suc nV) / k \<le> log 2 (RN k (k-t)) / k + x + y + (2 - ok_fun_61 k) / k"
      using \<open>k>0\<close> divide_right_mono [OF \<section>, of k] add_divide_distrib x_def y_def
      by (smt (verit) add_uminus_conv_diff of_nat_0_le_iff)
    also have "... = FF k x y + (2 - ok_fun_61 k) / k"
      by (simp add: FF_def x_def k_minus_t)
    also have "... \<le> FF k x y + ok_fun_11_1 \<mu> k / k"
      by (simp add: ok_fun_11_1_def divide_right_mono)
    finally have le_FF: "log 2 (Suc nV) / k \<le> FF k x y + ok_fun_11_1 \<mu> k / k" .

    have "nV div 2 \<le> card X0"
      using card_X0 by linarith
    then have 112: "log 2 (Suc nV) \<le> k * log 2 (1/\<mu>) + t * log 2 (1 / (1-\<mu>)) + s * log 2 (H \<mu> s t)
                + ok_fun_11_2 \<mu> k"
      using From_11_2 [OF \<mu> \<open>Colours k k\<close> big11_2] p0_half
      unfolding s_def t_def p0_def \<R>_def \<S>_def by blast
    have "log 2 (Suc nV) / k \<le> log 2 (1/\<mu>) + x * log 2 (1 / (1-\<mu>)) + y * log 2 (H \<mu> s t)
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
      have "y \<in> {0..\<mu> * x / (1-\<mu>) + \<eta>}"
        using divide_right_mono [OF \<dagger>, of k] \<open>k>0\<close> by (simp add: x_def y_def) argo
      then show "min (FF k x y) (GG \<mu> x y) + \<eta> \<in> (\<lambda>y. min (FF k x y) (GG \<mu> x y) + \<eta>) ` {0..\<mu> * x / (1-\<mu>) + \<eta>}"
        by blast
    next
      show "bdd_above ((\<lambda>y. min (FF k x y) (GG \<mu> x y) + \<eta>) ` {0..\<mu> * x / (1-\<mu>) + \<eta>})"
        by (meson FF_GG_bound [of x] x01 atLeastAtMost_iff bdd_aboveI2)
    qed auto
    finally show "log 2 (real (RN k k)) / k \<le> w" .
  next
    fix x y 
    assume "x \<in> {0..1}" "y \<in> {0..\<mu> * x / (1-\<mu>) + \<eta>}"
    then show "min (FF k x y) (GG \<mu> x y) + \<eta> \<le> FF_bound k (\<mu> / (1-\<mu>) + \<eta>) + \<eta>"
      using FF_GG_bound by blast
  qed (use \<mu> \<open>\<eta>>0\<close> in auto)
qed

theorem From_11_1:
  assumes \<mu>: "0 < \<mu>" "\<mu> < 1" and "\<eta> > 0" and "k\<ge>3" and p0_min12: "p0_min \<le> 1/2"
  and big: "Big_From_11_1 \<eta> \<mu> k"
  shows "log 2 (RN k k) / k \<le> (SUP x \<in> {0..1}. SUP y \<in> {0..\<mu>*x/(1-\<mu>)+\<eta>}. min (FF k x y) (GG \<mu> x y) + \<eta>)"
proof -
  have "k>0"
    using \<open>k\<ge>3\<close> by simp
  have big41: "Big_Blue_4_1 \<mu> k" and big61: "Big_Y_6_1 \<mu> k" 
    and big85: "Big_ZZ_8_5 \<mu> k" and big11_2: "Big_From_11_2 \<mu> k"
    and ok111_le_\<eta>: "ok_fun_11_1 \<mu> k / k \<le> \<eta>"
    and powr_le_\<eta>: "(2 / (1-\<mu>)) * k powr (-1/20) \<le> \<eta>"
    using big by (auto simp: Big_From_11_1_def Big_Y_6_1_def Big_Y_6_2_def)
  then have big53: "Big_Red_5_3 \<mu> k"
    by (meson Big_From_11_2_def)
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

end (*P0_min*)

hide_const H

end
