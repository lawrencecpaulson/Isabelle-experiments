section \<open>Bounding the Size of @{term X}\<close>

theory Bounding_X imports Bounding_Y

begin

context Diagonal
begin

text \<open>the set of moderate density-boost steps (page 20)\<close>
definition dboost_star where
  "dboost_star \<equiv> \<lambda>\<mu> l k. 
  {i \<in> Step_class \<mu> l k {dboost_step}. real (hgt k (pee \<mu> l k (Suc i))) - hgt k (pee \<mu> l k i) \<le> eps k powr (-1/4)}"

definition bigbeta where
  "bigbeta \<equiv> \<lambda>\<mu> l k. 
   let S = dboost_star \<mu> l k in if S = {} then \<mu> else (card S) * inverse (\<Sum>i\<in>S. inverse (beta \<mu> l k i))"

lemma dboost_star_subset: "dboost_star \<mu> l k \<subseteq> Step_class \<mu> l k {dboost_step}"
  by (auto simp: dboost_star_def)

lemma bigbeta_ge_0:
  assumes \<mu>: "0<\<mu>"  
  shows "bigbeta \<mu> l k \<ge> 0"
  using assms by (simp add: bigbeta_def Let_def beta_ge0 sum_nonneg)

lemma bigbeta_gt_0:
  assumes "0<\<mu>"  "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> bigbeta \<mu> l k > 0"
proof -
  { fix l k
    assume  0: "\<forall>i\<in>Step_class \<mu> l k {dboost_step}. 0 < beta \<mu> l k i" 
      and fin: "finite (Step_class \<mu> l k {dboost_step})"
    have *: "0 < bigbeta \<mu> l k"
    proof (cases "dboost_star \<mu> l k = {}")
      case True
      then show ?thesis
        using assms by (simp add: bigbeta_def)
    next
      case False
      then have "card (dboost_star \<mu> l k) > 0"
        by (meson card_gt_0_iff dboost_star_subset fin finite_subset)
      with 0 show ?thesis
        by (auto simp add: bigbeta_def Let_def zero_less_mult_iff card_gt_0_iff dboost_star_def intro!: sum_pos)
    qed
  }
  then show ?thesis
    using eventually_mono [OF eventually_conj [OF beta_gt_0 [OF assms] bblue_dboost_step_limit [OF \<open>\<mu>>0\<close>]]]
    unfolding Lemma_bblue_dboost_step_limit_def Lemma_beta_gt_0_def
    by presburger
qed


lemma bigbeta_less_1:
  assumes "0<\<mu>"  "\<mu><1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> bigbeta \<mu> l k < 1"
proof -
  { fix l k
    assume 0: "\<forall>i\<in>Step_class \<mu> l k {dboost_step}. 0 < beta \<mu> l k i" 
      and fin: "finite (Step_class \<mu> l k {dboost_step})"
    have *: "bigbeta \<mu> l k < 1"
    proof (cases "dboost_star \<mu> l k = {}")
      case True
      then show ?thesis
        using assms by (simp add: bigbeta_def)
    next
      case False
      then have gt0: "card (dboost_star \<mu> l k) > 0"
        by (meson card_gt_0_iff dboost_star_subset fin finite_subset)
      have "real (card (dboost_star \<mu> l k)) = (\<Sum>i\<in>dboost_star \<mu> l k. 1)"
        by simp
      also have "...  < (\<Sum>i\<in>dboost_star \<mu> l k. 1 / beta \<mu> l k i)"
      proof (intro sum_strict_mono)
        show "finite (dboost_star \<mu> l k)"
          using card_gt_0_iff gt0 by blast
        fix i
        assume "i \<in> dboost_star \<mu> l k"
        with assms
        show "1 < 1 / beta \<mu> l k i"
          by (smt (verit, ccfv_threshold) "0" Step_class_insert UnCI beta_le dboost_star_subset
              less_divide_eq_1 subset_iff)
      qed (use False in auto)
      finally show ?thesis
        using False by (simp add: bigbeta_def Let_def divide_simps)
    qed
  }
  then show ?thesis
    using eventually_mono [OF eventually_conj [OF beta_gt_0 [OF assms] bblue_dboost_step_limit [OF \<open>\<mu>>0\<close>]]]
      Lemma_bblue_dboost_step_limit_def
    by presburger
qed

subsection \<open>Lemma 7.2\<close>

lemma X_7_2:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  defines "f \<equiv> \<lambda>k. (real k / ln 2) * ln (1 - 1 / (k * (1-\<mu>)))"
  assumes big: "nat \<lceil>real l powr (3/4)\<rceil> \<ge> 3" "k\<ge>2" "k > 1 / (1-\<mu>)"
  assumes "Colours l k" and fin_red: "finite (Step_class \<mu> l k {red_step})"
  defines "X \<equiv> Xseq \<mu> l k"
  shows "(\<Prod>i \<in> Step_class \<mu> l k {red_step}. card (X(Suc i)) / card (X i)) 
        \<ge> 2 powr (f k) * (1-\<mu>) ^ card (Step_class \<mu> l k {red_step})"
proof -
  have "f \<in> o(real)"
    using p0_01 \<mu> unfolding eps_def f_def by real_asymp
  define R where "R \<equiv> RN k (nat \<lceil>real l powr (3/4)\<rceil>)"
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  have "R > k"
    using big RN_gt1 R_def by blast
  with big \<mu> have bigR: "1-\<mu> > 1/R"
    apply (simp add: divide_simps mult.commute)
    by (smt (verit, ccfv_SIG) divide_less_eq less_imp_of_nat_less)
  have *: "1-\<mu> - 1/R \<le> card (X (Suc i)) / card (X i)"
    if  "i \<in> Step_class \<mu> l k {red_step}" for i
  proof -
    let ?NRX = "\<lambda>i. Neighbours Red (cvx \<mu> l k i) \<inter> X i"
    have nextX: "X (Suc i) = ?NRX i" and nont: "\<not> termination_condition l k (X i) (Yseq \<mu> l k i)"
      using that by (auto simp: X_def step_kind_defs next_state_def cvx_def Let_def split: prod.split)
    then have cardX: "card (X i) > R"
      unfolding R_def by (meson not_less termination_condition_def)
    have 1: "card (?NRX i) \<ge> (1-\<mu>) * card (X i) - 1"
      using that card_cvx_Neighbours \<mu> by (simp add: Step_class_def X_def)
    have "R \<noteq> 0"
      unfolding RN_eq_0_iff R_def using lk by auto
    with cardX have "(1-\<mu>) - 1 / R \<le> (1-\<mu>) - 1 / card (X i)"
      by (simp add: inverse_of_nat_le)
    also have "\<dots> \<le> card (X (Suc i)) / card (X i)"
      using cardX nextX 1 by (simp add: divide_simps)
    finally show ?thesis .
  qed
  define t where "t \<equiv> card(Step_class \<mu> l k {red_step})"
  have "t\<ge>0"
    by (auto simp: t_def)
  have "(1-\<mu> - 1/R) ^ card Red_steps \<le> (\<Prod>i \<in> Red_steps. card (X(Suc i)) / card (X i))"
    if "Red_steps \<subseteq> Step_class \<mu> l k {red_step}" for Red_steps
    using finite_subset [OF that fin_red] that
  proof induction
    case empty
    then show ?case
      by auto
  next
    case (insert i Red_steps)
    then have i: "i \<in> Step_class \<mu> l k {red_step}"
      by auto
    have "((1-\<mu>) - 1/R) ^ card (insert i Red_steps) = ((1-\<mu>) - 1/R) * ((1-\<mu>) - 1/R) ^ card (Red_steps)"
      by (simp add: insert)
    also have "\<dots> \<le> (card (X (Suc i)) / card (X i)) * ((1-\<mu>) - 1/R) ^ card (Red_steps)"
      using bigR by (intro mult_right_mono * i) auto
    also have "\<dots> \<le> (card (X (Suc i)) / card (X i)) * (\<Prod>i \<in> Red_steps. card (X(Suc i)) / card (X i))"
      using insert by (intro mult_left_mono) auto
    also have "\<dots> = (\<Prod>i\<in>insert i Red_steps. card (X(Suc i)) / card (X i))"
      using insert by simp
    finally show ?case .
  qed
  then have *: "(1-\<mu> - 1/R) ^ t \<le> (\<Prod>i \<in> Step_class \<mu> l k {red_step}. card (X(Suc i)) / card (X i))"
    using t_def by blast
  \<comment> \<open>Asymptotic part of the argument\<close>
  have "1-\<mu> - 1/k \<le> 1-\<mu> - 1/R"
    using \<open>0<k\<close> \<open>k < R\<close> by (simp add: inverse_of_nat_le)
  then have ln_le: "ln (1-\<mu> - 1/k) \<le> ln (1-\<mu> - 1/R)"
    using \<mu> big \<open>k>0\<close> \<open>R>k\<close> 
    by (simp add: bigR divide_simps mult.commute pos_divide_less_eq less_le_trans)
  have "f k * ln 2 = k * ln (1 - 1 / (k * (1-\<mu>)))"
    by (simp add: f_def)
  also have "\<dots> \<le> t * ln (1 - 1 / (k * (1-\<mu>)))"
  proof (intro mult_right_mono_neg)
    obtain red_steps: "finite (Step_class \<mu> l k {red_step})" "card (Step_class \<mu> l k {red_step}) < k"
      using red_step_limit \<open>0<\<mu>\<close> \<open>Colours l k\<close> by blast
    show "real t \<le> real k"
      using nat_less_le red_steps(2) by (simp add: t_def)
    show "ln (1 - 1 / (k * (1-\<mu>))) \<le> 0"
      using \<mu>(2) divide_less_eq big ln_one_minus_pos_upper_bound by fastforce
  qed
  also have "\<dots> = t * ln ((1-\<mu> - 1/k) / (1-\<mu>))"
    using \<open>t\<ge>0\<close> \<mu> by (simp add: diff_divide_distrib)
  also have "\<dots> = t * (ln (1-\<mu> - 1/k) - ln (1-\<mu>))"
    using \<open>t\<ge>0\<close> \<mu> big \<open>0<k\<close> by (simp add: ln_div mult.commute pos_divide_less_eq)
  also have "\<dots> \<le> t * (ln (1-\<mu> - 1/R) - ln (1-\<mu>))"
    by (simp add: ln_le mult_left_mono)
  finally have "f k * ln 2 + t * ln (1-\<mu>) \<le> t * ln (1-\<mu> - 1/R)"
    by (simp add: ring_distribs)
  then have "2 powr f k * (1-\<mu>) ^ t \<le> (1-\<mu> - 1/R) ^ t"
    using \<mu> by (simp add: bigR ln_mult ln_powr ln_realpow flip: ln_le_cancel_iff)
  with * show ?thesis
    by (simp add: t_def)
qed

subsection \<open>Lemma 7.3\<close>

definition "Bdelta \<equiv> \<lambda> \<mu> l k i. Bseq \<mu> l k (Suc i) \<setminus> Bseq \<mu> l k i"

lemma card_Bdelta: "card (Bdelta \<mu> l k i) = card (Bseq \<mu> l k (Suc i)) - card (Bseq \<mu> l k i)"
  by (simp add: Bseq_mono Bdelta_def card_Diff_subset finite_Bseq)

lemma card_Bseq_mono: "card (Bseq \<mu> l k (Suc i)) \<ge> card (Bseq \<mu> l k i)"
  by (simp add: Bseq_Suc_subset card_mono finite_Bseq)

lemma card_Bseq_sum: "card (Bseq \<mu> l k i) = (\<Sum>j<i. card (Bdelta \<mu> l k j))"
proof (induction i)
  case 0
  then show ?case
    by auto
next
  case (Suc i)
  with card_Bseq_mono show ?case
    unfolding card_Bdelta sum.lessThan_Suc
    by (smt (verit, del_insts) Nat.add_diff_assoc diff_add_inverse)
qed

definition "get_blue_book \<equiv> \<lambda>\<mu> l k i. let (X,Y,A,B) = stepper \<mu> l k i in choose_blue_book \<mu> (X,Y,A,B)"

text \<open>Tracking changes to X and B. The sets are necessarily finite\<close>
lemma Bdelta_bblue_step:
  fixes \<mu>::real
  assumes i: "i \<in> Step_class \<mu> l k {bblue_step}" 
  shows "\<exists>S \<subseteq> Xseq \<mu> l k i. Bdelta \<mu> l k i = S
            \<and> card (Xseq \<mu> l k (Suc i)) \<ge> (\<mu> ^ card S) * card (Xseq \<mu> l k i) / 2"
proof -
  obtain X Y A B S T where step: "stepper \<mu> l k i = (X,Y,A,B)" and bb: "get_blue_book \<mu> l k i = (S,T)"
    and valid: "valid_state(X,Y,A,B)"
    by (metis surj_pair valid_state_stepper)
  with assms have *: "stepper \<mu> l k (Suc i) = (T, Y, A, B\<union>S) \<and> good_blue_book \<mu> X (S,T)" 
    and Xeq: "X = Xseq \<mu> l k i"
    by (simp_all add: step_kind_defs next_state_def valid_state_def get_blue_book_def choose_blue_book_works split: if_split_asm)
  show ?thesis
  proof (intro exI conjI)
    have "S \<subseteq> X"
    proof (intro choose_blue_book_subset [THEN conjunct1])
      show "(S, T) = choose_blue_book \<mu> (X, Y, A, B)"
        using bb step by (simp add: get_blue_book_def Xseq_def)
    qed (use valid valid_state_def in force)
    then show "S \<subseteq> Xseq \<mu> l k i"
      using Xeq by force
    have "disjnt X B"
      using valid by (auto simp: valid_state_def disjoint_state_def)
    then show "Bdelta \<mu> l k i = S"
      using * step \<open>S \<subseteq> X\<close> by (auto simp add: Bdelta_def Bseq_def disjnt_iff)
    show "\<mu> ^ card S * real (card (Xseq \<mu> l k i)) / 2 \<le> real (card (Xseq \<mu> l k (Suc i)))"
      using * by (auto simp add: Xseq_def good_blue_book_def step)
  qed
qed

lemma Bdelta_dboost_step:
  assumes "i \<in> Step_class \<mu> l k {dboost_step}" 
  shows "\<exists>x \<in> Xseq \<mu> l k i. Bdelta \<mu> l k i = {x}"
proof -
  obtain X Y A B where step: "stepper \<mu> l k i = (X,Y,A,B)" and valid: "valid_state(X,Y,A,B)"
    by (metis surj_pair valid_state_stepper)
  have cvx: "choose_central_vx \<mu> (X,Y,A,B) \<in> X"
    by (metis Step_class_insert Un_iff cvx_def cvx_in_Xseq assms step stepper_XYseq)
  then have "\<exists>X' Y'. stepper \<mu> l k (Suc i) = (X', Y', A, insert (choose_central_vx \<mu> (X,Y,A,B)) B)"
    using assms step
    by (auto simp add: step_kind_defs next_state_def Let_def split: if_split_asm)
  moreover have "choose_central_vx \<mu> (X,Y,A,B) \<notin> B"
    using valid cvx by (force simp add: valid_state_def disjoint_state_def disjnt_iff)
  ultimately show ?thesis
    using step cvx by (auto simp add: Bdelta_def Bseq_def disjnt_iff Xseq_def)
qed

lemma card_Bdelta_dboost_step:
  assumes "i \<in> Step_class \<mu> l k {dboost_step}" 
  shows "card (Bdelta \<mu> l k i) = 1"
  using Bdelta_dboost_step [OF assms] by force

lemma Bdelta_trivial_step:
  assumes i: "i \<in> Step_class \<mu> l k {red_step,dreg_step,halted}" 
  shows "Bdelta \<mu> l k i = {}"
  using assms
  by (auto simp: step_kind_defs next_state_def Bdelta_def Bseq_def Let_def degree_reg_def split: if_split_asm prod.split)

text \<open>limit version still needs to be written\<close>
lemma X_7_3:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  defines "f \<equiv> \<lambda>k. - (real k powr (3/4))"
  assumes bblue_limit: "Lemma_bblue_step_limit \<mu> l" 
    and bblue_dboost_step_limit: "Lemma_bblue_dboost_step_limit \<mu> l"
  assumes "Colours l k" 
  defines "X \<equiv> Xseq \<mu> l k"
  defines "\<B> \<equiv> Step_class \<mu> l k {bblue_step}"
  defines "\<S> \<equiv> Step_class \<mu> l k {dboost_step}"
  shows "(\<Prod>i \<in> \<B>. card (X(Suc i)) / card (X i)) \<ge> 2 powr (f k) * \<mu> ^ (l - card \<S>)"
proof -
  have "f \<in> o(real)"
    unfolding f_def by real_asymp
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  have "finite \<B>" and card\<B>: "card \<B> \<le> l powr (3/4)"
    using \<open>Colours l k\<close> bblue_limit by (auto simp: \<B>_def Lemma_bblue_step_limit_def)
  have "finite \<S>"
    using bblue_dboost_step_limit \<open>Colours l k\<close>
    unfolding \<S>_def Lemma_bblue_dboost_step_limit_def by blast
  define b where "b \<equiv> \<lambda>i. card (Bdelta \<mu> l k i)"
  obtain i where "card (Bseq \<mu> l k i) = sum b \<B> + card \<S>" 
  proof -
    define i where "i = Suc (Max (\<B> \<union> \<S>))"
    define TRIV where "TRIV \<equiv> Step_class \<mu> l k {red_step,dreg_step,halted} \<inter> {..<i}"
    have "finite TRIV"
      by (auto simp: TRIV_def)
    have eq: "\<B> \<union> \<S> \<union> TRIV = {..<i}"
    proof
      show "\<B> \<union> \<S> \<union> TRIV \<subseteq> {..<i}"
        by (auto simp add: i_def TRIV_def \<open>finite \<B>\<close> \<open>finite \<S>\<close> less_Suc_eq_le)
      show "{..<i} \<subseteq> \<B> \<union> \<S> \<union> TRIV"
        using  stepkind.exhaust by (auto simp: \<B>_def \<S>_def TRIV_def Step_class_def)
    qed
    have dis: "\<B> \<inter> \<S> = {}" "(\<B> \<union> \<S>) \<inter> TRIV = {}"
      by (auto simp: \<B>_def \<S>_def TRIV_def Step_class_def)
    show thesis
    proof
      have "card (Bseq \<mu> l k i) = (\<Sum>j \<in> \<B> \<union> \<S> \<union> TRIV. b j)"
        using card_Bseq_sum eq unfolding b_def by metis
      also have "\<dots> = (\<Sum>j\<in>\<B>. b j) + (\<Sum>j\<in>\<S>. b j) + (\<Sum>j\<in>TRIV. b j)"
        by (simp add: sum_Un_nat \<open>finite \<B>\<close> \<open>finite \<S>\<close> \<open>finite TRIV\<close> dis)
      also have "\<dots> = sum b \<B> + card \<S>"
      proof -
        have "sum b \<S> = card \<S>"
          by (simp add: b_def \<S>_def card_Bdelta_dboost_step)
        moreover have "sum b TRIV = 0"
          by (simp add: b_def TRIV_def Bdelta_trivial_step)
        ultimately show ?thesis
          by simp
      qed
      finally show "card (Bseq \<mu> l k i) = sum b \<B> + card \<S>" .
    qed
  qed
  then have sum_b_\<B>: "sum b \<B> \<le> l - card \<S>"
    by (metis less_diff_conv less_imp_le_nat Bseq_less_l [OF \<open>Colours l k\<close>])
  have "real (card \<B>) \<le> real k powr (3/4)"
    using card\<B> \<open>l\<le>k\<close> by (smt (verit) divide_nonneg_nonneg of_nat_0_le_iff of_nat_mono powr_mono2)
  then have "2 powr (f k) \<le> (1/2) ^ card \<B>"
    by (simp add: f_def powr_minus divide_simps flip: powr_realpow)
  then have "2 powr (f k) * \<mu> ^ (l - card \<S>) \<le> (1/2) ^ card \<B> * \<mu> ^ (l - card \<S>)"
    by (simp add: \<mu>)
  also have "(1/2) ^ card \<B> * \<mu> ^ (l - card \<S>) \<le> (1/2) ^ card \<B> * \<mu> ^ (sum b \<B>)" 
    using \<mu> sum_b_\<B> by simp
  also have "\<dots> = (\<Prod>i\<in>\<B>. \<mu> ^ b i / 2)"
    by (simp add: power_sum prod_dividef divide_simps)
  also have "\<dots> \<le> (\<Prod>i\<in>\<B>. card (X (Suc i)) / card (X i))"
  proof (rule prod_mono)
    fix i :: nat
    assume "i \<in> \<B>"
    then have "\<not> termination_condition l k (X i) (Yseq \<mu> l k i)"
      using step_non_terminating by (simp add: \<B>_def X_def Step_class_def)
    then have "card (X i) \<noteq> 0"
      using termination_condition_def by force
    with \<open>i\<in>\<B>\<close> \<mu> show "0 \<le> \<mu> ^ b i / 2 \<and> \<mu> ^ b i / 2 \<le> real (card (X (Suc i))) / real (card (X i))"
      by (force simp: b_def \<B>_def X_def divide_simps dest!: Bdelta_bblue_step)
  qed
  finally show ?thesis .
qed

subsection \<open>Lemma 7.5\<close>

definition 
  "Big_X_7_5 \<equiv> 
    \<lambda>\<mu> l. Lemma_Step_class_halted_nonempty \<mu> l \<and> Lemma_bblue_dboost_step_limit \<mu> l
        \<and> Lemma_bblue_step_limit \<mu> l \<and> Lemma_Y_6_4_dbooSt \<mu> l \<and> Lemma_Y_6_5_Bblue \<mu> l
        \<and> (\<forall>k\<ge>l. Lemma_height_upper_bound k \<and> k\<ge>16 \<and> (2 * ln k / eps k + 2 * k powr (7/8) \<le> k))"

text \<open>establishing the size requirements for 7.5\<close>
lemma Big_X_7_5:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_X_7_5 \<mu> l"
proof -
  have [simp]: "Ex ((\<le>) l)" for l::nat
    by auto
  have A: "\<forall>\<^sup>\<infinity>l. 2 * ln l / eps l + 2 * real l powr (7/8) \<le> l" 
    unfolding eps_def by real_asymp
  show ?thesis
    unfolding Big_X_7_5_def using assms eventually_all_ge_at_top [OF height_upper_bound]
    by (simp add: eventually_conj_iff Step_class_halted_nonempty bblue_dboost_step_limit 
        bblue_step_limit Y_6_4_dbooSt Y_6_5_Bblue height_upper_bound A eventually_all_ge_at_top)
qed

lemma X_7_5_aux:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  assumes "Colours l k" 
  defines "\<S> \<equiv> Step_class \<mu> l k {dboost_step}"
  defines "\<S>\<S> \<equiv> dboost_star \<mu> l k"
  assumes big: "Big_X_7_5 \<mu> l"
  shows "card (\<S>\<setminus>\<S>\<S>) \<le> 3 * eps k powr (1/4) * k"
proof -
  define \<D> where "\<D> \<equiv> Step_class \<mu> l k {dreg_step}"
  define \<R> where "\<R> \<equiv> Step_class \<mu> l k {red_step}"
  define \<B> where "\<B> \<equiv> Step_class \<mu> l k {bblue_step}"
  define \<H> where "\<H> \<equiv> Step_class \<mu> l k {halted}"
  define p where "p \<equiv> pee \<mu> l k"
  define m where "m \<equiv> Inf \<H>"
  define h where "h \<equiv> \<lambda>i. real (hgt k (p i))"
  have \<S>\<S>: "\<S>\<S> = {i \<in> \<S>. h(Suc i) - h i \<le> eps k powr (-1/4)}" and "\<S>\<S> \<subseteq> \<S>"
    by (auto simp add: \<S>\<S>_def \<S>_def dboost_star_def p_def h_def)
  have in_S: "h(Suc i) - h i > eps k powr (-1/4)" if "i \<in> \<S>\<setminus>\<S>\<S>" for i
    using that by (fastforce simp add: \<S>\<S>)
  have odd: "odd i" if "i \<in> \<R> \<or> i \<in> \<S>" for i
    using that unfolding \<R>_def \<S>_def by (metis Step_class_insert UnCI step_odd)
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  then have halt: "Lemma_Step_class_halted_nonempty \<mu> l" 
      and BS_limit: "Lemma_bblue_dboost_step_limit \<mu> l"
      and B_limit: "Lemma_bblue_step_limit \<mu> l"
      and Y64S: "Lemma_Y_6_4_dbooSt \<mu> l"
      and Y65B: "Lemma_Y_6_5_Bblue \<mu> l"
      and hub: "Lemma_height_upper_bound k"
      and 16: "k\<ge>16" (*for Y_6_5_Red*)
      and fg: "2 * ln k / eps k + 2 * k powr (7/8) \<le> k"
    using big by (auto simp: Big_X_7_5_def)
  have "finite \<R>"
    using \<mu> \<open>Colours l k\<close> red_step_limit by (auto simp: \<R>_def)
  have "finite \<B>"
    using B_limit \<open>Colours l k\<close> by (simp add: Lemma_bblue_step_limit_def \<B>_def)
  have "finite \<S>"
    using BS_limit by (simp add: Lemma_bblue_dboost_step_limit_def \<S>_def \<open>Colours l k\<close>)
  have [simp]: "\<R> \<inter> \<S> = {}" "\<B> \<inter> (\<R> \<union> \<S>) = {}"
    by (auto simp add: \<R>_def \<S>_def \<B>_def Step_class_def)
  have "Step_class \<mu> l k {halted} \<noteq> {}"
    using halt \<open>Colours l k\<close> by (simp add: Lemma_Step_class_halted_nonempty_def)
  then have "\<H> \<noteq> {}"
    using \<H>_def by blast
  then have "m \<in> \<H>"
    by (simp add: Inf_nat_def1 m_def)
  then have m_minimal: "i \<notin> \<H> \<longleftrightarrow> i < m" for i
    by (metis Step_class_halted_forever \<H>_def m_def linorder_not_le wellorder_Inf_le1)

  define f where "f \<equiv> \<lambda>k. 2 * ln k / eps k"  \<comment> \<open>a small bound for a summation\<close>
  have oddset: "{..<m} \<setminus> \<D> = {i \<in> {..<m}. odd i}" 
    using m_minimal step_odd step_even not_halted_even_dreg 
    by (auto simp: \<D>_def \<H>_def Step_class_insert_NO_MATCH)
  have "(\<Sum>i<m. h(Suc i) - h i) = h m - h 0" 
    by (simp add: sum_lessThan_telescope)
  also have "\<dots> \<le> f k"
  proof -
    have "hgt k (p i) \<ge> 1" for i
      by (simp add: Suc_leI hgt_gt_0)
    moreover have "hgt k (p m) \<le> f k"
      using hub p_def pee_le1 unfolding f_def Lemma_height_upper_bound_def by blast 
    ultimately show ?thesis
      by (simp add: h_def)
  qed
  finally have 25: "(\<Sum>i<m. h(Suc i) - h i) \<le> f k" .
      \<comment> \<open>working on 27\<close>
  obtain cardss:  "card \<S>\<S> \<le> card \<S>" "card (\<S>\<setminus>\<S>\<S>) = card \<S> - card \<S>\<S>"
    by (meson \<open>\<S>\<S> \<subseteq> \<S>\<close> \<open>finite \<S>\<close> card_Diff_subset card_mono infinite_super)
  have "(\<Sum>i \<in> \<S>. h(Suc i) - h(i-1)) \<ge> eps k powr (-1/4) * card (\<S>\<setminus>\<S>\<S>)"
  proof -
    have "(\<Sum>i \<in> \<S>\<setminus>\<S>\<S>. h(Suc i) - h(i-1)) \<ge> (\<Sum>i \<in> \<S>\<setminus>\<S>\<S>. eps k powr (-1/4))"
    proof (rule sum_mono)
      fix i :: nat
      assume i: "i \<in> \<S>\<setminus>\<S>\<S>"
      with i odd have "i-1 \<in> \<D>"       
        by (simp add: \<S>_def \<D>_def dreg_before_step Step_class_insert_NO_MATCH)
      with i odd show "eps k powr (-1/4) \<le> h(Suc i) - h(i-1)"
        using in_S[of i] Y_6_5_DegreeReg[of "i-1" \<mu> l k] \<open>k>0\<close>
        by (simp add: p_def \<D>_def h_def)
    qed
    moreover
    have "(\<Sum>i \<in> \<S>\<S>. h(Suc i) - h(i-1)) \<ge> 0"
      using Y64S \<open>Colours l k\<close> \<open>k>0\<close>  
      by (force simp add: Lemma_Y_6_4_dbooSt_def p_def h_def \<S>\<S> \<S>_def hgt_mono intro: sum_nonneg)
    ultimately show ?thesis
      by (simp add: mult.commute sum.subset_diff [OF \<open>\<S>\<S> \<subseteq> \<S>\<close> \<open>finite \<S>\<close>])
  qed
  moreover
  have "(\<Sum>i \<in> \<R>. h(Suc i) - h(i-1)) \<ge> (\<Sum>i \<in> \<R>. -2)"
  proof (rule sum_mono)
    fix i :: nat
    assume i: "i \<in> \<R>"
    with i odd have "i-1 \<in> \<D>"       
      by (simp add: \<R>_def \<D>_def dreg_before_step Step_class_insert_NO_MATCH)
    with i odd have "hgt k (p (i - 1)) - 2 \<le> hgt k (p (Suc i))"
      using Y_6_5_Red[of i] 16 Y_6_5_DegreeReg[of "i-1"]
      by (fastforce simp: algebra_simps \<R>_def \<D>_def p_def)
    then show "- 2 \<le> h(Suc i) - h(i-1)"
      unfolding h_def by linarith
  qed
  ultimately have 27: "(\<Sum>i \<in> \<R>\<union>\<S>. h(Suc i) - h(i-1)) \<ge> eps k powr (-1/4) * card (\<S>\<setminus>\<S>\<S>) - 2 * card \<R>"
    by (simp add: sum.union_disjoint \<open>finite \<R>\<close> \<open>finite \<S>\<close>)
      \<comment> \<open>working on 28\<close>
  define g where "g \<equiv> \<lambda>k. -2 * real k powr (7/8)"  \<comment> \<open>a small bound for a summation\<close>
  have "g k \<le> -2 * eps k powr (-1/2) * card \<B>"
  proof -
    have "k powr (1/8) * card \<B> \<le> k powr (1/8) * l powr (3/4)"
      using B_limit \<open>Colours l k\<close>
      by (simp add: Lemma_bblue_step_limit_def \<B>_def mult_left_mono)
    also have "... \<le> k powr (1/8) * k powr (3/4)"
      by (simp add: \<open>l\<le>k\<close> mult_mono powr_mono2)
    also have "... = k powr (7/8)"
      by (simp flip: powr_add)
    finally show ?thesis
      by (simp add: eps_def powr_powr g_def)
  qed
  also have "\<dots> \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
  proof -
    have "(\<Sum>i \<in> \<B>. -2 * eps k powr (-1/2)) \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
    proof (rule sum_mono)
      fix i :: nat
      assume i: "i \<in> \<B>"
      show "-2 * eps k powr (-1/2) \<le> h(Suc i) - h(i-1)"
        using Y65B \<open>Colours l k\<close> \<open>l\<le>k\<close> \<open>k>0\<close> i
        by (fastforce simp add: Lemma_Y_6_5_Bblue_def p_def \<B>_def h_def)
    qed
    then show ?thesis 
      by (simp add: mult.commute)
  qed
  finally have 28: "g k \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))" .
  with 27
  have "g k + (eps k powr (-1/4) * card (\<S>\<setminus>\<S>\<S>) - 2 * card \<R>) \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1)) + (\<Sum>i \<in> \<R>\<union>\<S>. h(Suc i) - h(i-1))"
    by simp
  also have "\<dots> = (\<Sum>i \<in> \<B> \<union> (\<R>\<union>\<S>). h(Suc i) - h(i-1))"
    by (simp add: \<open>finite \<B>\<close> \<open>finite \<R>\<close> \<open>finite \<S>\<close> sum.union_disjoint)
  also have "\<dots> = (\<Sum>i \<in> {..<m} \<setminus> \<D>. h(Suc i) - h(i-1))"
  proof -
    have "i \<in> \<B> \<union> (\<R>\<union>\<S>)" if "i<m" "i \<notin> \<D>" for i
      using that unfolding \<D>_def \<B>_def \<R>_def \<S>_def
      by (metis Step_class_insert not_halted_even_dreg not_halted_odd_RBS Un_iff \<H>_def m_minimal)
    moreover
    have "i \<in> {..<m} \<setminus> \<D>" if "i \<in> \<B> \<union> (\<R>\<union>\<S>)" for i
      using that by (auto simp: \<D>_def \<B>_def \<R>_def \<S>_def \<H>_def Step_class_def simp flip: m_minimal)
    ultimately have "\<B> \<union> (\<R>\<union>\<S>) = {..<m} \<setminus> \<D>"
      by auto
    then show ?thesis
      by simp
  qed
  also have "\<dots> \<le> h m - h 0"
  proof (cases "even m")
    case True
    then show ?thesis
      by (simp add: oddset sum_odds_even)
  next
    case False
    have "hgt k (p (m - Suc 0)) \<le> hgt k (p m)"
      using Y_6_5_DegreeReg [of "m-1"] \<open>k>0\<close> False m_minimal not_halted_even_dreg odd_pos  
      by (fastforce simp: p_def \<H>_def)
    then have "h(m - Suc 0) \<le> h m"
      using h_def of_nat_mono by blast
    with False show ?thesis
      by (simp add: oddset sum_odds_odd)
  qed
  also have "... = (\<Sum>i<m. h(Suc i) - h i)"
    by (simp add: sum_lessThan_telescope)
  finally have "g k + (eps k powr (-1/4) * card (\<S>\<setminus>\<S>\<S>) - real (2 * card \<R>)) \<le> (\<Sum>i<m. h (Suc i) - h i)" .
  then have "g k + (eps k powr (-1/4) * real (card (\<S> \<setminus> \<S>\<S>)) - real (2 * card \<R>)) \<le> f k"
    using 25 by linarith
  then have "real (card (\<S> \<setminus> \<S>\<S>)) \<le> (f k - g k + 2 * card \<R>) * eps k powr (1/4)"
    using eps_gt0 [OF \<open>k>0\<close>]
    by (simp add: powr_minus field_simps del: div_add div_mult_self3)
  moreover have "f k - g k \<le> k"
    using fg by (simp add: f_def g_def)
  moreover have "card \<R> < k"
    using red_step_limit \<mu> \<open>Colours l k\<close> unfolding \<R>_def by blast
  ultimately have "card (\<S>\<setminus>\<S>\<S>) \<le> (k + 2 * k) * eps k powr (1/4)"
    by (smt (verit, best) of_nat_add mult_2 mult_diff_mult nat_less_real_le pos_prod_lt powr_ge_pzero)
  then show ?thesis
    by (simp add: algebra_simps)
qed

proposition X_7_5:
  assumes "0<\<mu>" "\<mu><1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> card (Step_class \<mu> l k {dboost_step} \<setminus> dboost_star \<mu> l k) 
                \<le> 3 * eps k powr (1/4) * k"
  using assms
    by (rule eventually_mono [OF Big_X_7_5]) (intro X_7_5_aux strip, auto simp: assms)

subsection \<open>Lemma 7.4\<close>

definition 
  "Big_X_7_4 \<equiv> 
    \<lambda>\<mu> l. Lemma_bblue_dboost_step_limit \<mu> l \<and> Lemma_Red_5_3 \<mu> l \<and> Big_X_7_5 \<mu> l
        \<and> Lemma_beta_gt_0 \<mu> l"

lemma X_7_4_aux:
  fixes l k
  defines "f \<equiv> \<lambda>k. 6 * eps k powr (1/4) * k * ln k / ln 2"
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  assumes "Colours l k" 
  defines "X \<equiv> Xseq \<mu> l k"
  defines "\<S> \<equiv> Step_class \<mu> l k {dboost_step}"
  assumes big: "Big_X_7_4 \<mu> l"
  shows "(\<Prod>i\<in>\<S>. card (X (Suc i)) / card (X i)) \<ge> 2 powr f k * bigbeta \<mu> l k ^ card \<S>"
proof -
  define \<S>\<S> where "\<S>\<S> \<equiv> dboost_star \<mu> l k"
  define p where "p \<equiv> pee \<mu> l k"
  have X75: "card (\<S>\<setminus>\<S>\<S>) \<le> 3 * eps k powr (1/4) * k" 
  and R53:  "\<And>i. i \<in> \<S> \<Longrightarrow> p (Suc i) \<ge> p i \<and> beta \<mu> l k i \<ge> 1 / (real k)\<^sup>2"
    using X_7_5_aux assms by (auto simp: Big_X_7_4_def Lemma_Red_5_3_def p_def \<S>_def \<S>\<S>_def)
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  then have BS_limit: "Lemma_bblue_dboost_step_limit \<mu> l" 
    and "Lemma_beta_gt_0 \<mu> l"
    using big by (auto simp: Big_X_7_4_def)
  then have beta_gt_0: "\<forall>i\<in>\<S>. 0 < beta \<mu> l k i"
    by (simp add: Lemma_beta_gt_0_def \<S>_def \<open>Colours l k\<close>)
  have "finite \<S>"
    using BS_limit 
    by (simp add: Lemma_bblue_dboost_step_limit_def \<S>_def \<open>Colours l k\<close>)
  then have "finite \<S>\<S>"
    unfolding \<S>\<S>_def \<S>_def dboost_star_def by auto
  have \<beta>: "beta \<mu> l k i = card (X (Suc i)) / card (X i)" if "i \<in> \<S>" for i
  proof -
    have "X (Suc i) = Neighbours Blue (cvx \<mu> l k i) \<inter> X i"
      using that unfolding \<S>_def X_def
      by (auto simp add: step_kind_defs next_state_def cvx_def Let_def split: prod.split)
    then show ?thesis
      by (force simp add: X_def beta_eq)
  qed
  then have A: "(\<Prod>i\<in>\<S>. card (X (Suc i)) / card (X i)) = (\<Prod>i\<in>\<S>. beta \<mu> l k i)"
    by force
  \<comment> \<open>bounding the immoderate steps\<close>
  have "(\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. 1 / beta \<mu> l k i) \<le> (\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. real k ^ 2)"
  proof (rule prod_mono)
    fix i
    assume i: "i \<in> \<S> \<setminus> \<S>\<S>"
    with R53 \<open>k>0\<close> beta_ge0 [of \<mu> l k i]
    show "0 \<le> 1 / beta \<mu> l k i \<and> 1 / beta \<mu> l k i \<le> (real k)\<^sup>2"
      by (force simp: R53 divide_simps mult.commute)
  qed
  then have "(\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. 1 / beta \<mu> l k i) \<le> real k ^ (2 * card(\<S>\<setminus>\<S>\<S>))"
    by (simp add: power_mult)
  also have "... = real k powr (2 * card(\<S>\<setminus>\<S>\<S>))"
    by (metis \<open>k>0\<close> of_nat_0_less_iff powr_realpow)
  also have "... \<le> k powr (2 * 3 * eps k powr (1/4) * k)"
    using X75 \<open>k>0\<close> by (intro powr_mono; linarith) 
  also have "... \<le> exp (6 * eps k powr (1/4) * k * ln k)"
    by (simp add: powr_def)
  also have "... = 2 powr f k"
    by (simp add: f_def powr_def)
  finally have B: "(\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. 1 / beta \<mu> l k i) \<le> 2 powr f k" .
  have "f \<in> o(real)"
    unfolding eps_def f_def by real_asymp
  show ?thesis
  proof (cases "\<S>\<S> = {}")
  \<comment> \<open>bounding the moderate steps\<close>
    case True
    with B have "(\<Prod>i\<in>\<S>. 1 / beta \<mu> l k i) \<le> 2 powr f k"
      by simp
    with True \<mu> beta_gt_0 show ?thesis
      apply (simp add: bigbeta_def \<S>\<S>_def A)
      apply (simp add: prod_dividef divide_simps split: if_split_asm)
        defer
      using prod_pos apply force
      using Groups_Big.linordered_semidom_class.prod_pos apply blast
      apply (rule order_trans)

      sorry
  next
    case False
    then show ?thesis sorry
  qed  
  have "\<S>\<S> \<noteq> {}"
    sorry
  then have "card \<S>\<S> > 0"
    using \<open>finite \<S>\<S>\<close> card_0_eq by blast
  have "(\<Prod>i\<in>\<S>\<S>. 1 / beta \<mu> l k i) powr (1 / card \<S>\<S>) \<le> (\<Sum>i\<in>\<S>\<S>. 1 / beta \<mu> l k i / card \<S>\<S>)"
  proof (rule arith_geom_mean [OF \<open>finite \<S>\<S>\<close> \<open>\<S>\<S> \<noteq> {}\<close>])
    show "\<And>i. i \<in> \<S>\<S> \<Longrightarrow> 0 \<le> 1 / beta \<mu> l k i"
      by (simp add: beta_ge0)
  qed
  then have "((\<Prod>i\<in>\<S>\<S>. 1 / beta \<mu> l k i) powr (1 / card \<S>\<S>)) powr (card \<S>\<S>) 
          \<le> (\<Sum>i\<in>\<S>\<S>. 1 / beta \<mu> l k i / card \<S>\<S>) powr (card \<S>\<S>)"
    using powr_mono2 by auto
  with \<open>card \<S>\<S> > 0\<close> 
  have "(\<Prod>i\<in>\<S>\<S>. 1 / beta \<mu> l k i) \<le> (\<Sum>i\<in>\<S>\<S>. 1 / beta \<mu> l k i / card \<S>\<S>) powr (card \<S>\<S>)"
    by (simp add: powr_powr beta_ge0 prod_nonneg)
  also have "... \<le> (1 / (card \<S>\<S>) * (\<Sum>i\<in>\<S>\<S>. 1 / beta \<mu> l k i)) powr (card \<S>\<S>)"
    using \<open>card \<S>\<S> > 0\<close> by (simp add: field_simps sum_divide_distrib)
  also have "... \<le> bigbeta \<mu> l k powr (- (card \<S>\<S>))"
    using \<open>\<S>\<S> \<noteq> {}\<close> \<open>card \<S>\<S> > 0\<close> 
    apply (simp add: bigbeta_def divide_simps powr_minus flip: \<S>\<S>_def)
    apply (simp add: powr_divide beta_ge0 sum_nonneg)
    done
  finally have "(\<Prod>i\<in>\<S>\<S>. 1 / beta \<mu> l k i) \<le> bigbeta \<mu> l k powr (- (card \<S>\<S>))" .

  show ?thesis
    sorry
qed

end (*context Diagonal*)

end

