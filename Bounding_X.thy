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

lemma bigbeta_ge0:
  assumes \<mu>: "0<\<mu>"  
  shows "bigbeta \<mu> l k \<ge> 0"
  using assms by (simp add: bigbeta_def Let_def beta_ge0 sum_nonneg)

lemma bigbeta_gt0:
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
        by (auto simp: bigbeta_def Let_def zero_less_mult_iff card_gt_0_iff dboost_star_def intro!: sum_pos)
    qed
  }
  then show ?thesis
    using eventually_mono [OF eventually_conj [OF beta_gt_0 [OF assms] bblue_dboost_step_limit [OF \<open>\<mu>>0\<close>]]]
    unfolding Lemma_bblue_dboost_step_limit_def Lemma_beta_gt_0_def
    by presburger
qed


lemma bigbeta_less1:
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
      also have "\<dots>  < (\<Sum>i\<in>dboost_star \<mu> l k. 1 / beta \<mu> l k i)"
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
    unfolding Lemma_bblue_dboost_step_limit_def Lemma_beta_gt_0_def
    by presburger
qed

subsection \<open>Lemma 7.2\<close>

lemma X_7_2:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  defines "f \<equiv> \<lambda>k. (real k / ln 2) * ln (1 - 1 / (k * (1-\<mu>)))"
  defines "X \<equiv> Xseq \<mu> l k"
  assumes big: "nat \<lceil>real l powr (3/4)\<rceil> \<ge> 3" "k\<ge>2" "k > 1 / (1-\<mu>)"
  assumes "Colours l k" and fin_red: "finite (Step_class \<mu> l k {red_step})"
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
      using * step \<open>S \<subseteq> X\<close> by (auto simp: Bdelta_def Bseq_def disjnt_iff)
    show "\<mu> ^ card S * real (card (Xseq \<mu> l k i)) / 2 \<le> real (card (Xseq \<mu> l k (Suc i)))"
      using * by (auto simp: Xseq_def good_blue_book_def step)
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
    by (auto simp: step_kind_defs next_state_def Let_def split: if_split_asm)
  moreover have "choose_central_vx \<mu> (X,Y,A,B) \<notin> B"
    using valid cvx by (force simp: valid_state_def disjoint_state_def disjnt_iff)
  ultimately show ?thesis
    using step cvx by (auto simp: Bdelta_def Bseq_def disjnt_iff Xseq_def)
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
        by (auto simp: i_def TRIV_def \<open>finite \<B>\<close> \<open>finite \<S>\<close> less_Suc_eq_le)
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

text \<open>Small $o(k)$ bounds on summations for this section\<close>

definition "ok_fun_26 \<equiv> \<lambda>k. 2 * ln k / eps k" 

definition "ok_fun_28 \<equiv> \<lambda>k. -2 * real k powr (7/8)"  

lemma ok_fun_26: "ok_fun_26 \<in> o(real)" and ok_fun_28: "ok_fun_28 \<in> o(real)"
  unfolding ok_fun_26_def ok_fun_28_def eps_def by real_asymp+

definition 
  "Big_X_7_5 \<equiv> 
    \<lambda>\<mu> l. Lemma_Step_class_halted_nonempty \<mu> l \<and> Lemma_bblue_dboost_step_limit \<mu> l
        \<and> Lemma_bblue_step_limit \<mu> l \<and> Lemma_Y_6_4_dbooSt \<mu> l \<and> Lemma_Y_6_5_Bblue \<mu> l
        \<and> (\<forall>k\<ge>l. Lemma_height_upper_bound k \<and> k\<ge>16 \<and> (ok_fun_26 k - ok_fun_28 k \<le> k))"

text \<open>establishing the size requirements for 7.5\<close>
lemma Big_X_7_5:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_X_7_5 \<mu> l"
proof -
  have "\<forall>\<^sup>\<infinity>l. ok_fun_26 l - ok_fun_28 l \<le> l" 
    unfolding eps_def ok_fun_26_def ok_fun_28_def by real_asymp
  then show ?thesis
    unfolding Big_X_7_5_def using assms eventually_all_ge_at_top [OF height_upper_bound]
    by (simp add: eventually_conj_iff Step_class_halted_nonempty bblue_dboost_step_limit 
        bblue_step_limit Y_6_4_dbooSt Y_6_5_Bblue height_upper_bound eventually_all_ge_at_top)
qed


lemma X_26_and_28:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  assumes "Colours l k" 
  assumes big: "Big_X_7_5 \<mu> l"
  defines "\<D> \<equiv> Step_class \<mu> l k {dreg_step}"
  defines "\<B> \<equiv> Step_class \<mu> l k {bblue_step}"
  defines "\<H> \<equiv> Step_class \<mu> l k {halted}"
  defines "m \<equiv> Inf \<H>"
  defines "p \<equiv> pee \<mu> l k"
  defines "h \<equiv> \<lambda>i. real (hgt k (p i))"
  obtains "(\<Sum>i\<in>{..<m} \<setminus> \<D>. h (Suc i) - h (i-1)) \<le> ok_fun_26 k"
          "ok_fun_28 k \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
proof -
  define \<R> where "\<R> \<equiv> Step_class \<mu> l k {red_step}"
  define \<S> where "\<S> \<equiv> Step_class \<mu> l k {dboost_step}" 
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  then have "Lemma_Step_class_halted_nonempty \<mu> l" 
    and B_limit: "Lemma_bblue_step_limit \<mu> l"
    and Y65B: "Lemma_Y_6_5_Bblue \<mu> l"
    and hub: "Lemma_height_upper_bound k"
    using big by (auto simp: Big_X_7_5_def)
  then have "m \<in> \<H>"
    using \<H>_def \<open>Colours l k\<close> 
    by (simp add: Inf_nat_def1 m_def Lemma_Step_class_halted_nonempty_def)
  then have m_minimal: "i \<notin> \<H> \<longleftrightarrow> i < m" for i
    by (metis Step_class_halted_forever \<H>_def m_def linorder_not_le wellorder_Inf_le1)
  have oddset: "{..<m} \<setminus> \<D> = {i \<in> {..<m}. odd i}" 
    using m_minimal step_odd step_even not_halted_even_dreg 
    by (auto simp: \<D>_def \<H>_def Step_class_insert_NO_MATCH)
      \<comment> \<open>working on 28\<close>
  have "ok_fun_28 k \<le> -2 * eps k powr (-1/2) * card \<B>"
  proof -
    have "k powr (1/8) * card \<B> \<le> k powr (1/8) * l powr (3/4)"
      using B_limit \<open>Colours l k\<close>
      by (simp add: Lemma_bblue_step_limit_def \<B>_def mult_left_mono)
    also have "\<dots> \<le> k powr (1/8) * k powr (3/4)"
      by (simp add: \<open>l\<le>k\<close> mult_mono powr_mono2)
    also have "\<dots> = k powr (7/8)"
      by (simp flip: powr_add)
    finally show ?thesis
      by (simp add: eps_def powr_powr ok_fun_28_def)
  qed
  also have "\<dots> \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
  proof -
    have "(\<Sum>i \<in> \<B>. -2 * eps k powr (-1/2)) \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
    proof (rule sum_mono)
      fix i :: nat
      assume i: "i \<in> \<B>"
      show "-2 * eps k powr (-1/2) \<le> h(Suc i) - h(i-1)"
        using Y65B \<open>Colours l k\<close> \<open>l\<le>k\<close> \<open>k>0\<close> i
        by (fastforce simp: Lemma_Y_6_5_Bblue_def p_def \<B>_def h_def)
    qed
    then show ?thesis 
      by (simp add: mult.commute)
  qed
  finally have 28: "ok_fun_28 k \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))" .
  have "(\<Sum>i \<in> {..<m} \<setminus> \<D>. h(Suc i) - h(i-1)) \<le> h m - h 0"
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
  also have "\<dots> = (\<Sum>i<m. h(Suc i) - h i)"
    by (simp add: sum_lessThan_telescope)
  also have "\<dots> = h m - h 0" 
    by (simp add: sum_lessThan_telescope)
  also have "\<dots> \<le> ok_fun_26 k"
  proof -
    have "hgt k (p i) \<ge> 1" for i
      by (simp add: Suc_leI hgt_gt_0)
    moreover have "hgt k (p m) \<le> ok_fun_26 k"
      using hub p_def pee_le1 unfolding ok_fun_26_def Lemma_height_upper_bound_def by blast 
    ultimately show ?thesis
      by (simp add: h_def)
  qed
  finally have 26: "(\<Sum>i\<in>{..<m} \<setminus> \<D>. h (Suc i) - h (i-1)) \<le> ok_fun_26 k" .
  with 28 show ?thesis
    using that by blast
qed

lemma X_7_5_aux:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  assumes "Colours l k" 
  defines "\<S> \<equiv> Step_class \<mu> l k {dboost_step}" and "\<S>\<S> \<equiv> dboost_star \<mu> l k"
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
  obtain 26: "(\<Sum>i\<in>{..<m} \<setminus> \<D>. h (Suc i) - h (i-1)) \<le> ok_fun_26 k"
     and 28: "ok_fun_28 k \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
    unfolding \<B>_def \<D>_def \<H>_def h_def m_def p_def
    using X_26_and_28 assms(1-3) big by blast

  have \<S>\<S>: "\<S>\<S> = {i \<in> \<S>. h(Suc i) - h i \<le> eps k powr (-1/4)}" and "\<S>\<S> \<subseteq> \<S>"
    by (auto simp: \<S>\<S>_def \<S>_def dboost_star_def p_def h_def)
  have in_S: "h(Suc i) - h i > eps k powr (-1/4)" if "i \<in> \<S>\<setminus>\<S>\<S>" for i
    using that by (fastforce simp: \<S>\<S>)
  have odd: "odd i" if "i \<in> \<R> \<or> i \<in> \<S>" for i
    using that unfolding \<R>_def \<S>_def by (metis Step_class_insert UnCI step_odd)
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  then have "Lemma_Step_class_halted_nonempty \<mu> l" 
      and BS_limit: "Lemma_bblue_dboost_step_limit \<mu> l"
      and B_limit: "Lemma_bblue_step_limit \<mu> l"
      and Y64S: "Lemma_Y_6_4_dbooSt \<mu> l"
      and 16: "k\<ge>16" (*for Y_6_5_Red*)
      and ok_fun: "ok_fun_26 k - ok_fun_28 k \<le> k"
    using big by (auto simp: Big_X_7_5_def)
  then have "m \<in> \<H>"
    using \<H>_def \<open>Colours l k\<close> 
    by (simp add: Inf_nat_def1 m_def Lemma_Step_class_halted_nonempty_def)
  then have m_minimal: "i \<notin> \<H> \<longleftrightarrow> i < m" for i
    by (metis Step_class_halted_forever \<H>_def m_def linorder_not_le wellorder_Inf_le1)
  have "finite \<R>"
    using \<mu> \<open>Colours l k\<close> red_step_limit by (auto simp: \<R>_def)
  have "finite \<B>"
    using B_limit \<open>Colours l k\<close> by (simp add: Lemma_bblue_step_limit_def \<B>_def)
  have "finite \<S>"
    using BS_limit by (simp add: Lemma_bblue_dboost_step_limit_def \<S>_def \<open>Colours l k\<close>)
  have [simp]: "\<R> \<inter> \<S> = {}" "\<B> \<inter> (\<R>\<union>\<S>) = {}"
    by (auto simp: \<R>_def \<S>_def \<B>_def Step_class_def)

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
      by (force simp: Lemma_Y_6_4_dbooSt_def p_def h_def \<S>\<S> \<S>_def hgt_mono intro: sum_nonneg)
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
    with i odd have "hgt k (p (i-1)) - 2 \<le> hgt k (p (Suc i))"
      using Y_6_5_Red[of i] 16 Y_6_5_DegreeReg[of "i-1"]
      by (fastforce simp: algebra_simps \<R>_def \<D>_def p_def)
    then show "- 2 \<le> h(Suc i) - h(i-1)"
      unfolding h_def by linarith
  qed
  ultimately have 27: "(\<Sum>i \<in> \<R>\<union>\<S>. h(Suc i) - h(i-1)) \<ge> eps k powr (-1/4) * card (\<S>\<setminus>\<S>\<S>) - 2 * card \<R>"
    by (simp add: sum.union_disjoint \<open>finite \<R>\<close> \<open>finite \<S>\<close>)

  have "ok_fun_28 k + (eps k powr (-1/4) * card (\<S>\<setminus>\<S>\<S>) - 2 * card \<R>) \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1)) + (\<Sum>i \<in> \<R>\<union>\<S>. h(Suc i) - h(i-1))"
    using 27 28 by simp
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
  finally have "ok_fun_28 k + (eps k powr (-1/4) * card (\<S>\<setminus>\<S>\<S>) - real (2 * card \<R>)) \<le> ok_fun_26 k" 
    using 26 by simp
  then have "real (card (\<S> \<setminus> \<S>\<S>)) \<le> (ok_fun_26 k - ok_fun_28 k + 2 * card \<R>) * eps k powr (1/4)"
    using eps_gt0 [OF \<open>k>0\<close>]
    by (simp add: powr_minus field_simps del: div_add div_mult_self3)
  moreover have "card \<R> < k"
    using red_step_limit \<mu> \<open>Colours l k\<close> unfolding \<R>_def by blast
  ultimately have "card (\<S>\<setminus>\<S>\<S>) \<le> (k + 2 * k) * eps k powr (1/4)"
    by (smt (verit, best) ok_fun of_nat_add mult_2 mult_diff_mult nat_less_real_le pos_prod_lt powr_ge_pzero)
  then show ?thesis
    by (simp add: algebra_simps)
qed

definition 
  "Lemma_X_7_5 \<equiv> 
      \<lambda>\<mu> l. \<forall>k. Colours l k \<longrightarrow> card (Step_class \<mu> l k {dboost_step} \<setminus> dboost_star \<mu> l k) 
                \<le> 3 * eps k powr (1/4) * k"

proposition X_7_5:
  assumes "0<\<mu>" "\<mu><1" 
  shows "\<forall>\<^sup>\<infinity>l. Lemma_X_7_5 \<mu> l"
  using assms unfolding Lemma_X_7_5_def
    by (rule eventually_mono [OF Big_X_7_5]) (intro X_7_5_aux strip, auto simp: assms)

subsection \<open>Lemma 7.4\<close>

definition 
  "Big_X_7_4 \<equiv> 
    \<lambda>\<mu> l. Lemma_X_7_5 \<mu> l \<and> Lemma_bblue_dboost_step_limit \<mu> l \<and> Lemma_Red_5_3 \<mu> l
        \<and> Lemma_beta_gt_0 \<mu> l \<and> (\<forall>k. Colours l k \<longrightarrow> 0 < bigbeta \<mu> l k \<and> bigbeta \<mu> l k < 1)"

text \<open>establishing the size requirements for 7.4\<close>
lemma Big_X_7_4:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_X_7_4 \<mu> l"
proof -
  show ?thesis
    unfolding Big_X_7_4_def using assms eventually_all_ge_at_top [OF height_upper_bound]
    by (simp add: eventually_conj_iff all_imp_conj_distrib X_7_5 bblue_dboost_step_limit 
         Red_5_3 Y_6_5_Bblue height_upper_bound beta_gt_0 bigbeta_gt0 bigbeta_less1 eventually_all_ge_at_top)
qed

lemma X_7_4_aux:
  fixes l k
  defines "f \<equiv> \<lambda>k. -6 * eps k powr (1/4) * k * ln k / ln 2"
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  assumes "Colours l k" 
  assumes big: "Big_X_7_4 \<mu> l"
  defines "X \<equiv> Xseq \<mu> l k" and "\<S> \<equiv> Step_class \<mu> l k {dboost_step}"
  shows "(\<Prod>i\<in>\<S>. card (X (Suc i)) / card (X i)) \<ge> 2 powr f k * bigbeta \<mu> l k ^ card \<S>"
proof -
  define \<S>\<S> where "\<S>\<S> \<equiv> dboost_star \<mu> l k"
  define p where "p \<equiv> pee \<mu> l k"
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  then have BS_limit: "Lemma_bblue_dboost_step_limit \<mu> l" 
    and bigbeta_01: "0 < bigbeta \<mu> l k" "bigbeta \<mu> l k < 1"
    and "Lemma_beta_gt_0 \<mu> l" and X75: "card (\<S>\<setminus>\<S>\<S>) \<le> 3 * eps k powr (1/4) * k" 
    and R53:  "\<And>i. i \<in> \<S> \<Longrightarrow> p (Suc i) \<ge> p i \<and> beta \<mu> l k i \<ge> 1 / (real k)\<^sup>2"
    using big \<open>Colours l k\<close> 
    by (auto simp: Big_X_7_4_def Lemma_X_7_5_def Lemma_Red_5_3_def p_def \<S>_def \<S>\<S>_def)
  then have beta_gt_0: "\<forall>i\<in>\<S>. 0 < beta \<mu> l k i"
    by (simp add: Lemma_beta_gt_0_def \<S>_def \<open>Colours l k\<close>)
  have "finite \<S>"
    using BS_limit  by (simp add: Lemma_bblue_dboost_step_limit_def \<S>_def \<open>Colours l k\<close>)
  moreover have "\<S>\<S> \<subseteq> \<S>"
    unfolding \<S>\<S>_def \<S>_def dboost_star_def by auto
  ultimately have "finite \<S>\<S>"
    using finite_subset by auto
  have card_SSS: "card \<S>\<S> \<le> card \<S>"
    by (metis \<S>\<S>_def \<S>_def \<open>finite \<S>\<close> card_mono dboost_star_subset)
  have \<beta>: "beta \<mu> l k i = card (X (Suc i)) / card (X i)" if "i \<in> \<S>" for i
  proof -
    have "X (Suc i) = Neighbours Blue (cvx \<mu> l k i) \<inter> X i"
      using that unfolding \<S>_def X_def
      by (auto simp: step_kind_defs next_state_def cvx_def Let_def split: prod.split)
    then show ?thesis
      by (force simp: X_def beta_eq)
  qed
  then have *: "(\<Prod>i\<in>\<S>. card (X (Suc i)) / card (X i)) = (\<Prod>i\<in>\<S>. beta \<mu> l k i)"
    by force
  have prod_beta_gt_0: "prod (beta \<mu> l k) S' > 0" if "S' \<subseteq> \<S>" for S'
    using beta_gt_0 that
    by (force simp: beta_ge0 intro: prod_pos)
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
  also have "\<dots> = real k powr (2 * card(\<S>\<setminus>\<S>\<S>))"
    by (metis \<open>k>0\<close> of_nat_0_less_iff powr_realpow)
  also have "\<dots> \<le> k powr (2 * 3 * eps k powr (1/4) * k)"
    using X75 \<open>k>0\<close> by (intro powr_mono; linarith) 
  also have "\<dots> \<le> exp (6 * eps k powr (1/4) * k * ln k)"
    by (simp add: powr_def)
  also have "\<dots> = 2 powr -f k"
    by (simp add: f_def powr_def)
  finally have "(\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. 1 / beta \<mu> l k i) \<le> 2 powr -f k" .
  then have A: "(\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. beta \<mu> l k i) \<ge> 2 powr f k"
    using prod_beta_gt_0[of "\<S>\<setminus>\<S>\<S>"]
    by (simp add: powr_minus prod_dividef mult.commute divide_simps)
\<comment> \<open>bounding the moderate steps\<close>
  have "(\<Prod>i\<in>\<S>\<S>. 1 / beta \<mu> l k i) \<le> bigbeta \<mu> l k powr (- (card \<S>\<S>))"
  proof (cases "\<S>\<S> = {}")
    case True
    with bigbeta_01 show ?thesis by simp
  next
    case False
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
    also have "\<dots> \<le> (1 / (card \<S>\<S>) * (\<Sum>i\<in>\<S>\<S>. 1 / beta \<mu> l k i)) powr (card \<S>\<S>)"
      using \<open>card \<S>\<S> > 0\<close> by (simp add: field_simps sum_divide_distrib)
    also have "\<dots> \<le> bigbeta \<mu> l k powr (- (card \<S>\<S>))"
      using \<open>\<S>\<S> \<noteq> {}\<close> \<open>card \<S>\<S> > 0\<close> 
      apply (simp add: bigbeta_def divide_simps powr_minus flip: \<S>\<S>_def)
      apply (simp add: powr_divide beta_ge0 sum_nonneg)
      done
    finally show ?thesis .
  qed
  then have B: "(\<Prod>i\<in>\<S>\<S>. beta \<mu> l k i) \<ge> bigbeta \<mu> l k powr (card \<S>\<S>)"
    using prod_beta_gt_0[of "\<S>\<S>"] bigbeta_01
    by (simp add: \<open>\<S>\<S> \<subseteq> \<S>\<close> powr_minus prod_dividef mult.commute divide_simps)
  have "2 powr f k * bigbeta \<mu> l k powr card \<S> \<le> 2 powr f k * bigbeta \<mu> l k powr card \<S>\<S>"
    using bigbeta_01 card_SSS by (simp add: powr_mono')
  also have "\<dots> \<le> (\<Prod>i\<in>\<S>\<setminus>\<S>\<S>. beta \<mu> l k i) * (\<Prod>i\<in>\<S>\<S>. beta \<mu> l k i)"
    using beta_ge0 by (intro mult_mono A B) (auto simp: prod_nonneg)
  also have "\<dots> = (\<Prod>i\<in>\<S>. beta \<mu> l k i)"
    by (metis \<open>\<S>\<S> \<subseteq> \<S>\<close> \<open>finite \<S>\<close> prod.subset_diff)
  finally have "2 powr f k * bigbeta \<mu> l k powr real (card \<S>) \<le> prod (beta \<mu> l k) \<S>" .
  then show ?thesis
    by (simp add: "*" bigbeta_01 powr_realpow)
qed  

proposition X_7_4:
  assumes "0<\<mu>" "\<mu><1" 
  shows "\<exists>f \<in> o(\<lambda>k. real k).
     \<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> 
              (\<Prod>i \<in> Step_class \<mu> l k {dboost_step}. card (Xseq \<mu> l k (Suc i)) / card (Xseq \<mu> l k i)) 
            \<ge> 2 powr f k * bigbeta \<mu> l k ^ card (Step_class \<mu> l k {dboost_step})"
proof
  let ?f = "\<lambda>k. -6 * eps k powr (1/4) * k * ln k / ln 2"
  show "?f \<in> o(real)"
    unfolding eps_def by real_asymp
  show "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow>
               (\<Prod>i \<in> Step_class \<mu> l k {dboost_step}. card (Xseq \<mu> l k (Suc i)) / card (Xseq \<mu> l k i)) 
            \<ge> 2 powr ?f k * bigbeta \<mu> l k ^ card (Step_class \<mu> l k {dboost_step})"
    apply (rule eventually_mono [OF Big_X_7_4 [OF assms]])
    by (intro X_7_4_aux strip) (auto simp: assms)
qed

subsection \<open>Observation 7.7\<close>

lemma X_7_7:
  assumes "0<\<mu>" "\<mu><1" and "k>0" and i: "i \<in> Step_class \<mu> l k {dreg_step}"
  defines "X \<equiv> Xseq \<mu> l k"
  defines "p \<equiv> pee \<mu> l k"
  defines "q \<equiv> eps k powr (-1/2) * alpha k (hgt k (p i))"
  shows "p (Suc i) - p i \<ge> card (X i \<setminus> X (Suc i)) / card (X (Suc i)) * q \<and> card (X (Suc i)) > 0"
proof -
  have finX: "finite (X i)" for i
    using finite_Xseq X_def by blast
  define Y where "Y \<equiv> Yseq \<mu> l k"
  have "X (Suc i) = {x \<in> X i. red_dense k (Y i) (red_density (X i) (Y i)) x}"   
   and Y: "Y (Suc i) = Y i"
    using i
    by (simp_all add: step_kind_defs next_state_def X_degree_reg_def degree_reg_def 
        X_def Y_def split: if_split_asm prod.split_asm)
  then have X: "X (Suc i) = {x \<in> X i. card (Neighbours Red x \<inter> Y i) \<ge> (p i - q) * card (Y i)}"
    by (simp add: red_dense_def p_def q_def pee_def X_def Y_def)
  have Xsub[simp]: "X (Suc i) \<subseteq> X i"
    using Xseq_Suc_subset X_def by blast
  then have card_le: "card (X (Suc i)) \<le> card (X i)"
    by (simp add: card_mono finX)
  have [simp]: "disjnt (X i) (Y i)"
    using Xseq_Yseq_disjnt X_def Y_def by blast
  have Xnon0: "card (X i) > 0" and Ynon0: "card (Y i) > 0"
    using i by (simp_all add: X_def Y_def Xseq_gt_0 Yseq_gt_0 Step_class_def)
  have "q > 0"
    using \<open>k>0\<close>
    apply (simp add: q_def)
    by (smt (verit, best) eps_gt0 alpha_hgt_ge divide_le_0_iff nonzero_divide_mult_cancel_right of_nat_0_less_iff powr_nonneg_iff)
  have Xdif: "X i \<setminus> X (Suc i) = {x \<in> X i. card (Neighbours Red x \<inter> Y i) < (p i - q) * card (Y i)}"
    using X by force
  have disYX: "disjnt (Y i) (X i \<setminus> X (Suc i))"
    by (metis Diff_subset \<open>disjnt (X i) (Y i)\<close> disjnt_subset2 disjnt_sym)
  have "edge_card Red (Y i) (X i \<setminus> X (Suc i)) 
      = (\<Sum>x \<in> X i \<setminus> X (Suc i). real (card (Neighbours Red x \<inter> Y i)))"
    using edge_card_eq_sum_Neighbours [OF _ _ disYX] finX Red_E by simp
  also have "\<dots> \<le> (\<Sum>x \<in> X i \<setminus> X (Suc i). (p i - q) * card (Y i))"
    by (smt (verit, del_insts) Xdif mem_Collect_eq sum_mono)
  finally have A: "edge_card Red (X i \<setminus> X (Suc i)) (Y i) \<le> card (X i \<setminus> X (Suc i)) * (p i - q) * card (Y i)" 
    by (simp add: edge_card_commute)
  then have False if "X (Suc i) = {}"
    using \<open>q>0\<close> Xnon0 Ynon0 that  by (simp add: edge_card_eq_pee X_def Y_def p_def mult_le_0_iff)
  then have XSnon0: "card (X (Suc i)) > 0"
    using card_gt_0_iff finX by blast 
  have "p i * card (X i) * real (card (Y i)) - edge_card Red (X (Suc i)) (Y i)
     \<le> card (X i \<setminus> X (Suc i)) * (p i - q) * card (Y i)"
    by (metis A edge_card_eq_pee edge_card_mono X_def Y_def Xsub \<open>disjnt (X i) (Y i)\<close> p_def edge_card_diff finX of_nat_diff)
  moreover have "real (card (X (Suc i))) \<le> real (card (X i))"
    using Xsub by (simp add: card_le)
  ultimately have B: "edge_card Red (X (Suc i)) (Y i) \<ge> p i * card (X (Suc i)) * card (Y i) + card (X i \<setminus> X (Suc i)) * q * card (Y i)"
    using Xnon0 
    by (smt (verit, del_insts) Xsub card_Diff_subset card_gt_0_iff card_le left_diff_distrib finite_subset mult_of_nat_commute of_nat_diff) 
  have "edge_card Red (X (Suc i)) (Y i) / (card (X (Suc i)) * card (Y i)) \<ge> p i + card (X i \<setminus> X (Suc i)) * q / card (X (Suc i))"
    using divide_right_mono [OF B, of "card (X (Suc i)) * card (Y i)"] XSnon0 Ynon0
    by (simp add: add_divide_distrib split: if_split_asm)
  moreover have "p (Suc i) = real (edge_card Red (X (Suc i)) (Y i)) / (real (card (Y i)) * real (card (X (Suc i))))"
    using Y by (simp add: p_def pee_def gen_density_def X_def Y_def)
  ultimately show ?thesis
    by (simp add: algebra_simps XSnon0)
qed

subsection \<open>Lemma 7.8\<close>

lemma "\<forall>\<^sup>\<infinity>k. eps k powr (1/2) / k \<ge> 2 / k^2"
  unfolding eps_def
  by real_asymp

lemma X_7_8:
  assumes "0<\<mu>" "\<mu><1" and k: "k\<ge>2" "eps k powr (1/2) / k \<ge> 2 / k^2" 
    and i: "i \<in> Step_class \<mu> l k {dreg_step}"
  defines "X \<equiv> Xseq \<mu> l k"
  shows "card (X (Suc i)) \<ge> card (X i) / k^2"
proof -
  define p where "p \<equiv> pee \<mu> l k"
  define q where "q \<equiv> eps k powr (-1/2) * alpha k (hgt k (p i))"
  have "k>0" using k by auto
  have "2 / k^2 \<le> eps k powr (1/2) / k"
    using k by simp
  also have "\<dots> \<le> q"
    using \<open>k>0\<close> eps_gt0[of k] Red_5_7a [of k "p i"]
    by (simp add: q_def powr_minus divide_simps flip: powr_add)
  finally have q_ge: "q \<ge> 2 / k^2" .
  define Y where "Y \<equiv> Yseq \<mu> l k"
  have "X (Suc i) = {x \<in> X i. red_dense k (Y i) (red_density (X i) (Y i)) x}"   
   and Y: "Y (Suc i) = Y i"
    using i
    by (simp_all add: step_kind_defs next_state_def X_degree_reg_def degree_reg_def 
        X_def Y_def split: if_split_asm prod.split_asm)
  have XSnon0: "card (X (Suc i)) > 0"
    using X_7_7 assms by simp
  have finX: "finite (X i)" for i
    using finite_Xseq X_def by blast
  have Xsub[simp]: "X (Suc i) \<subseteq> X i"
    using Xseq_Suc_subset X_def by blast
  then have card_le: "card (X (Suc i)) \<le> card (X i)"
    by (simp add: card_mono finX)
  have "real k ^ 2 \<ge> 2"
    using \<open>k\<ge>2\<close> by (metis numeral_le_real_of_nat_iff of_nat_eq_of_nat_power_cancel_iff self_le_ge2_pow) 
  then have 2: "2 / (real k ^ 2 + 2) \<ge> 1 / k^2"
    by (simp add: divide_simps)
  have "q * card (X i \<setminus> X (Suc i)) / card (X (Suc i)) \<le> p (Suc i) - p i"
    using X_7_7 assms by (simp add: p_def q_def mult_of_nat_commute)
  also have "\<dots> \<le> 1"
    by (smt (verit) p_def pee_ge0 pee_le1)
  finally have "q * card (X i \<setminus> X (Suc i)) \<le> card (X (Suc i))" 
    using XSnon0 by auto
  with q_ge have "card (X (Suc i)) \<ge> (2 / k^2) * card (X i \<setminus> X (Suc i))"
    by (smt (verit, best) mult_right_mono of_nat_0_le_iff)
  then have "card (X (Suc i)) * (1 + 2/k^2) \<ge> (2/k^2) * card (X i)"
    by (simp add: card_Diff_subset finX of_nat_diff card_le diff_divide_distrib field_simps)
  then have "card (X (Suc i)) \<ge> (2/(real k ^ 2 + 2)) * card (X i)"
    using \<open>k>0\<close> add_nonneg_nonneg[of "real k^2" 2]
    by (simp del: add_nonneg_nonneg add: divide_simps split: if_split_asm)
  then show ?thesis
    using mult_right_mono [OF 2, of "card (X i)"] by simp
qed

subsection \<open>Lemma 7.9\<close>

definition "Big_X_7_9 \<equiv> \<lambda>k. ((1 + eps k) powr (eps k powr (-1/4) + 1) - 1) / eps k \<le> 2 * eps k powr (-1/4)"

lemma "\<forall>\<^sup>\<infinity>k. Big_X_7_9 k"
  unfolding eps_def Big_X_7_9_def
  by real_asymp

lemma one_plus_powr_le:
  fixes p::real
  assumes "0\<le>p" "p\<le>1" "x\<ge>0"  
  shows "(1+x) powr p - 1 \<le> x*p"
proof (rule gen_upper_bound_increasing [OF \<open>x\<ge>0\<close>])
  fix y::real
  assume y: "0 \<le> y" "y \<le> x"
  show "((\<lambda>x. x * p - ((1 + x) powr p - 1)) has_real_derivative p - (1+y)powr (p-1) * p) (at y)"
    using assms y by (intro derivative_eq_intros | simp)+
  show "p - (1+y)powr (p-1) * p \<ge> 0"
    using y assms less_eq_real_def powr_less_one by fastforce
qed auto

lemma X_7_9:
  assumes \<mu>: "0<\<mu>" "\<mu><1" and k: "k\<ge>2" "eps k powr (1/2) / k \<ge> 2 / k^2" 
    and i: "i \<in> Step_class \<mu> l k {dreg_step}"
  defines "X \<equiv> Xseq \<mu> l k" and "p \<equiv> pee \<mu> l k" 
  defines "hp \<equiv> \<lambda>i. hgt k (p i)"
  assumes "p i \<ge> p0" and hgt: "hp (Suc i) \<le> hp i + eps k powr (-1/4)"
    and big: "Big_X_7_9 k"
  shows "card (X (Suc i)) \<ge> (1 - 2 * eps k powr (1/4)) * card (X i)"
proof -
  let ?q = "eps k powr (-1/2) * alpha k (hp i)"
  have "k>0" using k by auto
  have Xsub[simp]: "X (Suc i) \<subseteq> X i"
    using Xseq_Suc_subset X_def by blast
  have finX: "finite (X i)" for i
    using finite_Xseq X_def by blast
  then have card_le: "card (X (Suc i)) \<le> card (X i)"
    by (simp add: card_mono finX)
  have XSnon0: "card (X (Suc i)) > 0"
    using X_7_7 X_def \<mu> \<open>0 < k\<close> i by blast
  have "card (X i \<setminus> X (Suc i)) / card (X (Suc i)) * ?q \<le> p (Suc i) - p i"
    using X_7_7 X_def \<mu> i k p_def hp_def by auto
  also have "\<dots> \<le> 2 * eps k powr (-1/4) * alpha k (hp i)"
  proof -
    have hgt_le: "hp i \<le> hp (Suc i)" 
      using Y_6_5_DegreeReg \<open>0 < k\<close> i p_def hp_def by blast
    have A: "p (Suc i) \<le> qfun k (hp (Suc i))"
      by (simp add: \<open>0 < k\<close> hp_def hgt_works)
    have B: "qfun k (hp i - 1) \<le> p i"
      using hgt_Least [of "hp i - 1" "p i" k] \<open>p i \<ge> p0\<close> by (force simp: hp_def)
    have "p (Suc i) - p i \<le> qfun k (hp (Suc i)) - qfun k (hp i - 1)"
      using A B by auto
    also have "\<dots> = ((1 + eps k) ^ (Suc (hp i - 1 + hp (Suc i)) - hp i) -
                      (1 + eps k) ^ (hp i - 1))    /  k"
      using \<open>k>0\<close> eps_gt0 [of k] hgt_le \<open>p i \<ge> p0\<close> hgt_gt_0 [of k]
      by (simp add: hp_def qfun_def Suc_diff_eq_diff_pred hgt_gt_0 diff_divide_distrib)
    also have "\<dots> = alpha k (hp i) / eps k * ((1 + eps k) ^ (1 + hp (Suc i) - hp i) - 1)"
      using \<open>k>0\<close>  hgt_le hgt_gt_0 [of k]
      by (simp add: hp_def alpha_eq right_diff_distrib flip: diff_divide_distrib power_add)
    also have "\<dots> \<le> 2 * eps k powr (-1/4) * alpha k (hp i)"
    proof -
      have "((1 + eps k) ^ (1 + hp (Suc i) - hp i) - 1)  / eps k \<le> ((1 + eps k) powr (eps k powr (-1/4) + 1) - 1) / eps k"
        using hgt eps_ge0 [of k] hgt_le powr_mono_both by (force simp flip: powr_realpow intro: divide_right_mono)
      also have "\<dots> \<le> 2 * eps k powr (-1/4)"
        using big by (meson Big_X_7_9_def)
      finally have *: "((1 + eps k) ^ (1 + hp (Suc i) - hp i) - 1) / eps k \<le> 2 * eps k powr (-1/4)" .
      show ?thesis
        using mult_left_mono [OF *, of "alpha k (hp i)"]
        by (smt (verit) alpha_ge0 mult.commute times_divide_eq_right)
    qed
    finally show ?thesis .
  qed
  finally have 29: "card (X i \<setminus> X (Suc i)) / card (X (Suc i)) * ?q \<le> 2 * eps k powr (-1/4) * alpha k (hp i)" .
  moreover have "alpha k (hp i) > 0"
    unfolding hp_def
    by (smt (verit, ccfv_SIG) eps_gt0 \<open>0 < k\<close> alpha_ge divide_le_0_iff hgt_gt_0 of_nat_0_less_iff)
  ultimately have "card (X i \<setminus> X (Suc i)) / card (X (Suc i)) * eps k powr (-1/2) \<le> 2 * eps k powr (-1/4)" 
    using mult_le_cancel_right by fastforce
  then have "card (X i \<setminus> X (Suc i)) / card (X (Suc i)) \<le> 2 * eps k powr (-1/4) * eps k powr (1/2)" 
    using \<open>0 < k\<close> eps_gt0 [of k]
    by (simp add: powr_minus divide_simps mult.commute zero_compare_simps split: if_split_asm)
  then have "card (X i \<setminus> X (Suc i)) \<le> 2 * eps k powr (1/4) * card (X (Suc i))"
    using XSnon0 by (simp add: field_simps flip: powr_add)
  also have "\<dots> \<le> 2 * eps k powr (1/4) * card (X i)"
    by (simp add: card_le mult_mono')
  finally show ?thesis
    by (simp add: card_Diff_subset finX of_nat_diff card_le algebra_simps)
qed

subsection \<open>Lemma 7.10\<close>

lemma X_7_10:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours l k"  
  defines "p \<equiv> pee \<mu> l k"
  defines "\<R> \<equiv> Step_class \<mu> l k {red_step}"
  defines "\<S> \<equiv> Step_class \<mu> l k {dboost_step}"
  defines "\<D> \<equiv> Step_class \<mu> l k {dreg_step}"
  defines "\<B> \<equiv> Step_class \<mu> l k {bblue_step}"
  defines "\<H> \<equiv> Step_class \<mu> l k {halted}"
  defines "m \<equiv> Inf \<H>"
  defines "h \<equiv> \<lambda>i. real (hgt k (p i))"
  defines "C \<equiv> {i. h i \<ge> h (i-1) + eps k powr (-1/4)}"
  assumes big: "Big_X_7_5 \<mu> l" and Y_6_5_S: "Lemma_6_5_dbooSt \<mu> l"
  shows "card ((\<R>\<union>\<S>) \<inter> C) \<le> 3 * eps k powr (1/4) * k"
proof -
  obtain 26: "(\<Sum>i\<in>{..<m} \<setminus> \<D>. h (Suc i) - h (i-1)) \<le> ok_fun_26 k"
     and 28: "ok_fun_28 k \<le> (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
    unfolding \<B>_def \<D>_def \<H>_def h_def m_def p_def
    using X_26_and_28 assms(1-3) big by blast
  have odd: "odd i" if "i \<in> \<R> \<or> i \<in> \<S>" for i
    using that unfolding \<R>_def \<S>_def by (metis Step_class_insert UnCI step_odd)
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  then have "Lemma_Step_class_halted_nonempty \<mu> l" 
    and BS_limit: "Lemma_bblue_dboost_step_limit \<mu> l"
    and hub: "Lemma_height_upper_bound k"
    and 16: "k\<ge>16" (*for Y_6_5_Red*)
    and ok_le_k: "ok_fun_26 k - ok_fun_28 k \<le> k"
    using big by (auto simp: Big_X_7_5_def)
  then have "m \<in> \<H>"
    using \<H>_def \<open>Colours l k\<close> 
    by (simp add: Inf_nat_def1 m_def Lemma_Step_class_halted_nonempty_def)
  then have m_minimal: "i \<notin> \<H> \<longleftrightarrow> i < m" for i
    by (metis Step_class_halted_forever \<H>_def m_def linorder_not_le wellorder_Inf_le1)
  have "\<R>\<union>\<S> \<subseteq> {..<m} \<setminus> \<D> \<setminus> \<B>" and BmD: "\<B> \<subseteq> {..<m} \<setminus> \<D>"
    by (auto simp: \<R>_def \<S>_def \<D>_def \<B>_def \<H>_def Step_class_def simp flip: m_minimal)
  then have RS_eq: "\<R>\<union>\<S> = {..<m} \<setminus> \<D> - \<B>"
    apply (auto simp: \<R>_def \<S>_def \<D>_def \<B>_def \<H>_def Step_class_def simp flip: m_minimal)
    using stepkind.exhaust by blast
  have "(\<Sum>i\<in>\<R>\<union>\<S>. h (Suc i) - h (i-1)) = (\<Sum>i\<in>{..<m} \<setminus> \<D>. h (Suc i) - h (i-1)) - (\<Sum>i \<in> \<B>. h(Suc i) - h(i-1))"
    unfolding RS_eq by (intro sum_diff BmD) auto
  also have "... \<le> ok_fun_26 k - ok_fun_28 k"
    using 26 28 by linarith
  finally have *: "(\<Sum>i\<in>\<R>\<union>\<S>. h (Suc i) - h (i-1)) \<le> ok_fun_26 k - ok_fun_28 k" .

  have "finite \<R>"
    using \<mu> \<open>Colours l k\<close> red_step_limit by (auto simp: \<R>_def)
  have "finite \<S>"
    using BS_limit by (simp add: Lemma_bblue_dboost_step_limit_def \<S>_def \<open>Colours l k\<close>)

  have h_ge_0_if_S: "h(Suc i) - h(i-1) \<ge> 0" if "i \<in> \<S>" for i
  proof -
    have *: "hgt k (pee \<mu> l k i) \<le> hgt k (pee \<mu> l k (Suc i))"
      using Y_6_5_S that unfolding Lemma_6_5_dbooSt_def
      using assms(3) \<S>_def by blast
    with that odd have "i-1 \<in> \<D>"       
      by (simp add: \<S>_def \<D>_def dreg_before_step Step_class_insert_NO_MATCH)
    then have "hgt k (pee \<mu> l k (i-1)) \<le> hgt k (pee \<mu> l k i)"
      using that \<open>k>0\<close> unfolding h_def p_def
      by (metis Suc_diff_1 Y_6_5_DegreeReg \<D>_def odd odd_pos)
    with * show "0 \<le> h(Suc i) - h(i-1)"
      using \<open>k>0\<close> unfolding h_def p_def by linarith
  qed

  have "card ((\<R>\<union>\<S>) \<inter> C) * eps k powr (-1/4) + real (card \<R>) * (-2)
      = (\<Sum>i \<in> \<R>\<union>\<S>. if i\<in>C then eps k powr (-1/4) else 0) + (\<Sum>i \<in> \<R>\<union>\<S>. if i\<in>\<R> then -2 else 0)"
    by (simp add: \<open>finite \<R>\<close> \<open>finite \<S>\<close> Int_commute Int_left_commute flip: sum.inter_restrict)
  also have "\<dots> = (\<Sum>i \<in> \<R>\<union>\<S>. (if i\<in>C then eps k powr (-1/4) else 0) + (if i\<in>\<R> then -2 else 0))"
    by (simp add: sum.distrib)
  also have "\<dots> \<le> (\<Sum>i \<in> \<R>\<union>\<S>. h(Suc i) - h(i-1))"
  proof (rule sum_mono)
    fix i :: nat
    assume i: "i \<in> \<R>\<union>\<S>"
    with i odd[of i] dreg_before_step'[of i] have D: "i-1 \<in> \<D>"       
      by (auto simp: \<S>_def \<R>_def \<D>_def dreg_before_step Step_class_def)
    then have *: "hgt k (p (i-1)) \<le> hgt k (p i)"
      using \<open>k>0\<close> unfolding h_def p_def \<D>_def
      by (metis Suc_pred' Y_6_5_DegreeReg diff_0_eq_0 gr0I le_eq_less_or_eq)
    show "(if i\<in>C then eps k powr (-1/4) else 0) + (if i\<in>\<R> then - 2 else 0) \<le> h (Suc i) - h (i-1)"
    proof (cases "i\<in>\<R>")
      case True
      then have "h i - 2 \<le> h (Suc i)"
        using Y_6_5_Red[of i] 16 by (force simp: algebra_simps \<R>_def h_def p_def)
      with * True show ?thesis
        by (simp add: h_def C_def)
    next
      case nonR: False
      with i have "i\<in>\<S>" by blast
      show ?thesis
      proof (cases "i\<in>C")
        case True
        then have "h (i - Suc 0) + eps k powr (-1/4) \<le> h i"
          by (simp add: C_def)
        then show ?thesis
          using * i nonR \<open>k>0\<close> Y_6_5_S \<open>Colours l k\<close>
          by (force simp add: h_def p_def \<S>_def Lemma_6_5_dbooSt_def)
      next
        case False
        with nonR \<open>i\<in>\<S>\<close> h_ge_0_if_S show ?thesis
          by simp
      qed
    qed
  qed
  also have "... \<le> k"
    using * ok_le_k
    by linarith
  finally have "card ((\<R>\<union>\<S>) \<inter> C) * eps k powr (-1/4) - 2 * card \<R> \<le> k"
    by linarith 
  moreover have "card \<R> \<le> k"
    by (metis \<R>_def \<open>\<mu>>0\<close> \<open>Colours l k\<close> nless_le red_step_limit(2))
  ultimately have "card ((\<R>\<union>\<S>) \<inter> C) * eps k powr (-1/4) \<le> 3 * k"
    by linarith
  with eps_gt0 [OF\<open>k>0\<close>] show ?thesis
    by (simp add: powr_minus divide_simps mult.commute split: if_split_asm)
qed


subsection \<open>Lemma 7.11\<close>


definition "Big_X_7_11 \<equiv> \<lambda>k. 
   eps k * eps k powr (-1/4) \<le> (1 + eps k) ^ (2 * nat \<lfloor>eps k powr (-1/4)\<rfloor>) - 1
    \<and> k \<ge> 2 * eps k powr (-1/2) * k powr (3/4)
    \<and> ((1 + eps k) * (1 + eps k) powr (2 * eps k powr (-1/4))) \<le> 2"

lemma "\<forall>\<^sup>\<infinity>k. Big_X_7_11 k"
  unfolding eps_def Big_X_7_11_def
  by real_asymp

lemma "\<forall>\<^sup>\<infinity>k. k \<ge> 2 * eps k powr (-1/2) * k powr (3/4)"
  unfolding eps_def 
  by real_asymp

lemma "\<forall>\<^sup>\<infinity>k. ((1 + eps k) * (1 + eps k) powr (2 * eps k powr (-1/4))) \<le> 2"
  unfolding eps_def 
  by real_asymp

lemma X_7_11:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours l k"  
  defines "p \<equiv> pee \<mu> l k"
  defines "\<R> \<equiv> Step_class \<mu> l k {red_step}"
  defines "\<S> \<equiv> Step_class \<mu> l k {dboost_step}"
  defines "\<D> \<equiv> Step_class \<mu> l k {dreg_step}"
  defines "\<B> \<equiv> Step_class \<mu> l k {bblue_step}"
  defines "\<H> \<equiv> Step_class \<mu> l k {halted}"
  defines "m \<equiv> Inf \<H>"
  defines "h \<equiv> \<lambda>i. real (hgt k (p i))"
  defines "C \<equiv> {i. p i \<ge> p (i-1) + eps k powr (-1/4) * alpha k 1 \<and> p (i-1) \<le> p0}"
  assumes big: "Big_X_7_5 \<mu> l" and Y_6_5_S: "Lemma_6_5_dbooSt \<mu> l"
         and big_711: "Big_X_7_11 k"
  shows "card ((\<R>\<union>\<S>) \<inter> C) \<le> 4 * eps k powr (1/4) * k"
proof -
  define qstar where "qstar \<equiv> p0 + eps k powr (-1/4) * alpha k 1"
  define pstar where "pstar \<equiv> \<lambda>i. min (p i) qstar"
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  then have halt: "Lemma_Step_class_halted_nonempty \<mu> l" 
    and BS_limit: "Lemma_bblue_dboost_step_limit \<mu> l"
    and hub: "Lemma_height_upper_bound k"
    and 16: "k\<ge>16" (*for Y_6_5_Red*)
    and ok_le_k: "ok_fun_26 k - ok_fun_28 k \<le> k"
    using big by (auto simp: Big_X_7_5_def)
  with \<open>Colours l k\<close> have "m \<in> \<H>"
    by (simp add: Inf_nat_def1 \<H>_def m_def Lemma_Step_class_halted_nonempty_def)
  then have m_minimal: "i \<notin> \<H> \<longleftrightarrow> i < m" for i
    by (metis Step_class_halted_forever \<H>_def m_def linorder_not_le wellorder_Inf_le1)

  have 711: "eps k * eps k powr (-1/4) \<le> (1 + eps k) ^ (2 * nat \<lfloor>eps k powr (-1/4)\<rfloor>) - 1"
    and big34: "k \<ge> 2 * eps k powr (-1/2) * k powr (3/4)"
    and le2: "((1 + eps k) * (1 + eps k) powr (2 * eps k powr (-1/4))) \<le> 2"
    using big_711 by (auto simp: Big_X_7_11_def)

  have "hgt k qstar \<le> 2 * eps k powr (-1/4)"
  proof (intro real_hgt_Least [where h = "2 * nat(floor (eps k powr (-1/4)))"])
    show "0 < 2 * nat \<lfloor>eps k powr (- 1 / 4)\<rfloor>"
      using \<open>k>0\<close> eps_gt0 [of k] by (simp add: eps_le1 powr_le1 powr_minus_divide)
    show "qstar \<le> qfun k (2 * nat \<lfloor>eps k powr (- 1 / 4)\<rfloor>)"
      using \<open>k>0\<close> 711
      by (simp add: qstar_def alpha_def qfun_def divide_right_mono mult.commute)
  qed auto
  then have "((1 + eps k) * (1 + eps k) ^ hgt k qstar) \<le> ((1 + eps k) * (1 + eps k) powr (2 * eps k powr (-1/4)))"
    by (smt (verit) eps_ge0 mult_left_mono powr_mono powr_realpow)
  also have "((1 + eps k) * (1 + eps k) powr (2 * eps k powr (-1/4))) \<le> 2"
    using le2 by simp
  finally have "(1 + eps k) * (1 + eps k) ^ hgt k qstar \<le> 2" .
  moreover have "card \<R> \<le> k"
    by (simp add: \<R>_def \<open>0<\<mu>\<close> \<open>Colours l k\<close> less_imp_le red_step_limit(2))
  ultimately have B: "((1 + eps k) * (1 + eps k) ^ hgt k qstar) * card \<R> \<le> 2 * real k"
    by (intro mult_mono) auto
  have "- 2 * alpha k 1 * k \<le> - alpha k (hgt k qstar + 2) * card \<R>"
    using mult_right_mono_neg [OF B, of "- (eps k)"] eps_ge0 [of k]
    by (simp add: alpha_eq divide_simps mult_ac)
  also have "... \<le> (\<Sum>i\<in>\<R>. pstar (Suc i) - pstar i)"
  proof -
    { fix i
      assume "i \<in> \<R>"
      moreover
      have "pstar (Suc i) = pstar i" if "hgt k (p i) > hgt k qstar + 2"
      proof -
        have "hgt k (p (Suc i)) > hgt k qstar"
          using that Y_6_5_Red 16 \<open>i \<in> \<R>\<close> by (force simp add: p_def \<R>_def)
        then show ?thesis
          by (smt (verit) that add_lessD1 hgt_mono' lk(3) pstar_def)
      qed
      ultimately have "- alpha k (hgt k qstar + 2) \<le> pstar (Suc i) - pstar i"
        unfolding pstar_def p_def \<R>_def
        by (smt (verit, del_insts) Y_6_4_Red alpha_ge0 alpha_mono hgt_gt_0 linorder_not_less)
    }
    then show ?thesis
      by (smt (verit, ccfv_SIG) mult_of_nat_commute sum_constant sum_mono)
  qed
  finally have A: "- 2 * alpha k 1 * k \<le> (\<Sum>i\<in>\<R>. pstar (Suc i) - pstar i)" .

  have "- alpha k 1 * k \<le> -2 * eps k powr (-1/2) * alpha k 1 * k powr (3/4)"
    using mult_right_mono_neg [OF big34, of "- alpha k 1"]  alpha_ge0 [of k 1]
    by (simp add: mult_ac)

  show ?thesis
    sorry
qed


end (*context Diagonal*)

end

