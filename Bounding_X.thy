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

lemma X_7_5_aux:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  assumes "Colours l k" 
  defines "\<S> \<equiv> Step_class \<mu> l k {dboost_step}"
  defines  "\<S>\<S> \<equiv> dboost_star \<mu> l k"
  assumes big: "Step_class \<mu> l k {halted} \<noteq> {}" 
          and BS_limit: "Lemma_bblue_dboost_step_limit \<mu> l"
          and B_limit: "Lemma_bblue_step_limit \<mu> l"
          and hub: "\<forall>p. p \<le> 1 \<longrightarrow> hgt k p \<le> 2 * ln k / eps k" (*height_upper_bound*)
          and 16: "k\<ge>16" (*for Y_6_5_Red*)
          and Y64S: "Lemma_Y_6_4_dbooSt \<mu> l"
          and Y65B: "Lemma_Y_6_5_Bblue \<mu> l"
  shows "card (\<S> \<setminus>\<S>\<S>) \<le> 3 * eps k powr (1/4) * k"
proof -
  define \<D> where "\<D> \<equiv> Step_class \<mu> l k {dreg_step}"
  define \<R> where "\<R> \<equiv> Step_class \<mu> l k {red_step}"
  define \<B> where "\<B> \<equiv> Step_class \<mu> l k {bblue_step}"
  define \<S> where "\<S> \<equiv> Step_class \<mu> l k {dboost_step}"
  define \<H> where "\<H> \<equiv> Step_class \<mu> l k {halted}"
  define p where "p \<equiv> pee \<mu> l k"
  define m where "m \<equiv> Inf \<H>"
  define h where "h \<equiv> \<lambda>i. real (hgt k (p i))"

  have \<S>\<S>: "\<S>\<S> = {i \<in> \<S>. h(Suc i) - h i \<le> eps k powr (-1/4)}"
       and "\<S>\<S> \<subseteq> \<S>"
    by (auto simp add: \<S>\<S>_def \<S>_def dboost_star_def p_def h_def)

  have in_S: "h(Suc i) - h i > eps k powr (-1/4)" if "i \<in> \<S>\<setminus>\<S>\<S>" for i
    using that by (fastforce simp add: \<S>\<S>)

  have odd: "odd i" if "i \<in> \<R> \<or> i \<in> \<S>" for i
    using that unfolding \<R>_def \<S>_def by (metis Step_class_insert UnCI step_odd)
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  have "finite \<R>"
    using \<mu> \<open>Colours l k\<close> red_step_limit by (auto simp: \<R>_def)
  have "finite \<B>"
    using B_limit \<open>Colours l k\<close> by (simp add: Lemma_bblue_step_limit_def \<B>_def)
  have "finite \<S>"
    using BS_limit by (simp add: Lemma_bblue_dboost_step_limit_def \<S>_def \<open>Colours l k\<close>)
  have [simp]: "\<R> \<inter> \<S> = {}" "\<B> \<inter> (\<R> \<union> \<S>) = {}"
    by (auto simp add: \<R>_def \<S>_def \<B>_def Step_class_def)
  have "\<H> \<noteq> {}"
    using \<H>_def big by blast
  then have "m \<in> \<H>"
    by (simp add: Inf_nat_def1 m_def)
  then have m_minimal: "i \<notin> \<H> \<longleftrightarrow> i < m" for i
    by (metis Step_class_halted_forever \<H>_def m_def linorder_not_le wellorder_Inf_le1)

  define f where "f \<equiv> \<lambda>k. 2 * ln k / eps k"  \<comment> \<open>a small bound for a summation\<close>
  have f_o: "f \<in> o[at_top](real)"
    using \<open>k>0\<close> unfolding eps_def f_def by real_asymp

  have oddset: "{..<n} \<setminus> \<D> = {i \<in> {..<n}. odd i}" if "n\<le>m" for n
    using m_minimal step_odd step_even not_halted_even_dreg that
    by (auto simp: \<D>_def \<H>_def Step_class_insert_NO_MATCH)


  have 26: "(\<Sum>i \<in> {..<m} \<setminus> \<D>. h(Suc i) - h(i-1)) \<le> h m - h 0"
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
  also have XXXXXXXXXXXXX: "\<dots> \<le> f k"
  proof -
    have "hgt k (p i) \<ge> 1" for i
      by (simp add: Suc_leI hgt_gt_0)
    moreover have "hgt k (p m) \<le> f k"
      using hub p_def pee_le1 unfolding f_def by blast 
    ultimately show ?thesis
      by (simp add: h_def)
  qed
  finally have 256: "(\<Sum>i \<in> {..<m} \<setminus> \<D>. h(Suc i) - h(i-1)) \<le> f k" .

  have 25: "(\<Sum>i<m. h(Suc i) - h i) \<le> f k" \<comment> \<open>is this the version we actually want?\<close>
    by (simp add: XXXXXXXXXXXXX sum_lessThan_telescope)

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
  have g_o: "g \<in> o[at_top](real)"
    using \<open>k>0\<close> unfolding g_def by real_asymp
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
    by (rule 26)   (* so: a big restructuring may be necessary*)
  also have "... = (\<Sum>i<m. h(Suc i) - h i)"
    by (simp add: sum_lessThan_telescope)
  finally have "g k + (eps k powr (-1/4) * card (\<S>\<setminus>\<S>\<S>) - real (2 * card \<R>)) \<le> (\<Sum>i<m. h (Suc i) - h i)" .
  moreover
  have "\<forall>\<^sup>\<infinity>k. f k - g k \<le> eps k powr (1/4) * k"
    unfolding f_def g_def eps_def by real_asymp
  ultimately
  show ?thesis
    using 25
    sorry
qed

end (*context Diagonal*)

end

