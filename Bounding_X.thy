section \<open>Bounding the Size of @{term X}\<close>

theory Bounding_X imports Bounding_Y

begin

context Diagonal
begin

text \<open>the set of moderate density-boost steps (page 20)\<close>
definition dboost_star where
  "dboost_star \<equiv> \<lambda>\<mu> l k. 
  {i \<in> Step_class \<mu> l k {dboost_step}. hgt k (pee \<mu> l k (Suc i)) - hgt k (pee \<mu> l k i) \<le> eps k powr (-1/4)}"

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
  defines "BB \<equiv> Step_class \<mu> l k {bblue_step}"
  defines "S \<equiv> Step_class \<mu> l k {dboost_step}"
  shows "(\<Prod>i \<in> BB. card (X(Suc i)) / card (X i)) \<ge> 2 powr (f k) * \<mu> ^ (l - card S)"
proof -
  have "f \<in> o(real)"
    unfolding f_def by real_asymp
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  have "finite BB" and cardBB: "card BB \<le> l powr (3/4)"
    using \<open>Colours l k\<close> bblue_limit by (auto simp: BB_def Lemma_bblue_step_limit_def)
  have "finite S"
    using bblue_dboost_step_limit \<open>Colours l k\<close>
    unfolding S_def Lemma_bblue_dboost_step_limit_def by blast
  define b where "b \<equiv> \<lambda>i. card (Bdelta \<mu> l k i)"
  obtain i where "card (Bseq \<mu> l k i) = sum b BB + card S" 
  proof -
    define i where "i = Suc (Max (BB \<union> S))"
    define TRIV where "TRIV \<equiv> Step_class \<mu> l k {red_step,dreg_step,halted} \<inter> {..<i}"
    have "finite TRIV"
      by (auto simp: TRIV_def)
    have eq: "BB \<union> S \<union> TRIV = {..<i}"
    proof
      show "BB \<union> S \<union> TRIV \<subseteq> {..<i}"
        by (auto simp add: i_def TRIV_def \<open>finite BB\<close> \<open>finite S\<close> less_Suc_eq_le)
      show "{..<i} \<subseteq> BB \<union> S \<union> TRIV"
        using  stepkind.exhaust by (auto simp: BB_def S_def TRIV_def Step_class_def)
    qed
    have dis: "BB \<inter> S = {}" "(BB \<union> S) \<inter> TRIV = {}"
      by (auto simp: BB_def S_def TRIV_def Step_class_def)
    show thesis
    proof
      have "card (Bseq \<mu> l k i) = (\<Sum>j \<in> BB \<union> S \<union> TRIV. b j)"
        using card_Bseq_sum eq unfolding b_def by metis
      also have "\<dots> = (\<Sum>j\<in>BB. b j) + (\<Sum>j\<in>S. b j) + (\<Sum>j\<in>TRIV. b j)"
        by (simp add: sum_Un_nat \<open>finite BB\<close> \<open>finite S\<close> \<open>finite TRIV\<close> dis)
      also have "\<dots> = sum b BB + card S"
      proof -
        have "sum b S = card S"
          by (simp add: b_def S_def card_Bdelta_dboost_step)
        moreover have "sum b TRIV = 0"
          by (simp add: b_def TRIV_def Bdelta_trivial_step)
        ultimately show ?thesis
          by simp
      qed
      finally show "card (Bseq \<mu> l k i) = sum b BB + card S" .
    qed
  qed
  then have sum_b_BB: "sum b BB \<le> l - card S"
    by (metis less_diff_conv less_imp_le_nat Bseq_less_l [OF \<open>Colours l k\<close>])
  have "real (card BB) \<le> real k powr (3/4)"
    using cardBB \<open>l\<le>k\<close> by (smt (verit) divide_nonneg_nonneg of_nat_0_le_iff of_nat_mono powr_mono2)
  then have "2 powr (f k) \<le> (1/2) ^ card BB"
    by (simp add: f_def powr_minus divide_simps flip: powr_realpow)
  then have "2 powr (f k) * \<mu> ^ (l - card S) \<le> (1/2) ^ card BB * \<mu> ^ (l - card S)"
    by (simp add: \<mu>)
  also have "(1/2) ^ card BB * \<mu> ^ (l - card S) \<le> (1/2) ^ card BB * \<mu> ^ (sum b BB)" 
    using \<mu> sum_b_BB by simp
  also have "\<dots> = (\<Prod>i\<in>BB. \<mu> ^ b i / 2)"
    by (simp add: power_sum prod_dividef divide_simps)
  also have "\<dots> \<le> (\<Prod>i\<in>BB. card (X (Suc i)) / card (X i))"
  proof (rule prod_mono)
    fix i :: nat
    assume "i \<in> BB"
    then have "\<not> termination_condition l k (X i) (Yseq \<mu> l k i)"
      using step_non_terminating by (simp add: BB_def X_def Step_class_def)
    then have "card (X i) \<noteq> 0"
      using termination_condition_def by force
    with \<open>i\<in>BB\<close> \<mu> show "0 \<le> \<mu> ^ b i / 2 \<and> \<mu> ^ b i / 2 \<le> real (card (X (Suc i))) / real (card (X i))"
      by (force simp: b_def BB_def X_def divide_simps dest!: Bdelta_bblue_step)
  qed
  finally show ?thesis .
qed

text \<open>Bhavik's @{text one_lt_q_function} (in his section 5)\<close>
lemma "\<forall>\<^sup>\<infinity>k. qfun k (nat \<lfloor>2 * ln k / eps k\<rfloor>) \<ge> 1"
proof -
  have A: "\<forall>\<^sup>\<infinity>k. 1 \<le> p0 + ((1 + eps k) powr (2 * ln (real k) / eps k - 1) - 1) / k"
    using p0_01 unfolding eps_def by real_asymp
  have B: "(1 + eps k) powr (2 * ln (real k) / eps k - 1) \<le> (1 + eps k) ^ (nat \<lfloor>2 * ln k / eps k\<rfloor>)" for k
    using eps_ge0 [of k] powr_realpow powr_mono
    by (smt (verit) of_nat_Suc le_nat_floor zero_less_one linorder_not_less nat_eq_iff One_nat_def of_nat_nat real_of_int_floor_add_one_gt)
  show ?thesis
    apply (rule eventually_mono [OF A])
    apply (simp add: qfun_def)
    using B
    by (smt (verit, ccfv_SIG) diff_divide_distrib divide_nonneg_nonneg of_nat_0_le_iff) 
qed

lemma X_7_5:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  assumes "Colours l k" 
  defines "S \<equiv> Step_class \<mu> l k {dboost_step}"
  assumes big: "Step_class \<mu> l k {halted} \<noteq> {}"
  shows "card (S \<setminus> dboost_star \<mu> l k) \<le> 3 * eps k powr (1/4) * k"
proof -
  define p where "p \<equiv> pee \<mu> l k"
  define m where "m \<equiv> Inf (Step_class \<mu> l k {halted})"
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)

  have "(\<lambda>k. 2 * ln k / eps k) \<in> o[at_top](real)"
    using \<open>k>0\<close> unfolding eps_def
    by real_asymp

  have "(\<Sum>i<m. real (hgt k (p (Suc i))) - real (hgt k (p i))) = real (hgt k (p m)) - real (hgt k (p 0))"
    by (rule sum_lessThan_telescope)
  also have "... \<le> 2 * ln k / eps k"
  proof -
    define h where "h \<equiv> nat \<lfloor>2 * ln (real k) / eps k\<rfloor>"
    have "hgt k (p i) \<ge> 1" for i
      by (simp add: Suc_leI hgt_gt_0)
    moreover have "hgt k (p m) \<le> 2 * ln (real k) / eps k"
 
    sorry
    show ?thesis
      sorry
  qed

end (*context Diagonal*)

end

