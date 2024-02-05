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
  defines "f \<equiv> \<lambda>k. (real k / ln 2) * ln (1 - 1 / 4^(k-1))"
  assumes \<mu>: "0<\<mu>" "\<mu><1" "Colours l k" and fin_red: "finite (Step_class \<mu> l k {red_step})"
  defines "X \<equiv> Xseq \<mu> l k"
  defines "NRX \<equiv> \<lambda>i. Neighbours Red (cvx \<mu> l k i) \<inter> X i"
  shows "(\<Prod>i \<in> Step_class \<mu> l k {red_step}. card (X(Suc i)) / card (X i)) 
        \<ge> 2 powr (f k) * (1-\<mu>) ^ card (Step_class \<mu> l k {red_step})"
proof -
  have "f \<in> o(real)"
    using p0_01 unfolding eps_def f_def by real_asymp
  define R where "R \<equiv> RN k (nat \<lceil>real l powr (3/4)\<rceil>)"
  obtain lk: "0<l" "l\<le>k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_ln0)
  have "nat \<lceil>real l powr (3/4)\<rceil> \<ge> 3" "k\<ge>2"
    sorry
  then have "R > k"
    using RN_gt1 R_def by blast
  moreover have "k > 1 / (1-\<mu>)"
    sorry
  ultimately have bigR: "1-\<mu> > 1/R"    \<comment> \<open>this is a (weak) bigness assumption\<close>
    using \<mu> apply (simp add: divide_simps mult.commute)
    by (smt (verit, ccfv_SIG) divide_less_eq less_imp_of_nat_less)
  have *: "1-\<mu> - 1/R \<le> card (X (Suc i)) / card (X i)"
    if  "i \<in> Step_class \<mu> l k {red_step}" for i
  proof -
    have nextX: "X (Suc i) = NRX i" and nont: "\<not> termination_condition l k (X i) (Yseq \<mu> l k i)"
      using that by (auto simp: X_def NRX_def step_kind_defs next_state_def cvx_def Let_def split: prod.split)
    then have cardX: "card (X i) > R"
      unfolding R_def by (meson not_less termination_condition_def)
    have 1: "card (NRX i) \<ge> (1-\<mu>) * card (X i) - 1"
      using that card_cvx_Neighbours \<mu> by (simp add: Step_class_def NRX_def X_def)
    have "R \<noteq> 0"
      unfolding RN_eq_0_iff R_def using lk by auto
    with cardX have "(1-\<mu>) - 1 / R \<le> (1-\<mu>) - 1 / card (X i)"
      by (simp add: inverse_of_nat_le)
    also have "... \<le> card (X (Suc i)) / card (X i)"
      using cardX nextX 1 by (simp add: divide_simps)
    finally show ?thesis .
  qed
  define t where "t \<equiv> card(Step_class \<mu> l k {red_step})"
  have "(1-\<mu> - 1/R) ^ card Red_steps \<le> (\<Prod>i \<in> Red_steps. card (X(Suc i)) / card (X i))"
    if "Red_steps \<subseteq> Step_class \<mu> l k {red_step}" for Red_steps
    using finite_subset [OF that fin_red] that
  proof induction
    case empty
    then show ?case
      by auto
  next
    case (insert i Red_steps)
    then have i: "i \<in> Step_class \<mu> l k {stepkind.red_step}"
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
  have "l powr (3 / 4) \<le> l powr 1"
    using lk by (intro powr_mono) auto
  then have "nat \<lceil>real l powr (3 / 4)\<rceil> \<le> k"
    using \<open>l\<le>k\<close> by simp
  then have "R \<le> RN k k"
    using RN_mono R_def by blast
  also have "... \<le> 4 ^(k-1)"
    by (metis RN_le_power4)
  finally have "R \<le> 4 ^ (k-1)" .
  then have "1 - 1/R \<le> 1 - 1 / 4^(k-1)"
    using \<open>k < R\<close> inverse_of_nat_le by fastforce
  then have ln_le: "ln (1 - 1/R) \<le> ln (1 - 1 / 4^(k-1))"
    by (smt (verit) \<mu>(1) bigR ln_le_cancel_iff)
  have "k * ln (1-\<mu> - 1/R) \<le> t * ln (1-\<mu> - 1/R)"
  proof (intro mult_right_mono_neg)
    obtain red_steps: "finite (Step_class \<mu> l k {red_step})" "card (Step_class \<mu> l k {red_step}) < k"
      using red_step_limit \<open>0<\<mu>\<close> \<open>Colours l k\<close> by blast
    then have "t \<le> k"
      using t_def by linarith
    then show "real t \<le> real k"
      by auto
    show "ln (1 - \<mu> - 1 / real R) \<le> 0"
      by (smt (verit) \<mu>(1) bigR ln_le_minus_one of_nat_0_le_iff zero_le_divide_1_iff)
  qed
  then have "f k * ln 2 + t * ln (1-\<mu>) \<le> t * ln (1-\<mu> - 1/R)"
    using mult_left_mono [OF ln_le, of "t"]
    by (simp add: f_def distrib_left)
  then have "f k * ln 2 + t * ln (1-\<mu>) \<le> t * ln (1-\<mu> - 1/R)"
    by simp
  then have "2 powr f k * (1-\<mu>) ^ t \<le> (1-\<mu> - 1/R) ^ t"
    using \<mu> by (simp add: bigR ln_mult ln_powr ln_realpow flip: ln_le_cancel_iff)
  with * show ?thesis
    by (simp add: t_def)
qed

end (*context Diagonal*)

end

