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

text \<open>requires some sort of Landau symbol in the conclusion\<close>
lemma X_7_2:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
    and lk: "0<l" "l\<le>k" and fin_red: "finite (Step_class \<mu> l k {red_step})"
  defines "X \<equiv> Xseq \<mu> l k"
  defines "NRX \<equiv> \<lambda>i. Neighbours Red (cvx \<mu> l k i) \<inter> X i"
  shows "(\<Prod>i \<in> Step_class \<mu> l k {red_step}. card (X(Suc i)) / card (X i)) 
        \<ge> what * (1-\<mu>) ^ card {i \<in> Step_class \<mu> l k {red_step}}"
proof -
  define R where "R \<equiv> RN k (nat \<lceil>real l powr (3/4)\<rceil>)"
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
  show ?thesis
    sorry
qed

end (*context Diagonal*)

end

