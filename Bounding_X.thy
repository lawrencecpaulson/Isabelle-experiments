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
    also have "... \<le> card (X (Suc i)) / card (X i)"
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
  have "1-\<mu> - 1/k \<le> 1-\<mu> - 1/R"
    using \<open>0<k\<close> \<open>k < R\<close> by (simp add: inverse_of_nat_le)
  then have ln_le: "ln (1-\<mu> - 1/k) \<le> ln (1-\<mu> - 1/R)"
    using \<mu> big \<open>k>0\<close> \<open>R>k\<close> 
    by (simp add: bigR divide_simps mult.commute pos_divide_less_eq less_le_trans)
  have "f k * ln 2 = k * ln (1 - 1 / (k * (1-\<mu>)))"
    by (simp add: f_def)
  also have "... \<le> t * ln (1 - 1 / (k * (1-\<mu>)))"
  proof (intro mult_right_mono_neg)
    obtain red_steps: "finite (Step_class \<mu> l k {red_step})" "card (Step_class \<mu> l k {red_step}) < k"
      using red_step_limit \<open>0<\<mu>\<close> \<open>Colours l k\<close> by blast
    show "real t \<le> real k"
      using nat_less_le red_steps(2) by (simp add: t_def)
    show "ln (1 - 1 / (k * (1-\<mu>))) \<le> 0"
      using \<mu>(2) divide_less_eq big ln_one_minus_pos_upper_bound by fastforce
  qed
  also have "... = t * ln ((1-\<mu> - 1/k) / (1-\<mu>))"
    using \<open>t\<ge>0\<close> \<mu> by (simp add: diff_divide_distrib)
  also have "... = t * (ln (1-\<mu> - 1/k) - ln (1-\<mu>))"
    using \<open>t\<ge>0\<close> \<mu> big \<open>0<k\<close> by (simp add: ln_div mult.commute pos_divide_less_eq)
  also have "... \<le> t * (ln (1-\<mu> - 1/R) - ln (1-\<mu>))"
    by (simp add: ln_le mult_left_mono)
  finally have "f k * ln 2 + t * ln (1-\<mu>) \<le> t * ln (1-\<mu> - 1/R)"
    by (simp add: ring_distribs)
  then have "2 powr f k * (1-\<mu>) ^ t \<le> (1-\<mu> - 1/R) ^ t"
    using \<mu> by (simp add: bigR ln_mult ln_powr ln_realpow flip: ln_le_cancel_iff)
  with * show ?thesis
    by (simp add: t_def)
qed

definition "get_blue_book \<equiv> \<lambda>\<mu> l k i. let (X,Y,A,B) = stepper \<mu> l k i in choose_blue_book \<mu> (X,Y,A,B)"

lemma
  assumes i: "i \<in> Step_class \<mu> l k {bblue_step}" 
    and step: "stepper \<mu> l k i = (X,Y,A,B)"
    and bb: "get_blue_book \<mu> l k i = (S,T)"
  shows "stepper \<mu> l k (Suc i) = (T, Y, A, B\<union>S)"
  using assms
  by (force simp add: step_kind_defs next_state_def get_blue_book_def split: if_split_asm)


lemma X_7_3:
  fixes l k
  assumes \<mu>: "0<\<mu>" "\<mu><1" 
  defines "f \<equiv> \<lambda>k. (real k / ln 2) * ln (1 - 1 / (k * (1-\<mu>)))"
  assumes bblue_limit: "Lemma_bblue_step_limit \<mu> l" 
  assumes "Colours l k" 
  defines "X \<equiv> Xseq \<mu> l k"
  defines "BB \<equiv> Step_class \<mu> l k {bblue_step}"
  shows "(\<Prod>i \<in> BB. card (X(Suc i)) / card (X i)) 
        \<ge> 2 powr (f k) * (1-\<mu>) ^ (l - card (Step_class \<mu> l k {dboost_step}))"
proof -
  have "f \<in> o(real)"
    using p0_01 \<mu> unfolding eps_def f_def by real_asymp
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  have "finite BB" "card BB \<le> l powr (3/4)"
    using \<open>Colours l k\<close> bblue_limit by (auto simp: BB_def Lemma_bblue_step_limit_def)



end (*context Diagonal*)

end

