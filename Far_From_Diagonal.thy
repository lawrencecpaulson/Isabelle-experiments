section \<open>An exponential improvement far from the diagonal\<close>

theory Far_From_Diagonal 
  imports Zigzag "Stirling_Formula.Stirling_Formula"

begin

subsection \<open>An asymptotic form for binomial coefficients via Stirling's formula\<close>

text \<open>From Appendix D.3, page 56\<close>

lemma const_smallo_real: "(\<lambda>n. x) \<in> o(real)"
  by real_asymp

lemma o_real_shift:
  assumes "f \<in> o(real)"
  shows "(\<lambda>i. f(i+j)) \<in> o(real)"
  unfolding smallo_def
proof clarify
  fix c :: real
  assume "(0::real) < c"
  then have *: "\<forall>\<^sup>\<infinity>i. norm (f i) \<le> c/2 * norm i"
    using assms half_gt_zero landau_o.smallD by blast
  have "\<forall>\<^sup>\<infinity>i. norm (f (i + j)) \<le> c/2 * norm (i + j)"
    using eventually_all_ge_at_top [OF *]
    by (metis (mono_tags, lifting) eventually_sequentially le_add1)
  then have "\<forall>\<^sup>\<infinity>i. i\<ge>j \<longrightarrow> norm (f (i + j)) \<le> c * norm i"
    apply eventually_elim
    apply clarsimp
    by (smt (verit, best) \<open>0 < c\<close> mult_left_mono nat_distrib(2) of_nat_mono)
  then show "\<forall>\<^sup>\<infinity>i. norm (f (i + j)) \<le> c * norm i"
    using eventually_mp by fastforce
qed

lemma tendsto_zero_imp_o1:
  fixes a :: "nat \<Rightarrow> real"
  assumes "a \<longlonglongrightarrow> 0"
  shows "a \<in> o(1)"
proof -
  have "\<forall>\<^sup>\<infinity>n. \<bar>a n\<bar> \<le> c" if "c>0" for c
  proof -
    have "\<forall>\<^sup>\<infinity>n. \<bar>a n\<bar> < c"
      by (metis assms order_tendstoD(2) tendsto_rabs_zero_iff that)
    then show ?thesis
      by (meson eventually_sequentially less_eq_real_def)
  qed
  then show ?thesis
    by (auto simp: smallo_def)
qed

lemma tendsto_imp_o1:
  assumes "a \<longlonglongrightarrow> x"
  shows "(\<lambda>n. norm (a n - x)) \<in> o(1)"
  by (simp add: LIM_zero assms tendsto_zero_imp_o1 tendsto_norm_zero)

definition "stir \<equiv> \<lambda>n. fact n / (sqrt (2 * pi * n) * (n / exp 1) ^ n) - 1"

lemma stir_ge0: "n>0 \<Longrightarrow> stir n \<ge> 0"
  using fact_bounds[of n] by (simp add: stir_def)

lemma stir_to_0: "stir \<longlonglongrightarrow> 0"
  using fact_asymp_equiv by (simp add: asymp_equiv_def stir_def LIM_zero)

lemma stir_o1: "stir \<in> o(1)"
  using stir_to_0 tendsto_zero_imp_o1 by presburger

lemma fact_eq_stir_times: "n \<noteq> 0 \<Longrightarrow> fact n = (1 + stir n) * (sqrt (2 * pi * n) * (n / exp 1) ^ n)"
  by (simp add: stir_def)

definition "logstir \<equiv> \<lambda>n. if n=0 then 0 else log 2 ((1 + stir n) * sqrt (2 * pi * n))"

lemma logstir_o_real: "logstir \<in> o(real)"
proof -
  have "\<forall>\<^sup>\<infinity>n. 0 < n \<longrightarrow> \<bar>log 2 ((1 + stir n) * sqrt (2 * pi * n))\<bar> \<le> c * real n" if "c>0" for c
  proof -
    have "\<forall>\<^sup>\<infinity>n. 2 powr (c*n) / sqrt (2 * pi * n) \<ge> c+1"
      using that by real_asymp
    moreover have "\<forall>\<^sup>\<infinity>n. \<bar>stir n\<bar> \<le> c"
      using stir_o1 that by (auto simp: smallo_def)
    ultimately have "\<forall>\<^sup>\<infinity>n. ((1 + stir n) * sqrt (2 * pi * n)) \<le> 2 powr (c * n)"
      apply eventually_elim
      apply (simp add: divide_simps mult_less_0_iff split: if_split_asm)
      by (smt (verit, best) mult_mono real_sqrt_ge_zero zero_le_mult_iff)
    then show ?thesis
    proof (eventually_elim, clarify)
      fix n
      assume n: "(1 + stir n) * sqrt (2 * pi * real n) \<le> 2 powr (c * real n)"
        and "n>0"
      have "(1 + stir n) * sqrt (2 * pi * real n) \<ge> 1"
        using stir_ge0
        by (smt (verit) of_nat_0 \<open>0 < n\<close> mult_less_cancel_left2 nat_less_real_le pi_ge_two real_sqrt_ge_1_iff)
      with n show "\<bar>log 2 ((1 + stir n) * sqrt (2 * pi * real n))\<bar> \<le> c * real n"
        by (simp add: abs_if le_powr_iff)
    qed
  qed
  then show ?thesis
    by (auto simp: smallo_def logstir_def)
qed

lemma logfact_eq_stir_times:
   "fact n = 2 powr (logstir n) * (n / exp 1) ^ n"
proof-
  have "1 + stir n > 0" if "n\<noteq>0"
    using that by (simp add: stir_def)
  then show ?thesis
    by (simp add: logstir_def fact_eq_stir_times)
qed

lemma fact_9_4:
  assumes l: "0 < l" "l \<le> k"
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  obtains f where "f \<in> o(real)" "k+l choose l = 2 powr f k * \<gamma> powr (-l) * (1-\<gamma>) powr (-k)" 
proof 
  define f where "f \<equiv> \<lambda>k. logstir (k+l) - (logstir k + logstir l)"
  have "(\<lambda>k. logstir (k+l)) \<in> o(real)"
    using logstir_o_real o_real_shift by blast
  then show "f \<in> o(real)"
    unfolding f_def by (intro sum_in_smallo logstir_o_real const_smallo_real)

  have "real (k+l choose l) = fact(k+l) / (fact k * fact l)"
    by (simp add: binomial_fact)
  also have "... = (2 powr (logstir (k+l)) / (2 powr (logstir k) * 2 powr (logstir l))) * (k+l) powr(k+l) / (k powr k * l powr l)"
    using l by (simp add: logfact_eq_stir_times powr_add divide_simps flip: powr_realpow)
  also have "... = (2 powr f k) * (k+l) powr(k+l) / (k powr k * l powr l)"
    by (simp add: f_def powr_add powr_diff)
  also have "... = 2 powr f k * \<gamma> powr (- real l) * (1-\<gamma>) powr (- real k)"
    by (simp add: \<gamma>_def powr_minus powr_add powr_divide divide_simps)
  finally show "k+l choose l = 2 powr f k * \<gamma> powr (- real l) * (1-\<gamma>) powr (- real k)" .
qed

context Book
begin

definition "Big_Far_9_3 \<equiv>     
   \<lambda>\<mu> l. Big_X_7_1 \<mu> l
      \<and> (\<forall>k. Colours l k \<longrightarrow> True)"

lemma Big_Far_9_3:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_Far_9_3 \<mu> l"
  unfolding Big_Far_9_3_def 
            eventually_conj_iff all_imp_conj_distrib eps_def
  apply (simp add: Big_X_7_1 assms)
  done

corollary Y_6_2_halted:
  fixes l k
  assumes \<section>: "0<\<mu>" "Colours l k" and big: "Big_Y_6_2 \<mu> l"
  defines "m \<equiv> halted_point \<mu> l k"
  shows "pee \<mu> l k m \<ge> p0 - 3 * eps k"
proof -
  have "m-1 \<notin> Step_class \<mu> l k {halted}"
    by (simp add: \<section> m_def halted_point_minimal halted_point_nonzero)
  then consider "m-1 \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}" | "m-1 \<in> Step_class \<mu> l k {dreg_step}"
    using Book.not_halted_even_dreg Book_axioms not_halted_odd_RBS by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (metis Y_6_2 Suc_diff_1 assms halted_point_nonzero)
  next
    case 2
    then consider "m=1" | "m-2 \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}"
      by (metis "\<section>"(1) One_nat_def Suc_1 Suc_diff_Suc assms(2) assms(4) halted_point_nonzero le_simps(3) nat_less_le step_before_dreg)
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        by (smt (verit, ccfv_SIG) "2" Book.Y_6_4_DegreeReg Book_axioms assms(4) eps_ge0 numeral_nat(7) pee_eq_p0 verit_minus_simplify(1))        
    next
      case 2
      then show ?thesis
        by (smt (verit, best) "\<section>"(2) Book.Y_6_2 Book_axioms Y_6_4_DegreeReg \<open>\<And>thesis. \<lbrakk>m - 1 \<in> Step_class \<mu> l k {stepkind.red_step, bblue_step, dboost_step} \<Longrightarrow> thesis; m - 1 \<in> Step_class \<mu> l k {dreg_step} \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close> add_diff_inverse_nat assms(1) assms(4) big diff_diff_left diff_is_0_eq' dreg_before_step1(2) less_Suc_eq_0_disj nat_1_add_1 nat_less_le plus_1_eq_Suc)
    qed
  qed
qed

lemma Far_9_3:
  fixes l k
  assumes "Colours l k"  \<comment> \<open>Not mentioned in paper but presumably needed\<close>
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  defines "\<delta> \<equiv> min (1/200) (\<gamma>/20)"
  defines "\<R> \<equiv> Step_class \<gamma> l k {red_step}"
  assumes \<gamma>15: "\<gamma> \<le> 1/5" and p0: "p0 \<ge> 1/4" and n: "card V \<ge> exp (-\<delta>*k) * (k+l choose l)"
  assumes big: "Big_Far_9_3 \<gamma> l"
  shows "card \<R> \<ge> 2*k / 3"
proof -
  define m where "m \<equiv> halted_point \<gamma> l k"
  define \<S> where "\<S> \<equiv> Step_class \<gamma> l k {dboost_step}"
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  then have \<gamma>01: "0 < \<gamma>" "\<gamma> < 1"
    by (auto simp: \<gamma>_def)
  then have "2 powr ok_fun_X_7_1 \<gamma> l k * \<gamma>^l * (1-\<gamma>) ^ card \<R> * (bigbeta \<gamma> l k / \<gamma>) ^ card \<S> * card X0
              \<le> card (Xseq \<gamma> l k m)"
    unfolding \<R>_def \<S>_def m_def
    using X_7_1 \<open>Colours l k\<close> big by (intro X_7_1) (auto simp: Big_Far_9_3_def)
  also have "... \<le> RN k (nat \<lceil>real l powr (3/4)\<rceil>)"
    sorry
  obtain f where "f \<in> o(real)" and f: "k+l choose l = 2 powr f k * \<gamma> powr (- real l) * (1-\<gamma>) powr (- real k)" 
    unfolding \<gamma>_def using fact_9_4 lk by blast

  have "exp (-\<delta>*k) * (1-\<gamma>) powr (-k + card \<R>) * (bigbeta \<gamma> l k / \<gamma>) ^ card \<S> \<le> xxx"

    sorry

  show ?thesis
    sorry
qed

end (*context Book*)

end
