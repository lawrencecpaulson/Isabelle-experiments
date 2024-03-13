section \<open>An exponential improvement far from the diagonal\<close>

theory Far_From_Diagonal 
  imports Zigzag "Stirling_Formula.Stirling_Formula"

begin

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

(*NOT USED. BUT INTERESTING?*)
lemma stirling_tendsto_sqrt_pi:
  "(\<lambda>n. fact n / (sqrt (2 * n) * (n / exp 1) ^ n)) \<longlonglongrightarrow> sqrt pi"
proof -
  have *: "(\<lambda>n. fact n / (sqrt (2 * pi * n) * (n / exp 1) ^ n)) \<longlonglongrightarrow> 1"
    using fact_asymp_equiv by (simp add: asymp_equiv_def)
  have "(\<lambda>n. sqrt pi * fact n / (sqrt (2 * pi * real n) * (real n / exp 1) ^ n))
               = (\<lambda>n. fact n / (sqrt (real (2 * n)) * (real n / exp 1) ^ n))"
    by (force simp add: divide_simps powr_realpow real_sqrt_mult)
  with tendsto_mult_left[OF *, of "sqrt pi"] show ?thesis by simp
qed

definition "stir \<equiv> \<lambda>n. fact n / (sqrt (2 * pi * n) * (n / exp 1) ^ n) - 1"

lemma stir_ge0: "n>0 \<Longrightarrow> stir n \<ge> 0"
  using fact_bounds[of n] by (simp add: stir_def)

lemma stir_to_0: "stir \<longlonglongrightarrow> 0"
  using fact_asymp_equiv by (simp add: asymp_equiv_def stir_def LIM_zero)

lemma stir_o1: "stir \<in> o(1)"
  using stir_to_0 tendsto_zero_imp_o1 by presburger

lemma stir_works: "n \<noteq> 0 \<Longrightarrow> fact n = (1 + stir n) * (sqrt (2 * pi * n) * (n / exp 1) ^ n)"
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

lemma logstir_works:
   "fact n = 2 powr (logstir n) * (n / exp 1) ^ n"
proof-
  have "1 + stir n > 0" if "n\<noteq>0"
    using that by (simp add: stir_def)
  then show ?thesis
    by (simp add: logstir_def stir_works)
qed

lemma fact_9_4:
  fixes k l
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  shows "k+l choose l = 2 powr f k * \<gamma> powr (-l) * (1-\<gamma>) powr (-k)"
proof -
  have "real (k+l choose l) = fact(k+l) / (fact k * fact l)"
    by (simp add: binomial_fact)
  also have "... = xxx * (k+l) powr(k+1) / (k powr k * l powr l)"
    sorry
  show ?thesis
    sorry
qed

context Book
begin

end (*context Book*)

end
