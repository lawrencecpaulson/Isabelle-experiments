section \<open>Red Steps: theorems\<close>

theory Red_Steps imports Big_Blue_Steps

begin

context Diagonal
begin

subsection \<open>Density-boost steps\<close>

abbreviation "Step_class_reddboost \<equiv> \<lambda>\<mu> l k. Step_class \<mu> l k red_step \<union> Step_class \<mu> l k dboost_step"

text \<open>Observation 5.5\<close>
lemma sum_Weight_ge0:
  assumes "X \<subseteq> V" "Y \<subseteq> V" "disjnt X Y"
  shows "(\<Sum>x\<in>X. \<Sum>x'\<in>X. Weight X Y x x') \<ge> 0"
proof -
  have "finite X" "finite Y"
    using assms finV finite_subset by blast+
  then have EXY: "edge_card Red X Y = (\<Sum>x\<in>X. card (Neighbours Red x \<inter> Y))"
    by (metis Red_E assms(3) disjnt_sym edge_card_commute edge_card_eq_sum_Neighbours subset_iff_psubset_eq)
  have "(\<Sum>x\<in>X. \<Sum>x'\<in>X. red_density X Y * card (Neighbours Red x \<inter> Y))
       = red_density X Y * card X * edge_card Red X Y"
    using assms Red_E
    by (simp add: EXY power2_eq_square edge_card_eq_sum_Neighbours flip: sum_distrib_left)
  also have "... = red_density X Y ^ 2 * card X ^ 2 * card Y"
    by (simp add: power2_eq_square gen_density_def)
  also have "... = ((\<Sum>i\<in>Y. card (Neighbours Red i \<inter> X)) / (real (card X) * real (card Y)))\<^sup>2 * (card X)\<^sup>2 * card Y"
    using Red_E \<open>finite Y\<close> assms
    by (simp add: psubset_eq gen_density_def edge_card_eq_sum_Neighbours)
  also have "... \<le> (\<Sum>y\<in>Y. real ((card (Neighbours Red y \<inter> X))\<^sup>2))"
  proof (cases "card Y = 0")
    case True
    then show ?thesis
      by (auto simp: sum_nonneg)
  next
    case False
    then have "(\<Sum>x\<in>Y. real (card (Neighbours Red x \<inter> X)))\<^sup>2
        \<le> (\<Sum>y\<in>Y. (real (card (Neighbours Red y \<inter> X)))\<^sup>2) * card Y"
      using \<open>finite Y\<close> assms by (intro sum_squared_le_sum_of_squares) auto
    then show ?thesis 
      using assms False by (simp add: divide_simps power2_eq_square sum_nonneg)
  qed
  also have "... = (\<Sum>x\<in>X. \<Sum>x'\<in>X. real (card (Neighbours Red x \<inter> Neighbours Red x' \<inter> Y)))"
  proof -
    define f::"'a \<times> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where "f \<equiv> \<lambda>(y,(x,x')). (x, (x', y))"
    have f: "bij_betw f (SIGMA y:Y. (Neighbours Red y \<inter> X) \<times> (Neighbours Red y \<inter> X))
                        (SIGMA x:X. SIGMA x':X. Neighbours Red x \<inter> Neighbours Red x' \<inter> Y)"
      by (auto simp add: f_def bij_betw_def inj_on_def image_iff in_Neighbours_iff doubleton_eq_iff insert_commute)
    have "(\<Sum>y\<in>Y. (card (Neighbours Red y \<inter> X))\<^sup>2) = card(SIGMA y:Y. (Neighbours Red y \<inter> X) \<times> (Neighbours Red y \<inter> X))"
      by (simp add: \<open>finite Y\<close> finite_Neighbours power2_eq_square)
    also have "... = card(Sigma X (\<lambda>x. Sigma X (\<lambda>x'. Neighbours Red x \<inter> Neighbours Red x' \<inter> Y)))"
      using bij_betw_same_card f by blast
    also have "... = (\<Sum>x\<in>X. \<Sum>x'\<in>X. card (Neighbours Red x \<inter> Neighbours Red x' \<inter> Y))"
      by (simp add: \<open>finite X\<close> finite_Neighbours power2_eq_square)
    finally
    have "(\<Sum>y\<in>Y. (card (Neighbours Red y \<inter> X))\<^sup>2) =
          (\<Sum>x\<in>X. \<Sum>x'\<in>X. card (Neighbours Red x \<inter> Neighbours Red x' \<inter> Y))" .
    then show ?thesis
      by (simp flip: of_nat_sum of_nat_power)
  qed
  finally have "(\<Sum>x\<in>X. \<Sum>y\<in>X. red_density X Y * card (Neighbours Red x \<inter> Y))
      \<le> (\<Sum>x\<in>X. \<Sum>y\<in>X. real (card (Neighbours Red x \<inter> Neighbours Red y \<inter> Y)))" .
  then show ?thesis
    by (simp add: Weight_def sum_subtractf inverse_eq_divide flip: sum_divide_distrib)
qed

lemma Red_5_6:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. k\<ge> l \<longrightarrow> RN k (nat\<lceil>l powr (3/4)\<rceil>) \<ge> k^6 * RN k (m_of l)"
proof -
  have "RN k (nat\<lceil>l powr (2/3)\<rceil>) \<ge> k^6 * RN k (m_of l)" if "l\<le>k" for l k
  proof -
    have "RN k (m_of l) \<le> (k + m_of l) choose m_of l"
      by (metis add.commute RN_commute RN_le_choose)
    also have "... \<le> k ^ (m_of l)"
      sorry
    also have "... \<le> exp (m_of l * ln k)"
      by (simp add: powr_def)
    show "RN k (nat\<lceil>l powr (2/3)\<rceil>) \<ge> k^6 * RN k (m_of l)"
      sorry
  qed
  then show ?thesis
    sorry
qed

lemma Red_5_4:
  assumes "0<\<mu>" "\<mu><1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> i \<in> Step_class_reddboost \<mu> l k \<longrightarrow>
     weight (Xseq \<mu> l k i) (Yseq \<mu> l k i) (cvx \<mu> l k i) \<ge> -card (Xseq \<mu> l k i) / (real k) ^ 5"
proof -
  let ?Big = "\<lambda>l. (\<forall>k\<ge>l. real k + 2 * real k ^ 6 \<le> real k ^ 7) \<and> (\<forall>k\<ge>l. RN k (nat\<lceil>l powr (3/4)\<rceil>) \<ge> k^6 * RN k (m_of l))"
  have 1: "\<forall>\<^sup>\<infinity>l. real l + 2 * real l ^ 6 \<le> real l ^ 7"
    by real_asymp
  have 2: "\<forall>\<^sup>\<infinity>l. \<forall>k. k\<ge> l \<longrightarrow> RN k (nat\<lceil>l powr (3/4)\<rceil>) \<ge> k^6 * RN k (m_of l)"
    using Red_5_6 assms by metis
  have big_enough_l: "\<forall>\<^sup>\<infinity>l. ?Big l"
    using eventually_conj[OF eventually_all_ge_at_top 2] 1 by blast

  have "weight (Xseq \<mu> l k i) (Yseq \<mu> l k i) (cvx \<mu> l k i) \<ge> -card (Xseq \<mu> l k i) / (real k) ^ 5"
    if l: "?Big l" and "Colours l k"  and i: "i \<in> Step_class_reddboost \<mu> l k" for l k 
  proof -
    define X where "X \<equiv> Xseq \<mu> l k i"
    define Y where "Y \<equiv> Yseq \<mu> l k i"
    let ?R = "RN k (m_of l)"
    have "finite X"
      unfolding X_def by (meson finV infinite_super Xseq_subset_V)
    have "finite Y"
      unfolding Y_def by (meson finV infinite_super Yseq_subset_V)
    have "k\<ge>l"
      using Colours_def that(2) by auto
    have "l>0"
      using Colours_ln0 that(2) by blast
    moreover have "l\<noteq>1"
      using l by auto
    ultimately have "l>1" by linarith
    with \<open>k\<ge>l\<close> have "k>0" "k>1" by auto
    have not_many_bluish: "\<not> many_bluish \<mu> l k X"
      using i red_dboost_not_many_bluish unfolding X_def by blast
    have nonterm: "\<not> termination_condition l k X Y"
      using X_def Y_def i red_dboost_non_terminating by blast
    moreover have "l powr (2/3) \<le> l powr (3/4)"
      using \<open>l>1\<close> by (simp add: powr_mono)
    ultimately have RNX: "?R < card X"
      apply (simp add: termination_condition_def m_of_def not_le)
      by (meson RN_mono basic_trans_rules(21) ceiling_mono nat_mono order.refl)

    have "0 \<le> (\<Sum>x \<in> X. \<Sum>x' \<in> X. Weight X Y x x')"
      by (simp add: X_def Y_def sum_Weight_ge0 Xseq_subset_V Yseq_subset_V Xseq_Yseq_disjnt)
    also have "... = (\<Sum>y \<in> X. weight X Y y + Weight X Y y y)"
      unfolding weight_def X_def
      by (smt (verit) sum.cong sum.infinite sum.remove)
    finally have ge0: "0 \<le> (\<Sum>y\<in>X. weight X Y y + Weight X Y y y)" .
    have w_maximal: "weight X Y (cvx \<mu> l k i) \<ge> weight X Y x"
      if "central_vertex \<mu> X x" for x
      by (metis X_def Y_def V_state i central_vx_is_best cvx_works prod_cases3 stepper_XYseq that)
    have W1abs: "\<bar>Weight X Y x y\<bar> \<le> 1"
      for x y 
      using RNX edge_card_le [of X Y Red]
      apply (simp add: Weight_def divide_simps gen_density_def)
      by (smt (verit, del_insts) mult.commute Int_lower2 of_nat_mult \<open>finite X\<close> card_gt_0_iff card_mono mult_mono of_nat_0_le_iff of_nat_le_iff) 
    then have W1: "Weight X Y x y \<le> 1" for x y
      by (smt (verit))
    have WW_le_cardX: "weight X Y y + Weight X Y y y \<le> card X"
      if "y \<in> X" for y
    proof -
      have "weight X Y y + Weight X Y y y = sum (Weight X Y y) X"
        by (smt (verit) X_def Xseq_subset_V finV finite_subset sum_diff1 that weight_def)
      also have "... \<le> card X"
        using W1 by (smt (verit) real_of_card sum_mono)
      finally show ?thesis .
    qed
    have "weight X Y x \<le> real (card(X - {x})) * 1" for x
      unfolding weight_def by (meson DiffE abs_le_D1 sum_bounded_above W1)
    then have wgt_le_X1: "weight X Y x \<le> card X - 1" if "x \<in> X" for x
      using that card_Diff_singleton One_nat_def by (smt (verit, best)) 
    define XB where "XB \<equiv> {x\<in>X. bluish \<mu> X x}"
    have card_XB: "card XB < ?R"
      using not_many_bluish by (auto simp: m_of_def many_bluish_def XB_def)
    have "XB \<subseteq> X" "finite XB"
      using \<open>finite X\<close> by (auto simp: XB_def)
    then have cv_non_XB: "\<And>y. y \<in> X - XB \<Longrightarrow> central_vertex \<mu> X y"
      by (auto simp: central_vertex_def XB_def bluish_def)
    have "0 \<le> (\<Sum>y\<in>X. weight X Y y + Weight X Y y y)"
      by (fact ge0)
    also have "... = (\<Sum>y\<in>XB. weight X Y y + Weight X Y y y) + (\<Sum>y\<in>X-XB. weight X Y y + Weight X Y y y)"
      using sum.subset_diff [OF \<open>XB\<subseteq>X\<close>] by (smt (verit) X_def Xseq_subset_V finV finite_subset)
    also have "... \<le> (\<Sum>y\<in>XB. weight X Y y + Weight X Y y y) + (\<Sum>y\<in>X-XB. weight X Y (cvx \<mu> l k i) + 1)"
      by (intro add_mono sum_mono w_maximal W1 order_refl cv_non_XB)
    also have "... = (\<Sum>y\<in>XB. weight X Y y + Weight X Y y y) + (card X - card XB) * (weight X Y (cvx \<mu> l k i) + 1)"
      using \<open>XB\<subseteq>X\<close> \<open>finite XB\<close> by (simp add: card_Diff_subset)
    also have "... \<le> card XB * card X + (card X - card XB) * (weight X Y (cvx \<mu> l k i) + 1)"
      using sum_bounded_above WW_le_cardX
      by (smt (verit, ccfv_threshold) XB_def mem_Collect_eq of_nat_mult)
    also have "... = real (?R * card X) + (real (card XB) - ?R) * card X + (card X - card XB) * (weight X Y (cvx \<mu> l k i) + 1)"
      using card_XB by (simp add: algebra_simps flip: of_nat_mult of_nat_diff)
    also have "... \<le> real (?R * card X) + (card X - ?R) * (weight X Y (cvx \<mu> l k i) + 1)"
    proof -
      have "(real (card X) - card XB) * (weight X Y (cvx \<mu> l k i) + 1) 
       \<le> (real (card X) - ?R) * (weight X Y (cvx \<mu> l k i) + 1) + (real (?R) - card XB) * (weight X Y (cvx \<mu> l k i) + 1)"
        by (simp add: algebra_simps)
      also have "... \<le>(real (card X) - ?R) * (weight X Y (cvx \<mu> l k i) + 1) + (real (?R) - card XB) * card X"
        using RNX X_def i card_XB cvx_in_Xseq wgt_le_X1 by fastforce
      finally
      have "(real (card XB) - ?R) * (card X) + (real (card X) - card XB) * (weight X Y (cvx \<mu> l k i) + 1)
        \<le> (real (card X) - ?R) * (weight X Y (cvx \<mu> l k i) + 1)"
        by (simp add: algebra_simps)
      with card_XB \<open>XB\<subseteq>X\<close> \<open>finite X\<close> RNX show ?thesis
        by (simp add: card_mono card_Diff_subset of_nat_diff)
    qed
    finally have B: "0 \<le> ?R * card X + (card X - ?R) * (weight X Y (cvx \<mu> l k i) + 1)" .

    have rk61: "real k ^ 6 > 1"
      using \<open>k>1\<close> by simp
    have k267: "real k + 2 * real k ^ 6 \<le> (real k ^ 7)"
      using \<open>l \<le> k\<close> l by auto
    have D: "real k ^ 6 + (?R * real k + ?R * (real k ^ 6)) \<le> 1 + ?R * (real k ^ 7)" 
      using mult_left_mono [OF k267, of ?R] that
      by (smt (verit, ccfv_SIG) distrib_left card_XB mult_le_cancel_right1 nat_less_real_le of_nat_0_le_iff zero_le_power)

    have "RN k (nat\<lceil>l powr (3/4)\<rceil>) \<ge> k^6 * ?R"
      using \<open>l \<le> k\<close> l by blast
    then have C: "card X \<ge> k^6 * ?R"
      using X_def i red_dboost_non_terminating termination_condition_def by fastforce
    then have "-1 / (real k)^5 \<le> - 1 / (real k^6 - 1) + -1 / (real k^6 * ?R)"
      using RNX rk61 card_XB mult_left_mono [OF D, of "real k ^ 5"]
      apply (simp add: divide_simps)
      apply (simp add: algebra_simps)
      by (smt (verit) mult.commute add_num_simps(3) add_num_simps(4) numeral_One power_add_numeral2 power_one_right)
    also have "... \<le> - ?R / (real k^6 * ?R - ?R) + -1 / (real k^6 * ?R)"
      using card_XB rk61 
      apply (simp add: frac_le_eq) apply (simp add: field_simps)
      done
    finally have "-1 / (real k)^5 \<le> - ?R / (real k^6 * ?R - ?R) + -1 / (real k^6 * ?R)" .
    also have "... \<le> - ?R / (real (card X) - ?R) + -1 / card X"
    proof (intro add_mono divide_left_mono_neg)
      show "real k ^ 6 * real ?R - real ?R \<le> real (card X) - real ?R"
        using C of_nat_mono by fastforce
      show "real k ^ 6 * real ?R \<le> real (card X)"
        using C of_nat_mono by fastforce
    qed (use RNX rk61 \<open>0 < k\<close> card_XB in auto)
    also have "... \<le> weight X Y (cvx \<mu> l k i) / card X"
      using RNX B
      apply (simp add: divide_simps)
      apply (simp add: algebra_simps)
      by (smt (verit, ccfv_SIG) less_or_eq_imp_le mult_diff_mult of_nat_diff)
    finally show ?thesis
      using RNX B by (simp add: X_def Y_def divide_simps)
  qed
  with eventually_mono [OF big_enough_l] show ?thesis
    by presburger 
qed

proposition Red_5_1:
  assumes "real (card (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i)) = \<beta> * real (card (Xseq \<mu> l k i))"
    and i: "i \<in> Step_class_reddboost \<mu> l k"
    and "0 \<le> \<beta>" "\<beta> \<le> \<mu>"    (*STRICT INEQUALITY? NOT MENTIONED by Mehta*)
  defines "p \<equiv> pee \<mu> l k i"
  shows "red_density (Neighbours Red (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i)
         \<ge> p - alpha k (hgt k p)
       \<or> red_density (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i)
         \<ge> p + (1 - eps k) * ((1-\<beta>) / \<beta>) * alpha k (hgt k p) \<and> \<beta> > 0"
  sorry

corollary Red_5_2:
  assumes i: "i \<in> Step_class \<mu> l k dboost_step" and "\<mu>>0"
  shows "pee \<mu> l k (Suc i) - pee \<mu> l k i
         \<ge> (1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k (hgt k (pee \<mu> l k i)) \<and>
           beta \<mu> l k i > 0"
proof -
  let ?x = "cvx \<mu> l k i"
  obtain X Y A B
    where step: "stepper \<mu> l k i = (X,Y,A,B)"
      and nonterm: "\<not> termination_condition l k X Y"
      and "even i"
      and non_mb: "\<not> many_bluish \<mu> l k X"
      and nonredd: "\<not> reddish k X Y (red_density X Y) (choose_central_vx \<mu> (X,Y,A,B))"
    using i
    by (auto simp: Step_class_def stepper_kind_def next_state_kind_def Xseq_def Yseq_def split: if_split_asm prod.split_asm)
  then have "?x \<in> Xseq \<mu> l k i"
    by (simp add: assms cvx_in_Xseq)
  then have "central_vertex \<mu> (Xseq \<mu> l k i) (cvx \<mu> l k i)"
    by (simp add: assms cvx_works)
  moreover have Xeq: "X = Xseq \<mu> l k i" and Yeq: "Y = Yseq \<mu> l k i"
    by (metis step stepper_XYseq surj_pair)+
  ultimately have "card (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) \<le> \<mu> * card (Xseq \<mu> l k i)"
    by (simp add: central_vertex_def)
  then have \<beta>eq: "card (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) = beta \<mu> l k i * card (Xseq \<mu> l k i)"
    using Xeq step by (auto simp add: beta_def)
  have SUC: "stepper \<mu> l k (Suc i) = (Neighbours Blue ?x \<inter> X, Neighbours Red ?x \<inter> Y, A, insert ?x B)"
    using step nonterm \<open>even i\<close> non_mb nonredd
    by (simp add: stepper_def next_state_def Let_def cvx_def)
  have pee: "pee \<mu> l k i = red_density X Y"
    by (simp add: pee_def Xeq Yeq)
  have "choose_central_vx \<mu> (X,Y,A,B) = cvx \<mu> l k i"
    by (simp add: cvx_def step)
  with nonredd have "red_density (Neighbours Red (cvx \<mu> l k i) \<inter> X) (Neighbours Red (cvx \<mu> l k i) \<inter> Y)
                   < pee \<mu> l k i - alpha k (hgt k (red_density X Y))"
    using nonredd by (simp add: reddish_def pee)
  then have "pee \<mu> l k i + (1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k (hgt k (pee \<mu> l k i))
      \<le> red_density (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i)
          (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i) \<and> beta \<mu> l k i > 0"
    using Red_5_1 [OF \<beta>eq _ beta_ge0 beta_le]
    by (smt (verit, del_insts) Un_iff Xeq Yeq assms gen_density_ge0 pee)
  moreover have "red_density (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i)
      (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i) \<le> pee \<mu> l k (Suc i)"
    using SUC Xeq Yeq stepper_XYseq by (simp add: pee_def)
  ultimately show ?thesis
    by linarith
qed


corollary Red_5_3:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. \<forall>i. i \<in> Step_class \<mu> l k dboost_step \<longrightarrow> Colours l k \<longrightarrow>
                  (pee \<mu> l k (Suc i) \<ge> pee \<mu> l k i \<and> beta \<mu> l k i \<ge> 1 / real k ^ 2)"
proof -
  define Big where "Big \<equiv> \<lambda>l. 1 / real l ^ 2 \<le> 1 / (l / eps l / (1 - eps l) + 1) \<and> l>1"
  have "\<forall>\<^sup>\<infinity>l. 1 / real l ^ 2 \<le> 1 / (l / eps l / (1 - eps l) + 1)"
    unfolding eps_def by real_asymp
  moreover have "\<forall>\<^sup>\<infinity>l. l>1"
    by auto
  ultimately have Big: "\<forall>\<^sup>\<infinity>l. Big l"
    using eventually_mono eventually_conj by (force simp add: Big_def)  
  have "pee \<mu> l k (Suc i) \<ge> pee \<mu> l k i \<and> beta \<mu> l k i \<ge> 1 / real k ^ 2"
    if l: "\<forall>k\<ge>l. Big k" and i: "i \<in> Step_class \<mu> l k dboost_step" and "Colours l k" for l k i
  proof 
    obtain ln0: "l>0" and kn0: "k>0" and "l\<le>k"
      using \<open>Colours l k\<close> Colours_kn0 Colours_ln0  by (auto simp: Colours_def)
    have "k>1"
      using \<open>l \<le> k\<close> l by (auto simp: Big_def)
    let ?h = "hgt k (pee \<mu> l k i)"
    have "?h > 0"
      by (simp add: hgt_gt_0 kn0 pee_le1)
    then obtain \<alpha>: "alpha k ?h \<ge> 0" and *: "alpha k ?h \<ge> eps k / k"
      using alpha_ge0 \<open>k>1\<close> alpha_ge by auto
    moreover have "-5/4 = -1/4 - (1::real)"
      by simp
    ultimately have \<alpha>54: "alpha k ?h \<ge> k powr (-5/4)"
      unfolding eps_def by (metis powr_diff of_nat_0_le_iff powr_one)
    have \<beta>: "beta \<mu> l k i \<le> \<mu>"
      by (simp add: \<open>0<\<mu>\<close> beta_le i)
    have "(1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k ?h \<ge> 0"
      using beta_ge0[of \<mu> l k i] epsk_le1 \<alpha> \<beta> \<open>\<mu><1\<close> \<open>k>1\<close>
      by (simp add: zero_le_mult_iff zero_le_divide_iff)
    then show "pee \<mu> l k (Suc i) \<ge> pee \<mu> l k i"
      using Red_5_2 [OF i \<open>\<mu>>0\<close>] by simp
    have "pee \<mu> l k (Suc i) - pee \<mu> l k i \<le> 1"
      by (smt (verit) pee_ge0 pee_le1)
    with Red_5_2 [OF i \<open>\<mu>>0\<close>]
    have "(1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k ?h \<le> 1" and beta_gt0: "beta \<mu> l k i > 0"
      by linarith+
    with * have "(1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * eps k / k \<le> 1"
      by (smt (verit, ccfv_SIG) divide_le_eq_1 epsk_gt0 kn0 mult_le_cancel_left2 mult_le_cancel_left_pos mult_neg_pos of_nat_0_less_iff times_divide_eq_right)
    then have "(1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) \<le> k / eps k"
      using beta_ge0 [of \<mu> l k i] epsk_gt0 [OF kn0] kn0
      by (auto simp add: divide_simps mult_less_0_iff mult_of_nat_commute split: if_split_asm)
    then have "((1 - beta \<mu> l k i) / beta \<mu> l k i) \<le> k / eps k / (1 - eps k)"
      by (smt (verit) epsk_less1 mult.commute pos_le_divide_eq \<open>1 < k\<close>)
    then have "1 / beta \<mu> l k i \<le> k / eps k / (1 - eps k) + 1"
      by (smt (verit, best) div_add_self2)
    then have "1 / (k / eps k / (1 - eps k) + 1) \<le> beta \<mu> l k i"
      using beta_gt0 epsk_gt0 epsk_less1 [OF \<open>k>1\<close>] kn0
      apply (simp add: divide_simps split: if_split_asm)
      by (smt (verit, ccfv_SIG) mult.commute mult_less_0_iff)
    moreover have "1 / k^2 \<le> 1 / (k / eps k / (1 - eps k) + 1)"
      using Big_def \<open>l \<le> k\<close> l by fastforce
    ultimately show "beta \<mu> l k i \<ge> 1 / real k ^ 2"
      by auto
  qed
  with Big show ?thesis
    unfolding eventually_sequentially by (meson order.trans)
qed

end
