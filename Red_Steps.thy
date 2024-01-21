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
  also have "\<dots> = red_density X Y ^ 2 * card X ^ 2 * card Y"
    by (simp add: power2_eq_square gen_density_def)
  also have "\<dots> = ((\<Sum>i\<in>Y. card (Neighbours Red i \<inter> X)) / (real (card X) * real (card Y)))\<^sup>2 * (card X)\<^sup>2 * card Y"
    using Red_E \<open>finite Y\<close> assms
    by (simp add: psubset_eq gen_density_def edge_card_eq_sum_Neighbours)
  also have "\<dots> \<le> (\<Sum>y\<in>Y. real ((card (Neighbours Red y \<inter> X))\<^sup>2))"
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
  also have "\<dots> = (\<Sum>x\<in>X. \<Sum>x'\<in>X. real (card (Neighbours Red x \<inter> Neighbours Red x' \<inter> Y)))"
  proof -
    define f::"'a \<times> 'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a" where "f \<equiv> \<lambda>(y,(x,x')). (x, (x', y))"
    have f: "bij_betw f (SIGMA y:Y. (Neighbours Red y \<inter> X) \<times> (Neighbours Red y \<inter> X))
                        (SIGMA x:X. SIGMA x':X. Neighbours Red x \<inter> Neighbours Red x' \<inter> Y)"
      by (auto simp add: f_def bij_betw_def inj_on_def image_iff in_Neighbours_iff doubleton_eq_iff insert_commute)
    have "(\<Sum>y\<in>Y. (card (Neighbours Red y \<inter> X))\<^sup>2) = card(SIGMA y:Y. (Neighbours Red y \<inter> X) \<times> (Neighbours Red y \<inter> X))"
      by (simp add: \<open>finite Y\<close> finite_Neighbours power2_eq_square)
    also have "\<dots> = card(Sigma X (\<lambda>x. Sigma X (\<lambda>x'. Neighbours Red x \<inter> Neighbours Red x' \<inter> Y)))"
      using bij_betw_same_card f by blast
    also have "\<dots> = (\<Sum>x\<in>X. \<Sum>x'\<in>X. card (Neighbours Red x \<inter> Neighbours Red x' \<inter> Y))"
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

lemma Red_5_6_Ramsey:
  assumes "0<c" "c<1/32"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. l \<le> k \<longrightarrow> exp (c * real l powr (3/4) * ln k) \<le> RN k (nat\<lceil>l powr (3/4)\<rceil>)"
proof -
  have B: "\<forall>\<^sup>\<infinity>l. nat \<lceil>real l powr (3/4)\<rceil> \<ge> 3"
    by real_asymp
  have C: "\<forall>\<^sup>\<infinity>l. l powr (3/4) * (c - 1/32) \<le> -1"
    using assms by real_asymp
  have D34: "\<And>l k. l \<le> k \<Longrightarrow> c * real l powr (3/4)  \<le> c * real k powr (3/4)"
    by (simp add: assms(1) powr_mono2)
  have "\<forall>\<^sup>\<infinity>l. l * (c * real l powr (3/4) * ln l - real l powr (7/8) / 4) \<le> -1"
    using \<open>c>0\<close> by real_asymp
  then have "\<forall>\<^sup>\<infinity>l.  \<forall>k\<ge>l. k * (c * real k powr (3/4) * ln k - real k powr (7/8) / 4) \<le> -1"
    using eventually_all_ge_at_top by blast
  then have D: "\<forall>\<^sup>\<infinity>l. \<forall>k\<ge>l. k * (c * real l powr (3/4) * ln k - real k powr (7/8) / 4) \<le> -1"
    apply (rule eventually_mono)
    apply (elim all_forward imp_forward2 asm_rl)
    by (smt (verit, best) D34 mult_left_mono ln_less_zero_iff mult_le_cancel_right nat_le_real_less of_nat_0_le_iff)

  define BIG where "BIG \<equiv> \<lambda>l. nat \<lceil>real l powr (3/4)\<rceil> \<ge> 3
                \<and> (l powr (3/4) * (c - 1/32) \<le> -1) 
                \<and> (\<forall>k\<ge>l. k * (c * real l powr (3/4) * ln k - real k powr (7/8) / 4) \<le> -1)"
  have big_enough_l: "\<forall>\<^sup>\<infinity>l. BIG l"
    unfolding BIG_def by (intro eventually_conj B C D)

  have "exp (c * real l powr (3/4) * ln k) \<le> RN k (nat\<lceil>l powr (3/4)\<rceil>)"
    if l: "BIG l" "l\<le>k" for l k
  proof -
    define r where "r \<equiv> nat \<lfloor>exp (c * real l powr (3/4) * ln k)\<rfloor>"
    define s where "s \<equiv> nat \<lceil>real l powr (3/4)\<rceil>"
    have "l\<noteq>0"
      using l unfolding BIG_def
      by (metis le_minus_one_simps(3) mult_eq_0_iff of_nat_0_eq_iff powr_eq_0_iff)
    have "3 \<le> s"
      using that by (auto simp: BIG_def s_def)
    also have "\<dots> \<le> l"
      using powr_mono [of "3/4" 1] \<open>l \<noteq> 0\<close> by (simp add: s_def)
    finally have "3 \<le> l" .
    then have "k\<ge>3" \<open>k>0\<close> \<open>l>0\<close>
      using that by auto
    define p where "p \<equiv> (real k) powr (-1/8)"
    have p01: "0 < p" "p < 1"
      using \<open>k\<ge>3\<close> powr_less_one by (auto simp: p_def)
    have r_le: "r \<le> k powr (c * l powr (3/4))"
      using p01 \<open>k\<ge>3\<close> unfolding r_def powr_def by force

    have left: "of_real r ^ s * p powr ((real s)\<^sup>2 / 4) < 1/2" 
    proof -
      have A: "r powr s \<le> k powr (s * c * l powr (3/4))"
        using r_le by (smt (verit) mult.commute of_nat_0_le_iff powr_mono2 powr_powr)
      have B: "p powr ((real s)\<^sup>2 / 4) \<le> k powr (-(real s)\<^sup>2 / 32)"
        by (simp add: powr_powr p_def power2_eq_square)
      have C: "(c * l powr (3/4) - s/32) \<le> -1"
        using l by (simp add: BIG_def s_def algebra_simps) linarith
      have "of_real r ^ s * p powr ((real s)\<^sup>2 / 4) \<le> k powr (s * (c * l powr (3/4) - s / 32))"
        using mult_mono [OF A B] \<open>s\<ge>3\<close>
        by (simp add: power2_eq_square algebra_simps powr_realpow' flip: powr_add)
      also have "\<dots> \<le> k powr - real s"
        using C \<open>s\<ge>3\<close> mult_left_mono \<open>k\<ge>3\<close> by fastforce
      also have "\<dots> \<le> k powr -3"
        using \<open>k\<ge>3\<close> \<open>s\<ge>3\<close> by (simp add: powr_minus powr_realpow)
      also have "\<dots> \<le> 3 powr -3"
        using \<open>k\<ge>3\<close> by (intro powr_mono2') auto
      also have "\<dots> < 1/2"
        by auto
      finally show ?thesis .
    qed
    have right: "of_real r ^ k * exp (- p * (real k)\<^sup>2 / 4) < 1/2" 
    proof -
      have A: "of_real r ^ k \<le> exp (c * l powr (3/4) * ln k * k)"
        using r_le \<open>0 < k\<close> \<open>0 < l\<close> by (simp add: powr_def exp_of_nat2_mult)
      have B: "exp (- p * (real k)\<^sup>2 / 4) \<le> exp (- k * k powr (7/8) / 4)"
        using \<open>k>0\<close> by (simp add: p_def mult_ac power2_eq_square powr_mult_base)
      have D: "k * (c * real l powr (3/4) * ln k - real k powr (7/8) / 4) \<le> -1"
        using that unfolding BIG_def by blast
      have "of_real r ^ k * exp (- p * (real k)\<^sup>2 / 4) \<le> exp (k * (c * l powr (3/4) * ln k - k powr (7/8) / 4))"
        using mult_mono [OF A B] by (simp add: algebra_simps s_def flip: exp_add)
      also have "\<dots> \<le> exp (-1)"
        using D by blast
      also have "\<dots> < 1/2"
        by (approximation 5)
      finally show ?thesis .
    qed
    have "\<not> is_Ramsey_number (nat\<lceil>l powr (3/4)\<rceil>) k (nat \<lfloor>exp (c * real l powr (3/4) * ln (real k))\<rfloor>)"
      using Ramsey_number_lower_simple [OF _ p01] left right \<open>k\<ge>3\<close> \<open>l\<ge>3\<close>
      unfolding r_def s_def by force
    then show ?thesis
      by (metis RN_commute is_Ramsey_number_RN le_nat_floor nle_le partn_lst_greater_resource)
  qed  
  with eventually_mono [OF big_enough_l] is_Ramsey_number_commute show ?thesis
    by presburger 
qed

definition "Lemma_5_6 \<equiv> \<lambda>l. \<forall>k. k \<ge> l \<longrightarrow> RN k (nat\<lceil>l powr (3/4)\<rceil>) \<ge> k ^ 6 * RN k (m_of l)"

lemma Red_5_6:
  shows "\<forall>\<^sup>\<infinity>l. Lemma_5_6 l"
proof -
  define c_spec where "c_spec \<equiv> \<lambda>c l. \<forall>k. l \<le> k \<longrightarrow> exp (c * real l powr (3/4) * ln k) \<le> RN k (nat\<lceil>l powr (3/4)\<rceil>)"
  define c::real where "c \<equiv> 1/128"
  have "0 < c" "c < 1/32"
    by (auto simp: c_def)
  then have c: "\<forall>\<^sup>\<infinity>l. c_spec c l"
    unfolding c_spec_def using Red_5_6_Ramsey exp_gt_zero by blast
  let ?Big = "\<lambda>l. 6 + m_of l \<le> c * l powr (3/4) \<and> c_spec c l"
  have "\<forall>\<^sup>\<infinity>l. 6 + m_of l \<le> c * l powr (3/4)"
    using \<open>c>0\<close> unfolding m_of_def by real_asymp
  with eventually_conj [OF _ c] have big_enough_l: "\<forall>\<^sup>\<infinity>l. ?Big l"
    by blast
  have "RN k (nat\<lceil>l powr (3/4)\<rceil>) \<ge> k ^ 6 * RN k (m_of l)" 
    if l: "?Big l" and "k \<ge> l" for l k
  proof (cases "k=0")
    case False
    then have "k>0" by simp
    have "RN k (m_of l) \<le> k ^ (m_of l)"
      by (metis RN_le_argpower' RN_mono diff_add_inverse diff_le_self le_refl le_trans)
    also have "\<dots> \<le> exp (m_of l * ln k)"
      using \<open>k>0\<close> by (simp add: exp_of_nat_mult)
    finally have "RN k (m_of l) \<le> exp (real (m_of l) * ln k)"
      by force 
    then have "real k ^ 6 * RN k (m_of l) \<le> real k ^ 6 * exp (real (m_of l) * ln k)"
      by (simp add: \<open>0 < k\<close>)
    also have "\<dots> \<le> exp (c * l powr (3/4) * ln k)"
    proof -
      have "(6 + real (m_of l)) * ln (real k) \<le> (c * real l powr (3/4)) * ln (real k)"
        using l \<open>0 < k\<close> mult_le_cancel_right by fastforce
      then have "ln (real k ^ 6 * exp (m_of l * ln k)) \<le> ln (exp (c * real l powr (3/4) * ln k))"
        using \<open>k>0\<close> by (simp add: ln_mult ln_powr algebra_simps flip: powr_numeral)
      then show ?thesis
        by (smt (verit) exp_gt_zero ln_le_cancel_iff)
    qed
    also have "\<dots> \<le> RN k (nat\<lceil>l powr (3/4)\<rceil>)"
      using c_spec_def of_nat_mono that by blast
    finally show "k ^ 6 * RN k (m_of l) \<le> RN k (nat\<lceil>l powr (3/4)\<rceil>)"
      by (metis of_nat_mult of_nat_le_iff of_nat_power)
  qed auto
  with eventually_mono [OF big_enough_l] show ?thesis
    unfolding Lemma_5_6_def by presburger 
qed

definition "Lemma_5_4 \<equiv> \<lambda>\<mu> l. \<forall>k i. Colours l k \<longrightarrow> i \<in> Step_class_reddboost \<mu> l k \<longrightarrow>
     weight (Xseq \<mu> l k i) (Yseq \<mu> l k i) (cvx \<mu> l k i) \<ge> - real (card (Xseq \<mu> l k i)) / (real k) ^ 5"

lemma Red_5_4: 
  assumes "0<\<mu>" "\<mu><1" 
  shows "\<forall>\<^sup>\<infinity>l. Lemma_5_4 \<mu> l"
proof -
  let ?Big = "\<lambda>l. (\<forall>k\<ge>l. real k + 2 * real k ^ 6 \<le> real k ^ 7) \<and> Lemma_5_6 l"
  have 1: "\<forall>\<^sup>\<infinity>l. real l + 2 * real l ^ 6 \<le> real l ^ 7"
    by real_asymp
  then have big_enough_l: "\<forall>\<^sup>\<infinity>l. ?Big l"
    using Red_5_6 eventually_conj eventually_all_ge_at_top by fastforce
  have "weight (Xseq \<mu> l k i) (Yseq \<mu> l k i) (cvx \<mu> l k i) \<ge> - real (card (Xseq \<mu> l k i)) / (real k) ^ 5"
    if l: "?Big l" and "Colours l k" and i: "i \<in> Step_class_reddboost \<mu> l k" for l k i
  proof -
    define X where "X \<equiv> Xseq \<mu> l k i"
    define Y where "Y \<equiv> Yseq \<mu> l k i"
    let ?R = "RN k (m_of l)"
    have "finite X" "finite Y"
      unfolding X_def Y_def by (meson finV infinite_super Xseq_subset_V Yseq_subset_V)+
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
      unfolding termination_condition_def m_of_def
      by (smt (verit, ccfv_SIG) RN_mono order.trans leI ceiling_mono nat_mono order.refl)
    have "0 \<le> (\<Sum>x \<in> X. \<Sum>x' \<in> X. Weight X Y x x')"
      by (simp add: X_def Y_def sum_Weight_ge0 Xseq_subset_V Yseq_subset_V Xseq_Yseq_disjnt)
    also have "\<dots> = (\<Sum>y \<in> X. weight X Y y + Weight X Y y y)"
      unfolding weight_def X_def
      by (smt (verit) sum.cong sum.infinite sum.remove)
    finally have ge0: "0 \<le> (\<Sum>y\<in>X. weight X Y y + Weight X Y y y)" .
    have w_maximal: "weight X Y (cvx \<mu> l k i) \<ge> weight X Y x"
      if "central_vertex \<mu> X x" for x
      by (metis X_def Y_def V_state i central_vx_is_best cvx_works prod_cases3 stepper_XYseq that)

    have "\<bar>real (card (S \<inter> Y)) * (real (card X) * real (card Y)) -
           real (edge_card Red X Y) * real (card (T \<inter> Y))\<bar>
        \<le> real (card X) * real (card Y) * real (card Y)" for S T
      using card_mono [OF _ Int_lower2] \<open>finite X\<close> \<open>finite Y\<close>
      by (smt (verit, best) of_nat_mult edge_card_le mult.commute mult_right_mono of_nat_0_le_iff of_nat_mono)
    then have W1abs: "\<bar>Weight X Y x y\<bar> \<le> 1" for x y 
      using RNX edge_card_le [of X Y Red] \<open>finite X\<close> 
      by (fastforce simp add: mult_ac Weight_def divide_simps gen_density_def)
    then have W1: "Weight X Y x y \<le> 1" for x y
      by (smt (verit))
    have WW_le_cardX: "weight X Y y + Weight X Y y y \<le> card X" if "y \<in> X" for y
    proof -
      have "weight X Y y + Weight X Y y y = sum (Weight X Y y) X"
        by (smt (verit) X_def Xseq_subset_V finV finite_subset sum_diff1 that weight_def)
      also have "\<dots> \<le> card X"
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
    also have "\<dots> = (\<Sum>y\<in>XB. weight X Y y + Weight X Y y y) + (\<Sum>y\<in>X-XB. weight X Y y + Weight X Y y y)"
      using sum.subset_diff [OF \<open>XB\<subseteq>X\<close>] by (smt (verit) X_def Xseq_subset_V finV finite_subset)
    also have "\<dots> \<le> (\<Sum>y\<in>XB. weight X Y y + Weight X Y y y) + (\<Sum>y\<in>X-XB. weight X Y (cvx \<mu> l k i) + 1)"
      by (intro add_mono sum_mono w_maximal W1 order_refl cv_non_XB)
    also have "\<dots> = (\<Sum>y\<in>XB. weight X Y y + Weight X Y y y) + (card X - card XB) * (weight X Y (cvx \<mu> l k i) + 1)"
      using \<open>XB\<subseteq>X\<close> \<open>finite XB\<close> by (simp add: card_Diff_subset)
    also have "\<dots> \<le> card XB * card X + (card X - card XB) * (weight X Y (cvx \<mu> l k i) + 1)"
      using sum_bounded_above WW_le_cardX
      by (smt (verit, ccfv_threshold) XB_def mem_Collect_eq of_nat_mult)
    also have "\<dots> = real (?R * card X) + (real (card XB) - ?R) * card X + (card X - card XB) * (weight X Y (cvx \<mu> l k i) + 1)"
      using card_XB by (simp add: algebra_simps flip: of_nat_mult of_nat_diff)
    also have "\<dots> \<le> real (?R * card X) + (card X - ?R) * (weight X Y (cvx \<mu> l k i) + 1)"
    proof -
      have "(real (card X) - card XB) * (weight X Y (cvx \<mu> l k i) + 1) 
          \<le> (real (card X) - ?R) * (weight X Y (cvx \<mu> l k i) + 1) + (real (?R) - card XB) * (weight X Y (cvx \<mu> l k i) + 1)"
        by (simp add: algebra_simps)
      also have "\<dots> \<le> (real (card X) - ?R) * (weight X Y (cvx \<mu> l k i) + 1) + (real (?R) - card XB) * card X"
        using RNX X_def i card_XB cvx_in_Xseq wgt_le_X1 by fastforce
      finally show ?thesis
        by (smt (verit, del_insts) RNX \<open>XB \<subseteq> X\<close> \<open>finite X\<close> card_mono nat_less_le of_nat_diff distrib_right)
    qed
    finally have weight_ge_0: "0 \<le> ?R * card X + (card X - ?R) * (weight X Y (cvx \<mu> l k i) + 1)" .
    have rk61: "real k ^ 6 > 1"
      using \<open>k>1\<close> by simp
    have k267: "real k + 2 * real k ^ 6 \<le> (real k ^ 7)"
      using \<open>l \<le> k\<close> l by auto
    have k_le: "real k ^ 6 + (?R * real k + ?R * (real k ^ 6)) \<le> 1 + ?R * (real k ^ 7)" 
      using mult_left_mono [OF k267, of ?R] that
      by (smt (verit, ccfv_SIG) distrib_left card_XB mult_le_cancel_right1 nat_less_real_le of_nat_0_le_iff zero_le_power)
    have [simp]: "real k ^ m = real k ^ n \<longleftrightarrow> m=n" "real k ^ m < real k ^ n \<longleftrightarrow> m<n" for m n
      using \<open>1 < k\<close> by auto
    have "RN k (nat\<lceil>l powr (3/4)\<rceil>) \<ge> k ^ 6 * ?R"
      using \<open>l \<le> k\<close> l unfolding Lemma_5_6_def by blast
    then have cardX_ge: "card X \<ge> k ^ 6 * ?R"
      using X_def i red_dboost_non_terminating termination_condition_def by fastforce
    have "-1 / (real k)^5 \<le> - 1 / (real k^6 - 1) + -1 / (real k^6 * ?R)"
    proof -
      have [simp]: "real k * (r * real k ^ 5) = r * k^6" for r
        by (simp add: eval_nat_numeral)
      show ?thesis
        using rk61 card_XB mult_left_mono [OF k_le, of "real k ^ 5"]
        by (simp add: field_split_simps)
    qed
    also have "\<dots> \<le> - ?R / (real k^6 * ?R - ?R) + -1 / (real k^6 * ?R)"
      using card_XB rk61  by (simp add: field_split_simps)
    finally have "-1 / (real k)^5 \<le> - ?R / (real k^6 * ?R - ?R) + -1 / (real k^6 * ?R)" .
    also have "\<dots> \<le> - ?R / (real (card X) - ?R) + -1 / card X"
    proof (intro add_mono divide_left_mono_neg)
      show "real k ^ 6 * real ?R - real ?R \<le> real (card X) - real ?R"
        using cardX_ge of_nat_mono by fastforce
      show "real k ^ 6 * real ?R \<le> real (card X)"
        using cardX_ge of_nat_mono by fastforce
    qed (use RNX rk61 \<open>0 < k\<close> card_XB in auto)
    also have "\<dots> \<le> weight X Y (cvx \<mu> l k i) / card X"
      using RNX mult_left_mono [OF weight_ge_0, of "card X"] by (simp add: field_split_simps of_nat_diff)
    finally show ?thesis
      using RNX by (simp add: X_def Y_def divide_simps)
  qed
  with eventually_mono [OF big_enough_l] show ?thesis
    unfolding Lemma_5_4_def by presburger 
qed

lemma Red_5_7a: "eps k / k \<le> alpha k (hgt k p)"
  by (simp add: alpha_ge hgt_gt_0)

lemma Red_5_7b: 
  assumes "p \<ge> qfun k 0" shows "alpha k (hgt k p) \<le> eps k * (p - qfun k 0 + 1/k)"
proof -
  have qh_le_p: "qfun k (hgt k p - Suc 0) \<le> p"
    by (smt (verit) assms diff_Suc_less diff_le_self hgt_Least le_antisym nat_less_le zero_less_iff_neq_zero)
  have "hgt k p > 0"
    by (simp add: Suc_leI hgt_gt_0)
  then have "alpha k (hgt k p) = eps k * (1 + eps k) ^ (hgt k p - 1) / k"
    using alpha_eq by blast
  also have "\<dots> = eps k * (qfun k (hgt k p - 1) - qfun k 0 + 1/k)"
    by (simp add: diff_divide_distrib qfun_def)
  also have "\<dots> \<le> eps k * (p - qfun k 0 + 1/k)"
    by (smt (verit) qh_le_p mult.commute mult_right_mono One_nat_def eps_def powr_ge_pzero)
  finally show ?thesis .
qed

lemma Red_5_7c: 
  assumes "p \<le> qfun k 1" shows "alpha k (hgt k p) = eps k / k"
proof -
  have "hgt k p > 0"
    by (simp add: Suc_leI hgt_gt_0)
  then have "alpha k (hgt k p) = alpha k 1"
    using Suc_le_D hgt_Least Suc_le_eq assms by fastforce
  also have "\<dots> = eps k / k"
    by (simp add: alpha_Suc_eq)
  finally show ?thesis .
qed

lemma Red_5_8:
  assumes i: "i \<in> Step_class \<mu> l k dreg_step" 
    and x: "x \<in> Xseq \<mu> l k (Suc i)" 
  shows "card (Neighbours Red x \<inter> Yseq \<mu> l k (Suc i))
         \<ge> (1 - (eps k) powr (1/2)) * pee \<mu> l k i * (card (Yseq \<mu> l k (Suc i)))"
proof -
  let ?p = "pee \<mu> l k i"
  obtain X Y A B
    where step: "stepper \<mu> l k i = (X,Y,A,B)"
      and nonterm: "\<not> termination_condition l k X Y"
      and "even i"
    using i
    by (auto simp: step_kind_defs split: if_split_asm prod.split_asm)
  then have Suc_i: "stepper \<mu> l k (Suc i) = degree_reg k (X,Y,A,B)"
    by simp
  have XY: "X = Xseq \<mu> l k i" "Y = Yseq \<mu> l k i"
    using step stepper_XYseq by auto
  have "Xseq \<mu> l k (Suc i) = ((\<lambda>(X, Y, A, B). X) \<circ> stepper \<mu> l k) (Suc i)"
    by (simp add: Xseq_def)
  also have "\<dots> = X_degree_reg k X Y"
    using \<open>even i\<close> step nonterm by (auto simp: degree_reg_def)
  finally have XSuc: "Xseq \<mu> l k (Suc i) = X_degree_reg k X Y" .
  have YSuc: "Yseq \<mu> l k (Suc i) = Yseq \<mu> l k i"
    using Suc_i step by (auto simp: degree_reg_def stepper_XYseq)
  have p_gt_invk: "?p > 1/k"
    using "XY" nonterm pee_def termination_condition_def by auto
  have RedN: "(?p - eps k powr -(1/2) * alpha k (hgt k ?p)) * card Y \<le> card (Neighbours Red x \<inter> Y)"
    using x XY by (simp add: XSuc YSuc X_degree_reg_def pee_def red_dense_def)
  show ?thesis
  proof (cases "?p \<ge> qfun k 0")
    case True
    have "i \<notin> Step_class \<mu> l k halted"
      using i by (simp add: Step_class_def)
    then have p0: "1/k < p0"
      by (metis Step_class_halted_forever le_eq_less_or_eq not_halted_pee_gt not_gr0 pee_eq_p0)
    have 0: "eps k powr -(1/2) \<ge> 0"
      by simp
    have "eps k powr -(1/2) * alpha k (hgt k ?p) \<le> eps k powr (1/2) * (?p - qfun k 0 + 1/k)"
      using mult_left_mono [OF Red_5_7b [OF True] 0]
      by (simp add: eps_def powr_mult_base flip: mult_ac)
    also have "\<dots> \<le> eps k powr (1/2) * ?p"
      using p0 by (intro mult_left_mono) (auto simp flip: pee_eq_p0)
    finally have "eps k powr -(1/2) * alpha k (hgt k ?p) \<le> eps k powr (1/2) * ?p" .
    then have "(1 - (eps k) powr (1/2)) * ?p * (card Y) \<le> (?p - eps k powr -(1/2) * alpha k (hgt k ?p)) * card Y"
      by (intro mult_right_mono) (auto simp: algebra_simps)
    with XY RedN YSuc show ?thesis by fastforce
  next
    case False
    then have "pee \<mu> l k i \<le> qfun k 1"
      by (smt (verit, best) alpha_eq alpha_ge0 One_nat_def add_diff_cancel_left' plus_1_eq_Suc q_Suc_diff zero_less_one)
    then have "eps k powr -(1/2) * alpha k (hgt k ?p) = eps k powr (1/2) / k"
      using powr_mult_base [of "eps k"] epsk_gt0 by (force simp add: Red_5_7c mult.commute)
    also have "\<dots> \<le> eps k powr (1/2) * ?p"
      using p_gt_invk by (smt (verit) divide_inverse inverse_eq_divide mult_left_mono powr_ge_pzero)
    finally have "eps k powr -(1/2) * alpha k (hgt k ?p) \<le> eps k powr (1/2) * ?p" .
    then have "(1 - (eps k) powr (1/2)) * ?p * (card Y) \<le> (?p - eps k powr -(1/2) * alpha k (hgt k ?p)) * card Y"
      by (intro mult_right_mono) (auto simp: algebra_simps)
    with XY RedN YSuc show ?thesis by fastforce
  qed
qed

corollary Y_Neighbours_nonempty_Suc:
  assumes i: "i \<in> Step_class \<mu> l k dreg_step" 
    and x: "x \<in> Xseq \<mu> l k (Suc i)" 
    and "k\<ge>2"
  shows "Neighbours Red x \<inter> Yseq \<mu> l k (Suc i) \<noteq> {}"
proof
  assume con: "Neighbours Red x \<inter> Yseq \<mu> l k (Suc i) = {}"
  have not_halted: "i \<notin> Step_class \<mu> l k halted"
    using i by (auto simp: Step_class_def)
  then have 0: "pee \<mu> l k i > 0"
    using not_halted_pee_gt0 by blast
  have Y': "card (Yseq \<mu> l k (Suc i)) > 0"
  proof -
    obtain X Y A B
      where step: "stepper \<mu> l k i = (X,Y,A,B)" and "even i"
      using i by (auto simp: step_kind_defs split: if_split_asm prod.split_asm)
    then show ?thesis
      apply (simp add: Yseq_def degree_reg_def)
      using Yseq_gt_0 not_halted stepper_XYseq by blast
  qed
  have "(1 - eps k powr (1 / 2)) * pee \<mu> l k i * card (Yseq \<mu> l k (Suc i)) \<le> 0"
    using Red_5_8 [OF i x] con by simp 
  with 0 Y' have "(1 - eps k powr (1 / 2)) \<le> 0"
    by (simp add: mult_le_0_iff zero_le_mult_iff)
  then show False
    using \<open>k\<ge>2\<close> powr_le_cancel_iff [of k "1/8" 0]
    by (simp add: eps_def powr_minus_divide powr_divide powr_powr)
qed

corollary Y_Neighbours_nonempty:
  assumes i: "i \<in> Step_class_reddboost \<mu> l k" 
    and x: "x \<in> Xseq \<mu> l k i" 
    and "k\<ge>2"
  shows "card (Neighbours Red x \<inter> Yseq \<mu> l k i) > 0"
proof (cases i)
  case 0
  with assms show ?thesis
    by (auto simp: Step_class_def stepper_kind_def split: if_split_asm)
next
  case (Suc i')
  then have "i' \<in> Step_class \<mu> l k dreg_step"
    using dreg_before_dboost_step dreg_before_red_step i by fastforce
  then have "Neighbours Red x \<inter> Yseq \<mu> l k (Suc i') \<noteq> {}"
    using Suc Y_Neighbours_nonempty_Suc assms by blast
  then show ?thesis
    by (simp add: Suc card_gt_0_iff finite_Neighbours)
qed

definition "Big_Red_5_1 \<equiv> \<lambda>\<mu> l. (1-\<mu>) * l > 1 \<and> l powr (5/2) \<ge> 3 / (1-\<mu>) \<and> l powr (1/4) \<ge> 4 
                    \<and> Lemma_5_4 \<mu> l \<and> Lemma_5_6 l" 

proposition Red_5_1:
  assumes i: "i \<in> Step_class_reddboost \<mu> l k" and \<mu>: "0<\<mu>" "\<mu><1" and Big: "Big_Red_5_1 \<mu> l" "Colours l k"
  defines "p \<equiv> pee \<mu> l k i"
  defines "x \<equiv> cvx \<mu> l k i"
  defines "X \<equiv> Xseq \<mu> l k i" and "Y \<equiv> Yseq \<mu> l k i"
  defines "NBX \<equiv> Neighbours Blue x \<inter> X"
  defines "NRX \<equiv> Neighbours Red x \<inter> X"
  defines "NRY \<equiv> Neighbours Red x \<inter> Y"
  defines "\<beta> \<equiv> card NBX / card X"
  shows "red_density NRX NRY \<ge> p - alpha k (hgt k p)
       \<or> red_density NBX NRY \<ge> p + (1 - eps k) * ((1-\<beta>) / \<beta>) * alpha k (hgt k p) \<and> \<beta> > 0"
proof -
  have Red_5_4: "weight X Y x \<ge> - real (card X) / (real k) ^ 5"
    using Big i by (auto simp: Big_Red_5_1_def Lemma_5_4_def x_def X_def Y_def)
  have lA: "(1-\<mu>) * l > 1" and "l\<le>k" and l144: "real l powr (1/4) \<ge> 4"
    using Big by (auto simp: Big_Red_5_1_def Colours_def)
  then have k_powr_14: "k powr (1/4) \<ge> 4"
    by (smt (verit) divide_nonneg_nonneg of_nat_0_le_iff of_nat_mono powr_mono2)
  have "k \<ge> 256"
    using powr_mono2 [of 4, OF _ _ k_powr_14] by (simp add: powr_powr flip: powr_numeral)
  then have "k>0" by linarith
  have k52: "3 / (1-\<mu>) \<le> k powr (5/2)"
    using Big \<open>l\<le>k\<close> unfolding Big_Red_5_1_def
    by (smt (verit) of_nat_0_le_iff of_nat_mono powr_mono2 zero_le_divide_iff)
  have RN_le_RN: "k ^ 6 * RN k (m_of l) \<le> RN k (nat \<lceil>real l powr (3/4)\<rceil>)"
    using Big \<open>l \<le> k\<close> by (auto simp: Big_Red_5_1_def Lemma_5_6_def)
  have l34_ge3: "real l powr (3/4) \<ge> 3"
    by (smt (verit, ccfv_SIG) l144 divide_nonneg_nonneg frac_le of_nat_0_le_iff powr_le1 powr_less_cancel)
  note XY = X_def Y_def
  obtain A B
    where step: "stepper \<mu> l k i = (X,Y,A,B)"
      and nonterm: "\<not> termination_condition l k X Y"
      and "odd i"
      and non_mb: "\<not> many_bluish \<mu> l k X"
    using i
    by (auto simp: XY step_kind_defs split: if_split_asm prod.split_asm)
  then have "card X > 0"
    using stepper_XYseq by (auto simp: termination_condition_def)
  have not_halted: "i \<notin> Step_class \<mu> l k halted"
    using i by (auto simp: Step_class_def)
  with Yseq_gt_0 XY have "card Y \<noteq> 0"
    by blast
  have cX_RN: "card X > RN k (nat \<lceil>real l powr (3/4)\<rceil>)"
    by (meson linorder_not_le nonterm termination_condition_def)
  then have X_gt_k: "card X > k"
    by (metis l34_ge3 RN_3plus' of_nat_numeral order.trans le_natceiling_iff not_less)
  have "0 < RN k (m_of l)"
    using RN_eq_0_iff m_of_def many_bluish_def non_mb by presburger
  then have "k^4 \<le> k^6 * RN k (m_of l)"
    by (simp add: eval_nat_numeral)
  also have "... < card X"
    using cX_RN RN_le_RN by linarith
  finally have "card X > k^4" .
  have "x \<in> X"
    using cvx_in_Xseq i XY x_def by blast
  have "X \<subseteq> V"
    by (simp add: Xseq_subset_V XY)
  have "finite NRX" "finite NBX" "finite NRY"
    by (auto simp add: NRX_def NBX_def NRY_def finite_Neighbours)
  have "disjnt X Y"
    using Xseq_Yseq_disjnt step stepper_XYseq by blast  
  then have "disjnt NRX NRY" "disjnt NBX NRY"
    by (auto simp add: NRX_def NBX_def NRY_def disjnt_iff)
  have card_NBX_le: "card NBX \<le> \<mu> * card X"
    using central_vertex_def cvx_works i XY x_def NBX_def by presburger
  moreover have card_NRBX: "card NRX + card NBX = card X - 1"
    using Neighbours_RB [of x X] \<open>finite NRX\<close> \<open>x\<in>X\<close> \<open>X\<subseteq>V\<close> disjnt_Red_Blue_Neighbours
    by (simp add: NRX_def NBX_def finite_Neighbours subsetD flip: card_Un_disjnt)
  ultimately have "card NRX \<ge> (1-\<mu>) * card X - 1"
    by (simp add: algebra_simps)
  with lA \<open>l\<le>k\<close> X_gt_k have "card NRX > 0"
    by (smt (verit, best) of_nat_0 \<open>\<mu><1\<close> gr0I mult_less_cancel_left_pos nat_less_real_le of_nat_mono)
  have "card NRY > 0"
    using Y_Neighbours_nonempty [OF i] \<open>k\<ge>256\<close> NRY_def \<open>finite NRY\<close> \<open>x \<in> X\<close> card_0_eq XY by force
  show ?thesis
  proof (cases "(\<Sum>y \<in> NRX. Weight X Y x y) 
             \<ge> - alpha k (hgt k p) * card NRX * card NRY / card Y")
    case True
    then have "(p - alpha k (hgt k p)) * (card NRX * card NRY) \<le> (\<Sum>y \<in> NRX. p * card NRY + Weight X Y x y * card Y)"
      using \<open>card Y \<noteq> 0\<close> by (simp add: field_simps sum_distrib_left sum.distrib)
    also have "\<dots> = (\<Sum>y \<in> NRX. card (Neighbours Red x \<inter> Neighbours Red y \<inter> Y))"
      using \<open>card Y \<noteq> 0\<close> by (simp add: Weight_def pee_def XY NRY_def field_simps p_def)
    also have "\<dots> = edge_card Red NRY NRX"
      using \<open>disjnt NRX NRY\<close> \<open>finite NRX\<close>
      by (simp add: disjnt_sym edge_card_eq_sum_Neighbours Red_E psubset_imp_subset NRY_def Int_ac)
    also have "\<dots> = edge_card Red NRX NRY"
      by (simp add: edge_card_commute)
    finally have "(p - alpha k (hgt k p)) * real (card NRX * card NRY) \<le> real (edge_card Red NRX NRY)" .
    then show ?thesis
      using \<open>card NRX > 0\<close> \<open>card NRY > 0\<close> 
      by (simp add: NRX_def NRY_def gen_density_def field_split_simps XY)
  next
    case False
    have "x \<in> X"
      unfolding x_def using cvx_in_Xseq i XY by blast
    with Neighbours_RB[of x X] have Xx: "X - {x} = NBX \<union> NRX"
      using Diagonal.Xseq_subset_V Diagonal_axioms NRX_def NBX_def XY by blast
    have disjnt: "NBX \<inter> NRX = {}"
      by (auto simp: Blue_eq NRX_def NBX_def disjoint_iff in_Neighbours_iff)
    then have "weight X Y x = (\<Sum>y \<in> NRX. Weight X Y x y) + (\<Sum>y \<in> NBX. Weight X Y x y)"
      by (simp add: weight_def Xx sum.union_disjoint finite_Neighbours NRX_def NBX_def)
    with False 
    have 15: "(\<Sum>y \<in> NBX. Weight X Y x y) 
        \<ge> weight X Y x + alpha k (hgt k p) * card NRX * card NRY / card Y"
      by linarith    
    have pm1: "pee \<mu> l k (i-1) > 1/k"
      by (meson Step_class_not_halted diff_le_self not_halted not_halted_pee_gt)
    have \<beta>_eq: "\<beta> = card NBX / card X"
      using NBX_def \<beta>_def XY by blast
    have "\<beta>\<le>\<mu>"
      by (simp add: \<beta>_eq \<open>0 < card X\<close> card_NBX_le pos_divide_le_eq)
    have im1: "i-1 \<in> Step_class \<mu> l k dreg_step"
      using i \<open>odd i\<close> dreg_before_dboost_step dreg_before_red_step by fastforce
    have "eps k \<le> 1/4"
      using \<open>k>0\<close> k_powr_14 by (simp add: eps_def powr_minus_divide)
    then have "eps k powr (1/2) \<le> (1/4) powr (1/2)"
      by (simp add: eps_def powr_mono2)
    then have A: "1/2 \<le> 1 - eps k powr (1/2)"
      by (simp add: powr_divide)
    have le: "1 / (2 * real k) \<le> (1 - eps k powr (1/2)) * pee \<mu> l k (i-1)"
      using pm1 \<open>k>0\<close> mult_mono [OF A less_imp_le [OF pm1]] A by simp
    have "card Y / (2 * real k) \<le> (1 - eps k powr (1/2)) * pee \<mu> l k (i-1) * card Y"
      using mult_left_mono [OF le] by (metis mult.commute divide_inverse inverse_eq_divide of_nat_0_le_iff)
    also have "... \<le> card NRY"
      using pm1 Red_5_8 im1 by (metis NRY_def One_nat_def \<open>odd i\<close> \<open>x \<in> X\<close> XY odd_Suc_minus_one)
    finally have Y_NRY: "card Y / (2 * real k) \<le> card NRY" .
    have "NBX \<noteq> {}"
    proof 
      assume empty: "NBX = {}"
      then have cNRX: "card NRX = card X - 1"
        using card_NRBX by auto
      have "card X > 3"
        using \<open>k\<ge>256\<close> X_gt_k by linarith
      then have "2 * card X / real (card X - 1) < 3"
        by (simp add: divide_simps)
      also have "... \<le> k ^ 2"
        using mult_mono [OF \<open>k\<ge>256\<close> \<open>k\<ge>256\<close>] by (simp add: power2_eq_square flip: of_nat_mult)
      also have "... \<le> eps k * k^3"
        using \<open>k\<ge>256\<close> by (simp add: eps_def flip: powr_numeral powr_add)
      finally have "(real (2 * card X) / real (card X - 1)) * k^2 < eps k * real (k ^ 3) * k^2"
        using \<open>k>0\<close> by (intro mult_strict_right_mono) auto
      then have "real (2 * card X) / real (card X - 1) * k^2 < eps k * real (k ^ 5)"
        by (simp add: mult.assoc flip: of_nat_mult)
      then have "0 < - real (card X) / (real k) ^ 5 + (eps k / k) * real (card X - 1) * (1 / (2 * real k))"
        using \<open>k>0\<close> X_gt_k by (simp add: field_simps power2_eq_square)
      also have "- real (card X) / (real k) ^ 5 + (eps k / k) * real (card X - 1) * (1 / (2 * real k)) 
               \<le> - real (card X) / (real k) ^ 5 + (eps k / k) * real (card NRX) * (card NRY / card Y)"
        using Y_NRY \<open>k>0\<close> \<open>card Y \<noteq> 0\<close>
        by (intro add_mono mult_mono) (auto simp: cNRX eps_def divide_simps)
      also have "... = - real (card X) / (real k) ^ 5 + (eps k / k) * real (card NRX) * card NRY / card Y"
        by simp
      also have "\<dots> \<le> - real (card X) / (real k) ^ 5 + alpha k (hgt k p) * real (card NRX) * card NRY / card Y"
        using alpha_ge [OF hgt_gt_0]
        by (intro add_mono mult_right_mono divide_right_mono) auto
      also have "\<dots> \<le> weight X Y x + alpha k (hgt k p) * real (card NRX) * card NRY / real (card Y)"
        using Red_5_4 by simp
      also have "... \<le> 0"
        using empty 15 by auto
      finally show False
        by simp
    qed
    have "card NBX > 0"
      by (simp add: \<open>NBX \<noteq> {}\<close> \<open>finite NBX\<close> card_gt_0_iff)
    then have "0 < \<beta>"
      by (simp add: \<beta>_eq \<open>0 < card X\<close>)
    have "\<beta> \<le> \<mu>"
      using X_gt_k card_NBX_le by (simp add: \<beta>_eq NBX_def divide_simps)
    have cNRX: "card NRX = (1-\<beta>) * card X - 1"
      using X_gt_k card_NRBX by (simp add: \<beta>_eq field_simps)
    have cNBX: "card NBX = \<beta> * card X"
      using \<open>0 < card X\<close> by (simp add: \<beta>_eq)
    let ?E16 = "p + ((1-\<beta>)/\<beta>) * alpha k (hgt k p) - alpha k (hgt k p) / (\<beta> * card X) + weight X Y x * card Y / (\<beta> * card X * card NRY)"
    have "p * card NBX * card NRY + alpha k (hgt k p) * card NRX * card NRY + weight X Y x * card Y
            \<le> (\<Sum>y \<in> NBX. p * card NRY + Weight X Y x y * card Y)"
      using 15 \<open>card Y \<noteq> 0\<close> apply (simp add: sum_distrib_left sum.distrib)
      by (simp only: sum_distrib_right divide_simps split: if_split_asm)
    also have "... \<le> (\<Sum>y \<in> NBX. card (Neighbours Red x \<inter> Neighbours Red y \<inter> Y))"
      using \<open>card Y \<noteq> 0\<close> by (simp add: Weight_def pee_def XY NRY_def field_simps p_def)
    also have "\<dots> = edge_card Red NRY NBX"
      using \<open>disjnt NBX NRY\<close> \<open>finite NBX\<close>
      by (simp add: disjnt_sym edge_card_eq_sum_Neighbours Red_E psubset_imp_subset NRY_def Int_ac)
    also have "\<dots> = edge_card Red NBX NRY"
      by (simp add: edge_card_commute)
    finally have Red_bound: 
      "p * card NBX * card NRY + alpha k (hgt k p) * card NRX * card NRY + weight X Y x * card Y \<le> edge_card Red NBX NRY" .
    then have "(p * card NBX * card NRY + alpha k (hgt k p) * card NRX * card NRY + weight X Y x * card Y) / (card NBX * card NRY) \<le> red_density NBX NRY"
      by (metis divide_le_cancel gen_density_def of_nat_less_0_iff)
    then have "p + alpha k (hgt k p) * card NRX / card NBX + weight X Y x * card Y / (card NBX * card NRY) \<le> red_density NBX NRY" 
      using \<open>card NBX > 0\<close> \<open>card NRY > 0\<close> by (simp add: add_divide_distrib)
    then have 16: "?E16 \<le> red_density NBX NRY" 
      using \<open>\<beta>>0\<close> \<open>card X > 0\<close>
      by (simp add: cNRX cNBX algebra_simps add_divide_distrib diff_divide_distrib)
    consider "qfun k 0 \<le> p" | "p \<le> qfun k 1"
      by (smt (verit) alpha_Suc_eq alpha_ge0 One_nat_def q_Suc_diff)
    then have alpha_le_1: "alpha k (hgt k p) \<le> 1"
    proof cases
      case 1
      have "p * eps k + eps k / real k \<le> 1 + eps k * p0"
      proof (intro add_mono)
        show "p * eps k \<le> 1"
          by (smt (verit) epsk_le1 \<open>0 < k\<close> mult_left_le p_def pee_ge0 pee_le1)
        have "p0 > 1/k"
          by (metis Step_class_not_halted diff_le_self not_halted not_halted_pee_gt diff_is_0_eq' pee_eq_p0)
        then show "eps k / real k \<le> eps k * p0"
          unfolding divide_inverse
          by (intro mult_left_mono) (auto simp: eps_def)
      qed
      then have "eps k * (p - qfun k 0 + 1 / real k) \<le> 1"
        by (simp add: algebra_simps)
      then show ?thesis
        using Red_5_7b [OF 1] by linarith
    next
      case 2
      show ?thesis
        using Red_5_7c [OF 2] \<open>k\<ge>256\<close> epsk_less1 [of k] by simp
    qed
    have B: "- (3 / (real k ^ 4)) \<le> (-2 / real k ^ 4) - alpha k (hgt k p) / card X"
      using \<open>card X > k^4\<close> \<open>card Y \<noteq> 0\<close> \<open>0 < k\<close> alpha_le_1 by (simp add: algebra_simps frac_le)
    have "- (3 / (\<beta> * real k ^ 4)) \<le> (-2 / real k ^ 4) / \<beta> - alpha k (hgt k p) / (\<beta> * card X)"
      using \<open>\<beta>>0\<close> divide_right_mono [OF B, of \<beta>] \<open>k>0\<close> by (simp add: field_simps)
    also have "... = (- real (card X) / real k ^ 5) / (\<beta> * real (card X)) * (2 * real k) - alpha k (hgt k p) / (\<beta> * card X)"
      using \<open>0 < card X\<close> by (simp add: field_split_simps eval_nat_numeral)
    also have "... = (- real (card X) / real k ^ 5) * card Y / (\<beta> * real (card X) * (card Y / (2 * real k))) - alpha k (hgt k p) / (\<beta> * card X)"
      using \<open>card Y \<noteq> 0\<close> by simp
    also have "\<dots>  \<le> (- real (card X) / real k ^ 5) * card Y / (\<beta> * real (card X) * card NRY) - alpha k (hgt k p) / (\<beta> * card X)"
      using Y_NRY \<open>k>0\<close> \<open>card NRY > 0\<close> \<open>card X > 0\<close> \<open>card Y \<noteq> 0\<close> \<open>\<beta>>0\<close>
      by (intro diff_mono divide_right_mono mult_left_mono divide_left_mono_neg) auto
    also have "\<dots>  \<le> weight X Y x * card Y / (\<beta> * real (card X) * card NRY) - alpha k (hgt k p) / (\<beta> * card X)"
      using Red_5_4 \<open>k>0\<close> \<open>0 < \<beta>\<close>
      by (intro diff_mono divide_right_mono mult_right_mono) auto
    finally have "- (3 / (\<beta> * real k ^ 4)) \<le> weight X Y x * card Y / (\<beta> * real (card X) * card NRY) - alpha k (hgt k p) / (\<beta> * card X)" .
    then have 17: "p + ((1-\<beta>)/\<beta>) * alpha k (hgt k p) - 3 / (\<beta> * real k ^ 4) \<le> ?E16"
      by simp
    have "3 / real k ^ 4 \<le> (1-\<mu>) * eps k ^ 2 / k"
      using \<open>k>0\<close> \<open>\<mu><1\<close> mult_left_mono [OF k52, of k] 
      by (simp add: field_simps eps_def powr_powr powr_mult_base flip: powr_numeral powr_add)
    also have "... \<le> (1-\<beta>) * eps k ^ 2 / k"
      using \<open>\<beta>\<le>\<mu>\<close>
      by (intro divide_right_mono mult_right_mono) auto
    also have "... \<le> (1-\<beta>) * eps k * alpha k (hgt k p)"
      using Red_5_7a [of k p] epsk_ge0 \<open>\<beta>\<le>\<mu>\<close> \<open>\<mu><1\<close>
      unfolding power2_eq_square divide_inverse mult.assoc
      by (intro mult_mono) auto
    finally have "3 / real k ^ 4 \<le> (1-\<beta>) * eps k * alpha k (hgt k p)" .
    then have "p + (1 - eps k) * ((1-\<beta>) / \<beta>) * alpha k (hgt k p) \<le> p + ((1-\<beta>)/\<beta>) * alpha k (hgt k p) - 3 / (\<beta> * real k ^ 4)"
      using \<open>0<\<beta>\<close> by (simp add: field_simps)
    with 16 17 have "p + (1 - eps k) * ((1 - \<beta>) / \<beta>) * alpha k (hgt k p) \<le> red_density NBX NRY"
      by linarith
    then show ?thesis
      using \<open>0 < \<beta>\<close> NBX_def NRY_def XY by fastforce
  qed
qed

text \<open>This and the previous result are proved under the assumption of a sufficiently large @{term l}\<close>
corollary Red_5_2_Main:
  assumes i: "i \<in> Step_class \<mu> l k dboost_step" and "0<\<mu>" "\<mu><1"
    and Big: "Big_Red_5_1 \<mu> l" "Colours l k"
  shows "pee \<mu> l k (Suc i) - pee \<mu> l k i
         \<ge> (1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k (hgt k (pee \<mu> l k i)) \<and>
           beta \<mu> l k i > 0"
proof -
  let ?x = "cvx \<mu> l k i"
  obtain X Y A B
    where step: "stepper \<mu> l k i = (X,Y,A,B)"
      and nonterm: "\<not> termination_condition l k X Y"
      and "odd i"
      and non_mb: "\<not> many_bluish \<mu> l k X"
      and nonredd: "\<not> reddish k X Y (red_density X Y) (choose_central_vx \<mu> (X,Y,A,B))"
    using i
    by (auto simp: step_kind_defs split: if_split_asm prod.split_asm)
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
    using step nonterm \<open>odd i\<close> non_mb nonredd
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
    using Red_5_1 Un_iff Xeq Yeq assms gen_density_ge0 pee
    by (smt (verit, ccfv_threshold) \<beta>eq divide_eq_eq)
  moreover have "red_density (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i)
      (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i) \<le> pee \<mu> l k (Suc i)"
    using SUC Xeq Yeq stepper_XYseq by (simp add: pee_def)
  ultimately show ?thesis
    by linarith
qed


text \<open>establishing the size requirements for 5.1\<close>
lemma Big_Red_5_1:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_Red_5_1 \<mu> l"
proof -
  have "\<forall>\<^sup>\<infinity>l. (1-\<mu>) * l > 1"
    using \<open>\<mu><1\<close> by real_asymp
  moreover have "\<forall>\<^sup>\<infinity>l. l powr (5/2) \<ge> 3 / (1-\<mu>)"
    using \<open>\<mu><1\<close> by real_asymp
  moreover have "\<forall>\<^sup>\<infinity>l. l powr (1/4) \<ge> 4"
    using \<open>\<mu><1\<close> by real_asymp
  ultimately show ?thesis
    by (simp add: Big_Red_5_1_def eventually_conj Red_5_4 [OF assms] Red_5_6)
qed


corollary Red_5_2:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. \<forall>i \<in> Step_class \<mu> l k dboost_step.
         Colours l k \<longrightarrow>
         pee \<mu> l k (Suc i) - pee \<mu> l k i
         \<ge> (1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k (hgt k (pee \<mu> l k i))
      \<and> beta \<mu> l k i > 0"
  using Big_Red_5_1 Red_5_2_Main assms 
  unfolding eventually_sequentially by (meson order.trans)

definition 
  "Lemma_5_3 \<equiv> 
      \<lambda>\<mu> l. \<forall>k. \<forall>i \<in> Step_class \<mu> l k dboost_step.
            Colours l k \<longrightarrow> pee \<mu> l k (Suc i) \<ge> pee \<mu> l k i \<and> beta \<mu> l k i \<ge> 1 / (real k)\<^sup>2"

text \<open>This is a weaker consequence of the previous results\<close>
corollary Red_5_3:
  assumes "0<\<mu>" "\<mu><1" shows "\<forall>\<^sup>\<infinity>l. Lemma_5_3 \<mu> l"
proof -
  define Big where 
    "Big \<equiv> \<lambda>l. 1 / (real l)\<^sup>2 \<le> 1 / (l / eps l / (1 - eps l) + 1) \<and> l>1 \<and> Big_Red_5_1 \<mu> l"
  have "\<forall>\<^sup>\<infinity>l. 1 / (real l)\<^sup>2 \<le> 1 / (l / eps l / (1 - eps l) + 1)"
    unfolding eps_def by real_asymp
  moreover have "\<forall>\<^sup>\<infinity>l. l>1"
    by auto
  ultimately have Big: "\<forall>\<^sup>\<infinity>l. Big l"
    using Big_Red_5_1 assms by (simp add: Big_def eventually_conj)
  have "pee \<mu> l k (Suc i) \<ge> pee \<mu> l k i \<and> beta \<mu> l k i \<ge> 1 / (real k)\<^sup>2"
    if l: "\<forall>k\<ge>l. Big k" and i: "i \<in> Step_class \<mu> l k dboost_step" and "Colours l k" for l k i
  proof 
    have Big: "Big_Red_5_1 \<mu> l"
      using l by (auto simp: Big_def)
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
      using Red_5_2_Main [OF i assms Big] \<open>Colours l k\<close> by linarith 
    have "pee \<mu> l k (Suc i) - pee \<mu> l k i \<le> 1"
      by (smt (verit) pee_ge0 pee_le1)
    with Red_5_2_Main [OF i assms Big] \<open>Colours l k\<close>
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
    ultimately show "beta \<mu> l k i \<ge> 1 / (real k)\<^sup>2"
      by auto
  qed
  with Big show ?thesis
    unfolding eventually_sequentially Lemma_5_3_def by (meson order.trans)
qed

end (*context Diagonal*)

end
