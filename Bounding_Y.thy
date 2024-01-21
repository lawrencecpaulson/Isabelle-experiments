section \<open>Bounding the Size of @{term Y}\<close>

theory Bounding_Y imports Red_Steps

begin

context Diagonal
begin

subsection \<open>The following results together are Lemma 6.4\<close>
text \<open>Compared with the paper, all the indices are greater by one\<close>

lemma Y_6_4_Red: 
  assumes i: "i \<in> Step_class \<mu> l k red_step"
  shows "pee \<mu> l k (Suc i) \<ge> pee \<mu> l k i - alpha k (hgt k (pee \<mu> l k i))"
proof -
  define X where "X \<equiv> Xseq \<mu> l k i" 
  define Y where "Y \<equiv> Yseq \<mu> l k i"
  obtain A B 
    where step: "stepper \<mu> l k i = (X,Y,A,B)"
      and nonterm: "\<not> termination_condition l k X Y"
      and "odd i"
      and non_mb: "\<not> many_bluish \<mu> l k X"
      and red: "reddish k X Y (red_density X Y) (cvx \<mu> l k i)"
    using i
    by (auto simp: X_def Y_def step_kind_defs cvx_def split: if_split_asm prod.split_asm)
  have "Xseq \<mu> l k (Suc i) = Neighbours Red (cvx \<mu> l k i) \<inter> X"
       "Yseq \<mu> l k (Suc i) = Neighbours Red (cvx \<mu> l k i) \<inter> Y"
    using step nonterm \<open>odd i\<close> non_mb red
    by (auto simp add: Xseq_def Yseq_def next_state_def cvx_def Let_def split: prod.split)
  then show ?thesis
    using red by (simp add: X_def Y_def reddish_def pee_def)
qed

lemma Y_6_4_DegreeReg: 
  assumes "i \<in> Step_class \<mu> l k dreg_step" 
  shows "pee \<mu> l k (Suc i) \<ge> pee \<mu> l k i"
proof -
  define X where "X \<equiv> Xseq \<mu> l k i" 
  define Y where "Y \<equiv> Yseq \<mu> l k i"
  obtain A B
    where step: "stepper \<mu> l k i = (X,Y,A,B)"
      and nonterm: "\<not> termination_condition l k X Y"
      and "even i"
    using assms by (auto simp: X_def Y_def step_kind_defs split: if_split_asm prod.split_asm)
  then have "Yseq \<mu> l k (Suc i) = Y" "Xseq \<mu> l k (Suc i) = X_degree_reg k X Y"
    by (simp_all add: step_kind_defs next_state_def degree_reg_def)
  then show ?thesis
    by (simp add: X_def Xseq_Yseq_disjnt Y_def pee_def red_density_X_degree_reg_ge)
qed

lemma Y_6_4_Bblue: 
  assumes i: "i \<in> Step_class \<mu> l k bblue_step" and "0 < \<mu>"
  shows "pee \<mu> l k (Suc i) \<ge> pee \<mu> l k (i-1) - (eps k powr (-1/2)) * alpha k (hgt k (pee \<mu> l k (i-1)))"
proof -
  define X where "X \<equiv> Xseq \<mu> l k i" 
  define Y where "Y \<equiv> Yseq \<mu> l k i"
  obtain A B S T
    where step: "stepper \<mu> l k i = (X,Y,A,B)"
      and nonterm: "\<not> termination_condition l k X Y"
      and "odd i"
      and mb: "many_bluish \<mu> l k X"
      and bluebook: "(S,T) = choose_blue_book \<mu> (X,Y,A,B)"
    using i  
    by (simp add: X_def Y_def step_kind_defs split: if_split_asm prod.split_asm) (metis mk_edge.cases)
  then have X1_eq: "Xseq \<mu> l k (Suc i) = T"
    by (force simp: Xseq_def next_state_def split: prod.split)
  have Y1_eq: "Yseq \<mu> l k (Suc i) = Y"
    using i by (simp add: Y_def step_kind_defs next_state_def split: if_split_asm prod.split_asm prod.split)
  have "disjnt X Y"
    using Xseq_Yseq_disjnt X_def Y_def by blast
  obtain fin: "finite X" "finite Y"
    by (metis V_state finX finY local.step)
  have "X \<noteq> {}" "Y \<noteq> {}"
    using gen_density_def nonterm termination_condition_def by fastforce+
  define i' where "i' = i-1"
  then have Suci': "Suc i' = i"
    by (simp add: \<open>odd i\<close>)
  have i': "i' \<in> Step_class \<mu> l k dreg_step"
    using \<open>odd i\<close> by (simp add: i'_def assms dreg_before_bblue_step)
  then have  "Xseq \<mu> l k (Suc i') = X_degree_reg k (Xseq \<mu> l k i') (Yseq \<mu> l k i')"
             "Yseq \<mu> l k (Suc i') = Yseq \<mu> l k i'"
      and nonterm': "\<not> termination_condition l k (Xseq \<mu> l k i') (Yseq \<mu> l k i')"
    by (auto simp add: degree_reg_def X_degree_reg_def step_kind_defs split: if_split_asm prod.split_asm)
  then have Xeq: "X = X_degree_reg k (Xseq \<mu> l k i') (Yseq \<mu> l k i')"
       and  Yeq: "Y = Yseq \<mu> l k i'"
    using Suci' by (auto simp: X_def Y_def)
  define pm where "pm \<equiv> (pee \<mu> l k i' - eps k powr -(1/2) * alpha k (hgt k (pee \<mu> l k i')))"
  have "T \<subseteq> X"
    using bluebook by (metis V_state choose_blue_book_subset local.step)
  then have T_reds: "\<And>x. x \<in> T \<Longrightarrow> pm * card Y \<le> card (Neighbours Red x \<inter> Y)"
    by (auto simp add: Xeq Yeq pm_def X_degree_reg_def pee_def red_dense_def)
  have "good_blue_book \<mu> X (S,T)"
    by (metis choose_blue_book_works V_state bluebook local.step)
  then have False if "real (card T) = 0"
    using \<open>0 < \<mu>\<close> \<open>X \<noteq> {}\<close> fin by (simp add: good_blue_book_def pos_prod_le that)
  then have "T\<noteq>{}"
    by force
  have "pm * card T * card Y = (\<Sum>x\<in>T. pm * card Y)"
    by simp
  also have "... \<le> (\<Sum>x\<in>T. card (Neighbours Red x \<inter> Y))"
    using T_reds by (simp add: sum_bounded_below)
  also have "... = edge_card Red T Y"
    using \<open>disjnt X Y\<close> \<open>finite X\<close> \<open>T\<subseteq>X\<close> Red_E
    by (metis disjnt_subset1 disjnt_sym edge_card_commute edge_card_eq_sum_Neighbours finite_subset)
  also have "... = red_density T Y * card T * card Y"
    using fin \<open>T\<subseteq>X\<close> by (simp add: finite_subset gen_density_def)
  finally have ***: "pm \<le> red_density T Y" 
    using fin \<open>T\<noteq>{}\<close> \<open>Y\<noteq>{}\<close>
    by (metis \<open>T \<subseteq> X\<close> card_gt_0_iff finite_subset mult_right_le_imp_le of_nat_0_less_iff)
  then show ?thesis
    by (simp add: X1_eq Y1_eq i'_def pee_def pm_def)
qed


lemmas Y_6_4_dbooSt = Red_5_3

subsection \<open>Towards Lemmas 6.3 and 6.2\<close>

definition "Z_class \<equiv> \<lambda>\<mu> l k. {i \<in> Step_class \<mu> l k red_step \<union> Step_class \<mu> l k bblue_step \<union> Step_class \<mu> l k dboost_step.
                        pee \<mu> l k (Suc i) < pee \<mu> l k (i-1) \<and> pee \<mu> l k (i-1) \<le> p0}"

text \<open>Lemma 6.3 except for the limit\<close>
lemma Y_6_3_Main:
  assumes "0<\<mu>" "\<mu><1" "Colours l k"
  assumes Red53: "Lemma_5_3 \<mu> l" and bblue_step_limit: "Lemma_bblue_step_limit \<mu> l"
  defines "p \<equiv> pee \<mu> l k"
  shows "(\<Sum>i \<in> Z_class \<mu> l k. p (i-1) - p (Suc i)) \<le> 2 * eps k"
proof -
  obtain "k > 0" \<open>l\<le>k\<close>
    by (meson Colours_def Colours_kn0 \<open>Colours l k\<close>)
  { fix i
    assume i: "i \<in> Step_class \<mu> l k dboost_step"
    then have "i-1 \<in> Step_class \<mu> l k dreg_step"
      using dboost_step_odd odd_pos dreg_before_dboost_step i by force
    then have "p (i-1) \<le> p i \<and> p i \<le> p (Suc i)"
      using Red53 \<open>Colours l k\<close> minus_nat.simps
      unfolding Lemma_5_3_def p_def
      by (metis Suc_diff_Suc Y_6_4_DegreeReg dboost_step_odd i One_nat_def odd_pos) 
  }        
  then have dboost: "Step_class \<mu> l k dboost_step \<inter> Z_class \<mu> l k = {}"
    by (fastforce simp: Z_class_def p_def)
  { fix i
    assume i: "i \<in> Step_class \<mu> l k bblue_step \<inter> Z_class \<mu> l k" 
    then have "i-1 \<in> Step_class \<mu> l k dreg_step"
      using dreg_before_bblue_step bblue_step_odd i by force
    have pee: "p (Suc i) < p (i-1)" "p (i-1) \<le> p0"
      and iB: "i \<in> Step_class \<mu> l k bblue_step"
      using i by (auto simp: Z_class_def p_def)
    have "hgt k (p (i-1)) = 1"
    proof -
      have "hgt k (p (i-1)) \<le> 1"
      proof (intro hgt_Least)
        show "p (i - 1) \<le> qfun k 1"
          unfolding qfun_def
          by (smt (verit) one_le_power pee divide_nonneg_nonneg epsk_ge0 of_nat_less_0_iff)
      qed auto
      then show ?thesis
        by (metis One_nat_def Suc_pred' diff_is_0_eq hgt_gt_0)
    qed
    then have "p (i-1) - p (Suc i) \<le> eps k powr -(1/2) * alpha k 1"
      using pee iB Y_6_4_Bblue \<open>0<\<mu>\<close> by (fastforce simp: p_def)
    also have "... \<le> 1/k"
    proof -
      have "real k powr - (1 / 8) \<le> 1"
        using \<open>k>0\<close> by (force simp add: less_eq_real_def nat_less_real_le powr_less_one)
      then show ?thesis
        by (simp add: alpha_eq eps_def powr_powr divide_le_cancel flip: powr_add)
    qed
    finally have "p (i-1) - p (Suc i) \<le> 1/k" .
  }
  then have "(\<Sum>i \<in> Step_class \<mu> l k bblue_step \<inter> Z_class \<mu> l k. p (i-1) - p (Suc i)) 
             \<le> card (Step_class \<mu> l k bblue_step \<inter> Z_class \<mu> l k) * (1/k)"
    using sum_bounded_above by (metis (mono_tags, lifting))
  also have "... \<le> card (Step_class \<mu> l k bblue_step) * (1/k)"
    using bblue_step_limit \<open>Colours l k\<close>
    by (simp add: divide_le_cancel card_mono Lemma_bblue_step_limit_def)
  also have "... \<le> l powr (3/4) / k"
    using bblue_step_limit \<open>Colours l k\<close> by (simp add: \<open>0 < k\<close> frac_le Lemma_bblue_step_limit_def)
  also have "... \<le> eps k"
  proof -
    have "l powr (3/4) \<le> k powr (3 / 4)"
      by (simp add: \<open>l \<le> k\<close> powr_mono2)
    then show ?thesis
      using powr_add [of k "3/4" "1/4"] 
    apply (simp add: eps_def powr_minus divide_simps)
      by (metis mult_le_cancel_right powr_non_neg)
  qed
  finally have bblue: "(\<Sum>i\<in>Step_class \<mu> l k bblue_step \<inter> Z_class \<mu> l k. p(i-1) - p (Suc i))
                     \<le> eps k" .
  { fix i
    assume i: "i \<in> Step_class \<mu> l k red_step \<inter> Z_class \<mu> l k" 
    then have pee_alpha: "p (i-1) - p (Suc i) 
                       \<le> p (i-1) - p i + alpha k (hgt k (p i))"
      using Y_6_4_Red by (force simp: p_def)
    have pee_le: "p (i-1) \<le> p i"
      unfolding p_def
      by (metis dreg_before_red_step Int_iff One_nat_def Y_6_4_DegreeReg i odd_Suc_minus_one red_step_odd)
    consider (1) "hgt k (p i) = 1" | (2) "hgt k (p i) > 1"
      by (metis hgt_gt_0 less_one nat_neq_iff)
    then have "p (i-1) - p i + alpha k (hgt k (p i)) \<le> eps k / k"
    proof cases
      case 1
      then show ?thesis
        by (smt (verit) Red_5_7c \<open>0 < k\<close> pee_le hgt_works) 
    next
      case 2
      then have p_gt_q: "p i > qfun k 1"
        by (meson hgt_Least not_le zero_less_one)
      have pee_le_q0: "p (i-1) \<le> qfun k 0"
        using 2 Z_class_def p_def i by auto
      also have pee2: "... \<le> p i"
        using alpha_eq p_gt_q 
        by (smt (verit, ccfv_SIG) One_nat_def alpha_ge0 diff_self_eq_0 q_Suc_diff zero_less_one)
      finally have "p (i - 1) \<le> p i" .
      then have "p (i-1) - p i + alpha k (hgt k (p i)) 
              \<le> qfun k 0 - p i + eps k * (p i - qfun k 0 + 1/k)"
        using Red_5_7b pee_le_q0 pee2 by fastforce
      also have "... \<le> eps k / k"
        using \<open>k>0\<close> pee2 by (simp add: algebra_simps) (smt (verit) affine_ineq epsk_le1)
      finally show ?thesis .
    qed
    with pee_alpha have "p (i-1) - p (Suc i) \<le> eps k / k"
      by linarith
  }
  then have "(\<Sum>i \<in> Step_class \<mu> l k red_step \<inter> Z_class \<mu> l k. p (i-1) - p (Suc i))
           \<le> card (Step_class \<mu> l k red_step \<inter> Z_class \<mu> l k) * (eps k / k)"
    using sum_bounded_above by (metis (mono_tags, lifting))
  also have "... \<le> card (Step_class \<mu> l k red_step) * (eps k / k)"
    using epsk_ge0[of k] assms
    by (simp add: divide_le_cancel mult_le_cancel_right card_mono red_step_limit)
  also have "... \<le> k * (eps k / k)"
    using red_step_limit [OF \<open>0<\<mu>\<close> \<open>Colours l k\<close>]
    by (smt (verit, best) divide_nonneg_nonneg epsk_ge0 mult_mono nat_less_real_le of_nat_0_le_iff)
  also have "... \<le> eps k"
    by (simp add: epsk_ge0)
  finally have red: "(\<Sum>i\<in>Step_class \<mu> l k stepkind.red_step \<inter> Z_class \<mu> l k. p (i - 1) - p (Suc i)) \<le> eps k" .
  have fin_bblue: "finite (Step_class \<mu> l k bblue_step)"
    using Lemma_bblue_step_limit_def \<open>Colours l k\<close> bblue_step_limit by presburger
  have fin_red: "finite (Step_class \<mu> l k red_step)"
    using \<open>0<\<mu>\<close> \<open>Colours l k\<close> red_step_limit(1) by blast
  have bblue_not_red: "\<And>x. x \<in> Step_class \<mu> l k bblue_step \<Longrightarrow> x \<notin> Step_class \<mu> l k red_step"
    by (meson disjnt_Step_class disjnt_iff stepkind.distinct(1))
  have eq: "Z_class \<mu> l k = Step_class \<mu> l k dboost_step \<inter> Z_class \<mu> l k 
                      \<union> Step_class \<mu> l k bblue_step \<inter> Z_class \<mu> l k
                      \<union> Step_class \<mu> l k red_step \<inter> Z_class \<mu> l k"
    by (auto simp: Z_class_def)
  show ?thesis
    using bblue red
    by (subst eq) (simp add: sum.union_disjoint dboost fin_bblue fin_red disjoint_iff bblue_not_red)
qed

corollary Y_6_3:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> (\<Sum>i \<in> Z_class \<mu> l k. pee \<mu> l k (i-1) - pee \<mu> l k (Suc i)) \<le> 2 * eps k"
proof -
  have "\<forall>\<^sup>\<infinity>l. Lemma_5_3 \<mu> l \<and> Lemma_bblue_step_limit \<mu> l"
    using eventually_conj Red_5_3 [OF assms] bblue_step_limit [OF \<open>0<\<mu>\<close>]
    by blast
  with Y_6_3_Main[OF assms] show ?thesis
    by (simp add: eventually_mono)
qed

lemma Y_6_5_Red:
  assumes i: "i \<in> Step_class \<mu> l k red_step" and "k\<ge>16"
  defines "p \<equiv> pee \<mu> l k"
  shows "hgt k (p (Suc i)) \<ge> hgt k (p i) - 2"
proof (cases "hgt k (p i) \<le> 3")
  case True
  have "hgt k (p (Suc i)) \<ge> 1"
    by (simp add: Suc_leI hgt_gt_0)
  with True show ?thesis
    by linarith
next
  case False
  have "k>0" using assms by auto
  have "eps k \<le> 1/2"
    using \<open>k\<ge>16\<close> by (simp add: epsk_eq_sqrt divide_simps real_le_rsqrt)
  moreover have "\<And>x::real. 0 \<le> x \<and> x \<le> 1/2 \<Longrightarrow> x * (1 + x)\<^sup>2 + 1 \<le> (1 + x)\<^sup>2"
    by sos
  ultimately have C: "eps k * (1 + eps k)\<^sup>2 + 1 \<le> (1 + eps k)\<^sup>2"
    using epsk_ge0 by presburger
  have le1: "eps k + 1 / (1 + eps k)\<^sup>2 \<le> 1"
    using mult_left_mono [OF C, of "inverse ((1 + eps k)\<^sup>2)"]
    by (simp add: ring_distribs inverse_eq_divide) (smt (verit))
  have 0: "0 \<le> (1 + eps k) ^ (hgt k (p i) - Suc 0)"
    using epsk_ge0 by auto
  have lesspi: "qfun k (hgt k (p i) - 1) < p i"
    using False hgt_Least [of "hgt k (p i)-1" "p i" k] by linarith
  have A: "(1 + eps k) ^ hgt k (p i) = (1 + eps k) * (1 + eps k) ^ (hgt k (p i) - Suc 0)"
    using False power.simps by (metis Suc_pred hgt_gt_0)
  have B: "(1 + eps k) ^ (hgt k (p i) - 3) = 1 / (1 + eps k)^2 * (1 + eps k) ^ (hgt k (p i) - Suc 0)"
    using epsk_gt0 [OF \<open>k>0\<close>] False
    by (simp add: divide_simps Suc_diff_Suc numeral_3_eq_3 flip: power_add)
  have "qfun k (hgt k (p i) - 3)
     \<le> qfun k (hgt k (p i) - 1) - (qfun k (hgt k (p i)) - qfun k (hgt k (p i) - 1))"
    using \<open>k>0\<close> mult_left_mono [OF le1 0]
    apply (simp add: qfun_def field_simps A)
    by (simp add: B)
  also have "... < p i - alpha k (hgt k (p i))"
    using lesspi by (simp add: alpha_def)
  also have "... \<le> p (Suc i)"
    using Y_6_4_Red assms(1) by (force simp add: p_def)
  finally have Y: "qfun k (hgt k (p i) - 3) < p (Suc i)" .
  with hgt_greater[OF\<open>k>0\<close> Y] show ?thesis
    by simp
qed

lemma Y_6_5_DegreeReg: 
  assumes "i \<in> Step_class \<mu> l k dreg_step" and "k>0"
  shows "hgt k (pee \<mu> l k (Suc i)) \<ge> hgt k (pee \<mu> l k i)"
  using hgt_mono Y_6_4_DegreeReg assms by presburger

lemma Y_6_5_dbooSt:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>i \<in> Step_class \<mu> l k dboost_step.
                     Colours l k \<longrightarrow> hgt k (pee \<mu> l k (Suc i)) \<ge> hgt k (pee \<mu> l k i)"
  using Y_6_4_dbooSt[OF assms] unfolding Lemma_5_3_def
  by (smt (verit, ccfv_threshold) eventually_at_top_linorder Colours_kn0 hgt_mono)

end (*context Diagonal*)

end
