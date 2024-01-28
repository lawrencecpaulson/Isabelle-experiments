section \<open>Bounding the Size of @{term Y}\<close>

theory Bounding_Y imports Red_Steps

begin

context Diagonal
begin

lemma "\<lbrakk>h' \<le> h; 0 < h'\<rbrakk> \<Longrightarrow> alpha k h' \<le> alpha k h"
  by (simp add: alpha_eq epsk_ge0 divide_right_mono mult_left_mono power_increasing)

subsection \<open>The following results together are Lemma 6.4\<close>
text \<open>Compared with the paper, all the indices are greater by one\<close>

lemma Y_6_4_Red: 
  assumes i: "i \<in> Step_class \<mu> l k {red_step}"
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
  assumes "i \<in> Step_class \<mu> l k {dreg_step}" 
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
  assumes i: "i \<in> Step_class \<mu> l k {bblue_step}" and "0 < \<mu>"
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
  have i': "i' \<in> Step_class \<mu> l k {dreg_step}"
    by (metis dreg_before_step Step_class_insert Suci' UnCI i)
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
  also have "\<dots> \<le> (\<Sum>x\<in>T. card (Neighbours Red x \<inter> Y))"
    using T_reds by (simp add: sum_bounded_below)
  also have "\<dots> = edge_card Red T Y"
    using \<open>disjnt X Y\<close> \<open>finite X\<close> \<open>T\<subseteq>X\<close> Red_E
    by (metis disjnt_subset1 disjnt_sym edge_card_commute edge_card_eq_sum_Neighbours finite_subset)
  also have "\<dots> = red_density T Y * card T * card Y"
    using fin \<open>T\<subseteq>X\<close> by (simp add: finite_subset gen_density_def)
  finally have ***: "pm \<le> red_density T Y" 
    using fin \<open>T\<noteq>{}\<close> \<open>Y\<noteq>{}\<close>
    by (metis \<open>T \<subseteq> X\<close> card_gt_0_iff finite_subset mult_right_le_imp_le of_nat_0_less_iff)
  then show ?thesis
    by (simp add: X1_eq Y1_eq i'_def pee_def pm_def)
qed


lemmas Y_6_4_dbooSt = Red_5_3

subsection \<open>Towards Lemmas 6.3 and 6.2\<close>

definition "Z_class \<equiv> \<lambda>\<mu> l k. {i \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}.
                                pee \<mu> l k (Suc i) < pee \<mu> l k (i-1) \<and> pee \<mu> l k (i-1) \<le> p0}"

lemma finite_Z_class:
  assumes "\<mu>>0"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> finite (Z_class \<mu> l k)"
proof -
  have R: "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> finite (Step_class \<mu> l k {red_step})"
    using assms red_step_limit(1) by auto
  have B: "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> finite (Step_class \<mu> l k {bblue_step})"
    using bblue_step_limit unfolding Lemma_bblue_step_limit_def
    by (smt (verit, ccfv_threshold) assms eventually_at_top_linorder)
  have S: "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> finite (Step_class \<mu> l k {dboost_step})"
    using bblue_dboost_step_limit [OF assms] eventually_sequentially by force
  have "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> finite (Step_class \<mu> l k {red_step,bblue_step,dboost_step})"
    using eventually_mono [OF eventually_conj [OF R eventually_conj [OF B S]]]
    by (simp add: Step_class_insert_NO_MATCH)
  then show ?thesis
    unfolding Z_class_def by (force elim!: eventually_mono)
qed

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
    assume i: "i \<in> Step_class \<mu> l k {dboost_step}"
    moreover have "odd i"
      using step_odd [of i] i  by (force simp add: Step_class_insert_NO_MATCH)
    ultimately have "i-1 \<in> Step_class \<mu> l k {dreg_step}"
      by (simp add: dreg_before_step Step_class_insert_NO_MATCH)
    then have "p (i-1) \<le> p i \<and> p i \<le> p (Suc i)"
      using \<open>Colours l k\<close> Red53 p_def
      by (metis Lemma_5_3_def One_nat_def Y_6_4_DegreeReg \<open>odd i\<close> i odd_Suc_minus_one)
  }        
  then have dboost: "Step_class \<mu> l k {dboost_step} \<inter> Z_class \<mu> l k = {}"
    by (fastforce simp: Z_class_def p_def)
  { fix i
    assume i: "i \<in> Step_class \<mu> l k {bblue_step} \<inter> Z_class \<mu> l k" 
    then have "i-1 \<in> Step_class \<mu> l k {dreg_step}"
      using dreg_before_step step_odd i by (force simp add: Step_class_insert_NO_MATCH)
    have pee: "p (Suc i) < p (i-1)" "p (i-1) \<le> p0"
      and iB: "i \<in> Step_class \<mu> l k {bblue_step}"
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
    also have "\<dots> \<le> 1/k"
    proof -
      have "real k powr - (1 / 8) \<le> 1"
        using \<open>k>0\<close> by (force simp add: less_eq_real_def nat_less_real_le powr_less_one)
      then show ?thesis
        by (simp add: alpha_eq eps_def powr_powr divide_le_cancel flip: powr_add)
    qed
    finally have "p (i-1) - p (Suc i) \<le> 1/k" .
  }
  then have "(\<Sum>i \<in> Step_class \<mu> l k {bblue_step} \<inter> Z_class \<mu> l k. p (i-1) - p (Suc i)) 
             \<le> card (Step_class \<mu> l k {bblue_step} \<inter> Z_class \<mu> l k) * (1/k)"
    using sum_bounded_above by (metis (mono_tags, lifting))
  also have "\<dots> \<le> card (Step_class \<mu> l k {bblue_step}) * (1/k)"
    using bblue_step_limit \<open>Colours l k\<close>
    by (simp add: divide_le_cancel card_mono Lemma_bblue_step_limit_def)
  also have "\<dots> \<le> l powr (3/4) / k"
    using bblue_step_limit \<open>Colours l k\<close> by (simp add: \<open>0 < k\<close> frac_le Lemma_bblue_step_limit_def)
  also have "\<dots> \<le> eps k"
  proof -
    have "l powr (3/4) \<le> k powr (3 / 4)"
      by (simp add: \<open>l \<le> k\<close> powr_mono2)
    then show ?thesis
      using powr_add [of k "3/4" "1/4"] 
    apply (simp add: eps_def powr_minus divide_simps)
      by (metis mult_le_cancel_right powr_non_neg)
  qed
  finally have bblue: "(\<Sum>i\<in>Step_class \<mu> l k {bblue_step} \<inter> Z_class \<mu> l k. p(i-1) - p (Suc i))
                     \<le> eps k" .
  { fix i
    assume i: "i \<in> Step_class \<mu> l k {red_step} \<inter> Z_class \<mu> l k" 
    then have pee_alpha: "p (i-1) - p (Suc i) 
                       \<le> p (i-1) - p i + alpha k (hgt k (p i))"
      using Y_6_4_Red by (force simp: p_def)
    have pee_le: "p (i-1) \<le> p i"
      using dreg_before_step Y_6_4_DegreeReg i step_odd
      apply (simp add: p_def Step_class_insert_NO_MATCH)
      by (metis odd_Suc_minus_one)
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
      also have pee2: "\<dots> \<le> p i"
        using alpha_eq p_gt_q by (smt (verit, best) \<open>0 < k\<close> qfun_mono zero_le_one) 
      finally have "p (i - 1) \<le> p i" .
      then have "p (i-1) - p i + alpha k (hgt k (p i)) 
              \<le> qfun k 0 - p i + eps k * (p i - qfun k 0 + 1/k)"
        using Red_5_7b pee_le_q0 pee2 by fastforce
      also have "\<dots> \<le> eps k / k"
        using \<open>k>0\<close> pee2 by (simp add: algebra_simps) (smt (verit) affine_ineq epsk_le1)
      finally show ?thesis .
    qed
    with pee_alpha have "p (i-1) - p (Suc i) \<le> eps k / k"
      by linarith
  }
  then have "(\<Sum>i \<in> Step_class \<mu> l k {red_step} \<inter> Z_class \<mu> l k. p (i-1) - p (Suc i))
           \<le> card (Step_class \<mu> l k {red_step} \<inter> Z_class \<mu> l k) * (eps k / k)"
    using sum_bounded_above by (metis (mono_tags, lifting))
  also have "\<dots> \<le> card (Step_class \<mu> l k {red_step}) * (eps k / k)"
    using epsk_ge0[of k] assms
    by (simp add: divide_le_cancel mult_le_cancel_right card_mono red_step_limit)
  also have "\<dots> \<le> k * (eps k / k)"
    using red_step_limit [OF \<open>0<\<mu>\<close> \<open>Colours l k\<close>]
    by (smt (verit, best) divide_nonneg_nonneg epsk_ge0 mult_mono nat_less_real_le of_nat_0_le_iff)
  also have "\<dots> \<le> eps k"
    by (simp add: epsk_ge0)
  finally have red: "(\<Sum>i\<in>Step_class \<mu> l k {red_step} \<inter> Z_class \<mu> l k. p (i - 1) - p (Suc i)) \<le> eps k" .
  have fin_bblue: "finite (Step_class \<mu> l k {bblue_step})"
    using Lemma_bblue_step_limit_def \<open>Colours l k\<close> bblue_step_limit by presburger
  have fin_red: "finite (Step_class \<mu> l k {red_step})"
    using \<open>0<\<mu>\<close> \<open>Colours l k\<close> red_step_limit(1) by blast
  have bblue_not_red: "\<And>x. x \<in> Step_class \<mu> l k {bblue_step} \<Longrightarrow> x \<notin> Step_class \<mu> l k {red_step}"
    by (simp add: Step_class_def)
  have eq: "Z_class \<mu> l k = Step_class \<mu> l k {dboost_step} \<inter> Z_class \<mu> l k 
                      \<union> Step_class \<mu> l k {bblue_step} \<inter> Z_class \<mu> l k
                      \<union> Step_class \<mu> l k {red_step} \<inter> Z_class \<mu> l k"
    by (auto simp: Z_class_def Step_class_insert_NO_MATCH)
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
  assumes i: "i \<in> Step_class \<mu> l k {red_step}" and "k\<ge>16"
  defines "p \<equiv> pee \<mu> l k"
  defines "h \<equiv> hgt k (p i)"
  shows "hgt k (p (Suc i)) \<ge> h - 2"
proof (cases "h \<le> 3")
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
  have 0: "0 \<le> (1 + eps k) ^ (h - Suc 0)"
    using epsk_ge0 by auto
  have lesspi: "qfun k (h-1) < p i"
    using False hgt_Least [of "h-1" "p i" k] unfolding h_def by linarith
  have A: "(1 + eps k) ^ h = (1 + eps k) * (1 + eps k) ^ (h - Suc 0)"
    using False power.simps by (metis h_def Suc_pred hgt_gt_0)
  have B: "(1 + eps k) ^ (h - 3) = 1 / (1 + eps k)^2 * (1 + eps k) ^ (h - Suc 0)"
    using epsk_gt0 [OF \<open>k>0\<close>] False
    by (simp add: divide_simps Suc_diff_Suc numeral_3_eq_3 flip: power_add)
  have "qfun k (h-3) \<le> qfun k (h-1) - (qfun k h - qfun k (h-1))"
    using \<open>k>0\<close> mult_left_mono [OF le1 0]
    apply (simp add: qfun_def field_simps A)
    by (simp add: B)
  also have "\<dots> < p i - alpha k (h)"
    using lesspi by (simp add: alpha_def)
  also have "\<dots> \<le> p (Suc i)"
    using Y_6_4_Red i by (force simp add: h_def p_def)
  finally have "qfun k (h-3) < p (Suc i)" .
  with hgt_greater[OF\<open>k>0\<close>] show ?thesis
    by force
qed

lemma Y_6_5_DegreeReg: 
  assumes "i \<in> Step_class \<mu> l k {dreg_step}" and "k>0"
  shows "hgt k (pee \<mu> l k (Suc i)) \<ge> hgt k (pee \<mu> l k i)"
  using hgt_mono Y_6_4_DegreeReg assms by presburger


lemma Y_6_5_dbooSt:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>i \<in> Step_class \<mu> l k {dboost_step}.
                     Colours l k \<longrightarrow> hgt k (pee \<mu> l k (Suc i)) \<ge> hgt k (pee \<mu> l k i)"
  using Y_6_4_dbooSt[OF assms] unfolding Lemma_5_3_def
  by (smt (verit, ccfv_threshold) eventually_at_top_linorder Colours_kn0 hgt_mono)

text \<open>this remark near the top of page 19 only holds in the limit\<close>
lemma "\<forall>\<^sup>\<infinity>k. (1 + eps k) powr (- real (nat \<lfloor>2 * eps k powr (-1/2)\<rfloor>)) \<le> 1 - eps k powr (1/2)"
  unfolding eps_def
  by real_asymp


definition "Big_Y_6_5_Bblue \<equiv> \<lambda>k. (1 + eps k) powr (- real (nat \<lfloor>2*(eps k powr (-1/2))\<rfloor>)) \<le> 1 - eps k powr (1/2)" 

lemma Y_6_5_Bblue:
  fixes k::nat and \<kappa>::real
  defines "\<kappa> \<equiv> eps k powr (-1/2)"
  assumes i: "i \<in> Step_class \<mu> l k {bblue_step}" and "k>0" "0<\<mu>"
    and big: "Big_Y_6_5_Bblue k"
  defines "p \<equiv> pee \<mu> l k"
  defines "h \<equiv> hgt k (p (i-1))"
  shows "hgt k (p (Suc i)) \<ge> h - 2*\<kappa>"
proof (cases "h > 2*\<kappa> + 1")
  case True
  then have "0 < h - 1"
    by (smt (verit, best) \<kappa>_def one_less_of_natD powr_non_neg zero_less_diff)
  with True have "p (i-1) > qfun k (h-1)"
    by (smt (verit, best) h_def diff_le_self diff_less hgt_Least le_antisym zero_less_one nat_less_le)
  then have "qfun k (h-1) - eps k powr (1/2) * (1 + eps k) ^ (h-1) / k < p (i-1) - \<kappa> * alpha k h"
    using \<open>0 < h-1\<close> Y_6_4_Bblue [OF i] \<open>0<\<mu>\<close> epsk_ge0
    apply (simp add: alpha_eq p_def \<kappa>_def)
    by (smt (verit, best) field_sum_of_halves mult.assoc mult.commute powr_mult_base)
  also have "\<dots> \<le> p (Suc i)"
    using Y_6_4_Bblue i \<open>0<\<mu>\<close> h_def p_def \<kappa>_def by blast
  finally have A: "qfun k (h-1) - eps k powr (1/2) * (1 + eps k) ^ (h-1) / k < p (Suc i)" .
  have ek0: "0 < 1 + eps k"
    by (smt (verit, best) epsk_ge0)
  have less_h: "nat \<lfloor>2 * \<kappa>\<rfloor> < h"
    using True \<open>0 < h - 1\<close> by linarith
  have "qfun k (h - nat \<lfloor>2 * \<kappa>\<rfloor> - 1) = p0 + ((1 + eps k) ^ (h - nat \<lfloor>2 * \<kappa>\<rfloor> - 1) - 1) / k"
    by (simp add: qfun_def)
  also have "\<dots> \<le> p0 + ((1 - eps k powr (1/2)) * (1 + eps k) ^ (h-1) - 1) / k"
  proof -
    have ge0: "(1 + eps k) ^ (h-1) \<ge> 0"
      using epsk_ge0 by auto
    have "(1 + eps k) ^ (h - nat \<lfloor>2 * \<kappa>\<rfloor> - 1) = (1 + eps k) ^ (h-1) * (1 + eps k) powr - real(nat \<lfloor>2*\<kappa>\<rfloor>)"
      using less_h ek0 by (simp add: of_nat_diff algebra_simps flip: powr_realpow powr_add)
    also have "\<dots> \<le> (1 - eps k powr (1/2)) * (1 + eps k) ^ (h-1)"
      using big unfolding \<kappa>_def Big_Y_6_5_Bblue_def
      by (metis mult.commute  ge0 mult_left_mono)
    finally have "(1 + eps k) ^ (h - nat \<lfloor>2 * \<kappa>\<rfloor> - 1)
        \<le> (1 - eps k powr (1/2)) * (1 + eps k) ^ (h-1)" .
    then show ?thesis
      by (intro add_left_mono divide_right_mono diff_right_mono) auto
  qed
  also have "\<dots> \<le> qfun k (h-1) - eps k powr (1/2) * (1 + eps k) ^ (h-1) / real k"
    using \<open>k>0\<close> epsk_ge0 by (simp add: qfun_def powr_half_sqrt field_simps)
  also have "\<dots> < p (Suc i)"
    using A by blast
  finally have "qfun k (h - nat \<lfloor>2 * \<kappa>\<rfloor> - 1) < p (Suc i)" .
  then have "h - nat \<lfloor>2 * \<kappa>\<rfloor> \<le> hgt k (p (Suc i))"
    using hgt_greater [OF \<open>k>0\<close>] by force
  with less_h show ?thesis
    by (smt (verit) assms(1) less_imp_le_nat of_nat_diff of_nat_floor of_nat_mono powr_ge_pzero)
next
  case False
  then show ?thesis
    by (smt (verit, del_insts) of_nat_0 hgt_gt_0 nat_less_real_le)
qed


lemma "\<forall>\<^sup>\<infinity>k. (1 + eps k) powr (2 * eps k powr (- 1 / 2)) \<le> 2"
  apply (simp add: eps_def)
  by real_asymp

lemma "\<forall>\<^sup>\<infinity>k. ((1 + eps k)^2) * eps k powr (1 / 2) \<le> 1"
  apply (simp add: eps_def)
  by real_asymp

text \<open>Following Bravik in excluding the even steps (degree regularisation)\<close>
proposition Y_6_2_aux:
  fixes l k
  assumes "0<\<mu>" "\<mu><1"
  defines "p \<equiv> pee \<mu> l k"
  defines "RBS \<equiv> Step_class \<mu> l k {red_step,bblue_step,dboost_step}"
  assumes j: "j \<in> RBS" and "k>0" "0<\<mu>"
  assumes Y_6_3_Main: "(\<Sum>i \<in> Z_class \<mu> l k. p (i-1) - p (Suc i)) \<le> 2 * eps k" 
    and Y_6_5_dbooSt: 
      "\<And>i. i \<in> Step_class \<mu> l k {dboost_step} \<Longrightarrow> hgt k (pee \<mu> l k (Suc i)) \<ge> hgt k (pee \<mu> l k i)"
    and Y_6_5_Bblue: 
      "\<And>i. i \<in> Step_class \<mu> l k {bblue_step} \<Longrightarrow> hgt k (p (Suc i)) \<ge> hgt k (p (i-1)) - 2*(eps k powr (-1/2))"
      and Y_6_4_dbooSt: " \<And>i. i\<in>Step_class \<mu> l k {dboost_step} \<Longrightarrow> p i \<le> p (Suc i)"
    and finite_Z_class: "finite (Z_class \<mu> l k)"
    and big2: "(1 + eps k) powr (2 * eps k powr (- 1 / 2)) \<le> 2"
    and big1: "((1 + eps k)^2) * eps k powr (1 / 2) \<le> 1"
    and "k\<ge>16"  \<comment> \<open>bigness assumptions\<close>
  shows "p (Suc j) \<ge> p0 - 3 * eps k"
proof (cases "p (Suc j) \<ge> p0")
  case True
  then show ?thesis
    by (smt (verit) epsk_ge0)
next
  case False
  then have pj_less: "p(Suc j) < p0" by linarith
  define J where "J \<equiv> {j'. j'<j \<and> p (Suc j') \<ge> p0}"
  have "finite J"
    by (auto simp: J_def)
  have "p 0 = p0"
    by (simp add: p_def pee_eq_p0)
  have odd_RBS: "odd i" if "i \<in> RBS" for i
    using step_odd that unfolding RBS_def by blast
  with odd_pos j False have "j>0" by auto
  have non_halted: "j \<notin> Step_class \<mu> l k {halted}"
    using j by (auto simp: Step_class_def RBS_def)
  then have "0 \<notin> Step_class \<mu> l k {halted}"
    using Step_class_not_halted by blast
  then have "\<not> termination_condition l k X0 Y0"
    by (auto simp add: Step_class_def stepper_kind_def)
  then have "0 \<in> Step_class \<mu> l k {dreg_step}"
    using dreg_step_0 by force
  then have "p 1 \<ge> p 0"
    using Y_6_4_DegreeReg [of 0] by (simp add: p_def) 
  have exists: "J \<noteq> {}"
    using \<open>0 < j\<close> \<open>p 0 = p0\<close> \<open>p 0 \<le> p 1\<close> by (auto simp: J_def)
  define j' where "j' \<equiv> Max J"
  have "j' \<in> J"
    using \<open>finite J\<close> exists by (force simp add: j'_def)
  then have "j' < j"
    by (auto simp add: J_def odd_RBS)
  then have Suc_j'_not_halted: "Suc j' \<notin> Step_class \<mu> l k {halted}"
    using j Step_class_not_halted non_halted Suc_leI by blast
  then have j'_not_halted: "j' \<notin> Step_class \<mu> l k {halted}"
    using Step_class_halted_forever le_eq_less_or_eq by blast
  have maximal: "j'' \<le> j'" if "j'' \<in> J" for j''
    using \<open>finite J\<close> exists by (simp add: j'_def that)
  { assume "odd j'"
    then have "Suc j' \<in> Step_class \<mu> l k {dreg_step}"
      by (simp add: Suc_j'_not_halted not_halted_even_dreg)
    then have "p (Suc (Suc j')) \<ge> p (Suc j')"
      using Y_6_4_DegreeReg unfolding p_def by blast
    then have 0: "p (Suc (Suc j')) \<ge> p0"
      using J_def \<open>j' \<in> J\<close> by auto
    then have "Suc j' < j"
      using False Suc_lessI \<open>j' < j\<close> by blast
    then have "False"
      using J_def Suc_n_not_le_n maximal 0 by blast
  }
  then have "even j'" by metis
  have "p (j'+2) - 2 * eps k \<le> p (j'+2) - (\<Sum>i \<in> Z_class \<mu> l k. p (i-1) - p (Suc i))"
    using Y_6_3_Main by simp
  also have "\<dots> \<le> p (Suc j)"
  proof -
    define Z where "Z \<equiv> \<lambda>j. {i. p (Suc i) < p (i-1) \<and> j'+2 < i \<and> i\<le>j \<and> i \<in> RBS}"
    have "Z i \<subseteq> {Suc j'<..i}" for i
      by (auto simp: Z_def)
    then have finZ: "finite (Z i)" for i
      by (meson finite_greaterThanAtMost finite_subset)
    have *: "(\<Sum>i \<in> Z j. p (i-1) - p (Suc i)) \<le> (\<Sum>i \<in> Z_class \<mu> l k. p (i-1) - p (Suc i))"
    proof (intro sum_mono2)
      show "finite (Z_class \<mu> l k)"
        using finite_Z_class by force
      show "Z j \<subseteq> Z_class \<mu> l k" 
      proof 
        fix i
        assume i: "i \<in> Z j"
        then have dreg: "i-1 \<in> Step_class \<mu> l k {dreg_step}" and "i\<noteq>0"
          by (auto simp add: Z_def RBS_def dreg_before_step)
        have "j' < i"
          using i by (auto simp: Z_def)
        with maximal have "i-2 \<notin> J"
          using Z_def i by force
        with i have "p (i-1) < p0"
          using step_odd_minus2 [of i \<mu> l k] Suc_less_eq2 
          by (force simp add: Z_def J_def RBS_def)
        then show "i \<in> Z_class \<mu> l k"
          using i by (simp add: Z_def RBS_def Z_class_def p_def)
      qed
      show "0 \<le> p (i-1) - p (Suc i)" if "i \<in> Z_class \<mu> l k - Z j" for i
        using that by (auto simp: Z_def Z_class_def p_def)
    qed
    then have "p (j'+2) - (\<Sum>i\<in>Z_class \<mu> l k. p (i - 1) - p (Suc i))
            \<le> p (j'+2) - (\<Sum>i \<in> Z j. p (i-1) - p (Suc i))"
      by auto
    also have "\<dots> \<le> p (Suc j)"
    proof -
      have "p (j'+2) - p (Suc m) \<le> (\<Sum>i \<in> Z m. p (i-1) - p (Suc i))"
        if "m \<in> RBS" "j' < m" "m\<le>j" for m
        using that
      proof (induction m rule: less_induct)
        case (less m)
        then have "odd m"
          using odd_RBS by blast
        show ?case
        proof (cases "j'+2 < m") 
          case True
          with less.prems \<open>odd m\<close> \<open>even j'\<close>
          have Z_if: "Z m = (if p (Suc m) < p (m-1) then insert m (Z (m-2)) else Z (m-2))"
            by (auto simp add: Z_def; 
                metis le_diff_conv2 Suc_leI add_2_eq_Suc' add_leE even_Suc nat_less_le odd_RBS)
          have "m-2 \<in> RBS"
            using True assms(4) less(2) step_odd_minus2 by auto
          then have *: "p (j'+2) - p (m - Suc 0) \<le> (\<Sum>i\<in>Z (m - 2). p (i - 1) - p (Suc i))"
            using less.IH [of "m-2"] True less Suc_less_eq2
            using \<open>j' \<in> J\<close> by (force simp add: J_def)
          moreover have "m \<notin> Z (m - 2)"
            by (auto simp: Z_def)
          ultimately show ?thesis
            by (simp add: Z_if finZ)
        next
          case False
          have "odd m"
            using \<open>j' \<in> J\<close> \<open>m \<in> RBS\<close> unfolding J_def
            using odd_RBS by force+
          then have [simp]: "m = Suc j'"
            using False less(3) \<open>even j'\<close> by presburger
          then have "Z m = {}"
            by (simp add: Z_def)
          then show ?thesis
            using less.prems False by (simp add: eval_nat_numeral)
        qed
      qed
      then show ?thesis
        using j J_def \<open>j' \<in> J\<close> by fastforce 
    qed
    finally show ?thesis .
  qed
  finally have D: "p (j'+2) - 2 * eps k \<le> p (Suc j)" .
  have "Suc j' \<in> RBS"
    unfolding RBS_def
  proof (intro not_halted_odd_RBS)
    show "Suc j' \<notin> Step_class \<mu> l k {halted}"
      using Step_class_halted_forever Suc_leI \<open>j' < j\<close> non_halted by blast
  qed (use \<open>even j'\<close> in auto)
  then have "p (j'+2) < p0"
    using maximal[of "j'+1"] False \<open>j' < j\<close> less_le by (fastforce simp add: J_def)
  then have le1: "hgt k (p (j'+2)) \<le> 1"
    using \<open>k>0\<close> zero_less_one
    by (smt (verit, best) hgt_Least q0 qfun_mono less_imp_le)
  moreover 
  have j'_dreg: "j' \<in> Step_class \<mu> l k {dreg_step}"
    using RBS_def \<open>Suc j' \<in> RBS\<close> dreg_before_step by blast
  have 1: "eps k powr - (1/2) \<ge> 1"
    using \<open>k>0\<close> by (simp add: eps_def powr_powr ge_one_powr_ge_zero)
  consider (R) "Suc j' \<in> Step_class \<mu> l k {red_step}"
         | (B) "Suc j' \<in> Step_class \<mu> l k {bblue_step}"
         | (S) "Suc j' \<in> Step_class \<mu> l k {dboost_step}"
    by (metis Step_class_insert UnE \<open>Suc j' \<in> RBS\<close> RBS_def)
  note j'_cases = this
  then have hgt_le_hgt: "hgt k (p j') \<le> hgt k (p (j'+2)) + 2 * eps k powr (-1/2)"
  proof cases
    case R
    have "real (hgt k (p j')) \<le> real (hgt k (pee \<mu> l k (Suc j')))"
      using Y_6_5_DegreeReg[OF j'_dreg] \<open>k>0\<close> by (simp add: eval_nat_numeral p_def)
    also have "\<dots> \<le> hgt k (p (j'+2)) + 2 * eps k powr (-1/2)"
      using Y_6_5_Red[OF R \<open>k\<ge>16\<close>] 1 by (simp add: eval_nat_numeral p_def)
    finally show ?thesis .
  next
    case B
    show ?thesis
      using Y_6_5_Bblue [OF B] by (simp add: p_def)
  next
    case S
    then show ?thesis
      using Y_6_5_dbooSt Y_6_5_DegreeReg[OF j'_dreg] \<open>Suc j' \<in> RBS\<close> \<open>k>0\<close>  
      unfolding RBS_def p_def
      by (smt (verit) Suc_1 Suc_eq_plus1 add_Suc_right of_nat_le_iff powr_non_neg)
  qed
  ultimately have B: "hgt k (p j') \<le> 1 + 2 * eps k powr (-1/2)"
    by linarith
  have "2 \<le> real k powr (1 / 2)"
    using \<open>k\<ge>16\<close> by (simp add: powr_half_sqrt real_le_rsqrt)
  then have 8: "2 \<le> real k powr 1 * real k powr - (1 / 8)"
    unfolding powr_add [symmetric]
    using \<open>k\<ge>16\<close> order.trans nle_le by fastforce
  have "p0 - eps k \<le> qfun k 0 - 2 * eps k powr (1/2) / k"
    using mult_left_mono [OF 8, of "k powr (-1/8)"] \<open>k>0\<close> 
    by (simp add: qfun_def eps_def powr_powr field_simps flip: powr_add)
  also have "\<dots> \<le> p j'  - eps k powr (-1/2) * alpha k (hgt k (p j'))"
  proof -
    have *: "hgt k (pee \<mu> l k j') = Suc (hgt k (pee \<mu> l k j') - 1)"
      using Suc_pred' hgt_gt_0 by blast
    show ?thesis
      using \<open>k>0\<close> epsk_gt0[OF\<open>k>0\<close>]
      apply (simp add: p_def alpha_def powr_minus)
      apply (simp add: field_simps)
      apply (simp add: qfun_def algebra_simps flip: powr_add)
      apply (subst *)
      apply (simp add: algebra_simps)
      apply (subst add.commute)
      apply (rule add_mono)
       apply (intro mult_left_mono)
      using big2 B hgt_le_hgt * of_nat_add of_nat_1
      unfolding p_def
      apply (smt (verit) One_nat_def plus_1_eq_Suc powr_mono powr_realpow)
        apply simp
       apply (intro mult_left_mono)
        apply (subst mult.commute)
        apply (intro mult_left_mono)
         apply (auto simp: )
      using hgt_works [OF \<open>k>0\<close>] B
       apply (simp add: p_def)
      sorry
  qed
  also have "\<dots> \<le> p (j'+2)"
    using j'_cases
  proof cases
    case R
    have hs_le3: "hgt k (pee \<mu> l k (Suc j')) \<le> 3"
      using le1  Y_6_5_Red[OF R \<open>k\<ge>16\<close>] by (simp add: p_def)
    then have h_le3: "hgt k (p j') \<le> 3"
      using Y_6_5_DegreeReg [OF j'_dreg \<open>k>0\<close>] by (simp add: p_def)
    have alpha1: "alpha k (hgt k (p (Suc j'))) \<le> eps k * (1 + eps k) ^ 2 / k"
      by (metis alpha_Suc_eq alpha_mono p_def hgt_gt_0 hs_le3 numeral_nat(3))
    have alpha2: "alpha k (hgt k (p j')) \<ge> eps k / k"
      by (simp add: Red_5_7a)
    have "p j' - eps k powr (- 1 / 2) * alpha k (hgt k (p j')) 
       \<le> p (Suc j') - alpha k (hgt k (p (Suc j')))"
    proof -
      have "alpha k (hgt k (p (Suc j'))) \<le> (1 + eps k)\<^sup>2 * alpha k (hgt k (p j'))"
        using alpha1 mult_left_mono [OF alpha2, of "(1 + eps k)\<^sup>2"]
        by (simp add: mult.commute)
      also have "... \<le> inverse (eps k powr (1 / 2)) * alpha k (hgt k (p j'))"
        using mult_left_mono [OF big1, of "alpha k (hgt k (p j'))"] epsk_gt0[OF \<open>k>0\<close>] alpha_ge0 [of k]
        by (simp add: divide_simps mult_ac)
      finally have "alpha k (hgt k (p (Suc j')))
        \<le> inverse (eps k powr (1 / 2)) * alpha k (hgt k (p j'))" .
      then show ?thesis
        using Y_6_4_DegreeReg[OF j'_dreg] by (simp add: p_def powr_minus)
    qed
    also have "... \<le> p (j' + 2)"
      by (simp add: R Y_6_4_Red p_def)
    finally show ?thesis .
  next
    case B
    then show ?thesis
      using Y_6_4_Bblue \<open>0<\<mu>\<close> by (force simp: p_def)
  next
    case S
    show ?thesis
      using Y_6_4_dbooSt [OF S] J_def \<open>j' \<in> J\<close> \<open>p (j'+2) < p0\<close> by fastforce
  qed
  finally have "p0 - eps k \<le> p (j'+2)" .
  then have "p0 - 3 * eps k \<le> p (j'+2) - 2 * eps k"
    by simp
  also have "\<dots> \<le> p (Suc j)"
    using D by blast
  finally show ?thesis .
qed

end (*context Diagonal*)

end

