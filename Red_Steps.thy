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
  also have "... \<le> (\<Sum>y\<in>Y. real ((card (Neighbours Red y \<inter> X))\<^sup>2))"
    sorry
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


lemma Red_5_4:
  assumes "i \<in> Step_class_reddboost \<mu> l k"
  shows "weight (Xseq \<mu> l k i) (Yseq \<mu> l k i) (cvx \<mu> l k i) \<ge> - card (Xseq \<mu> l k i) / (real k) ^ 5"
  sorry


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
