section \<open>Bounding the Size of @{term Y}\<close>

theory Bounding_Y imports Red_Steps

begin

context Diagonal
begin

lemma Y_6_4_R: 
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

lemma Y_6_4_D: 
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

lemma Y_6_4_B: 
  assumes i: "i \<in> Step_class \<mu> l k bblue_step"
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
  then have "Xseq \<mu> l k (Suc i) = T"
    by (force simp: Xseq_def next_state_def split: prod.split)
  define i' where "i' = i-1"
  then have Suci': "Suc i' = i"
    by (simp add: \<open>odd i\<close>)
  have i': "i' \<in> Step_class \<mu> l k dreg_step"
    using \<open>odd i\<close> by (simp add: i'_def assms dreg_before_bblue_step)
  then have  "Xseq \<mu> l k (Suc i') = X_degree_reg k (Xseq \<mu> l k i') (Yseq \<mu> l k i')"
             "Yseq \<mu> l k (Suc i') = Yseq \<mu> l k i'"
    by (auto simp add: degree_reg_def X_degree_reg_def step_kind_defs split: if_split_asm prod.split_asm)
  then have Xeq: "X = X_degree_reg k (Xseq \<mu> l k i') (Yseq \<mu> l k i')"
       and  Yeq: "Y = Yseq \<mu> l k i'"
    using Suci' by (auto simp: X_def Y_def)
  then have X_reds: "red_dense k (Yseq \<mu> l k i') (pee \<mu> l k i') x" 
    if "x \<in> X" for x
    using that by (simp add: X_degree_reg_def pee_def)

  have "Yseq \<mu> l k (Suc i) = Y"
    using i by (simp add: Y_def step_kind_defs next_state_def split: if_split_asm prod.split_asm prod.split)
  have "Xseq \<mu> l k (Suc i) = T"
    using step nonterm \<open>odd i\<close> mb bluebook by (force simp: Xseq_def next_state_def split: prod.split)

  have "pee \<mu> l k i' \<le> pee \<mu> l k i"
    using Y_6_4_D i' Suci' by blast
  also have "... \<le> pee \<mu> l k (Suc i) + (eps k powr (-1/2)) * alpha k (hgt k (pee \<mu> l k (i-1)))"
    using X_reds
    sorry
  finally show ?thesis
    by (simp add: i'_def)
qed

lemmas Y_6_4_S = Red_5_3



end (*context Diagonal*)

end
