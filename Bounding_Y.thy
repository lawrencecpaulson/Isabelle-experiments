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
    by (auto simp: X_def Y_def Step_class_def stepper_kind_def next_state_kind_def cvx_def Xseq_def Yseq_def split: if_split_asm prod.split_asm)
  have "Xseq \<mu> l k (Suc i) = Neighbours Red (cvx \<mu> l k i) \<inter> X"
       "Yseq \<mu> l k (Suc i) = Neighbours Red (cvx \<mu> l k i) \<inter> Y"
    using step nonterm \<open>odd i\<close> non_mb red
    by (auto simp add: Xseq_def Yseq_def next_state_def cvx_def Let_def split: prod.split)
  then show ?thesis
    using red by (simp add: X_def Y_def reddish_def pee_def)
qed

lemma Y_6_4_B: 
  assumes i: "i \<in> Step_class \<mu> l k bblue_step"
  shows "pee \<mu> l k (Suc i) \<ge> pee \<mu> l k i - (eps k powr (-1/2)) * alpha k (hgt k (pee \<mu> l k (i-1)))"
proof -
  define X where "X \<equiv> Xseq \<mu> l k i" 
  define Y where "Y \<equiv> Yseq \<mu> l k i"
  obtain A B
    where step: "stepper \<mu> l k i = (X,Y,A,B)"
      and nonterm: "\<not> termination_condition l k X Y"
      and "odd i"
      and mb: "many_bluish \<mu> l k X"
    using i
    by (auto simp: X_def Y_def Step_class_def stepper_kind_def next_state_kind_def cvx_def Xseq_def Yseq_def split: if_split_asm prod.split_asm)
  have step_Suc_m1: "stepper \<mu> l k i = stepper \<mu> l k (Suc (i-1))"
    using One_nat_def \<open>odd i\<close> odd_Suc_minus_one by presburger
  define i' where "i' = i-1"
  have "i' \<in> Step_class \<mu> l k dreg_step"
    using \<open>odd i\<close> by (simp add: i'_def assms dreg_before_bblue_step)
  then have "Yseq \<mu> l k (Suc i') = Yseq \<mu> l k i'"
    by (simp add: degree_reg_def X_degree_reg_def Step_class_def stepper_kind_def next_state_kind_def
            Yseq_def split: if_split_asm prod.split_asm)
  have "Yseq \<mu> l k (Suc i) = Yseq \<mu> l k i"
    using i by (simp add: Step_class_def stepper_kind_def next_state_kind_def next_state_def Yseq_def 
        split: if_split_asm prod.split_asm prod.split)


      sorry
  have "Xseq \<mu> l k (Suc i) = Neighbours Red (cvx \<mu> l k i) \<inter> X"
       "Yseq \<mu> l k (Suc i) = Y"
    using step nonterm \<open>odd i\<close> mb 
     apply (simp_all add: Xseq_def Yseq_def next_state_def degree_reg_def X_degree_reg_def Let_def split: prod.split)
    apply (intro strip conjI)

  then show ?thesis
    using red by (simp add: X_def Y_def reddish_def pee_def)
qed

lemma Y_6_4_D: 
  assumes i: "i \<in> Step_class \<mu> l k red_step" and "0<\<mu>" "\<mu><1"
  shows "pee \<mu> l k (Suc i) \<ge> pee \<mu> l k i"



end (*context Diagonal*)

end
