section \<open>Red Steps: theorems\<close>

theory Red_Steps imports Big_Blue_Steps

begin

context Diagonal
begin

proposition Red_5_1:
  assumes "card (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) = \<beta> * card (Xseq \<mu> l k i)"
    and i: "i \<in> Step_class \<mu> l k red_step \<union> Step_class \<mu> l k dboost_step"
    and "0 < \<beta>" "\<beta> \<le> \<mu>"
  defines "p \<equiv> pee \<mu> l k i"
  shows "red_density (Neighbours Red (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i)
         \<ge> p - alpha k (hgt k p)
       \<or> red_density (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i)
         \<ge> p + (1 - eps k) * ((1-\<beta>) / \<beta>) * alpha k (hgt k p)"
  sorry

corollary Red_5_2:
  assumes i: "i \<in> Step_class \<mu> l k dboost_step" and "\<mu>>0"
  shows "pee \<mu> l k i - pee \<mu> l k (i-1)
         \<ge> p + (1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k (hgt k (pee \<mu> l k (i-1)))"
proof -
  obtain X Y AB
    where step: "stepper \<mu> l k i = (X,Y,AB)"
      and nonterm: "\<not> termination_condition l k X Y"
      and "even i"
      and "\<not> many_bluish \<mu> l k X"
      and nonredd: "\<not> reddish k X Y (red_density X Y) (choose_central_vx \<mu> (X, Y, AB::'a set \<times> 'a set))"
    using i
    by (simp add: Step_class_def stepper_kind_def next_state_kind_def Xseq_def Yseq_def split: if_split_asm prod.split_asm)
  then have "cvx \<mu> l k i \<in> Xseq \<mu> l k i"
    by (simp add: assms cvx_in_Xseq)
  then have "central_vertex \<mu> (Xseq \<mu> l k i) (cvx \<mu> l k i)"
    by (simp add: assms cvx_works)
  moreover have "X = Xseq \<mu> l k i"
    by (metis step stepper_XYseq surj_pair)
  ultimately have A: "card (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) \<le> \<mu> * card (Xseq \<mu> l k i)"
    by (simp add: central_vertex_def)
  define \<beta> where "\<beta> \<equiv> card (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) / card X"
  then have "0 \<le> \<beta>" "\<beta>\<le>\<mu>" 
    using A \<open>0<\<mu>\<close> by (auto simp: divide_simps \<open>X = Xseq \<mu> l k i\<close>)

  then show ?thesis
    sorry
qed

end
