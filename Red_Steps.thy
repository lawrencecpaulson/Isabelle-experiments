section \<open>Red Steps: theorems\<close>

theory Red_Steps imports Big_Blue_Steps

begin

context Diagonal
begin

proposition Red_5_1:
  assumes "real (card (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i)) = \<beta> * real (card (Xseq \<mu> l k i))"
    and i: "i \<in> Step_class \<mu> l k red_step \<union> Step_class \<mu> l k dboost_step"
    and "0 \<le> \<beta>" "\<beta> \<le> \<mu>"    (*STRICT INEQUALITY? NOT MENTIONED by Mehta*)
  defines "p \<equiv> pee \<mu> l k i"
  shows "red_density (Neighbours Red (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i)
         \<ge> p - alpha k (hgt k p)
       \<or> red_density (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i)
         \<ge> p + (1 - eps k) * ((1-\<beta>) / \<beta>) * alpha k (hgt k p)"
  sorry

corollary Red_5_2:
  assumes i: "i \<in> Step_class \<mu> l k dboost_step" and "\<mu>>0"
  shows "pee \<mu> l k (Suc i) - pee \<mu> l k i
         \<ge> (1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k (hgt k (pee \<mu> l k i))"
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
          (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i)"
    using Red_5_1 [OF \<beta>eq _ beta_ge0 beta_le]
    by (smt (verit, del_insts) Un_iff Xeq Yeq assms gen_density_ge0 pee)
  also have "... \<le> pee \<mu> l k (Suc i)"
    using SUC Xeq Yeq stepper_XYseq by (simp add: pee_def)
  finally show ?thesis
    by linarith
qed

corollary Red_5_3a:
  fixes h::nat
  assumes i: "i \<in> Step_class \<mu> l k dboost_step" and "0<\<mu>" "\<mu><1" "k>0"
  shows "pee \<mu> l k (Suc i) \<ge> pee \<mu> l k i"
proof -
  let ?h = "hgt k (pee \<mu> l k i)"
  have "?h > 0"
    sorry
  then obtain \<alpha>: "alpha k ?h \<ge> 0" "alpha k ?h \<ge> eps k / k"
    using alpha_ge0 \<open>k>0\<close> using alpha_ge by blast
  have \<beta>: "beta \<mu> l k i \<le> \<mu>"
    by (simp add: assms beta_le)
  have "(1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k ?h \<ge> 0"
    using beta_ge0[of \<mu> l k i] epsk_le1[OF \<open>k>0\<close>] \<alpha> \<beta> \<open>\<mu><1\<close>
    by (simp add: zero_le_mult_iff zero_le_divide_iff)
  then show ?thesis
    using Red_5_2 [OF i \<open>\<mu>>0\<close>] by simp
  have "pee \<mu> l k (Suc i) - pee \<mu> l k i \<le> 1"
    by (smt (verit) pee_ge0 pee_le1)
  have "beta \<mu> l k i \<ge> 1 / k^2"

    sorry
    sorry

qed



end
