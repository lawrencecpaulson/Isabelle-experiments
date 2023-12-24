section \<open>Red Steps: theorems\<close>

theory Red_Steps imports Big_Blue_Steps

begin

context Diagonal
begin

proposition Red_5_1:
  assumes "card (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) = \<beta> * card (Xseq \<mu> l k i)"
    and i: "i \<in> Step_class \<mu> l k red_step \<union> Step_class \<mu> l k dboost_step"
    and "0 < \<beta>" "\<beta> \<le> \<mu>"
  defines "p \<equiv> red_density (Xseq \<mu> l k i) (Yseq \<mu> l k i)"
  shows "red_density (Neighbours Red (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i)
         \<ge> p - alpha k (hgt k p)
       \<or> red_density (Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) (Neighbours Red (cvx \<mu> l k i) \<inter> Yseq \<mu> l k i)
         \<ge> p + (1-\<epsilon>) * ((1-\<beta>) / \<beta>) * alpha k (hgt k p)"
  sorry

end
