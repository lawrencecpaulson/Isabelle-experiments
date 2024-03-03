section \<open>The Zigzag Lemma\<close>

theory Zigzag imports Bounding_X

begin

context Diagonal
begin

definition "Big_ZZ_8_1 \<equiv>
   \<lambda>\<mu> l. True"

definition "ok_fun_ZZ_8_1 \<equiv> \<lambda>k.0" 

lemma ZZ_8_1:
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours l k" and big: "Big_ZZ_8_1 \<mu> l" 
  defines "\<S>\<S> \<equiv> dboost_star \<mu> l k" and "\<R> \<equiv> Step_class \<mu> l k {red_step}"
  shows "(\<Sum>i\<in>\<S>\<S>. (1 - beta \<mu> l k i) / beta \<mu> l k i) \<le> card \<R> + ok_fun_ZZ_8_1 k"
proof -
  show ?thesis
    sorry
qed

end

end
