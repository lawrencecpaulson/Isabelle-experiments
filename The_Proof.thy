section \<open>The Proof of Theorem 1.1\<close>

theory The_Proof
  imports From_Diagonal "Source_Coding_Theorem.Source_Coding_Theorem"

begin

definition "H \<equiv> \<lambda>p. -p * log 2 p - (1-p) * log 2 (1-p)"

text \<open>Many thanks to Fedor Petrov on mathoverflow\<close>
lemma H_12_1:
  fixes a b::nat
  assumes "a \<ge> b"
  shows "log 2 (a choose b) \<le> a * H(b/a)"
proof (cases "a=b \<or> b=0")
  case True
  with assms show ?thesis
    by (auto simp: H_def)
next
  let ?p = "b/a"
  case False
  then have p01: "0 < ?p" "?p < 1"
    using assms by auto
  then have "(a choose b) * ?p ^ b * (1-?p) ^ (a-b) \<le> (?p + (1-?p)) ^ a"
    apply (subst binomial_ring)
    apply (rule member_le_sum)
    using assms apply (simp add: )
     apply (simp add: )
    apply (simp add: )
    done
  also have "\<dots> = 1"
    by simp
  finally have \<section>: "(a choose b) * ?p ^ b * (1-?p) ^ (a-b) \<le> 1" .
  have "log 2 (a choose b) + b * log 2 ?p + (a-b) * log 2 (1-?p) \<le> 0"
    using Transcendental.log_mono [OF _ _ \<section>]
    by (simp add: p01 assms log_mult log_nat_power)
  then show ?thesis
    using p01 False assms unfolding H_def by (simp add: field_simps)
qed 

definition "g \<equiv> GG (2/5)"

lemma "g x y = log 2 (5/2) + x * log 2 (5/3) + y * log 2 ((2 * (x+y)) / (5*y))"
  by (simp add: g_def GG_def)