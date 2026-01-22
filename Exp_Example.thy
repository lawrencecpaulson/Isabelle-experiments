
theory Exp_Example
imports
  Complex_Main
begin

lemma exp_tends_to_zero: 
  fixes b :: "'a :: archimedean_field"
  assumes c: "c > 0" and  b: "0 < b" "b < 1"
  shows "\<exists> x. b ^ x \<le> c" 
proof (rule ccontr)
  assume not: "\<not> ?thesis"
  define bb where "bb = inverse b"
  define cc where "cc = inverse c"
  from b have bb: "bb > 1" unfolding bb_def by (rule one_less_inverse)  
  from c have cc: "cc > 0" unfolding cc_def by simp
  define bbb where "bbb = bb - 1"
  have id: "bb = 1 + bbb" and bbb: "bbb > 0" and bm1: "bbb \<ge> -1" unfolding bbb_def using bb by auto
  have "\<exists> n. cc / bbb < of_nat n" by (rule reals_Archimedean2)
  then obtain n where lt: "cc / bbb < of_nat n" by auto
  from not have "\<not> b ^ n \<le> c" by auto
  hence bnc: "b ^ n > c" by simp
  have "bb ^ n = inverse (b ^ n)" unfolding bb_def by (rule power_inverse)
  also have "\<dots> < cc" unfolding cc_def
    by (rule less_imp_inverse_less[OF bnc c])
  also have "\<dots> < bbb * of_nat n" using lt bbb by (metis mult.commute pos_divide_less_eq)
  also have "\<dots> \<le> bb ^ n"
    using Bernoulli_inequality[OF bm1, folded id, of n] by (simp add: ac_simps)
  finally show False by simp
qed

(* also a non-standard version?*)

end
