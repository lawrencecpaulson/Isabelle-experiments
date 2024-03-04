section \<open>The Zigzag Lemma\<close>

theory Zigzag imports Bounding_X

begin


lemma sum_from_1_telescope:
  "m > 0 \<Longrightarrow> (\<Sum>n=1..<m. f (Suc n) - f n :: 'a :: ab_group_add) = f m - f 1"
  by (induction m) (simp_all add: algebra_simps)


context Diagonal
begin

text \<open>Bhavit: "The maximum value of the height, for the sums in section 8"\<close>
definition "max_height \<equiv> \<lambda>k. nat \<lfloor>2 / eps k * ln k\<rfloor> + 1" 

definition "ok_fun_ZZ_8_1 \<equiv> \<lambda>k. 0" 

definition "Big_ZZ_8_1 \<equiv>
   \<lambda>\<mu> l. (\<forall>k. k\<ge>l \<longrightarrow> max_height k > 1)"

lemma Big_ZZ_8_1:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_ZZ_8_1 \<mu> l"
  unfolding Big_ZZ_8_1_def eventually_conj_iff all_imp_conj_distrib max_height_def eps_def
  apply (simp add:  eventually_all_ge_at_top assms)
  apply (intro conjI eventually_all_ge_at_top; real_asymp)
  done


lemma ZZ_8_1:
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours l k" and big: "Big_ZZ_8_1 \<mu> l" 
  defines "\<S>\<S> \<equiv> dboost_star \<mu> l k" and "\<R> \<equiv> Step_class \<mu> l k {red_step}"
  shows "(\<Sum>i\<in>\<S>\<S>. (1 - beta \<mu> l k i) / beta \<mu> l k i) \<le> card \<R> + ok_fun_ZZ_8_1 k"
proof -
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  define m where "m \<equiv> halted_point \<mu> l k"
  define p where "p \<equiv> pee \<mu> l k"
  define pp where "pp \<equiv> \<lambda>i h. if h=1 then min (p i) (qfun k 1)
                          else if p i \<le> qfun k (h-1) then qfun k (h-1) 
                          else if p i \<ge> qfun k h then qfun k h
                          else p i"
  define \<Delta> where "\<Delta> \<equiv> \<lambda>i. p (Suc i) - p i"
  define \<Delta>\<Delta> where "\<Delta>\<Delta> \<equiv> \<lambda>i h. pp (Suc i) h - pp i h"
  have pp_eq: "pp i h = (if h=1 then min (p i) (qfun k 1)
                          else max (qfun k (h-1)) (min (p i) (qfun k h)))" for i h
    using qfun_mono [OF \<open>k>0\<close>, of "h-1" h] by (auto simp: pp_def max_def)
  have mh_gt1: "max_height k > 1"
    using big by (simp add: Big_ZZ_8_1_def \<open>l\<le>k\<close>) 

  have "\<Delta> i  \<ge> 0 \<longleftrightarrow> (\<forall>h>0. \<Delta>\<Delta> i h \<ge> 0)" for i
    apply (auto simp: \<Delta>_def \<Delta>\<Delta>_def) 
     apply (simp add: pp_def)
     apply (auto simp: )[1]
    using diff_le_self lk(3) qfun_mono apply presburger
    using diff_le_self lk(3) qfun_mono apply presburger
    apply (simp add: pp_def split: )
    apply (frule_tac x="hgt k (p i)" in spec)
    apply (drule_tac x="hgt k (p (Suc i))" in spec)
    using hgt_less_imp_qfun_less [of "hgt k _ - 1", where k=k] 
    using hgt_le_imp_qfun_ge [OF order_refl, where k=k] \<open>k>0\<close>
    using hgt_gt_0 [of k "p i"]     using hgt_gt_0 [of k "p (Suc i)"]

    apply (simp add:  split: if_split_asm)
    apply (smt (verit, best))
    apply (smt (verit, best))
    apply (smt (verit, best))
    apply (smt (verit, best))
    apply (smt (verit, ccfv_threshold) diff_Suc_less hgt_greater hgt_gt_0)
    apply (smt (verit, best))
    apply (metis basic_trans_rules(24) hgt_gt_0)
    apply (smt (verit, best))
               defer
               defer
               apply (smt (verit, best))
              apply (smt (verit, best))
    defer
             apply (smt (verit, best))
            apply (smt (verit, best))
    apply (smt (verit, best))
          apply (smt (verit, best))
    apply (smt (verit, best))
    apply (smt (verit, best))
    apply (smt (verit, best))
    apply (smt (verit) Suc_leI diff_Suc_less nat_less_le)
    apply (smt (verit) Suc_leI diff_Suc_less nat_less_le)
    apply (smt (verit) Suc_leI diff_Suc_less nat_less_le)
    done



  have "\<Delta>\<Delta> i h = (if h=1 then pp (Suc i) h - pp i h
     else if (p i \<le> qfun k (h-1) \<and> p (Suc i) \<le> qfun k (h-1)) \<or> (p i \<ge> qfun k h \<and> p (Suc i) \<ge> qfun k h) then 0 
     else  p (Suc i) - p i)" if "h>0" for i h
    unfolding \<Delta>\<Delta>_def pp_def
    using qfun_strict_mono [OF \<open>k>0\<close>, of "h-1" h] that

    apply (simp add: )
apply (auto simp: )
    apply linarith
    sorry

  have "\<Delta> i = (\<Sum>h=1..<max_height k. \<Delta>\<Delta> i h)" if "i<m" for i
    unfolding \<Delta>\<Delta>_def \<Delta>_def


    sorry

  show ?thesis
    sorry
qed

end

end
