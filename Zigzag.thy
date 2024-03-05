section \<open>The Zigzag Lemma\<close>

theory Zigzag imports Bounding_X

begin


lemma sum_from_1_telescope:
  "m > 0 \<Longrightarrow> (\<Sum>n=1..<m. f (Suc n) - f n :: 'a :: ab_group_add) = f m - f 1"
  by (induction m) (simp_all add: algebra_simps)


context Diagonal
begin

definition "ok_fun_ZZ_8_1 \<equiv> \<lambda>k. 0" 

definition "Big_ZZ_8_1 \<equiv>
   \<lambda>\<mu> l. (\<forall>k. k\<ge>l \<longrightarrow> True)"

lemma Big_ZZ_8_1:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_ZZ_8_1 \<mu> l"
  unfolding Big_ZZ_8_1_def eventually_conj_iff all_imp_conj_distrib  eps_def
  apply (simp add:  eventually_all_ge_at_top assms)
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

  define maxh where "maxh \<equiv> Suc (hgt k 1)"  (*alternatively, use height_upper_bound*)
  have "maxh > 1"
    by (simp add: maxh_def hgt_gt_0)
  have hgt_le_maxh: "hgt k (p i) \<le> maxh" for i
    using \<open>k>0\<close> by (simp add: hgt_mono le_SucI maxh_def p_def pee_le1)

  have pp_eq_hgt [simp]: "pp i (hgt k (p i)) = p i" for i
    using hgt_less_imp_qfun_less [of "hgt k (p i) - 1" k "p i"]  
    using hgt_works [of k "p i"] hgt_gt_0 [of k "p i"] \<open>k>0\<close> pp_eq by force

  have pp_less_hgt [simp]: "pp i h = qfun k h" if "0<h" "h < hgt k (p i)" for h i
  proof (cases "h=1")
    case True
    then show ?thesis
      using hgt_less_imp_qfun_less pp_def that by auto
  next
    case False
    with that show ?thesis
      using hgt_works [of k "p i"] hgt_gt_0 [of k "p i"] \<open>k>0\<close> 
      using hgt_less_imp_qfun_less qfun_strict_mono that
      by (force simp add: pp_eq)
  qed

  have pp_gt_hgt [simp]: "pp i h = qfun k (h-1)" if "h > hgt k (p i)" for h i
    using hgt_gt_0 [of k "p i"] \<open>k>0\<close> that
    by (simp add: pp_def hgt_le_imp_qfun_ge)

  have \<Delta>0: "\<Delta> i \<ge> 0 \<longleftrightarrow> (\<forall>h>0. \<Delta>\<Delta> i h \<ge> 0)" for i
  proof (intro iffI strip)
    fix h::nat
    assume "0 \<le> \<Delta> i" "0 < h" then show "0 \<le> \<Delta>\<Delta> i h"
      using qfun_mono [of k "h-1" h] \<open>k>0\<close> by (auto simp: \<Delta>_def \<Delta>\<Delta>_def pp_def) 
  next
    assume "\<forall>h>0. 0 \<le> \<Delta>\<Delta> i h"
    then have "p i \<le> pp (Suc i) (hgt k (p i))"
      unfolding \<Delta>\<Delta>_def
      by (smt (verit, best) hgt_gt_0 pp_eq_hgt)
    then show "0 \<le> \<Delta> i"
      using hgt_less_imp_qfun_less [of "hgt k (p i) - 1" k "p i"]  
      using hgt_gt_0 [of k "p i"] \<open>k>0\<close>
      by (simp add: \<Delta>_def pp_def split: if_split_asm)
  qed

  have sum_pp_aux: "(\<Sum>h=Suc 0..n. pp i h) = (if hgt k (p i) \<le> n then p i + (\<Sum>h=1..<n. qfun k h) else (\<Sum>h=1..n. qfun k h))" 
    if "n>0" for n i
    using that
  proof (induction n)
    case (Suc n)
    show ?case
    proof (cases "n=0")
      case True
      then show ?thesis
        using \<open>k>0\<close> hgt_Least [of 1 "p i" k]
        by (simp add: pp_def hgt_le_imp_qfun_ge min_def)
    next
      case False
      with Suc show ?thesis
        by (simp split: if_split_asm) (smt (verit) le_Suc_eq not_less_eq pp_eq_hgt sum.head_if)
    qed
  qed auto
  have sum_pp: "(\<Sum>h=Suc 0..maxh. pp i h) = p i + (\<Sum>h=1..<maxh. qfun k h)" for i
    using \<open>1 < maxh\<close> by (simp add: hgt_le_maxh sum_pp_aux)
  have \<Delta>_eq: "\<Delta> i = (\<Sum>h=1..maxh. \<Delta>\<Delta> i h)" for i
    by (simp add: \<Delta>\<Delta>_def \<Delta>_def sum_subtractf sum_pp)


  show ?thesis
    sorry
qed

end

end
