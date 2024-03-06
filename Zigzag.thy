section \<open>The Zigzag Lemma\<close>

theory Zigzag imports Bounding_X

begin

context Diagonal
begin

definition "ok_fun_ZZ_8_1 \<equiv> \<lambda>k. 0" 

definition "Big_ZZ_8_2 \<equiv> \<lambda>k. (1 + eps k powr (1/2)) \<ge> (1 + eps k) powr (eps k powr (-1/4))"

definition "Big_ZZ_8_1 \<equiv>
   \<lambda>\<mu> l. Lemma_Red_5_2 \<mu> l \<and> Lemma_Red_5_3 \<mu> l \<and> Big_finite_components \<mu> l \<and> 
         (\<forall>k. k\<ge>l \<longrightarrow> Lemma_height_upper_bound k \<and> Big_ZZ_8_2 k)"

lemma Big_ZZ_8_1:
  assumes "0<\<mu>" "\<mu><1"
  shows "\<forall>\<^sup>\<infinity>l. Big_ZZ_8_1 \<mu> l"
  unfolding Big_ZZ_8_1_def Big_ZZ_8_2_def eventually_conj_iff all_imp_conj_distrib eps_def
  apply (simp add: Red_5_2 Red_5_3 Big_finite_components height_upper_bound eventually_all_ge_at_top assms)
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

  define maxh where "maxh \<equiv> nat\<lfloor>2 * ln k / eps k\<rfloor> + 1"  
  have maxh: "\<And>p. p\<le>1 \<Longrightarrow> hgt k p \<le> 2 * ln k / eps k" 
    using big \<open>k\<ge>l\<close> by (auto simp: Big_ZZ_8_1_def Lemma_height_upper_bound_def)
  then have "1 \<le> 2 * ln k / eps k"
    using hgt_gt0 [of k 1] by force
  then have "maxh > 1"
    by (simp add: maxh_def eps_gt0)
  have "hgt k p < maxh" if "p\<le>1"for p
    using that \<open>k>0\<close> maxh[of "p"] unfolding maxh_def by linarith
  then have hgt_le_maxh: "hgt k (p i) < maxh" for i
    using p_def pee_le1 by auto

  have pp_eq_hgt [simp]: "pp i (hgt k (p i)) = p i" for i
    using hgt_less_imp_qfun_less [of "hgt k (p i) - 1" k "p i"]  
    using hgt_works [of k "p i"] hgt_gt0 [of k "p i"] \<open>k>0\<close> pp_eq by force

  have pp_less_hgt [simp]: "pp i h = qfun k h" if "0<h" "h < hgt k (p i)" for h i
  proof (cases "h=1")
    case True
    then show ?thesis
      using hgt_less_imp_qfun_less pp_def that by auto
  next
    case False
    with that show ?thesis
      using hgt_works [of k "p i"] hgt_gt0 [of k "p i"] \<open>k>0\<close> 
      using hgt_less_imp_qfun_less qfun_strict_mono that
      by (force simp add: pp_eq)
  qed

  have pp_gt_hgt [simp]: "pp i h = qfun k (h-1)" if "h > hgt k (p i)" for h i
    using hgt_gt0 [of k "p i"] \<open>k>0\<close> that
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
      by (smt (verit, best) hgt_gt0 pp_eq_hgt)
    then show "0 \<le> \<Delta> i"
      using hgt_less_imp_qfun_less [of "hgt k (p i) - 1" k "p i"]  
      using hgt_gt0 [of k "p i"] \<open>k>0\<close>
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
    using \<open>1 < maxh\<close> by (simp add: hgt_le_maxh less_or_eq_imp_le sum_pp_aux)
  have 33: "\<Delta> i = (\<Sum>h=1..maxh. \<Delta>\<Delta> i h)" for i
    by (simp add: \<Delta>\<Delta>_def \<Delta>_def sum_subtractf sum_pp)

  have "(\<Sum>i<m. \<Delta>\<Delta> i h) = 0" if "\<And>i. i\<le>m \<Longrightarrow> h > hgt k (p i)" for h
    using that by (simp add: sum.neutral \<Delta>\<Delta>_def)
  then have B: "(\<Sum>i<m. \<Delta>\<Delta> i h) = 0" if "h \<ge> maxh" for h
    by (meson hgt_le_maxh le_simps le_trans not_less_eq that)
  have "(\<Sum>h=Suc 0..maxh. \<Sum>i<m. \<Delta>\<Delta> i h / alpha k h) \<le> (\<Sum>h=Suc 0..maxh. 1)"
  proof (intro sum_mono)
    fix h
    assume "h \<in> {Suc 0..maxh}"
    have "(\<Sum>i<m. \<Delta>\<Delta> i h) \<le> alpha k h"
      using qfun_mono [of k "h-1" h] \<open>k>0\<close>
      unfolding \<Delta>\<Delta>_def alpha_def sum_lessThan_telescope [where f = "\<lambda>i. pp i h"]
      by (auto simp add: pp_def p_def pee_eq_p0)
    then show "(\<Sum>i<m. \<Delta>\<Delta> i h / alpha k h) \<le> 1"
      using alpha_ge0 [of k h] by (simp add: divide_simps flip: sum_divide_distrib) 
  qed
  also have "\<dots> \<le> 1 + 2 * ln k / eps k"
    using \<open>maxh > 1\<close> by (simp add: maxh_def)
  finally have 34: "(\<Sum>h=Suc 0..maxh. \<Sum>i<m. \<Delta>\<Delta> i h / alpha k h) \<le> 1 + 2 * ln k / eps k" .

  define \<B> where "\<B> \<equiv> Step_class \<mu> l k {bblue_step}" 
  define \<S> where "\<S> \<equiv> Step_class \<mu> l k {dboost_step}" 
  define \<S>\<S> where "\<S>\<S> \<equiv> dboost_star \<mu> l k"
  have "\<S>\<S> \<subseteq> \<S>"
    unfolding \<S>\<S>_def \<S>_def dboost_star_def by auto
  have "finite (Step_class \<mu> l k {red_step,bblue_step,dboost_step,dreg_step})"
    using big \<mu> \<open>Colours l k\<close> by (auto simp: Big_ZZ_8_1_def finite_components) 
  then have "finite \<B>" "finite \<R>" "finite \<S>"
    by (auto simp add: \<B>_def \<R>_def \<S>_def Step_class_insert_NO_MATCH)

  have R52: "p (Suc i) - p i \<ge> (1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k (hgt k (p i))"
    and beta_gt0: "beta \<mu> l k i > 0"
    and R53: "p (Suc i) \<ge> p i \<and> beta \<mu> l k i \<ge> 1 / (real k)\<^sup>2"
    if "i \<in> \<S>" for i
    using big \<open>Colours l k\<close> that
    by (auto simp: Big_ZZ_8_1_def Lemma_Red_5_2_def Lemma_Red_5_3_def p_def \<S>_def)

  have \<Delta>\<Delta>_ge0: "\<Delta>\<Delta> i h \<ge> 0" if "i \<in> \<S>" "h \<ge> 1" for i h
    using that R53 [OF \<open>i \<in> \<S>\<close>] by (fastforce simp add: \<Delta>\<Delta>_def pp_eq)

  have \<Delta>\<Delta>_eq_0: "\<Delta>\<Delta> i h = 0" if "hgt k (p i) \<le> hgt k (p (Suc i))" "hgt k (p (Suc i)) < h" for h i
    using \<Delta>\<Delta>_def that by fastforce

  have 35: "(1 - eps k powr (1/2)) * ((1 - beta \<mu> l k i) / beta \<mu> l k i)
          \<le> (\<Sum>h=1..maxh. \<Delta>\<Delta> i h / alpha k h)"   (is "?L \<le> ?R")
    if "i \<in> \<S>\<S>" for i
  proof -
    have "i \<in> \<S>"
      using \<open>\<S>\<S> \<subseteq> \<S>\<close> that by blast
    have [simp]: "real (hgt k x - Suc 0) = real (hgt k x) - 1" for x
      using hgt_gt0 [of k x] by linarith

    have 36: "(1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) \<le> \<Delta> i / alpha k (hgt k (p i))"
      using R52 alpha_gt0 [OF \<open>k>0\<close> hgt_gt0] beta_gt0 that \<open>\<S>\<S> \<subseteq> \<S>\<close> by (force simp add: \<Delta>_def divide_simps)

    have k_big: "(1 + eps k powr (1/2)) \<ge> (1 + eps k) powr (eps k powr (-1/4))"
      using big \<open>k\<ge>l\<close> by (auto simp: Big_ZZ_8_1_def Big_ZZ_8_2_def)
    have *: "\<And>x::real. x > 0 \<Longrightarrow> (1 - x powr (1 / 2)) * (1 + x powr (1 / 2)) = 1 - x"
      by (simp add: algebra_simps flip: powr_add)
    have "?L = (1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) / (1 + eps k powr (1/2))"
      using beta_gt0 [OF \<open>i \<in> \<S>\<close>] eps_gt0 [OF \<open>k>0\<close>] k_big by (force simp add: divide_simps *)
    also have "\<dots> \<le> \<Delta> i / alpha k (hgt k (p i)) / (1 + eps k powr (1/2))"
      by (intro 36 divide_right_mono) auto
    also have "\<dots> \<le> \<Delta> i / alpha k (hgt k (p i)) / (1 + eps k) powr (real (hgt k (p (Suc i))) - hgt k (p i))"
    proof (intro divide_left_mono)
      have "real (hgt k (p (Suc i))) - hgt k (p i) \<le> eps k powr (-1/4)"
        using that by (simp add: \<S>\<S>_def dboost_star_def p_def)
      then show "(1 + eps k) powr (real (hgt k (p (Suc i))) - real (hgt k (p i))) \<le> 1 + eps k powr (1 / 2)"
        using k_big by (smt (verit) eps_ge0 powr_mono)
      show "0 \<le> \<Delta> i / alpha k (hgt k (p i))"
        by (simp add: \<Delta>0 \<Delta>\<Delta>_ge0 \<open>i \<in> \<S>\<close> alpha_ge0)
      show "0 < (1 + eps k powr (1 / 2)) * (1 + eps k) powr (real (hgt k (p (Suc i))) - real (hgt k (p i)))"
        using eps_gt0 [OF \<open>k>0\<close>] by (smt (verit) powr_gt_zero zero_less_mult_iff)
    qed
    also have "\<dots> \<le> \<Delta> i / alpha k (hgt k (p (Suc i)))"
    proof -
      have "alpha k (hgt k (p (Suc i))) \<le> alpha k (hgt k (p i)) * (1 + eps k) powr (real (hgt k (p (Suc i))) - real (hgt k (p i)))"
        using eps_gt0[OF \<open>k>0\<close>] hgt_gt0[of k]
        by (simp add: alpha_eq divide_right_mono flip: powr_realpow powr_add)
      moreover have "0 \<le> \<Delta> i"
        by (simp add: \<Delta>0 \<Delta>\<Delta>_ge0 \<open>i \<in> \<S>\<close>)
      moreover have "0 < alpha k (hgt k (p i)) * (1 + eps k) powr (real (hgt k (p (Suc i))) - hgt k (p i)) * alpha k (hgt k (p (Suc i)))"
        by (smt (verit) alpha_gt0 eps_gt0 hgt_gt0 \<open>k>0\<close> mult_pos_pos powr_gt_zero)
      ultimately show ?thesis
        by (simp add: divide_left_mono)
    qed
    also have "\<dots> \<le> ?R"
      unfolding 33 sum_divide_distrib
    proof (intro sum_mono)
      fix h
      assume h: "h \<in> {1..maxh}"
      show "\<Delta>\<Delta> i h / alpha k (hgt k (p (Suc i))) \<le> \<Delta>\<Delta> i h / alpha k h"
      proof (cases  "hgt k (p i) \<le> hgt k (p (Suc i)) \<and> hgt k (p (Suc i)) < h")
        case False
        then show ?thesis
          using \<open>k>0\<close> h
          apply (auto simp: )
          using R53 \<open>i \<in> \<S>\<close> hgt_mono \<open>k>0\<close> apply blast
          apply (simp add: not_less)
          apply (intro divide_left_mono)
          apply (metis alpha_0' alpha_ge0 alpha_mono gr0I)
           defer
           apply (simp add: zero_less_mult_iff)
           apply (auto simp: )
          using alpha_gt0 hgt_gt0 apply presburger
             apply (intro alpha_gt0)
              apply (auto simp: )
          using alpha_gt0 hgt_gt0 apply presburger
          using Suc_le_lessD alpha_gt0 apply blast
          by (simp add: \<Delta>\<Delta>_ge0 \<open>i \<in> \<S>\<close>)
      qed (auto simp: \<Delta>\<Delta>_eq_0)
    qed
    finally show ?thesis .
  qed
  \<comment> \<open>now we are able to prove claim 8.2\<close>
  have "(1 - eps k powr (1/2)) * (\<Sum>i\<in>\<S>\<S>. ((1 - beta \<mu> l k i) / beta \<mu> l k i))
     = (\<Sum>i\<in>\<S>\<S>. (1 - eps k powr (1/2)) * ((1 - beta \<mu> l k i) / beta \<mu> l k i))"
    using sum_distrib_left by blast
  also have "\<dots> \<le> (\<Sum>i\<in>\<S>\<S>. \<Sum>h=1..maxh. \<Delta>\<Delta> i h / alpha k h)"
    by (intro sum_mono 35)
  also have "\<dots> = (\<Sum>h=1..maxh. \<Sum>i\<in>\<S>\<S>. \<Delta>\<Delta> i h / alpha k h)"
    using sum.swap by fastforce
  also have "\<dots> \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<S>. \<Delta>\<Delta> i h / alpha k h)"
    by (intro sum_mono sum_mono2) (auto simp: \<open>finite \<S>\<close> \<open>\<S>\<S> \<subseteq> \<S>\<close> \<Delta>\<Delta>_ge0 alpha_ge0)
  finally have 82: "(1 - eps k powr (1/2)) * (\<Sum>i\<in>\<S>\<S>. ((1 - beta \<mu> l k i) / beta \<mu> l k i))
      \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<S>. \<Delta>\<Delta> i h / alpha k h)" .

  have "(\<lambda>k. 1 + 2 * ln k / eps k) \<in> o(real)"  (*? ?*)
    unfolding eps_def by real_asymp

  show ?thesis
    sorry
qed

end

end
