section \<open>The Zigzag Lemma\<close>
                                                        
theory Zigzag imports Bounding_X
                                             
begin                  
          
subsection \<open>Lemma 8.1 (the actual Zigzag Lemma)\<close>

definition "Big_ZZ_8_2 \<equiv> \<lambda>k. (1 + eps k powr (1/2)) \<ge> (1 + eps k) powr (eps k powr (-1/4))"
                                                 
text \<open>An inequality that pops up in the proof of (39)\<close>
definition "Big39 \<equiv> \<lambda>k. 1/2 \<le> (1 + eps k) powr (-2 * eps k powr (-1/2))"

text \<open>Two inequalities that pops up in the proof of (42)\<close>
definition "Big42a \<equiv> \<lambda>k. (1 + eps k)\<^sup>2 / (1 - eps k powr (1/2)) \<le> 1 + 2 * k powr (-1/16)" 

definition "Big42b \<equiv> \<lambda>k. 2 * k powr (-1/16) * k
                        + (1 + 2 * ln k / eps k + 2 * k powr (7/8)) / (1 - eps k powr (1/2))
                       \<le> real k powr (19/20)"

definition "Big_ZZ_8_1 \<equiv>
   \<lambda>\<mu> l. Big_Blue_4_1 \<mu> l \<and> Big_Red_5_1 \<mu> l \<and> Big_Red_5_3 \<mu> l \<and> Big_Y_6_5_Bblue l
        \<and> (\<forall>k. k\<ge>l \<longrightarrow> Big_height_upper_bound k \<and> Big_ZZ_8_2 k \<and> k\<ge>16 \<and> Big39 k
                      \<and> Big42a k \<and> Big42b k)"

text \<open>@{term "k\<ge>16"} is for @{text Y_6_5_Red}\<close>


lemma Big_ZZ_8_1:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_ZZ_8_1 \<mu> l"
  using assms Big_Blue_4_1 Big_Red_5_1 Big_Red_5_3 Big_Y_6_5_Bblue
  unfolding Big_ZZ_8_1_def Big_ZZ_8_2_def Big39_def Big42a_def Big42b_def
            eventually_conj_iff all_imp_conj_distrib eps_def
  apply (simp add: eventually_conj_iff eventually_frequently_const_simps)   
  apply (intro conjI strip eventually_all_ge_at_top Big_height_upper_bound; real_asymp)
  done

lemma (in Book) ZZ_8_1:
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours l k" and big: "Big_ZZ_8_1 \<mu> l" 
  defines "\<S>\<S> \<equiv> dboost_star \<mu> l k" and "\<R> \<equiv> Step_class \<mu> l k {red_step}"
  defines "sum_\<S>\<S> \<equiv> (\<Sum>i\<in>\<S>\<S>. (1 - beta \<mu> l k i) / beta \<mu> l k i)"
  shows "sum_\<S>\<S> \<le> real (card \<R>) + k powr (19/20)"
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
  have maxh: "\<And>p. p\<le>1 \<Longrightarrow> hgt k p \<le> 2 * ln k / eps k" and "k\<ge>16"
    using big \<open>k\<ge>l\<close> by (auto simp: Big_ZZ_8_1_def height_upper_bound)
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
      by (force simp: pp_eq)
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
      by (auto simp: pp_def p_def pee_eq_p0)
    then show "(\<Sum>i<m. \<Delta>\<Delta> i h / alpha k h) \<le> 1"
      using alpha_ge0 [of k h] by (simp add: divide_simps flip: sum_divide_distrib) 
  qed
  also have "\<dots> \<le> 1 + 2 * ln k / eps k"
    using \<open>maxh > 1\<close> by (simp add: maxh_def)
  finally have 34: "(\<Sum>h=Suc 0..maxh. \<Sum>i<m. \<Delta>\<Delta> i h / alpha k h) \<le> 1 + 2 * ln k / eps k" .

  define \<D> where "\<D> \<equiv> Step_class \<mu> l k {dreg_step}" 
  define \<B> where "\<B> \<equiv> Step_class \<mu> l k {bblue_step}" 
  define \<S> where "\<S> \<equiv> Step_class \<mu> l k {dboost_step}" 
  have "\<S>\<S> \<subseteq> \<S>"
    unfolding \<S>\<S>_def \<S>_def dboost_star_def by auto
  have BD_disj: "\<B>\<inter>\<D> = {}" and disj: "\<R>\<inter>\<B> = {}" "\<S>\<inter>\<B> = {}" "\<R>\<inter>\<D> = {}" "\<S>\<inter>\<D> = {}" "\<R>\<inter>\<S> = {}"
    by (auto simp: \<D>_def \<R>_def \<B>_def \<S>_def Step_class_def)

  have [simp]: "finite \<D>" "finite \<B>" "finite \<R>" "finite \<S>"
    using finite_components assms 
    by (auto simp: \<D>_def \<B>_def \<R>_def \<S>_def Step_class_insert_NO_MATCH)
  have "card \<R> < k"
    using red_step_limit \<open>0<\<mu>\<close> \<open>Colours l k\<close> by (auto simp: \<R>_def)

  have R52: "p (Suc i) - p i \<ge> (1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) * alpha k (hgt k (p i))"
    and beta_gt0: "beta \<mu> l k i > 0"
    and R53: "p (Suc i) \<ge> p i \<and> beta \<mu> l k i \<ge> 1 / (real k)\<^sup>2"
        if "i \<in> \<S>" for i
    using \<mu> big \<open>Colours l k\<close> Red_5_2 that
    by (auto simp: Big_ZZ_8_1_def Red_5_3 p_def \<B>_def \<S>_def)
  have card\<B>: "card \<B> \<le> l powr (3/4)" and bigY65B: "Big_Y_6_5_Bblue l"
    using \<mu> big \<open>Colours l k\<close> bblue_step_limit by (auto simp: Big_ZZ_8_1_def \<B>_def)

  have \<Delta>\<Delta>_ge0: "\<Delta>\<Delta> i h \<ge> 0" if "i \<in> \<S>" "h \<ge> 1" for i h
    using that R53 [OF \<open>i \<in> \<S>\<close>] by (fastforce simp: \<Delta>\<Delta>_def pp_eq)
  have \<Delta>\<Delta>_eq_0: "\<Delta>\<Delta> i h = 0" if "hgt k (p i) \<le> hgt k (p (Suc i))" "hgt k (p (Suc i)) < h" for h i
    using \<Delta>\<Delta>_def that by fastforce
  define oneminus where "oneminus \<equiv> 1 - eps k powr (1/2)"
  have 35: "oneminus * ((1 - beta \<mu> l k i) / beta \<mu> l k i)
          \<le> (\<Sum>h=1..maxh. \<Delta>\<Delta> i h / alpha k h)"   (is "?L \<le> ?R")
    if "i \<in> \<S>\<S>" for i
  proof -
    have "i \<in> \<S>"
      using \<open>\<S>\<S> \<subseteq> \<S>\<close> that by blast
    have [simp]: "real (hgt k x - Suc 0) = real (hgt k x) - 1" for x
      using hgt_gt0 [of k x] by linarith
    have 36: "(1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) \<le> \<Delta> i / alpha k (hgt k (p i))"
      using R52 alpha_gt0 [OF \<open>k>0\<close> hgt_gt0] beta_gt0 that \<open>\<S>\<S> \<subseteq> \<S>\<close> by (force simp: \<Delta>_def divide_simps)
    have k_big: "(1 + eps k powr (1/2)) \<ge> (1 + eps k) powr (eps k powr (-1/4))"
      using big \<open>k\<ge>l\<close> by (auto simp: Big_ZZ_8_1_def Big_ZZ_8_2_def)
    have *: "\<And>x::real. x > 0 \<Longrightarrow> (1 - x powr (1/2)) * (1 + x powr (1/2)) = 1 - x"
      by (simp add: algebra_simps flip: powr_add)
    have "?L = (1 - eps k) * ((1 - beta \<mu> l k i) / beta \<mu> l k i) / (1 + eps k powr (1/2))"
      using beta_gt0 [OF \<open>i \<in> \<S>\<close>] eps_gt0 [OF \<open>k>0\<close>] k_big 
      by (force simp: oneminus_def divide_simps *)
    also have "\<dots> \<le> \<Delta> i / alpha k (hgt k (p i)) / (1 + eps k powr (1/2))"
      by (intro 36 divide_right_mono) auto
    also have "\<dots> \<le> \<Delta> i / alpha k (hgt k (p i)) / (1 + eps k) powr (real (hgt k (p (Suc i))) - hgt k (p i))"
    proof (intro divide_left_mono)
      have "real (hgt k (p (Suc i))) - hgt k (p i) \<le> eps k powr (-1/4)"
        using that by (simp add: \<S>\<S>_def dboost_star_def p_def)
      then show "(1 + eps k) powr (real (hgt k (p (Suc i))) - real (hgt k (p i))) \<le> 1 + eps k powr (1/2)"
        using k_big by (smt (verit) eps_ge0 powr_mono)
      show "0 \<le> \<Delta> i / alpha k (hgt k (p i))"
        by (simp add: \<Delta>0 \<Delta>\<Delta>_ge0 \<open>i \<in> \<S>\<close> alpha_ge0)
      show "0 < (1 + eps k) powr (real (hgt k (p (Suc i))) - real (hgt k (p i)))"
        using eps_gt0 [OF \<open>k>0\<close>] by auto
    qed
    also have "\<dots> \<le> \<Delta> i / alpha k (hgt k (p (Suc i)))"
    proof -
      have "alpha k (hgt k (p (Suc i))) \<le> alpha k (hgt k (p i)) * (1 + eps k) powr (real (hgt k (p (Suc i))) - real (hgt k (p i)))"
        using eps_gt0[OF \<open>k>0\<close>] hgt_gt0[of k]
        by (simp add: alpha_eq divide_right_mono flip: powr_realpow powr_add)
      moreover have "0 \<le> \<Delta> i"
        by (simp add: \<Delta>0 \<Delta>\<Delta>_ge0 \<open>i \<in> \<S>\<close>)
      moreover have "0 < alpha k (hgt k (p (Suc i)))"
        by (simp add: alpha_gt0 hgt_gt0 \<open>k>0\<close>)
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
        then consider "hgt k (p i) > hgt k (p (Suc i))" | "hgt k (p (Suc i)) \<ge> h"
          by linarith
        then show ?thesis
        proof cases
          case 1
          then show ?thesis
            using R53 \<open>i \<in> \<S>\<close> hgt_mono' by fastforce
        next
          case 2
          have "alpha k h \<le> alpha k (hgt k (p (Suc i)))"
            using "2" alpha_mono h by auto
          moreover have "0 \<le> \<Delta>\<Delta> i h"
            using \<Delta>\<Delta>_ge0 \<open>i \<in> \<S>\<close> h by presburger
          moreover have "0 < alpha k h"
            using h \<open>k>0\<close> by (simp add: alpha_gt0 hgt_gt0)
          ultimately show ?thesis
            by (simp add: divide_left_mono)
        qed
      qed (auto simp: \<Delta>\<Delta>_eq_0)
    qed
    finally show ?thesis .
  qed
  \<comment> \<open>now we are able to prove claim 8.2\<close>
  have "oneminus * sum_\<S>\<S>
     = (\<Sum>i\<in>\<S>\<S>. oneminus * ((1 - beta \<mu> l k i) / beta \<mu> l k i))"
    using sum_distrib_left sum_\<S>\<S>_def by blast
  also have "\<dots> \<le> (\<Sum>i\<in>\<S>\<S>. \<Sum>h=1..maxh. \<Delta>\<Delta> i h / alpha k h)"
    by (intro sum_mono 35)
  also have "\<dots> = (\<Sum>h=1..maxh. \<Sum>i\<in>\<S>\<S>. \<Delta>\<Delta> i h / alpha k h)"
    using sum.swap by fastforce
  also have "\<dots> \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<S>. \<Delta>\<Delta> i h / alpha k h)"
    by (intro sum_mono sum_mono2) (auto simp: \<open>\<S>\<S> \<subseteq> \<S>\<close> \<Delta>\<Delta>_ge0 alpha_ge0)
  finally have 82: "oneminus * sum_\<S>\<S>
      \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<S>. \<Delta>\<Delta> i h / alpha k h)" .
  \<comment> \<open>leading onto claim 8.3\<close>
  have \<Delta>alpha: "- 1 \<le> \<Delta> i / alpha k (hgt k (p i))" if "i \<in> \<R>" for i
    using Y_6_4_Red [of i] \<open>i \<in> \<R>\<close> alpha_ge0 \<open>k>0\<close>
    unfolding \<Delta>_def \<R>_def p_def
    by (smt (verit, best) hgt_gt0 alpha_gt0 divide_minus_left less_divide_eq_1_pos)

  have "(\<Sum>i\<in>\<R>. - (1 + eps k)\<^sup>2) \<le> (\<Sum>i\<in>\<R>. \<Sum>h=1..maxh. \<Delta>\<Delta> i h / alpha k h)"
  proof (intro sum_mono)
    fix i :: nat
    assume "i \<in> \<R>"
    show "- (1 + eps k)\<^sup>2 \<le> (\<Sum>h = 1..maxh. \<Delta>\<Delta> i h / alpha k h)"
    proof (cases "\<Delta> i < 0")
      case True
      have "(1 + eps k)\<^sup>2 * -1 \<le> (1 + eps k)\<^sup>2 * (\<Delta> i / alpha k (hgt k (p i)))"
        using \<Delta>alpha \<open>k>0\<close>
        by (smt (verit, best) power2_less_0 \<open>i \<in> \<R>\<close> mult_le_cancel_left2 mult_minus_right)
      also have "\<dots> \<le> (\<Sum>h = 1..maxh. \<Delta>\<Delta> i h / alpha k h)"
      proof -
        have le0: "\<Delta>\<Delta> i h \<le> 0" for h 
          using True by (auto simp: \<Delta>\<Delta>_def \<Delta>_def pp_eq)
        have eq0: "\<Delta>\<Delta> i h = 0" if "1 \<le> h" "h < hgt k (p i) - 2" for h 
        proof -
          have "hgt k (p i) - 2 \<le> hgt k (p (Suc i))"
            using Y_6_5_Red \<open>16 \<le> k\<close> \<open>i \<in> \<R>\<close> p_def unfolding \<R>_def by blast
          then show ?thesis
            using that pp_less_hgt[of h] by (auto simp: \<Delta>\<Delta>_def pp_def)
        qed
        show ?thesis
          unfolding 33 sum_distrib_left sum_divide_distrib
        proof (intro sum_mono)
          fix h :: nat
          assume "h \<in> {1..maxh}"
          then have "1 \<le> h" "h \<le> maxh" by auto
          show "(1 + eps k)\<^sup>2 * (\<Delta>\<Delta> i h / alpha k (hgt k (p i))) \<le> \<Delta>\<Delta> i h / alpha k h"
          proof (cases "h < hgt k (p i) - 2")
            case True
            then show ?thesis
              using \<open>1 \<le> h\<close> eq0 by force
          next
            case False
            have *: "(1 + eps k) ^ (hgt k (p i) - Suc 0) \<le> (1 + eps k)\<^sup>2 * (1 + eps k) ^ (h - Suc 0)"
              using False eps_ge0 unfolding power_add [symmetric] 
              by (intro power_increasing) auto
            have **: "(1 + eps k)\<^sup>2 * alpha k h \<ge> alpha k (hgt k (p i))"
              using \<open>1 \<le> h\<close> mult_left_mono [OF *, of "eps k"] eps_ge0
              by (simp add: alpha_eq hgt_gt0 mult_ac divide_right_mono)
            show ?thesis
              using le0 alpha_gt0 \<open>k>0\<close> \<open>h\<ge>1\<close> hgt_gt0
              using mult_left_mono_neg [OF **, of "\<Delta>\<Delta> i h"]
              by (simp add: divide_simps mult_ac)
          qed
        qed
      qed
      finally show ?thesis
        by linarith 
    next
      case False
      then have "\<Delta>\<Delta> i h \<ge> 0" for h
        using \<Delta>\<Delta>_def \<Delta>_def pp_eq by auto
      then have "(\<Sum>h = 1..maxh. \<Delta>\<Delta> i h / alpha k h) \<ge> 0"
        by (simp add: alpha_ge0 sum_nonneg)
      then show ?thesis
        by (smt (verit, ccfv_SIG) sum_power2_ge_zero)
    qed
  qed
  then have 83: "- (1 + eps k)\<^sup>2 * card \<R> \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<R>. \<Delta>\<Delta> i h / alpha k h)" 
    by (simp add: mult.commute sum.swap [of _ \<R>])

  \<comment> \<open>now to tackle claim 8.4\<close>

  have \<Delta>0: "\<Delta> i \<ge> 0" if "i \<in> \<D>" for i
    using Y_6_4_DegreeReg that unfolding \<D>_def \<Delta>_def p_def by auto

  have 39: "-2 * eps k powr(-1/2) \<le> (\<Sum>h = 1..maxh. (\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h) / alpha k h)" (is "?L \<le> ?R")
    if "i \<in> \<B>" for i
  proof -
    have "odd i"
      using step_odd that by (force simp: Step_class_insert_NO_MATCH \<B>_def)
    then have "i>0"
      using odd_pos by auto
    show ?thesis
    proof (cases "\<Delta> (i-1) + \<Delta> i \<ge> 0")
      case True
      with \<open>i>0\<close> have "\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h \<ge> 0" if "h\<ge>1" for h
        by (fastforce simp: \<Delta>\<Delta>_def \<Delta>_def pp_eq)
      then have "(\<Sum>h = 1..maxh. (\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h) / alpha k h) \<ge> 0"
        by (force simp: alpha_ge0 intro: sum_nonneg)
      then show ?thesis
        by (smt (verit, ccfv_SIG) powr_ge_pzero)
    next
      case False
      then have \<Delta>\<Delta>_le0: "\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h \<le> 0" if "h\<ge>1" for h
        by (smt (verit, best) One_nat_def \<Delta>\<Delta>_def \<Delta>_def \<open>odd i\<close> odd_Suc_minus_one pp_eq)
      have hge: "hgt k (p (Suc i)) \<ge> hgt k (p (i-1)) - 2 * eps k powr (-1/2)"
        using bigY65B \<mu> \<open>Colours l k\<close> that Y_6_5_Bblue 
        by (fastforce simp: p_def \<B>_def )
      have \<Delta>\<Delta>0: "\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h = 0" if "0<h" "h < hgt k (p (i-1)) - 2 * eps k powr (-1/2)" for h
        using \<open>odd i\<close> that hge  unfolding \<Delta>\<Delta>_def One_nat_def
        by (smt (verit) of_nat_less_iff odd_Suc_minus_one powr_non_neg pp_less_hgt)
      have big39: "1/2 \<le> (1 + eps k) powr (-2 * eps k powr (-1/2))"
        using big \<open>k\<ge>l\<close> by (auto simp: Big_ZZ_8_1_def Big39_def)
      have "?L * alpha k (hgt k (p (i-1))) * (1 + eps k) powr (-2 * eps k powr (-1/2))
           \<le> - (eps k powr (-1/2)) * alpha k (hgt k (p (i-1)))"
        using mult_left_mono_neg [OF big39, of "- (eps k powr (-1/2)) * alpha k (hgt k (p (i-1))) / 2"]
        using alpha_ge0 [of k "hgt k (p (i-1))"] eps_ge0 [of k]
        by (simp add: mult_ac)
      also have "\<dots> \<le> \<Delta> (i-1) + \<Delta> i"
      proof -
        have "p (Suc i) \<ge> p (i-1) - (eps k powr (-1/2)) * alpha k (hgt k (p (i-1)))"
          using Y_6_4_Bblue that \<B>_def \<open>\<mu>>0\<close> p_def by blast
        with \<open>i>0\<close> show ?thesis
          by (simp add: \<Delta>_def)
      qed
      finally have "?L * alpha k (hgt k (p (i-1))) * (1 + eps k) powr (-2 * eps k powr (-1/2)) \<le> \<Delta> (i-1) + \<Delta> i" .
      then have "?L \<le> (1 + eps k) powr (2 * eps k powr (-1/2)) * (\<Delta> (i-1) + \<Delta> i) / alpha k (hgt k (p (i-1)))"
        using alpha_ge0 [of k "hgt k (p (i-1))"] eps_ge0 [of k]
        by (simp add: powr_minus divide_simps mult_ac)
      also have "\<dots> \<le> ?R"
      proof -
        have "(1 + eps k) powr (2 * eps k powr - (1/2)) * (\<Delta>\<Delta> (i - Suc 0) h + \<Delta>\<Delta> i h) / alpha k (hgt k (p (i - Suc 0))) \<le> (\<Delta>\<Delta> (i - Suc 0) h + \<Delta>\<Delta> i h) / alpha k h"
          if h: "Suc 0 \<le> h" "h \<le> maxh" for h
        proof (cases "h < hgt k (p (i-1)) - 2 * eps k powr (-1/2)")
          case False
          then have *: "(1 + eps k) powr (2 * eps k powr - (1/2)) / alpha k (hgt k (p (i - Suc 0))) \<ge> 1 / alpha k h"
            using that eps_gt0[of k] \<open>k>0\<close> hgt_gt0[of k]
            apply (simp add: alpha_eq divide_simps flip: powr_realpow powr_add)
            by (smt (verit) Num.of_nat_simps(3) Suc_pred)
          show ?thesis
            using mult_left_mono_neg [OF * \<Delta>\<Delta>_le0] that by (simp add: Groups.mult_ac) 
        qed (use h \<Delta>\<Delta>0 in auto)
        then show ?thesis
          by (force simp: 33 sum_distrib_left sum_divide_distrib simp flip: sum.distrib intro: sum_mono)
      qed
      finally show ?thesis .
    qed
  qed

  have B34: "card \<B> \<le> k powr (3/4)"
    by (smt (verit) card\<B> \<open>l\<le>k\<close> of_nat_0_le_iff of_nat_mono powr_mono2 zero_le_divide_iff)
  have "-2 * k powr (7/8) \<le> -2 * eps k powr(-1/2) * k powr (3/4)"
    by (simp add: eps_def powr_powr flip: powr_add)
  also have "\<dots> \<le> -2 * eps k powr(-1/2) * card \<B>"
    using B34 by (intro mult_left_mono_neg powr_mono2) auto
  also have "\<dots> = (\<Sum>i\<in>\<B>. -2 * eps k powr(-1/2))"
    by simp
  also have "\<dots> \<le> (\<Sum>h = 1..maxh. \<Sum>i\<in>\<B>. (\<Delta>\<Delta> (i-1) h + \<Delta>\<Delta> i h) / alpha k h)"
    unfolding sum.swap [of _ \<B>] by (intro sum_mono 39)
  also have "\<dots> \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<B>\<union>\<D>. \<Delta>\<Delta> i h / alpha k h)"
  proof (intro sum_mono)
    fix h
    assume "h \<in> {1..maxh}"
    have inj_pred: "inj_on (\<lambda>i. i - Suc 0) \<B>"
      using odd_pos [OF step_odd]   
      apply (simp add: \<B>_def inj_on_def Step_class_insert_NO_MATCH)
      by (metis Suc_pred)
    have "(\<Sum>i\<in>\<B>. \<Delta>\<Delta> (i - Suc 0) h) = (\<Sum>i \<in> (\<lambda>i. i-1) ` \<B>. \<Delta>\<Delta> i h)"
      by (simp add: sum.reindex [OF inj_pred])
    also have "\<dots> \<le> (\<Sum>i\<in>\<D>. \<Delta>\<Delta> i h)"
    proof (intro sum_mono2)
      show "(\<lambda>i. i - 1) ` \<B> \<subseteq> \<D>"
        by (force simp: \<D>_def \<B>_def Step_class_insert_NO_MATCH intro: dreg_before_step')
      show "0 \<le> \<Delta>\<Delta> i h" if "i \<in> \<D> \<setminus> (\<lambda>i. i - 1) ` \<B>" for i
        using that \<Delta>0 \<Delta>\<Delta>_def \<Delta>_def pp_eq by fastforce
    qed auto
    finally have "(\<Sum>i\<in>\<B>. \<Delta>\<Delta> (i - Suc 0) h) \<le> (\<Sum>i\<in>\<D>. \<Delta>\<Delta> i h)" .
    with alpha_ge0 [of k h]
    show "(\<Sum>i\<in>\<B>. (\<Delta>\<Delta> (i - 1) h + \<Delta>\<Delta> i h) / alpha k h) \<le> (\<Sum>i \<in> \<B>\<union>\<D>. \<Delta>\<Delta> i h / alpha k h)"
      by (simp add: BD_disj divide_right_mono sum.distrib sum.union_disjoint flip: sum_divide_distrib)
    qed
  finally have 84: "-2 * k powr (7/8) \<le> (\<Sum>h=1..maxh. \<Sum>i\<in>\<B>\<union>\<D>. \<Delta>\<Delta> i h / alpha k h)" .

  have m_eq: "{..<m} = \<R> \<union> \<S> \<union> (\<B> \<union> \<D>)"
    using before_halted_eq \<open>\<mu>>0\<close> \<open>Colours l k\<close>
    by (auto simp: \<B>_def \<D>_def \<S>_def \<R>_def m_def Step_class_insert_NO_MATCH)

  have "- (1 + eps k)\<^sup>2 * real (card \<R>)
     + oneminus * sum_\<S>\<S> 
     - 2 * real k powr (7/8) \<le> (\<Sum>h = Suc 0..maxh. \<Sum>i\<in>\<R>. \<Delta>\<Delta> i h / alpha k h)
      + (\<Sum>h = Suc 0..maxh. \<Sum>i\<in>\<S>. \<Delta>\<Delta> i h / alpha k h)
      + (\<Sum>h = Suc 0..maxh. \<Sum>i \<in> \<B> \<union> \<D>. \<Delta>\<Delta> i h / alpha k h) "
    using 82 83 84 by simp
  also have "\<dots> = (\<Sum>h = Suc 0..maxh. \<Sum>i \<in> \<R> \<union> \<S> \<union> (\<B> \<union> \<D>). \<Delta>\<Delta> i h / alpha k h)"
    by (simp add: sum.distrib disj sum.union_disjoint Int_Un_distrib Int_Un_distrib2)
  also have "\<dots> \<le> 1 + 2 * ln (real k) / eps k"
    using 34 by (simp add: m_eq)
  finally
  have 41: "oneminus * sum_\<S>\<S> - (1 + eps k)\<^sup>2 * card \<R> - 2 * k powr (7/8)
          \<le> 1 + 2 * ln k / eps k" 
    by simp
  have big42: "(1 + eps k)\<^sup>2 / oneminus \<le> 1 + 2 * k powr (-1/16)"
              "2 * k powr (-1/16) * k
             + (1 + 2 * ln k / eps k + 2 * k powr (7/8)) / oneminus
       \<le> real k powr (19/20)"
    using big \<open>l\<le>k\<close> \<open>Colours l k\<close> by (auto simp: Big_ZZ_8_1_def Big42a_def Big42b_def oneminus_def)
  have "oneminus > 0"
    using \<open>16 \<le> k\<close> eps_gt0 eps_less1 powr01_less_one by (auto simp: oneminus_def)
  with 41 have "sum_\<S>\<S>
        \<le> (1 + 2 * ln k / eps k + (1 + eps k)\<^sup>2 * card \<R> + 2 * k powr (7/8)) / oneminus" 
    by (simp add: mult_ac pos_le_divide_eq diff_le_eq)
  also have "\<dots> \<le> card \<R> * (((1 + eps k)\<^sup>2) / oneminus) 
                 + (1 + 2 * ln k / eps k + 2 * k powr (7/8)) / oneminus"
    by (simp add: field_simps add_divide_distrib)
  also have "\<dots> \<le> card \<R> * (1 + 2 * k powr (-1/16)) 
                 + (1 + 2 * ln k / eps k + 2 * k powr (7/8)) / oneminus"
    using big42 \<open>oneminus > 0\<close> by (intro add_mono mult_mono) auto
  also have "\<dots> \<le> card \<R> + 2 * k powr (-1/16) * k
                 + (1 + 2 * ln k / eps k + 2 * k powr (7/8)) / oneminus"
    using \<open>card \<R> < k\<close> by (intro add_mono mult_mono) (auto simp: algebra_simps)
  also have "\<dots> \<le> real (card \<R>) + real k powr (19/20)"
    using big42 by force
  finally show ?thesis .
qed

subsection \<open>Lemma 8.5\<close>

text \<open>An inequality that pops up in the proof of (39)\<close>
definition "inequality85 \<equiv> \<lambda>k. 3 * eps k powr (1/4) * k \<le> k powr (19/20)"

definition "Big_ZZ_8_5 \<equiv>     
   \<lambda>\<mu> l. Big_X_7_5 \<mu> l \<and> Big_ZZ_8_1 \<mu> l \<and> Big_Red_5_3 \<mu> l
      \<and> (\<forall>k\<ge>l. inequality85 k)"

lemma Big_ZZ_8_5:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_ZZ_8_5 \<mu> l"
  using assms Big_Red_5_3 Big_X_7_5 Big_ZZ_8_1
  unfolding Big_ZZ_8_5_def inequality85_def eps_def
  apply (simp add: eventually_conj_iff all_imp_conj_distrib)       
  apply (intro conjI strip eventually_all_ge_at_top; real_asymp)     
  done

lemma (in Book) ZZ_8_5:
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours l k" and big: "Big_ZZ_8_5 \<mu> l" 
  defines "\<R> \<equiv> Step_class \<mu> l k {red_step}" and "\<S> \<equiv> Step_class \<mu> l k {dboost_step}"
  shows "card \<S> \<le> (bigbeta \<mu> l k / (1 - bigbeta \<mu> l k)) * card \<R> 
        + (2 / (1-\<mu>)) * k powr (19/20)"
proof -
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  define \<S>\<S> where "\<S>\<S> \<equiv> dboost_star \<mu> l k" 
  have [simp]: "finite \<S>"
    by (simp add: assms dboost_step_finite)
  moreover have "\<S>\<S> \<subseteq> \<S>"
    by (auto simp: \<S>\<S>_def \<S>_def dboost_star_def)
  ultimately have "real (card \<S>) - real (card \<S>\<S>) = card (\<S>\<setminus>\<S>\<S>)"
    by (metis card_Diff_subset card_mono finite_subset of_nat_diff)
  also have "\<dots> \<le> 3 * eps k powr (1/4) * k"
    using \<mu> \<open>Colours l k\<close> big X_7_5 by (auto simp: Big_ZZ_8_5_def \<S>\<S>_def \<S>_def)
  also have "\<dots> \<le> k powr (19/20)"
    using big \<open>Colours l k\<close> by (auto simp: Big_ZZ_8_5_def inequality85_def Colours_def)
  finally have *: "real (card \<S>) - card \<S>\<S> \<le> k powr (19/20)" .
  have bigbeta_lt1: "bigbeta \<mu> l k < 1"
    and bigbeta_gt0: "0 < bigbeta \<mu> l k"
    and beta_gt0: "\<And>i. i \<in> \<S> \<Longrightarrow> beta \<mu> l k i > 0" 
    using bigbeta_ge0 big \<mu> \<open>Colours l k\<close> 
    by (auto simp: Big_ZZ_8_5_def \<S>_def beta_gt0 bigbeta_gt0 bigbeta_less1)
  then have ge0: "bigbeta \<mu> l k / (1 - bigbeta \<mu> l k) \<ge> 0"
    by auto
  show ?thesis
  proof (cases "\<S>\<S> = {}")
    case True
    with * have "card \<S> \<le> k powr (19/20)"
      by simp
    also have "\<dots> \<le> (2 / (1-\<mu>)) * k powr (19/20)"
      using \<mu> \<open>k>0\<close> by (simp add: divide_simps)
    finally show ?thesis
      by (smt (verit, ccfv_SIG) mult_nonneg_nonneg of_nat_0_le_iff ge0) 
  next
    case False    
    have bb_le: "bigbeta \<mu> l k \<le> \<mu>"
      using big bigbeta_le [OF \<mu> \<open>Colours l k\<close>] by (auto simp: Big_ZZ_8_5_def)
    have "(card \<S> - k powr (19/20)) / bigbeta \<mu> l k \<le> card \<S>\<S> / bigbeta \<mu> l k"
      by (smt (verit) "*" \<mu> bigbeta_ge0 divide_right_mono)
    also have "\<dots> = (\<Sum>i\<in>\<S>\<S>. 1 / beta \<mu> l k i)"
    proof (cases "card \<S>\<S> = 0")
      case False
      then show ?thesis
        by (simp add: bigbeta_def Let_def \<S>\<S>_def inverse_eq_divide)
    qed (simp add: False card_eq_0_iff)
    also have "\<dots> \<le> real(card \<S>\<S>) + card \<R> + k powr (19/20)"
    proof -
      have "(\<Sum>i\<in>\<S>\<S>. (1 - beta \<mu> l k i) / beta \<mu> l k i)
            \<le> real (card \<R>) + k powr (19/20)"
        using ZZ_8_1 big \<mu> \<open>Colours l k\<close> 
        unfolding Big_ZZ_8_5_def \<R>_def \<S>\<S>_def by blast
      moreover have "(\<Sum>i\<in>\<S>\<S>. beta \<mu> l k i / beta \<mu> l k i) = (\<Sum>i\<in>\<S>\<S>. 1)"
        using \<open>\<S>\<S> \<subseteq> \<S>\<close> beta_gt0 by (intro sum.cong) (force simp: )+
      ultimately show ?thesis
        by (simp add: field_simps diff_divide_distrib sum_subtractf)
    qed
    also have "\<dots> \<le> real(card \<S>) + card \<R> + k powr (19/20)"
      by (simp add: \<open>\<S>\<S> \<subseteq> \<S>\<close> card_mono)
    finally have "(card \<S> - k powr (19/20)) / bigbeta \<mu> l k \<le> real (card \<S>) + card \<R> + k powr (19/20)" .
    then have "card \<S> - k powr (19/20) \<le> (real (card \<S>) + card \<R> + k powr (19/20)) * bigbeta \<mu> l k"
      using bigbeta_gt0 by (simp add: field_simps)
    then have "card \<S> * (1 - bigbeta \<mu> l k) \<le> bigbeta \<mu> l k * card \<R> + (1 + bigbeta \<mu> l k) * k powr (19/20)"
      by (simp add: algebra_simps)
    then have "card \<S> \<le> (bigbeta \<mu> l k * card \<R> + (1 + bigbeta \<mu> l k) * k powr (19/20)) / (1 - bigbeta \<mu> l k)"
      using bigbeta_lt1 by (simp add: field_simps)
    also have "\<dots> = (bigbeta \<mu> l k / (1 - bigbeta \<mu> l k)) * card \<R> 
                  + ((1 + bigbeta \<mu> l k) / (1 - bigbeta \<mu> l k)) * k powr (19/20)"
      using bigbeta_gt0 bigbeta_lt1 by (simp add: divide_simps)
    also have "\<dots> \<le> (bigbeta \<mu> l k / (1 - bigbeta \<mu> l k)) * card \<R> + (2 / (1-\<mu>)) * k powr (19/20)"
      using \<mu> bb_le by (intro add_mono order_refl mult_right_mono frac_le) auto
    finally show ?thesis .
  qed
qed

subsection \<open>Lemma 8.6\<close>

text \<open>For some reason this was harder than it should have been.
      It does require a further small limit argument.\<close>

definition "Big_ZZ_8_6 \<equiv>     
   \<lambda>\<mu> l. Big_ZZ_8_5 \<mu> l \<and> (\<forall>k\<ge>l. 2 / (1-\<mu>) * k powr (19/20) < k powr (39/40))"

lemma Big_ZZ_8_6:
  assumes "0<\<mu>0" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. \<mu> \<in> {\<mu>0..\<mu>1} \<longrightarrow> Big_ZZ_8_6 \<mu> l"
  using assms Big_ZZ_8_5
  unfolding Big_ZZ_8_6_def
  apply (simp add: eventually_conj_iff all_imp_conj_distrib)  
  apply (intro conjI strip eventually_all_ge_at_top eventually_all_geI1 [where L=1])   
   apply real_asymp
  apply (auto simp: )
  by (smt (verit, best) frac_le powr_ge_pzero)

lemma (in Book) ZZ_8_6:
  assumes \<mu>: "0<\<mu>" "\<mu><1" and "Colours l k" and big: "Big_ZZ_8_6 \<mu> l" 
  defines "\<R> \<equiv> Step_class \<mu> l k {red_step}" and "\<S> \<equiv> Step_class \<mu> l k {dboost_step}"
    and "a \<equiv> 2 / (1-\<mu>)"
  assumes s_ge: "card \<S> \<ge> k powr (39/40)"
  shows "bigbeta \<mu> l k \<ge> (1 - a * k powr (-1/40)) * (card \<S> / (card \<S> + card \<R>))"
proof -
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  have bigbeta_lt1: "bigbeta \<mu> l k < 1" and bigbeta_gt0: "0 < bigbeta \<mu> l k"
    using bigbeta_ge0 big \<mu> \<open>Colours l k\<close> 
    by (auto simp: Big_ZZ_8_6_def Big_ZZ_8_5_def bigbeta_less1 bigbeta_gt0 \<S>_def)
  have "a > 0"
    using \<mu> by (simp add: a_def)
  have s_gt_a: "a * k powr (19/20) < card \<S>"
        and 85: "card \<S> \<le> (bigbeta \<mu> l k / (1 - bigbeta \<mu> l k)) * card \<R> + a * k powr (19/20)"
    using big \<open>k\<ge>l\<close> assms
    unfolding \<R>_def \<S>_def a_def Big_ZZ_8_6_def by (fastforce intro: ZZ_8_5)+
  then have t_non0: "card \<R> \<noteq> 0"   \<comment> \<open>seemingly not provable without our assumption\<close>
    using mult_eq_0_iff by fastforce
  then have "(card \<S> - a * k powr (19/20)) / card \<R> \<le> bigbeta \<mu> l k / (1 - bigbeta \<mu> l k)"
    using 85 bigbeta_gt0 bigbeta_lt1 t_non0 by (simp add: pos_divide_le_eq)
  then have "bigbeta \<mu> l k \<ge> (1 - bigbeta \<mu> l k) * (card \<S> - a * k powr (19/20)) / card \<R>"
    by (smt (verit, ccfv_threshold) bigbeta_lt1 mult.commute le_divide_eq times_divide_eq_left)
  then have *: "bigbeta \<mu> l k * (card \<R> + card \<S> - a * k powr (19/20)) \<ge> card \<S> - a * k powr (19/20)"
    using t_non0 by (simp add: field_simps)
  have "(1 - a * k powr - (1/40)) * card \<S> \<le> card \<S> - a * k powr (19/20)"
    using s_ge \<open>k>0\<close> \<open>a>0\<close> t_non0 by (simp add: powr_minus field_simps flip: powr_add)
  then have "(1 - a * k powr (-1/40)) * (card \<S> / (card \<S> + card \<R>)) 
          \<le> (card \<S> - a * k powr (19/20)) / (card \<S> + card \<R>)"
    by (force simp: divide_right_mono)
  also have "\<dots> \<le> (card \<S> - a * k powr (19/20)) / (card \<R> + card \<S> - a * k powr (19/20))"
    using s_gt_a \<open>a>0\<close> t_non0 by (intro divide_left_mono) auto
  also have "\<dots> \<le> bigbeta \<mu> l k"
    using * s_gt_a
    by (simp add: divide_simps split: if_split_asm)
  finally show ?thesis .
qed

end
