section \<open>An exponential improvement closer to the diagonal\<close>

theory Closer_To_Diagonal
  imports Far_From_Diagonal

begin

subsection \<open>Lemma 10.2\<close>


context P0_min
begin

lemma error_10_2:
  assumes "\<mu> / real d > 1/200"
  shows "\<forall>\<^sup>\<infinity>k. ok_fun_95b k + \<mu> * real k / real d \<ge> k/200"
proof -
  have "d>0" "\<mu>>0"
    using assms  by (auto simp: divide_simps split: if_split_asm)
  then have *: "real k \<le> \<mu> * (real k * 200) / real d" for k
    using assms by (fastforce simp add: divide_simps less_eq_real_def)
  have "\<forall>\<^sup>\<infinity>k. \<bar>ok_fun_95b k\<bar> \<le> (\<mu>/d - 1/200) * k"
    using ok_fun_95b assms unfolding smallo_def
    by (auto dest!: spec [where x = "\<mu>/d"])
  then show ?thesis
    apply eventually_elim
    using assms \<open>d>0\<close> *
    by (simp add: algebra_simps not_less abs_if add_increasing split: if_split_asm)
qed

text \<open>The "sufficiently large" assumptions are problematical.
  The proof's calculation for @{term "\<gamma> > 3/20"} is sharp. 
  We need a finite gap for the limit to exist.  We can get away with 1/300.\<close>
definition x320::real where "x320 \<equiv> 3/20 + 1/300"

lemma error_10_2_True: "\<forall>\<^sup>\<infinity>k. ok_fun_95b k + x320 * real k / real 30 \<ge> k/200"
  unfolding x320_def
  by (intro error_10_2) auto

lemma error_10_2_False: "\<forall>\<^sup>\<infinity>k. ok_fun_95b k + (1/10) * real k / real 15 \<ge> k/200"
  by (intro error_10_2) auto

definition "Big_Closer_10_2 \<equiv> \<lambda>\<mu> l. Big_Far_9_3 \<mu> l \<and> Big_Far_9_5 \<mu> l
                \<and> (\<forall>k\<ge>l. ok_fun_95b k + (if \<mu> > x320 then \<mu>*k/30 else \<mu>*k/15) \<ge> k/200)"

lemma Big_Closer_10_2:
  assumes "1/10\<le>\<mu>1" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. 1/10 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> Big_Closer_10_2 \<mu> l"
proof -
  have T: "\<forall>\<^sup>\<infinity>l. \<forall>k\<ge>l. (\<forall>\<mu>. x320 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> k/200 \<le> ok_fun_95b k + \<mu>*k / real 30)"
    using assms 
    apply (intro eventually_all_ge_at_top eventually_all_geI0 error_10_2_True)
    apply (auto simp: mult_right_mono elim!: order_trans)
    done
  have F: "\<forall>\<^sup>\<infinity>l. \<forall>k\<ge>l. (\<forall>\<mu>. 1/10 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> k/200 \<le> ok_fun_95b k + \<mu>*k / real 15)"
    using assms 
    apply (intro eventually_all_ge_at_top eventually_all_geI0 error_10_2_False)
    using less_eq_real_def apply (fastforce elim!: order_trans)
    done
  have "\<forall>\<^sup>\<infinity>l. \<forall>k\<ge>l. (\<forall>\<mu>. 1/10 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> k/200 \<le> ok_fun_95b k + (if \<mu> > x320 then \<mu>*k/30 else \<mu>*k/15))"
    using assms
    apply (split if_split)
    unfolding eventually_conj_iff all_imp_conj_distrib all_conj_distrib 
    by (force intro:  eventually_mono [OF T] eventually_mono [OF F])
  then show ?thesis
    using assms Big_Far_9_3[of "1/10"] Big_Far_9_5[of "1/10"]
    unfolding Big_Closer_10_2_def eventually_conj_iff all_imp_conj_distrib 
    by (force simp add: elim!: eventually_mono)
qed

end (*context P0_min*)

text \<open>A little tricky to express since my "Colours" assumption includes the allowed 
    assumption that there are no cliques in the original graph (page 10). So it's a contrapositive\<close>
lemma (in Book) Closer_10_2_aux:
  fixes l k
  fixes \<gamma>::real
  defines "\<gamma> \<equiv> l / (real k + real l)"
  assumes 0: "real (card X0) \<ge> nV/2" "card Y0 \<ge> nV div 2" "p0 \<ge> 1-\<gamma>"
     \<comment>\<open>These are the assumptions about the red density of the graph\<close>
  assumes "Colours l k" and \<gamma>: "1/10 \<le> \<gamma>" "\<gamma> \<le> 1/5"
  assumes nV: "real nV \<ge> exp (-k/200) * (k+l choose l)" 
  assumes big: "Big_Closer_10_2 \<gamma> l"
  shows False
proof -
  define \<R> where "\<R> \<equiv> Step_class \<gamma> l k {red_step}"
  define t where "t \<equiv> card \<R>"
  define m where "m \<equiv> halted_point \<gamma> l k"
  define \<delta>::real where "\<delta> \<equiv> 1/200"
  obtain lk: "0<l" "l\<le>k" "0<k"
    using \<open>Colours l k\<close> by (meson Colours_def Colours_kn0 Colours_ln0)
  have \<gamma>01: "0 < \<gamma>" "\<gamma> < 1"
    using lk by (auto simp: \<gamma>_def)
  have "t<k"
    unfolding t_def \<R>_def using \<gamma>01 \<open>Colours l k\<close> red_step_limit by blast
  have big93: "Big_Far_9_3 \<gamma> l" 
    using big by (auto simp: Big_Closer_10_2_def Big_Far_9_2_def)
  have t23: "t \<ge> 2*k / 3"
    unfolding t_def \<R>_def \<gamma>_def
  proof (rule Far_9_3)
    show "l / (real k + real l) \<le> 1/5"
      using \<gamma> unfolding \<gamma>_def by linarith
    have "min (1/200) (l / (real k + real l) / 20) = 1/200"
       using \<gamma> \<open>0<l\<close> by (simp add: \<gamma>_def)
    then show "exp (- min (1/200) (l / (real k + real l) / 20) * real k) * real (k + l choose l) \<le> nV"
      using nV by (metis divide_real_def inverse_eq_divide minus_mult_right mult.commute)
    show "1/4 \<le> p0"
      using \<gamma> 0 by linarith
    show "Big_Far_9_3 (l / (real k + real l)) l"
      using \<gamma>_def big93 by blast
  qed (use assms in auto)

  have "card (Yseq \<gamma> l k m) \<ge> 
               exp (-\<delta> * k + ok_fun_95b k) * (1-\<gamma>) powr (\<gamma>*t / (1-\<gamma>)) * ((1-\<gamma>)/(1-\<gamma>))^t 
             * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) * (k-t+l choose l)"
    unfolding \<gamma>_def m_def 
  proof (rule order_trans [OF _ Far_9_5])
    show "exp (-\<delta> * k) * real (k + l choose l) \<le> real nV"
      using nV by (auto simp: \<delta>_def)
    show "1 / 2 \<le> 1 - l / (k + real l) - 0"
      using divide_le_eq_1 \<open>l\<le>k\<close> by fastforce
  next
    show "Big_Far_9_5 (l / (k + real l)) l"
      using big by (simp add: Big_Closer_10_2_def Big_Far_9_2_def \<gamma>_def)
  qed (use 0 \<open>k>0\<close> \<open>Colours l k\<close> in \<open>auto simp flip: t_def \<gamma>_def \<R>_def\<close>)
  then have 52: "card (Yseq \<gamma> l k m) \<ge> 
               exp (-\<delta> * k + ok_fun_95b k) * (1-\<gamma>) powr (\<gamma>*t / (1-\<gamma>)) * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) * (k-t+l choose l)"
    using \<gamma> by simp

  define gamf where "gamf \<equiv> \<lambda>x::real. (1-x) powr (1/(1-x))"
  have deriv_gamf: "\<exists>y. DERIV gamf x :> y \<and> y \<le> 0" if "0<a" "a\<le>x" "x\<le>b" "b<1" for a b x
    unfolding gamf_def
    apply (rule exI conjI DERIV_powr derivative_eq_intros | use that in force)+
    by (smt (verit, del_insts) divide_le_0_iff ln_one_minus_pos_upper_bound mult_le_0_iff powr_ge_pzero that)

  have "(1-\<gamma>) powr (\<gamma>*t / (1-\<gamma>)) * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) \<ge> exp (\<delta>*k - ok_fun_95b k)"
  proof (cases "\<gamma> > x320")
    case True
    then have "ok_fun_95b k + \<gamma>*k / 30 \<ge> k/200"
      using big \<open>k\<ge>l\<close> by (auto simp: Big_Closer_10_2_def Big_Far_9_2_def)
    with True \<open>k>0\<close> have "\<delta> * k - ok_fun_95b k \<le> (\<gamma>/30) * k"
      by (simp add: \<delta>_def)
    also have "\<dots> \<le> 3 * \<gamma> * (real t)\<^sup>2 / (40*k)"
      using True mult_right_mono [OF mult_mono [OF t23 t23], of "3*\<gamma> / (40*k)"] \<open>k>0\<close> 
      by (simp add: power2_eq_square x320_def)
    finally have \<dagger>: "\<delta>*k - ok_fun_95b k \<le> 3 * \<gamma> * (real t)\<^sup>2 / (40*k)" .

    have "gamf \<gamma> \<ge> gamf (1/5)"
      by (smt (verit, best) DERIV_nonpos_imp_nonincreasing[of \<gamma> "1/5" gamf] \<gamma> \<gamma>01 deriv_gamf divide_less_eq_1)
    moreover have "ln (gamf (1/5)) \<ge> -1/3 + 1/20"
      unfolding gamf_def by (approximation 10)
    moreover have "gamf (1/5) > 0"
      by (simp add: gamf_def)
    ultimately have "gamf \<gamma> \<ge> exp (-1/3 + 1/20)"
      using ln_ge_iff by auto
    from powr_mono2 [OF _ _ this]
    have "(1-\<gamma>) powr (\<gamma>*t / (1-\<gamma>)) \<ge> exp (-17/60) powr (\<gamma>*t)"
      unfolding gamf_def using \<gamma>01 powr_powr by fastforce
    from mult_left_mono [OF this, of "exp (\<gamma> * (real t)\<^sup>2 / (2*k))"]
    have "(1-\<gamma>) powr (\<gamma>*t / (1-\<gamma>)) * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) \<ge> exp (-17/60 * (\<gamma>*t) + (\<gamma> * (real t)\<^sup>2 / (2*k)))"
      by (smt (verit) mult.commute exp_add exp_ge_zero exp_powr_real)
    moreover have "(-17/60 * (\<gamma>*t) + (\<gamma> * (real t)\<^sup>2 / (2*k))) \<ge> (3*\<gamma> * (real t)\<^sup>2 / (40*k))"
      using t23 \<open>k>0\<close> \<open>\<gamma>>0\<close> by (simp add: divide_simps eval_nat_numeral)
    ultimately have "(1-\<gamma>) powr (\<gamma>*t / (1-\<gamma>)) * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) \<ge> exp (3*\<gamma> * (real t)\<^sup>2 / (40*k))"
      by (smt (verit) exp_mono)
    with \<dagger> show ?thesis
      by (smt (verit, best) exp_le_cancel_iff)
  next
    case False
    then have "ok_fun_95b k + \<gamma>*k/15 \<ge> k/200"
      using big \<open>k\<ge>l\<close> by (auto simp: Big_Closer_10_2_def Big_Far_9_2_def)
    with \<open>k>0\<close> have "\<delta> * k - ok_fun_95b k \<le> (\<gamma>/15) * k"
      by (simp add: \<delta>_def x320_def)    
    also have "\<dots> \<le> 3 * \<gamma> * (real t)\<^sup>2 / (20*k)"
      using \<gamma> mult_right_mono [OF mult_mono [OF t23 t23], of "3*\<gamma> / (40*k)"] \<open>k>0\<close>
      by (simp add: power2_eq_square field_simps)
    finally have \<dagger>: "\<delta>*k - ok_fun_95b k \<le> 3 * \<gamma> * (real t)\<^sup>2 / (20*k)" .

    have "gamf \<gamma> \<ge> gamf x320"
      using False \<gamma>
      by (intro DERIV_nonpos_imp_nonincreasing[of \<gamma> "x320" gamf] deriv_gamf)
         (auto simp: x320_def)
    moreover have "ln (gamf x320) \<ge> -1/3 + 1/10"
      unfolding gamf_def x320_def by (approximation 6)
    moreover have "gamf x320 > 0"
      by (simp add: gamf_def x320_def)
    ultimately have "gamf \<gamma> \<ge> exp (-1/3 + 1/10)"
      using ln_ge_iff by auto
    from powr_mono2 [OF _ _ this]
    have "(1-\<gamma>) powr (\<gamma>*t / (1-\<gamma>)) \<ge> exp (-7/30) powr (\<gamma>*t)"
      unfolding gamf_def using \<gamma>01 powr_powr by fastforce
    from mult_left_mono [OF this, of "exp (\<gamma> * (real t)\<^sup>2 / (2*k))"]
    have "(1-\<gamma>) powr (\<gamma>*t / (1-\<gamma>)) * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) \<ge> exp (-7/30 * (\<gamma>*t) + (\<gamma> * (real t)\<^sup>2 / (2*k)))"
      by (smt (verit) mult.commute exp_add exp_ge_zero exp_powr_real)
    moreover have "(-7/30 * (\<gamma>*t) + (\<gamma> * (real t)\<^sup>2 / (2*k))) \<ge> (3*\<gamma> * (real t)\<^sup>2 / (20*k))"
      using t23 \<open>k>0\<close> \<open>\<gamma>>0\<close> by (simp add: divide_simps eval_nat_numeral)
    ultimately have "(1-\<gamma>) powr (\<gamma>*t / (1-\<gamma>)) * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) \<ge> exp (3*\<gamma> * (real t)\<^sup>2 / (20*k))"
      by (smt (verit) exp_mono)
    with \<dagger> show ?thesis
      by (smt (verit, best) exp_le_cancel_iff)
  qed
  then have "1 \<le> exp (-\<delta>*k + ok_fun_95b k) * (1 - \<gamma>) powr (\<gamma> * real t / (1 - \<gamma>)) * exp (\<gamma> * (real t)\<^sup>2 / real (2 * k))"
    by (simp add: exp_add exp_diff mult_ac pos_divide_le_eq)
  then have "(k-t+l choose l) \<le>
        exp (-\<delta> * k + ok_fun_95b k) * (1-\<gamma>) powr (\<gamma>*t / (1-\<gamma>)) * exp (\<gamma> * (real t)\<^sup>2 / (2*k)) * (k-t+l choose l)"
    by auto
  with 52 have "(k-t+l choose l) \<le> card (Yseq \<gamma> l k m)" by linarith
  then show False
    using Far_9_2_conclusion [OF \<open>Colours l k\<close> \<gamma>01] by (simp flip: \<R>_def m_def t_def)
qed


text \<open>Needs to be proved OUTSIDE THE BOOK LOCALE\<close>
lemma (in Book_Basis) Closer_10_2:
  fixes Red Blue :: "'a set set"
  fixes l k
  fixes \<gamma>::real
  defines "\<gamma> \<equiv> l / (real k + real l)"
  assumes complete: "E = all_edges V"
  assumes Red_E: "Red \<subseteq> E"
  assumes Blue_def: "Blue = E-Red"
  assumes infinite_UNIV: "infinite (UNIV::'a set)"
  assumes nV: "real nV \<ge> exp (-k/200) * (k+l choose l)" 
  assumes gd: "graph_density Red \<ge> 1-\<gamma>" 
    and p0_min_OK: "p0_min \<le> 1-\<gamma>"  
  assumes big: "Big_Closer_10_2 \<gamma> l" and "l\<le>k"
  assumes \<gamma>: "1/10 \<le> \<gamma>" "\<gamma> \<le> 1/5"
  shows "(\<exists>K. size_clique k K Red) \<or> (\<exists>K. size_clique l K Blue)"
proof (rule ccontr)
  assume neg: "\<not> ((\<exists>K. size_clique k K Red) \<or> (\<exists>K. size_clique l K Blue))"
  then obtain X0 Y0 where "l\<ge>2" and card_X0: "card X0 \<ge> nV/2" 
    and card_Y0: "card Y0 = gorder div 2" 
    and X0_def: "X0 = V \<setminus> Y0" and "Y0\<subseteq>V" 
    and gd_le: "graph_density Red \<le> gen_density Red Y0 (V\<setminus>Y0)"
    and "Book V E p0_min Red Blue X0 Y0" 
    by (smt (verit, ccfv_SIG) Basis_imp_Book assms p0_min)
  then interpret Book V E p0_min Red Blue X0 Y0
    by blast 
  have "Colours l k"
    using neg \<open>l\<le>k\<close> by (auto simp: Colours_def)
  show False
  proof (intro Closer_10_2_aux [of l k])
    show "1 - real l / (real k + real l) \<le> p0"
      using X0_def \<gamma>_def gd gd_le gen_density_commute p0_def by auto
  qed (use assms card_X0 card_Y0 \<open>Colours l k\<close> in auto)
qed

subsection \<open>Lemma 10.1\<close>

context P0_min
begin

lemma Big_10_imp_Big_9:
  assumes big: "Big_Closer_10_2 \<mu> l" and \<mu>: "0 < \<mu>" "\<mu> \<le> 1/10"
  shows "Big_Far_9_2 \<mu> l"
  unfolding Big_Far_9_2_def
proof (intro conjI strip)
  show "Big_Far_9_3 \<mu> l" "Big_Far_9_5 \<mu> l"
    using Big_Closer_10_2_def big by presburger+
next
  fix k :: nat
  assume "l \<le> k"
  have \<section>: "\<mu>/15 - 1/200 \<le> \<mu>/60"
    using \<mu> by simp
  have "\<mu> \<le> x320"
    using assms by (auto simp: x320_def)
  with \<open>l\<le>k\<close> have "real k/200 \<le> ok_fun_95b k + \<mu> * k/15"
    using big by (auto simp: Big_Closer_10_2_def)
  moreover
  have "\<mu> * k/15 - k/200 \<le> \<mu> * k/60"
    using mult_right_mono [OF \<section>, of k] 
    unfolding left_diff_distrib by linarith
  ultimately show "0 \<le> ok_fun_95b k + \<mu> * k/60"
    by linarith
qed

(*MAYBE NO NEED TO DEFINE THIS*)
definition "Big_Closer_10_1 \<equiv> \<lambda>\<mu> l. Big_Closer_10_2 \<mu> l" 

lemma Big_Closer_10_1:
  assumes "1/10\<le>\<mu>1" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. 1/10 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> Big_Closer_10_1 \<mu> l"
  using assms 
  unfolding Big_Closer_10_1_def eventually_conj_iff all_imp_conj_distrib eps_def
  using Big_Closer_10_2 by blast

lemma Closer_10_1:
  fixes l k::nat
  fixes \<delta> \<gamma>::real
  defines "\<gamma> \<equiv> real l / (real k + real l)"
  defines "\<delta> \<equiv> \<gamma>/40"
  assumes \<gamma>: "\<gamma> \<le> 1/5" 
  assumes big: "\<forall>l'. real l' \<ge> (10/11) * \<gamma> * l \<longrightarrow> (\<forall>\<mu>. \<gamma>\<^sup>2 \<le> \<mu> \<and> \<mu> \<le> 1/5 \<longrightarrow> Big_Closer_10_1 \<mu> l')"
  assumes p0_min_91: "p0_min \<le> 1 - (1/10) * (1 + 1/15)"
  shows "RN k l \<le> exp (-\<delta>*k + 1) * (k+l choose l)"
proof (rule ccontr)
  assume non: "\<not> RN k l \<le> exp (-\<delta> * k + 1) * (k+l choose l)"
  with RN_eq_0_iff have "l>0" by force
  have l4k: "4*l \<le> k"
    using \<open>l>0\<close> \<gamma> by (auto simp: \<gamma>_def divide_simps)
  have "l\<le>k"
    using \<gamma>_def \<gamma> nat_le_real_less by fastforce
  with \<open>l>0\<close> have "k>0" by linarith
  have ln1: False if "l = 1"
    using non \<open>k>0\<close> by (simp add: that \<gamma>_def \<delta>_def mult_le_1_iff)
  with \<open>l>0\<close> have "l\<ge>2"
    by force
  show False
  proof (cases "\<gamma> \<le> 1/10")
    case True
    have "\<gamma>>0"
      using \<open>0 < l\<close> \<gamma>_def by auto
    have "RN k l \<le> exp (-\<delta>*k + 1) * (k+l choose l)"
    proof (intro order.trans [OF Far_9_1] strip)
      fix l' \<mu> 
      assume l': "10 / 11 * (l / (k + real l)) * l \<le> real l'"
        and tenth: "(l / (k + real l))\<^sup>2 \<le> \<mu> \<and> \<mu> \<le> 1/10"
      then have "\<gamma>\<^sup>2 \<le> \<mu> \<and> \<mu> \<le> 1/5"
        by (simp add: \<gamma>_def)
      with l' big have "Big_Closer_10_2 \<mu> l'"
        by (auto simp: Big_Closer_10_1_def \<gamma>_def)
      then show "Big_Far_9_2 \<mu> l'"
        by (smt (verit, ccfv_threshold) Big_10_imp_Big_9 \<gamma>_def tenth \<open>0 < \<gamma>\<close> zero_less_power)
    next
      show "exp (- (l / (k + real l) / 20) * k + 1) * (k + l choose l) \<le> exp (-\<delta>*k + 1) * (k + l choose l)"
        by (smt (verit, best) \<open>0 < \<gamma>\<close> \<gamma>_def \<delta>_def exp_mono frac_le mult_right_mono of_nat_0_le_iff)
    qed (use p0_min_91 True \<gamma>_def in auto)
    then show False
      using non by blast
  next
    case False
      \<comment> \<open>unfortunately, a considerable overlap with the proof of 9.2\<close>
    define U_lower_bound_ratio where 
      "U_lower_bound_ratio \<equiv> \<lambda>m. (\<Prod>i<m. (l - real i) / (k+l - real i))"
    define n where "n \<equiv> nat\<lceil>RN k l / exp 1\<rceil>"
    have "n < RN k l"
      using RN_divide_e_less \<open>2 \<le> l\<close> \<open>l \<le> k\<close> n_def by force

    have "(k+l choose l) / exp (-1 + \<delta>*k) < real (RN k l)"
      by (smt (verit) divide_inverse exp_minus mult_minus_left mult_of_nat_commute non)
    then have "(RN k l / exp 1) * exp (\<delta>*k) > ((k+l) choose l)"
      unfolding exp_add exp_minus by (simp add: field_simps)
    then have nexp_gt: "n * exp (\<delta>*k) > ((k+l) choose l)"
      by (metis less_le_trans exp_ge_zero mult_right_mono n_def real_nat_ceiling_ge)

    define V where "V \<equiv> {..<n}"
    define E where "E \<equiv> all_edges V" 
    interpret Book_Basis V E
    proof
      show "\<And>e. e \<in> E \<Longrightarrow> e \<subseteq> V"
        by (simp add: E_def comp_sgraph.wellformed)
      show "\<And>e. e \<in> E \<Longrightarrow> card e = 2"
        by (simp add: E_def comp_sgraph.two_edges)
    qed (use p0_min_91 V_def E_def in auto)
    have [simp]: "nV = n"
      by (simp add: V_def)
    then obtain Red Blue
      where Red_E: "Red \<subseteq> E" and Blue_def: "Blue = E-Red" 
        and no_Red_K: "\<not> (\<exists>K. size_clique k K Red)"
        and no_Blue_K: "\<not> (\<exists>K. size_clique l K Blue)"
      by (metis \<open>n < RN k l\<close> less_RN_Red_Blue)
    have Blue_E: "Blue \<subseteq> E" and disjnt_Red_Blue: "disjnt Red Blue" and Blue_eq: "Blue = all_edges V - Red"
      using complete by (auto simp: Blue_def disjnt_iff E_def) 
    define is_good_clique where
      "is_good_clique \<equiv> \<lambda>i K. clique K Blue \<and> K \<subseteq> V \<and>
                                   card (V \<inter> (\<Inter>w\<in>K. Neighbours Blue w))
                                  \<ge> real i * U_lower_bound_ratio (card K) - card K"
    have is_good_card: "card K < l" if "is_good_clique i K" for i K
      using no_Blue_K that
      unfolding is_good_clique_def 
      by (metis nat_neq_iff size_clique_def size_clique_smaller)
    define GC where "GC \<equiv> {C. is_good_clique n C}"
    have "GC \<noteq> {}"
      by (auto simp: GC_def is_good_clique_def U_lower_bound_ratio_def E_def V_def)
    have "GC \<subseteq> Pow V"
      by (auto simp: is_good_clique_def GC_def)
    then have "finite GC"
      by (simp add: finV finite_subset)
    then obtain W where "W \<in> GC" and MaxW: "Max (card ` GC) = card W"
      using \<open>GC \<noteq> {}\<close> obtains_MAX by blast
    then have 53: "is_good_clique n W"
      using GC_def by blast
    have max53: "\<not> is_good_clique n (insert x W)" if "x\<in>V\<setminus>W" for x
    proof 
      assume x: "is_good_clique n (insert x W)"
      then have "card (insert x W) = Suc (card W)"
        using finV is_good_clique_def finite_subset that by fastforce
      with x \<open>finite GC\<close> have "Max (card ` GC) \<ge> Suc (card W)"
        by (simp add: GC_def rev_image_eqI)
      then show False
        by (simp add: MaxW)
    qed
    have "W\<subseteq>V"
      using 53 by (auto simp: is_good_clique_def)
    define m where "m \<equiv> card W"
    define \<gamma>' where "\<gamma>' \<equiv> (l - real m) / (k+l-real m)"

    have Red_Blue_RN: "\<exists>K \<subseteq> X. size_clique m K Red \<or> size_clique n K Blue"
      if "card X \<ge> RN m n" "X\<subseteq>V" for m n and X 
      using partn_lst_imp_is_clique_RN [OF is_Ramsey_number_RN [of m n]] finV that  
      unfolding is_clique_RN_def size_clique_def clique_indep_def Blue_eq 
      by (metis clique_iff_indep finite_subset subset_trans)
    define U where "U \<equiv> V \<inter> (\<Inter>w\<in>W. Neighbours Blue w)"
    define EU where "EU \<equiv> E \<inter> Pow U"
    define RedU where "RedU \<equiv> Red \<inter> Pow U"
    define BlueU where "BlueU \<equiv> Blue \<inter> Pow U"

    have "RN k l > 0"
      by (metis RN_eq_0_iff gr0I \<open>k>0\<close> \<open>l>0\<close>)
    with \<open>n < RN k l\<close> have n_less: "n < (k+l choose l)"
      by (metis add.commute RN_commute RN_le_choose le_trans linorder_not_less)

    have "\<gamma>' > 0"
      using is_good_card [OF 53] by (simp add: \<gamma>'_def m_def)
    have "finite W"
      using \<open>W \<subseteq> V\<close> finV finite_subset by (auto simp: V_def)
    have "U \<subseteq> V"
      by (force simp: U_def)
    then have VUU: "V \<inter> U = U"
      by blast
    have "disjnt U W"
      using Blue_E not_own_Neighbour unfolding E_def V_def U_def disjnt_iff by blast
    have "m<l"
      using 53 is_good_card m_def by blast
    have "\<gamma>' \<le> 1"
      using \<open>m<l\<close> by (simp add: \<gamma>'_def divide_simps)

    have cardU: "n * U_lower_bound_ratio m \<le> m + card U"
      using 53 VUU unfolding is_good_clique_def m_def U_def by force

    obtain [iff]: "finite RedU" "finite BlueU" "RedU \<subseteq> EU"
      using BlueU_def EU_def RedU_def E_def V_def Red_E Blue_E fin_edges finite_subset  by blast 
    have card_RedU_le: "card RedU \<le> card EU"
      by (metis EU_def E_def \<open>RedU \<subseteq> EU\<close> card_mono fin_all_edges finite_Int)
    interpret UBB: Book_Basis U "E \<inter> Pow U" p0_min 
    proof
      fix e 
      assume "e \<in> E \<inter> Pow U"
      with two_edges show "e \<subseteq> U" "card e = 2" by auto
    next
      show "finite U"
        using \<open>U \<subseteq> V\<close> by (simp add: V_def finite_subset)
      have "x \<in> E" if "x \<in> all_edges U" for x 
        using \<open>U \<subseteq> V\<close> all_edges_mono that complete E_def by blast
      then show "E \<inter> Pow U = all_edges U"
        using comp_sgraph.wellformed \<open>U \<subseteq> V\<close> by (auto intro: e_in_all_edges_ss)
    qed auto

    have clique_W: "size_clique m W Blue"
      using 53 is_good_clique_def m_def size_clique_def V_def by blast

    have prod_gt0: "U_lower_bound_ratio m > 0"
      unfolding U_lower_bound_ratio_def using \<open>m<l\<close> by (intro prod_pos) auto
    have kl_choose: "real(k+l choose l) = (k+l-m choose (l-m)) / U_lower_bound_ratio m"
      unfolding U_lower_bound_ratio_def using kl_choose \<open>0 < k\<close> \<open>m < l\<close> by blast

    have "card U > 1"  \<comment>\<open>the proof used in 9.2 does not work, but maybe 9.4 helps\<close>
      sorry

    have card_EU: "card EU > 0"
      using \<open>card U > 1\<close> UBB.complete by (simp add: EU_def UBB.finV card_all_edges)
    have BlueU_eq: "BlueU = EU \<setminus> RedU" 
      using Blue_eq complete by (fastforce simp add: BlueU_def RedU_def EU_def V_def E_def)
    have [simp]: "UBB.graph_size = card EU"
      using EU_def by blast

\<comment> \<open>in both cases below, we find a blue key click of size @{term"l-m"}\<close>
    have extend_Blue_clique: "\<exists>K'. size_clique l K' Blue" 
      if "K \<subseteq> U" "size_clique (l-m) K Blue" for K
    proof -
      have K: "card K = l-m" "clique K Blue"
        using that by (auto simp: size_clique_def)
      define K' where "K' \<equiv> K \<union> W"
      have "card K' = l"
        unfolding K'_def
      proof (subst card_Un_disjnt)
        show "finite K" "finite W"
          using UBB.finV \<open>K \<subseteq> U\<close> finite_subset \<open>finite W\<close> by blast+
        show "disjnt K W"
          using \<open>disjnt U W\<close> \<open>K \<subseteq> U\<close> disjnt_subset1 by blast
        show "card K + card W = l"
          using K \<open>m < l\<close> m_def by auto
      qed
      moreover have "clique K' Blue"
        using \<open>clique K Blue\<close> clique_W \<open>K \<subseteq> U\<close>
        unfolding K'_def size_clique_def U_def 
        by (force simp: in_Neighbours_iff insert_commute intro: Ramsey.clique_Un)
      ultimately show ?thesis
        unfolding K'_def size_clique_def using \<open>K \<subseteq> U\<close> \<open>U \<subseteq> V\<close> \<open>W \<subseteq> V\<close> by auto
    qed

    show False
    proof (cases "\<gamma>' \<ge> 1/10")
      case True

      have False if "UBB.graph_density BlueU >  \<gamma>'"
      proof -    \<comment>\<open>by maximality, etc.\<close>

        have Nx: "Neighbours BlueU x \<inter> (U \<setminus> {x}) = Neighbours BlueU x" for x 
          using that by (auto simp: BlueU_eq EU_def Neighbours_def)

        have "BlueU \<subseteq> E \<inter> Pow U"
          using BlueU_eq EU_def by blast
        with UBB.exists_density_edge_density [of 1 BlueU]
        obtain x where "x\<in>U" and x: "UBB.graph_density BlueU \<le> UBB.gen_density BlueU {x} (U\<setminus>{x})"
          by (metis UBB.complete \<open>1 < UBB.gorder\<close> card_1_singletonE insertI1 zero_less_one subsetD)
        with that have "\<gamma>' \<le> UBB.gen_density BlueU (U\<setminus>{x}) {x}"
          using UBB.gen_density_commute by auto
        then have *: "\<gamma>' * (card U - 1) \<le> card (Neighbours BlueU x)"
          using \<open>BlueU \<subseteq> E \<inter> Pow U\<close> \<open>card U > 1\<close> \<open>x \<in> U\<close>
          by (simp add: UBB.gen_density_def UBB.edge_card_eq_sum_Neighbours UBB.finV divide_simps Nx)

        have x: "x \<in> V\<setminus>W"
          using \<open>x \<in> U\<close> \<open>U \<subseteq> V\<close> \<open>disjnt U W\<close> by (auto simp: U_def disjnt_iff)
        moreover
        have "is_good_clique n (insert x W)"
          unfolding is_good_clique_def
        proof (intro conjI)
          show "clique (insert x W) Blue"
          proof (intro clique_insert)
            show "clique W Blue"
              using 53 is_good_clique_def by blast
            show "all_edges_betw_un {x} W \<subseteq> Blue"
              using \<open>x\<in>U\<close> by (auto simp: U_def all_edges_betw_un_def insert_commute in_Neighbours_iff )
          qed (use \<open>W \<subseteq> V\<close> \<open>x \<in> V\<setminus>W\<close> in auto)
        next
          show "insert x W \<subseteq> V"
            using \<open>W \<subseteq> V\<close> \<open>x \<in> V\<setminus>W\<close> by auto
        next
          have NB_Int_U: "Neighbours Blue x \<inter> U = Neighbours BlueU x"
            using \<open>x \<in> U\<close> by (auto simp: BlueU_def U_def Neighbours_def)
          have ulb_ins: "U_lower_bound_ratio (card (insert x W)) = U_lower_bound_ratio m * \<gamma>'"
            using \<open>x \<in> V\<setminus>W\<close> \<open>finite W\<close> by (simp add: m_def U_lower_bound_ratio_def \<gamma>'_def)
          have "n * U_lower_bound_ratio (card (insert x W))  = n * U_lower_bound_ratio m * \<gamma>'"
            by (simp add: ulb_ins)
          also have "\<dots> \<le> real (m + card U) * \<gamma>'"
            using mult_right_mono [OF cardU, of "\<gamma>'"] \<open>0 < \<gamma>'\<close> by argo
          also have "\<dots> \<le> m + card U * \<gamma>'"
            using mult_left_mono [OF \<open>\<gamma>'\<le>1\<close>, of m] by (simp add: algebra_simps)
          also have "\<dots> \<le> Suc m + \<gamma>' * (UBB.gorder - Suc 0)"
            using * \<open>x \<in> V\<setminus>W\<close> \<open>finite W\<close> \<open>1 < UBB.gorder\<close> \<open>\<gamma>'\<le>1\<close>
            by (simp add: U_lower_bound_ratio_def algebra_simps)
          also have "\<dots> \<le> Suc m + card (V \<inter> \<Inter> (Neighbours Blue ` insert x W))"
            using * NB_Int_U finV by (simp add: U_def Int_ac)
          also have "\<dots> = real (card (insert x W) + card (V \<inter> \<Inter> (Neighbours Blue ` insert x W)))"
            using x \<open>finite W\<close> VUU by (auto simp: m_def U_def)
          finally show "n * U_lower_bound_ratio (card(insert x W)) - card(insert x W)
                   \<le> card (V \<inter> \<Inter> (Neighbours Blue ` insert x W))" 
            by simp
        qed
        ultimately show False
          using max53 by blast
      qed
      then have *: "UBB.graph_density BlueU \<le>  \<gamma>'" by force

      have YMK: "\<gamma>-\<gamma>' \<le> m/k"
        using \<open>l>0\<close> \<open>m<l\<close> 
        apply (simp add: \<gamma>_def \<gamma>'_def divide_simps)
        apply (simp add: algebra_simps)
        by (smt (verit, best) mult_left_mono mult_right_mono nat_less_real_le of_nat_0_le_iff)

      define \<delta>' where "\<delta>' \<equiv> \<gamma>'/40"
      have no_RedU_K: "\<not> (\<exists>K. UBB.size_clique k K RedU)"
        unfolding UBB.size_clique_def RedU_def
        by (metis Int_subset_iff  VUU all_edges_subset_iff_clique no_Red_K size_clique_def)
      have "(\<exists>K. UBB.size_clique k K RedU) \<or> (\<exists>K. UBB.size_clique (l-m) K BlueU)"
      proof (intro UBB.Closer_10_2)
        show "E \<inter> Pow U = all_edges U"
          by (simp add: UBB.complete)
        show "RedU \<subseteq> E \<inter> Pow U"
          using EU_def \<open>RedU \<subseteq> EU\<close> by auto
        show "BlueU = E \<inter> Pow U \<setminus> RedU"
          using BlueU_eq EU_def by fastforce

        have "exp (\<delta>*k) * exp (-\<delta>'*k) = exp (\<gamma>*k/40 - \<gamma>'*k/40)"
          unfolding \<delta>_def \<delta>'_def by (simp add: mult_exp_exp) 
        also have "\<dots> \<le> exp (m/40)"
          using YMK \<open>0 < k\<close> by (simp add: left_diff_distrib divide_simps)
        finally have expexp: "exp (\<delta>*k) * exp (-\<delta>'*k) \<le> exp (m/40)" .

        have "exp (-\<delta>'*k) * (k + (l-m) choose (l-m)) = exp (-\<delta>'*k) * U_lower_bound_ratio m * (k+l choose l)"
          using \<open>m < l\<close> klm_choose by force
        also have "\<dots> < n * exp (\<delta>*k) * exp (-\<delta>'*k) * U_lower_bound_ratio m"
          using nexp_gt prod_gt0 by auto 
        also have "\<dots> \<le> n * (1+\<xi>) ^ m * U_lower_bound_ratio m"
          using expexp less_eq_real_def prod_gt0 by fastforce
        also have "\<dots> = n * U_lower_bound_ratio m"
          by (simp add: U_lower_m)
        also have "\<dots> \<le> n * U_lower_bound_ratio m - m"  \<comment> \<open>stuck here: the "minus m"\<close>
          sorry
        finally have "exp (-\<delta>'*k) * (k + (l-m) choose (l-m)) \<le> real n * U_lower_bound_ratio m - m"
          by linarith 
        also have "\<dots> \<le> UBB.nV"
          using cardU by linarith
        finally have "exp (-\<delta>'*k) * (k + (l-m) choose (l-m)) \<le> UBB.nV" .
        then show "exp (- real k / 200) * (k + (l-m) choose (l-m)) \<le> UBB.nV"
          using \<open>m < l\<close> apply (simp add: \<delta>'_def \<gamma>'_def of_nat_diff)
          by argo
      next
        show "1 - real (l-m) / (real k + real (l-m)) - \<eta> \<le> UBB.graph_density RedU"
          using * \<open>\<gamma>' \<le> \<gamma>\<close> \<open>m < l\<close> unfolding \<gamma>_def \<gamma>'_def
          by (smt (verit) less_or_eq_imp_le of_nat_add of_nat_diff)
        have "p0_min \<le> 1 - (1/10) * (1+\<xi>)"
          using p0_min_91 by (auto simp: \<xi>_def)
        also have "\<dots> \<le> 1 - \<gamma> - \<eta>"
          using \<open>\<gamma>' \<le> \<gamma>\<close> \<gamma> by (auto simp: \<eta>_def \<xi>_def)
        also have "\<dots> \<le> 1 - (l-m) / (real k + real (l-m)) - \<eta>"
          using \<open>\<gamma>' \<le> \<gamma>\<close> \<open>m<l\<close> by (simp add: \<gamma>_def \<gamma>'_def of_nat_diff algebra_simps)
        finally show "p0_min \<le> 1 - (l-m) / (real k + real (l-m)) - \<eta>" .
      next
        have "Big_Closer_10_2 \<gamma>' (l-m)"
          using False big \<open>\<gamma>' \<le> \<gamma>\<close> \<gamma> \<open>m<l\<close> lm_bound unfolding Big_Far_9_2_def
          by (smt (verit, del_insts) less_imp_le of_nat_diff)
        then show "Big_Far_9_2 ((l-m) / (real k + real (l-m))) (l-m)"
          by (simp add: \<gamma>'_def \<open>m < l\<close> add_diff_eq less_or_eq_imp_le of_nat_diff)
        show "l-m \<le> k"
          using \<open>l \<le> k\<close> by auto
        show "(l-m) / (real k + real (l-m)) \<le> 1/10"
          using \<gamma> \<gamma>_def \<open>m < l\<close> by fastforce
        show "0 \<le> \<eta>"
          using \<open>0 < \<eta>\<close> by linarith
        show "\<eta> \<le> (l-m) / (real k + real (l-m)) / 15"
          using mult_right_mono [OF \<open>\<gamma>' \<le> \<gamma>\<close>, of \<xi>]
          by (simp add: \<eta>_def \<gamma>'_def \<open>m < l\<close> \<xi>_def add_diff_eq less_or_eq_imp_le mult.commute of_nat_diff)
      qed auto
      with no_RedU_K obtain K where "K \<subseteq> U" "UBB.size_clique (l-m) K BlueU"
        by (meson UBB.size_clique_def)
      then show False
        using no_Blue_K extend_Blue_clique VUU
        unfolding UBB.size_clique_def size_clique_def BlueU_def
        by (metis Int_subset_iff all_edges_subset_iff_clique) 


      then show False 
        using UBB.Closer_10_2
        sorry
    next
      case False
      then show False sorry
    qed
  qed
qed

end
