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

definition "Big_Far_10_2 \<equiv> \<lambda>\<mu> l. Big_Far_9_3 \<mu> l \<and> Big_Far_9_5 \<mu> l
                \<and> (\<forall>k\<ge>l. ok_fun_95b k + (if \<mu> > x320 then \<mu>*k/30 else \<mu>*k/15) \<ge> k/200)"

lemma Big_Far_10_2:
  assumes "1/10\<le>\<mu>1" "\<mu>1<1" 
  shows "\<forall>\<^sup>\<infinity>l. \<forall>\<mu>. 1/10 \<le> \<mu> \<and> \<mu> \<le> \<mu>1 \<longrightarrow> Big_Far_10_2 \<mu> l"
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
    unfolding Big_Far_10_2_def eventually_conj_iff all_imp_conj_distrib 
    by (force simp add: elim!: eventually_mono)
qed


text \<open>A little tricky to express since my "Colours" assumption includes the allowed 
    assumption that there are no cliques in the original graph (page 10). So it's a contrapositive\<close>
lemma (in Book) Far_10_2_aux:
  fixes l k
  fixes \<gamma>::real
  defines "\<gamma> \<equiv> l / (real k + real l)"
  assumes 0: "real (card X0) \<ge> nV/2" "card Y0 \<ge> nV div 2" "p0 \<ge> 1-\<gamma>"
     \<comment>\<open>These are the assumptions about the red density of the graph\<close>
  assumes "Colours l k" and \<gamma>: "1/10 \<le> \<gamma>" "\<gamma> \<le> 1/5"
  assumes nV: "real nV \<ge> exp (-k/200) * (k+l choose l)" 
  assumes big: "Big_Far_10_2 \<gamma> l"
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
    using big by (auto simp: Big_Far_10_2_def Big_Far_9_2_def)
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
    show "Big_Far_9_5 (real l / (real k + real l)) l"
      using big by (simp add: Big_Far_10_2_def Big_Far_9_2_def \<gamma>_def)
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
      using big \<open>k\<ge>l\<close> by (auto simp: Big_Far_10_2_def Big_Far_9_2_def)
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
    then have "ok_fun_95b k + \<gamma>*k / 15 \<ge> k/200"
      using big \<open>k\<ge>l\<close> by (auto simp: Big_Far_10_2_def Big_Far_9_2_def)
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

end
