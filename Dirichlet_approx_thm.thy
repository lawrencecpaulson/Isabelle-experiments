theory Dirichlet_approx_thm

imports "Complex_Main" "HOL-Library.FuncSet"

begin

chapter \<open>Dirichlet's Approximation Theorem\<close>

text \<open>Theorem 7.1\<close>

theorem Dirichlet_approx:
  fixes \<theta>::real and N::nat
  assumes "N > 0" 
  obtains h k where "0 < k" "k \<le> int N" "\<bar>of_int k*\<theta> - of_int h\<bar> < 1/N"
proof -
  have lessN: "nat \<lfloor>x * N\<rfloor> < N" if "0 \<le> x" "x < 1" for x::real
    using that assms floor_less_iff nat_less_iff by fastforce
  define X where "X \<equiv> (\<lambda>k. frac (k*\<theta>)) ` {..N}"
  define Y where "Y \<equiv> (\<lambda>k::nat. {k/N..< Suc k/N}) ` {..<N}"
  have False 
    if non: "\<not> (\<exists>b\<le>N. \<exists>a<b. \<bar>frac (real b * \<theta>) - frac (real a * \<theta>)\<bar> < 1/N)"
  proof -
    have "inj_on (\<lambda>k::nat. frac (k*\<theta>)) {..N}"
      using non by (intro linorder_inj_onI; force)
    then have caX: "card X = Suc N"
      by (simp add: X_def card_image)
    have caY: "card Y \<le> N" "finite Y"
      unfolding Y_def using card_image_le by force+
    define f where "f \<equiv> \<lambda>x::real. let k = nat \<lfloor>x * N\<rfloor> in {k/N ..< Suc k/N}"
    have "f \<in> X \<rightarrow> Y"
      by (force simp: f_def Let_def X_def Y_def frac_lt_1 intro!: lessN)
    then have "\<not> inj_on f X"
      using \<open>finite Y\<close> caX caY card_inj by fastforce
    then obtain x x' where "x\<noteq>x'" "x \<in> X" "x' \<in> X" and eq: "f x = f x'"
      by (auto simp: inj_on_def)
    then obtain c d::nat where c: "c \<noteq> d" "c \<le> N" "d \<le> N" 
            and xeq: "x = frac (c*\<theta>)" and xeq': "x' = frac (d*\<theta>)"
      by (metis (no_types, lifting) X_def atMost_iff image_iff)
    define i where "i \<equiv> nat \<lfloor>x * N\<rfloor>"
    then have i: "x \<in> {i/N ..< Suc i/N}" 
      using assms by (auto simp: divide_simps xeq) linarith
    have i': "x' \<in> {i/N ..< Suc i/N}" 
      using eq assms unfolding f_def Let_def xeq' i_def
      by (simp add:  divide_simps) linarith
    with assms i have "\<bar>frac (d*\<theta>) - frac (c*\<theta>)\<bar> < 1 / N"
      by (simp add: xeq xeq' abs_if add_divide_distrib)
    with c show False
      by (metis abs_minus_commute nat_neq_iff non)
  qed
  then obtain a b::nat where *: "a<b" "b\<le>N" "\<bar>frac (b*\<theta>) - frac (a*\<theta>)\<bar> < 1/N" 
    by metis
  let ?k = "b-a" and ?h = "\<lfloor>b*\<theta>\<rfloor> - \<lfloor>a*\<theta>\<rfloor>"
  show ?thesis
  proof
    have "frac (b*\<theta>) - frac (a*\<theta>) = ?k*\<theta> - ?h"
      using \<open>a < b\<close> by (simp add: frac_def left_diff_distrib')
    with * show "\<bar>of_int ?k*\<theta> - ?h\<bar> < 1 / N"
      by (metis of_int_of_nat_eq)
  qed (use * in auto)
qed


text \<open>Theorem 7.2\<close>
corollary Dirichlet_approx_coprime:
  fixes \<theta>:: real and N:: nat
  assumes "N > 0" 
  obtains h k where "coprime h k" "0 < k" "k \<le> int N" "\<bar>of_int k*\<theta> - of_int h\<bar> < 1/N"
proof -
  obtain h' k' where k': "0 < k'" "k' \<le> int N" 
    and *: "\<bar>of_int k'*\<theta> - of_int h'\<bar> < 1/N"
    by (meson Dirichlet_approx assms)
  let ?d = "gcd h' k'"
  show thesis
  proof (cases "?d = 1")
    case True
    with k' * that show ?thesis by auto
  next
    case False
    then have 1: "?d > 1"
      by (smt (verit, ccfv_threshold) \<open>k'>0\<close> gcd_pos_int)
    let ?k = "k' div ?d"
    let ?h = "h' div ?d"
    show ?thesis
    proof
      show "coprime (?h::int) ?k"
        by (metis "1" div_gcd_coprime gcd_eq_0_iff not_one_less_zero)
      show k0: "0 < ?k"
        using k'(1) pos_imp_zdiv_pos_iff by force
      show "?k \<le> int N"
        using k' "1" int_div_less_self by fastforce
      have "\<bar>\<theta> - of_int ?h / of_int ?k\<bar> = \<bar>\<theta> - of_int h' / of_int k'\<bar>"
        by (simp add: real_of_int_div)
      also have "\<dots> < 1 / of_int (N * k')"
        using k' * by (simp add: field_simps)
      also have "\<dots> < 1 / of_int (N * ?k)"
        using assms \<open>k'>0\<close> k0 1
        by (simp add: frac_less2 int_div_less_self)
      finally show "\<bar>of_int ?k*\<theta> - of_int ?h\<bar> < 1 / real N"
        using k0 k' by (simp add: field_simps)
    qed
  qed
qed

end