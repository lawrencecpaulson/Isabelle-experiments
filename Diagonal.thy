theory Diagonal imports
  "HOL-Library.Disjoint_Sets" "HOL-Library.Ramsey" "Undirected_Graph_Theory.Undirected_Graph_Basics" 
  "Special_Function_Bounds.Exp_Bounds" "HOL-Decision_Procs.Approximation" "HOL-Probability.Probability" 
  "HOL-Library.Infinite_Set"  "HOL-Library.Countable_Set"  "HOL-Library.Equipollence" 
  "HOL-Library.Nat_Bijection"
  "HOL-ex.Sketch_and_Explore"

   
begin

text \<open>useful for counting the number of edges containing a clique\<close>
lemma card_Pow_diff:
  assumes "A \<subseteq> B" "finite B"
  shows "card {X \<in> Pow B. A \<subseteq> X} = 2 ^ (card B - card A)"
proof -
  have inj: "inj_on ((\<union>) A) (Pow (B-A))"
    using assms by (auto simp: inj_on_def)
  have "{X \<in> Pow B. A \<subseteq> X} = (\<union>)A ` Pow (B-A)"
    using assms by auto
  moreover have "card \<dots> = 2 ^ (card B - card A)"
    using inj assms by (simp add: card_Diff_subset card_Pow card_image finite_subset)
  ultimately show ?thesis
    by presburger
qed

context linordered_semidom
begin

thm power_le_one_iff (*MOVE TO A BETTER PLACE AND GENERALISE THUS*)
lemma power_le_one_iff: "0 \<le> a \<Longrightarrow> a ^ n \<le> 1 \<longleftrightarrow> (n = 0 \<or> a \<le> 1)"
  by (metis (mono_tags) gr0I nle_le one_le_power power_le_one self_le_power power.power.power_0)

lemma power_less_one_iff: "0 \<le> a \<Longrightarrow> a ^ n < 1 \<longleftrightarrow> (n > 0 \<and> a < 1)" 
  by (smt (verit, best) neq0_conv neq_iff not_le one_le_power power.simps power_eq_0_iff power_strict_decreasing)

end

lemma powr_less_one: "0 \<le> (a::real) \<Longrightarrow> a < 1 \<Longrightarrow> e>0 \<Longrightarrow> a powr e < 1 "
  by (metis powr_less_mono2 powr_one_eq_one)


lemma exp_powr_real [simp]:
  fixes x::real shows "exp x powr y = exp (x*y)"
  by (simp add: powr_def)

lemma exp_minus_greater: 
  fixes x::real shows "1 - x < exp (-x) \<longleftrightarrow> x \<noteq> 0"
  by (smt (verit, best) exp_ge_add_one_self exp_gt_zero exp_zero ln_eq_minus_one ln_exp)


lemma exp_powr_complex [simp]:
  fixes x::complex 
  assumes "-pi < Im(x)" "Im(x) \<le> pi"
  shows "exp x powr y = exp (x*y)"
  using assms by (simp add: powr_def mult.commute)

thm choose_two
lemma choose_two_real: "n choose 2 = n * (n - 1) / 2"
proof (cases "even n")
  case True
  then show ?thesis
    by (auto simp add: choose_two dvd_def)
next
  case False
  then have "even (n-1)"
    by simp
  then show ?thesis
    by (auto simp add: choose_two dvd_def)
qed

definition "upair_define \<equiv> \<lambda>f e. THE u. \<exists>x y. e = {x,y} \<and> u = f x y"

lemma upair_define_apply:
  assumes "\<And>x y. f x y = f y x"
  shows "upair_define f {x,y} = f x y"
  using assms
  by (force simp add: upair_define_def doubleton_eq_iff)

lemma upair_define_apply_dom:
  assumes "\<And>x y. \<lbrakk>x\<in>A; y\<in>A\<rbrakk> \<Longrightarrow> f x y = f y x" "x\<in>A" "y\<in>A"
  shows "upair_define f {x,y} = f x y"
  using assms
  by (force simp add: upair_define_def doubleton_eq_iff)



thm powr_half_sqrt
lemma powr_half_sqrt_powr: "0 \<le> x \<Longrightarrow> x powr (a/2) = sqrt(x powr a)"
  by (metis divide_inverse mult.left_neutral powr_ge_pzero powr_half_sqrt powr_powr)

text \<open>derivatives of real powers\<close>
lemma has_derivative_powr [derivative_intros]:
  assumes "\<And>x. (f has_derivative f') (at x)" "\<And>x. (g has_derivative g') (at x)"
    "\<And>x. f x > (0::real)"
  shows "((\<lambda>x. f x powr g x) has_derivative (\<lambda>y. (g x * (f' y / f x) + g' y * ln (f x)) * (f x) powr (g x))) (at x)"
proof -
  have [simp]: "\<And>x. f x \<noteq> 0"
    by (smt (verit, best) assms(3))
  show ?thesis
  using assms
  apply (simp add: powr_def)
  apply (rule exI assms derivative_eq_intros refl)+
  apply (simp add: powr_def divide_inverse assms mult_ac)
  done
qed

lemma has_derivative_const_powr [derivative_intros]:
  assumes "\<And>x. (f has_derivative f') (at x)"
    "a \<noteq> (0::real)"
  shows "((\<lambda>x. a powr (f x)) has_derivative (\<lambda>y. f' y * ln a * a powr (f x))) (at x)"
  using assms
  apply (simp add: powr_def)
  apply (rule assms derivative_eq_intros refl)+
  done

lemma has_real_derivative_const_powr [derivative_intros]:
  assumes "\<And>x. (f has_real_derivative f' x) (at x)"
    "a \<noteq> (0::real)"
  shows "((\<lambda>x. a powr (f x)) has_real_derivative (f' x * ln a * a powr (f x))) (at x)"
  using assms
  apply (simp add: powr_def)
  apply (rule assms derivative_eq_intros refl | simp)+
  done

(*for Equipollence*)
text \<open>Dedekind's definition of infinite set\<close>
lemma infinite_iff_psubset: "infinite A \<longleftrightarrow> (\<exists>B. B \<subset> A \<and> A\<approx>B)"
proof
  assume "infinite A"
  then obtain f :: "nat \<Rightarrow> 'a" where "inj f" and f: "range f \<subseteq> A"
    by (meson infinite_countable_subset)
  define C where "C \<equiv> A - range f"
  have C: "A = range f \<union> C" "range f \<inter> C = {}"
    using f by (auto simp: C_def)
  have *: "range (f \<circ> Suc) \<subset> range f"
    using inj_eq [OF \<open>inj f\<close>] by (fastforce simp: set_eq_iff)
  have "range f \<union> C \<approx> range (f \<circ> Suc) \<union> C"
  proof (intro Un_eqpoll_cong)
    show "range f \<approx> range (f \<circ> Suc)"
      by (meson \<open>inj f\<close> eqpoll_refl inj_Suc inj_compose inj_on_image_eqpoll_2)
    show "disjnt (range f) C"
      by (simp add: C disjnt_def)
    then show "disjnt (range (f \<circ> Suc)) C"
      using "*" disjnt_subset1 by blast
  qed auto
  moreover have "range (f \<circ> Suc) \<union> C \<subset> A"
    using "*" f C_def by blast
  ultimately show "\<exists>B\<subset>A. A \<approx> B"
    by (metis C(1))
next
  assume "\<exists>B\<subset>A. A \<approx> B" then show "infinite A"
    by (metis card_subset_eq eqpoll_finite_iff eqpoll_iff_card psubsetE)
qed

lemma infinite_iff_psubset_le: "infinite A \<longleftrightarrow> (\<exists>B. B \<subset> A \<and> A \<lesssim> B)"
  by (meson eqpoll_imp_lepoll infinite_iff_psubset lepoll_antisym psubsetE subset_imp_lepoll)

(*Binomial*)
lemma binomial_mono:
  assumes "m \<le> n" shows "m choose k \<le> n choose k"
proof -
  have "{K. K \<subseteq> {0..<m} \<and> card K = k} \<subseteq> {K. K \<subseteq> {0..<n} \<and> card K = k}"
    using assms by auto
  then show ?thesis
    by (simp add: binomial_def card_mono)
qed

lemma gbinomial_is_prod: "(a gchoose k) = (\<Prod>i<k. (a - of_nat i) / (1 + of_nat i))"
  unfolding gbinomial_prod_rev
  by (induction k; simp add: divide_simps)

(*Ramsey*)
lemma finite_imp_finite_nsets: "finite A \<Longrightarrow> finite ([A]\<^bsup>k\<^esup>)"
  by (simp add: nsets_def)

lemma nsets2_E:
  assumes "e \<in> [A]\<^bsup>2\<^esup>"
  obtains x y where "e = {x,y}" "x \<in> A" "y \<in> A" "x\<noteq>y"
  using assms by (auto simp: nsets_def card_2_iff)

lemma subset_nsets_2:
  assumes "card A \<ge> 2" shows "A \<subseteq> \<Union>([A]\<^bsup>2\<^esup>)"
proof -
  obtain x y where "x \<in> A" "y \<in> A" "x\<noteq>y"
    using assms
    by (metis One_nat_def Suc_1 card.infinite card_le_Suc0_iff_eq nat_le_linear not_less_eq_eq)
  then show ?thesis
    by (auto simp: nsets_2_eq all_edges_def)
qed

lemma Pow_equals_UN_nsets:
  assumes "finite A" shows "Pow A = \<Union> (nsets A ` {..card A})"
  proof
    show "Pow A \<subseteq> \<Union> (nsets A ` {..card A})"
      using assms finite_subset by (force simp: nsets_def card_mono)
qed (auto simp: nsets_def)

lemma nsets_eq_iff:
  assumes "m \<le> card A" "n \<le> card A"
  shows "[A]\<^bsup>m\<^esup> = [A]\<^bsup>n\<^esup> \<longleftrightarrow> m=n \<or> A={}"
proof
  assume "[A]\<^bsup>m\<^esup> = [A]\<^bsup>n\<^esup>"
  then
  show "m = n \<or> A = {}"
    unfolding nsets_def by (smt (verit, del_insts) assms(1) mem_Collect_eq obtain_subset_with_card_n)
qed (use assms in auto)

lemma nsets_disjoint_iff:
  assumes "m \<le> card A" "n \<le> card A" "A \<noteq> {}"
  shows "nsets A m \<inter> nsets A n \<noteq> {} \<longleftrightarrow> m=n"
proof
  assume "[A]\<^bsup>m\<^esup> \<inter> [A]\<^bsup>n\<^esup> \<noteq> {}"
  then show "m = n"
    unfolding nsets_def by fastforce
qed (use assms in \<open>auto simp: nsets_eq_empty_iff\<close>)

lemma partn_lst_less:
  assumes M: "partn_lst \<beta> \<alpha> n" and eq: "length \<alpha>' = length \<alpha>" 
    and le: "\<And>i. i < length \<alpha> \<Longrightarrow> \<alpha>'!i \<le> \<alpha>!i "
  shows "partn_lst \<beta> \<alpha>' n"
proof (clarsimp simp: partn_lst_def)
  fix f
  assume "f \<in> [\<beta>]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>'}"
  then obtain i H where i: "i < length \<alpha>"
                   and "H \<subseteq> \<beta>"  and H: "card H = (\<alpha>!i)" and "finite H"
                   and fi: "f ` nsets H n \<subseteq> {i}"
    using assms by (auto simp: partn_lst_def nsets_def)
  then have bij: "bij_betw (to_nat_on H) H {0..<\<alpha>!i}"
    by (metis atLeast0LessThan to_nat_on_finite)
  then have inj: "inj_on (inv_into H (to_nat_on H)) {0..<\<alpha>' ! i}"
    by (metis bij_betw_def dual_order.refl i inj_on_inv_into ivl_subset le)
  define H' where "H' = inv_into H (to_nat_on H) ` {0..<\<alpha>'!i}"
  show "\<exists>i<length \<alpha>'. \<exists>H\<in>[\<beta>]\<^bsup>(\<alpha>' ! i)\<^esup>. f ` [H]\<^bsup>n\<^esup> \<subseteq> {i}"
  proof (intro exI bexI conjI)
    show "i < length \<alpha>'"
      by (simp add: assms(2) i)
    have "H' \<subseteq> H"
      using bij \<open>i < length \<alpha>\<close> bij_betw_imp_surj_on le
      by (force simp: H'_def image_subset_iff intro: inv_into_into)
    then have "finite H'"
      by (simp add: \<open>finite H\<close> finite_subset)
    with \<open>H' \<subseteq> H\<close> have cardH': "card H' = (\<alpha>'!i)"
      unfolding H'_def by (simp add: inj card_image)
    show "f ` [H']\<^bsup>n\<^esup> \<subseteq> {i}"
      by (meson \<open>H' \<subseteq> H\<close> dual_order.trans fi image_mono nsets_mono)
    show "H' \<in> [\<beta>]\<^bsup>(\<alpha>'! i)\<^esup>"
      using \<open>H \<subseteq> \<beta>\<close> \<open>H' \<subseteq> H\<close> \<open>finite H'\<close> cardH' nsets_def by fastforce
  qed
qed

(*Ramsey?*)
lemma nsets_lepoll_cong:
  assumes "A \<lesssim> B"
  shows "[A]\<^bsup>k\<^esup> \<lesssim> [B]\<^bsup>k\<^esup>"
proof -
  obtain f where f: "inj_on f A" "f ` A \<subseteq> B"
    by (meson assms lepoll_def)
  define F where "F \<equiv> \<lambda>N. f ` N"
  have "inj_on F ([A]\<^bsup>k\<^esup>)"
    using F_def f inj_on_nsets by blast
  moreover
  have "F ` ([A]\<^bsup>k\<^esup>) \<subseteq> [B]\<^bsup>k\<^esup>"
    by (metis F_def bij_betw_def bij_betw_nsets f nsets_mono)
  ultimately show ?thesis
    by (meson lepoll_def)
qed

lemma nsets_eqpoll_cong:
  assumes "A\<approx>B"
  shows "[A]\<^bsup>k\<^esup> \<approx> [B]\<^bsup>k\<^esup>"
  by (meson assms eqpoll_imp_lepoll eqpoll_sym lepoll_antisym nsets_lepoll_cong)

lemma infinite_imp_infinite_nsets:
  assumes inf: "infinite A" and "k>0"
  shows "infinite ([A]\<^bsup>k\<^esup>)"
proof -
  obtain B where "B \<subset> A" "A\<approx>B"
    by (meson inf infinite_iff_psubset)
  then obtain a where a: "a \<in> A" "a \<notin> B"
    by blast
  then obtain N where "N \<subseteq> B" "finite N" "card N = k-1" "a \<notin> N"
    by (metis \<open>A \<approx> B\<close> inf eqpoll_finite_iff infinite_arbitrarily_large subset_eq)
  with a \<open>k>0\<close> \<open>B \<subset> A\<close> have "insert a N \<in> [A]\<^bsup>k\<^esup>"
    by (simp add: nsets_def)
  with a have "nsets B k \<noteq> nsets A k"
    by (metis (no_types, lifting) in_mono insertI1 mem_Collect_eq nsets_def)
  moreover have "nsets B k \<subseteq> nsets A k"
    using \<open>B \<subset> A\<close> nsets_mono by auto
  ultimately show ?thesis
    unfolding infinite_iff_psubset_le
    by (meson \<open>A \<approx> B\<close> eqpoll_imp_lepoll nsets_eqpoll_cong psubsetI)
qed

lemma finite_nsets_iff:
  assumes "k>0"
  shows "finite ([A]\<^bsup>k\<^esup>) \<longleftrightarrow> finite A"
  using assms finite_imp_finite_nsets infinite_imp_infinite_nsets by blast

lemma card_nsets [simp]: "card (nsets A k) = card A choose k"
proof (cases "finite A")
  case True
  then show ?thesis
    by (metis bij_betw_nsets bij_betw_same_card binomial_eq_nsets ex_bij_betw_nat_finite)
next
  case False
  then show ?thesis
    by (cases "k=0"; simp add: finite_nsets_iff)
qed

lemma pow_is_const_prod: "a ^ n = (\<Prod>i<n. a)" for a :: "'a::comm_monoid_mult"
  by simp

(*TAKEN FROM Weighted_Arithmetic_Geometric_Mean-- ADD TO LIBRARY*)
lemma (in linordered_semidom) prod_mono_strict':
  assumes "i \<in> A"
  assumes "finite A"
  assumes "\<And>i. i \<in> A \<Longrightarrow> 0 \<le> f i \<and> f i \<le> g i"
  assumes "\<And>i. i \<in> A \<Longrightarrow> 0 < g i"
  assumes "f i < g i"
  shows   "prod f A < prod g A"
proof -
  have "prod f A = f i * prod f (A - {i})"
    using assms by (intro prod.remove)
  also have "\<dots> \<le> f i * prod g (A - {i})"
    using assms by (intro mult_left_mono prod_mono) auto
  also have "\<dots> < g i * prod g (A - {i})"
    using assms by (intro mult_strict_right_mono prod_pos) auto
  also have "\<dots> = prod g A"
    using assms by (intro prod.remove [symmetric])
  finally show ?thesis .
qed


lemma fact_less_fact_power:
  assumes "1 < s" "s \<le> n" shows "fact n < fact (n - s) * real n ^ s"
proof -
  have eq: "{Suc 0..n} \<inter> {x. x \<le> n - s} = {Suc 0..n-s}" "{Suc 0..n} \<inter> -{x. x \<le> n-s} = {Suc (n-s)..n}" 
    using assms by auto
  have inj: "inj_on ((+)s) A" for A
    by simp
  have "fact n = (\<Prod>i=1..n. real i)"
    by (simp add: fact_prod)
  also have "\<dots> < (\<Prod>i=1..n. if i\<le>n-s then real i else n)"
    using assms by (intro prod_mono_strict' [where i="n-1"]) auto
  also have "\<dots> = (\<Prod>i = 1..n-s. real i) * real n ^ s"
    using \<open>s \<le> n\<close> by (force simp add: prod.If_cases eq)
  also have "\<dots> = fact (n - s) * real n ^ s"
    by (simp add: fact_prod)
  finally show ?thesis .
qed


subsection \<open>Fact D1\<close>

text \<open>from appendix D, page 55\<close>
lemma Fact_D1_73_aux:
  fixes \<sigma>::real and m b::nat  
  assumes \<sigma>: "0<\<sigma>" and bm: "real b < real m"
  shows  "((\<sigma>*m) gchoose b) * inverse (m gchoose b) = \<sigma>^b * (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))"
proof -
  have "((\<sigma>*m) gchoose b) * inverse (m gchoose b) = (\<Prod>i<b. (\<sigma>*m - i) / (real m - real i))"
    using bm by (simp add: gbinomial_prod_rev prod_dividef atLeast0LessThan)
  also have "\<dots> = \<sigma>^b * (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))"
    using bm
  proof (induction b)
    case 0
    then show ?case
      by simp
  next
    case (Suc b)
    then have "b<m"
      by linarith
    with \<sigma> show ?case 
      by (simp add: Suc field_simps)
  qed
  finally show ?thesis .
qed

lemma Fact_D1_73:
  fixes \<sigma>::real and m b::nat  
  assumes \<sigma>: "0<\<sigma>" "\<sigma><1" and b: "real b \<le> \<sigma> * m / 2"
  shows  "(\<sigma>*m) gchoose b \<in> {\<sigma>^b * (real m gchoose b) * exp (- (real b ^ 2) / (\<sigma>*m)) .. \<sigma>^b * (m gchoose b)}"
proof (cases "m=0 \<or> b=0")
  case True
  then show ?thesis
    using True assms by auto
next
  case False
  then have "\<sigma> * m / 2 < real m"
    using \<sigma> by auto
  with b \<sigma> False have bm: "real b < real m"
    by linarith
  then have nonz: "m gchoose b \<noteq> 0"
    by (simp add: flip: binomial_gbinomial)
  have EQ: "((\<sigma>*m) gchoose b) * inverse (m gchoose b) = \<sigma>^b * (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))" 
    using Fact_D1_73_aux \<open>0<\<sigma>\<close> bm by blast
  also have "\<dots> \<le> \<sigma> ^ b * 1"
  proof (intro mult_left_mono prod_le_1 conjI)
    fix i assume "i \<in> {..<b}"
    with b \<sigma> bm show "0 \<le> 1 - (1 - \<sigma>) * i / (\<sigma> * (real m - i))"
      by (simp add: field_split_simps)
  qed (use \<sigma> bm in auto)
  finally have upper: "(\<sigma>*m) gchoose b \<le> \<sigma>^b * (m gchoose b)"
    using nonz by (simp add: divide_simps flip: binomial_gbinomial)
  have *: "exp (-2 * real i / (\<sigma>*m)) \<le> 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i))" if "i<b" for i
  proof -
    have exp_le: "1-x \<ge> exp (-2 * x)" if "0 \<le>x" "x \<le> 1/2" for x::real
    proof -
      have "exp (-2 * x) = inverse (exp (2*x))"
        by (simp add: exp_minus)
      also have "\<dots> \<le> inverse (1 + 2*x)"
        using exp_ge_add_one_self that by auto
      also have "\<dots> \<le> 1-x"
        using that by (simp add: mult_left_le field_simps)
      finally show ?thesis .
    qed
    have "exp (-2 * real i / (\<sigma>*m)) = exp (-2 * (i / (\<sigma>*m)))"
      by simp
    also have "\<dots> \<le> 1 - i/(\<sigma> * m)"
    using b that by (intro exp_le) auto
    also have "\<dots> \<le> 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i))"
      using \<sigma> b that 
      apply (simp add: field_split_simps)
      using bm by linarith
    finally show ?thesis .
  qed
  have "sum real {..<b} \<le> real b ^ 2 / 2"
    by (induction b) (auto simp: power2_eq_square algebra_simps)
  with \<sigma> have "exp (- (real b ^ 2) / (\<sigma>*m)) \<le> exp (- (2 * (\<Sum>i<b. i) / (\<sigma>*m)))"
    by (simp add: mult_less_0_iff divide_simps)
  also have "\<dots> = exp (\<Sum>i<b. -2 * real i / (\<sigma>*m))"
    by (simp add: sum_negf sum_distrib_left sum_divide_distrib)
  also have "\<dots> = (\<Prod>i<b. exp (-2 * real i / (\<sigma>*m)))"
    using exp_sum by blast
  also have "\<dots> \<le> (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))"
    using * by (force intro: prod_mono)
  finally have "exp (- (real b)\<^sup>2 / (\<sigma> * real m)) \<le> (\<Prod>i<b. 1 - (1 - \<sigma>) * real i / (\<sigma> * (real m - real i)))" .
  with EQ have "\<sigma>^b * exp (- (real b ^ 2) / (\<sigma>*m)) \<le> ((\<sigma>*m) gchoose b) * inverse (real m gchoose b)"
    by (simp add: \<sigma>)
  with \<sigma> bm have lower: "\<sigma>^b * (real m gchoose b) * exp (- (real b ^ 2) / (\<sigma>*m)) \<le> (\<sigma>*m) gchoose b"
    by (simp add: field_split_simps flip: binomial_gbinomial)
  with upper show ?thesis 
    by simp
qed

lemma exp_inequality_17:
  fixes x::real
  assumes "0 \<le> x" "x \<le> 1/7"
  shows "1 - 4*x/3 \<ge> exp (-3*x/2)"
proof -
  have "x * 7 \<le> 1"
    using assms by auto
  with \<open>0 \<le> x\<close> have "45 * (x * (x * x)) + (42 * (x * x)) + 36/49 * x * x \<le> x * 8"
    using assms by sos
  moreover have "x * x * (36 * x * x) \<le> (1/7)*(1/7) * (36 * x * x)"
    using assms by (intro mult_mono) auto
  ultimately have *: "45 * (x * (x * x)) + (42 * (x * x) + x * (x * (x * x) * 36)) \<le> x * 8"
    by simp
  have "exp (-3*x/2) = inverse (exp (3*x/2))"
    by (simp add: exp_minus)
  also have "\<dots> \<le> inverse (1 + 3*x/2 + (1/2)*(3*x/2)^2 + (1/6)*(3*x/2)^3)"
    apply (intro le_imp_inverse_le exp_lower_taylor_2)
    by (smt (verit) divide_nonneg_nonneg mult_nonneg_nonneg \<open>0 \<le> x\<close> zero_le_power)
  also have "\<dots> \<le> 1 - 4*x/3"
    using assms *
    apply (simp add: field_split_simps eval_nat_numeral not_less)
    by (smt (verit, best) mult_nonneg_nonneg)
  finally show ?thesis .
qed

text \<open>additional part\<close>
lemma Fact_D1_75:
  fixes \<sigma>::real and m b::nat  
  assumes \<sigma>: "0<\<sigma>" "\<sigma><1" and b: "real b \<le> \<sigma> * m / 2" and b': "b \<le> m/7" and \<sigma>': "\<sigma> \<ge> 7/15"
  shows  "(\<sigma>*m) gchoose b \<ge> exp (- (3 * real b ^ 2) / (4*m)) * \<sigma>^b * (m gchoose b)"
proof (cases "m=0 \<or> b=0")
  case True
  then show ?thesis
    using True assms by auto
next
  case False
  with b \<sigma> have bm: "real b < real m"
    by (smt (verit, ccfv_SIG) le_divide_eq_1_pos of_nat_le_0_iff pos_less_divide_eq times_divide_eq_left)
  have *: "exp (- 3 * real i / (2*m)) \<le> 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i))" if "i<b" for i
  proof -
    have im: "0 \<le> i/m" "i/m \<le> 1/7"
      using b' that by auto
    have "exp (- 3* real i / (2*m)) \<le> 1 - 4*i / (3*m)"
      using exp_inequality_17 [OF im] by (simp add: mult.commute)
    also have "\<dots> \<le> 1 - 8*i / (7 * (real m - real b))"
    proof -
      have "real i * (real b * 7) \<le> real i * real m"
        using b' by (simp add: mult_left_mono)
      then show ?thesis
        using b' by (simp add: field_split_simps)
    qed
    also have "\<dots> \<le> 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i))"
    proof -
      have 1: "(1 - \<sigma>) / \<sigma> \<le> 8/7"
        using \<sigma> \<sigma>' that
        by (simp add: field_split_simps)
      have 2: "1 / (real m - real i) \<le> 1 / (real m - real b)"
        using \<sigma> \<sigma>' b'  that by (simp add: field_split_simps)
      have "(1 - \<sigma>) / (\<sigma> * (real m - real i)) \<le> 8 / (7 * (real m - real b))"
        using mult_mono [OF 1 2] b' that by auto 
      then show ?thesis
        apply simp
        by (metis mult.commute mult_left_mono of_nat_0_le_iff times_divide_eq_right)
    qed
    finally show ?thesis .
  qed

  have EQ: "((\<sigma>*m) gchoose b) * inverse (m gchoose b) = \<sigma>^b * (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))" 
    using Fact_D1_73_aux \<open>0<\<sigma>\<close> bm by blast
  have "sum real {..<b} \<le> real b ^ 2 / 2"
    by (induction b) (auto simp: power2_eq_square algebra_simps)
  with \<sigma> have "exp (- (3 * real b ^ 2) / (4*m)) \<le> exp (- (3 * (\<Sum>i<b. i) / (2*m)))"
    by (simp add: mult_less_0_iff divide_simps)
  also have "\<dots> = exp (\<Sum>i<b. -3 * real i / (2*m))"
    by (simp add: sum_negf sum_distrib_left sum_divide_distrib)
  also have "\<dots> = (\<Prod>i<b. exp (-3 * real i / (2*m)))"
    using exp_sum by blast
  also have "\<dots> \<le> (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))"
    using * by (force intro: prod_mono)
  finally have "exp (- (3 * real b ^ 2) / (4*m)) \<le> (\<Prod>i<b. 1 - (1-\<sigma>) * i / (\<sigma> * (real m - real i)))" .
  with EQ have "\<sigma>^b * exp (- (3 * real b ^ 2) / (4*m)) \<le> ((\<sigma>*m) gchoose b) * inverse (real m gchoose b)"
    by (simp add: assms(1))
  with \<sigma> bm show ?thesis
    by (simp add: field_split_simps flip: binomial_gbinomial)
qed

section \<open>Lemmas relating to Ramsey's theorem\<close>

lemma nsets2_eq_all_edges: "[A]\<^bsup>2\<^esup> = all_edges A"
  using card_2_iff' unfolding nsets_def all_edges_def
  by fastforce

(* not sure that the type class is the best approach when using Chelsea's locale*)
class infinite =
  assumes infinite_UNIV: "infinite (UNIV::'a set)"

instance nat :: infinite
  by (intro_classes) simp
instance prod :: (infinite, type) infinite
  by intro_classes (simp add: finite_prod infinite_UNIV)
instance list :: (type) infinite
  by intro_classes (simp add: infinite_UNIV_listI)


lemma indep_eq_clique_compl: "indep R E = clique R (all_edges R - E)"
  by (auto simp: indep_def clique_def all_edges_def)

lemma all_edges_subset_iff_clique: "all_edges K \<subseteq> E \<longleftrightarrow> clique K E"
  by (fastforce simp add: card_2_iff clique_def all_edges_def)

lemma smaller_clique: "\<lbrakk>clique R E; R' \<subseteq> R\<rbrakk> \<Longrightarrow> clique R' E"
  by (auto simp: clique_def)

lemma smaller_indep: "\<lbrakk>indep R E; R' \<subseteq> R\<rbrakk> \<Longrightarrow> indep R' E"
  by (auto simp: indep_def)

definition "clique_indep \<equiv> \<lambda>m n K E. card K = m \<and> clique K E \<or> card K = n \<and> indep K E"

lemma clique_all_edges_iff: "clique K (E \<inter> all_edges K) \<longleftrightarrow> clique K E"
  by (simp add: clique_def all_edges_def)

lemma indep_all_edges_iff: "indep K (E \<inter> all_edges K) \<longleftrightarrow> indep K E"
  by (simp add: indep_def all_edges_def)

lemma clique_indep_all_edges_iff: "clique_indep s t K (E \<inter> all_edges K) = clique_indep s t K E"
  by (simp add: clique_all_edges_iff clique_indep_def indep_all_edges_iff)

(** at issue here is whether we benefit from the clique definition, which is found in the literature **)

text \<open>identifying Ramsey numbers (not the minimum) for a given type and pair of integers\<close>
definition IS_RN where
  "IS_RN \<equiv> \<lambda>U::'a itself. \<lambda>m n r. 
       (\<forall>V::'a set. \<forall>E. finite V \<longrightarrow> card V \<ge> r \<longrightarrow> (\<exists>K\<subseteq>V. clique_indep m n K E))"

text \<open>could be generalised to allow e.g. any hereditarily finite set\<close>
abbreviation is_Ramsey_number :: "[nat,nat,nat] \<Rightarrow> bool" where 
  "is_Ramsey_number m n r \<equiv> partn_lst {..<r} [m,n] 2"


definition "monochromatic \<equiv> \<lambda>\<beta> \<alpha> \<gamma> f i. \<exists>H \<in> nsets \<beta> \<alpha>. f ` (nsets H \<gamma>) \<subseteq> {i}"

lemma partn_lst_iff:
  "partn_lst \<beta> \<alpha> \<gamma> \<equiv> \<forall>f \<in> nsets \<beta> \<gamma>  \<rightarrow>  {..<length \<alpha>}. \<exists>i < length \<alpha>. monochromatic \<beta> (\<alpha>!i) \<gamma> f i"
  by (simp add: partn_lst_def monochromatic_def)

lemma IS_RN_imp_partn_lst:  (*EVENTUALLY, RENAME*)
  fixes U :: "'a itself"
  assumes r: "IS_RN U m n r" and inf: "infinite (UNIV::'a set)"
  shows "partn_lst {..<r} [m,n] 2"
  unfolding partn_lst_def
proof (intro strip)
  fix f
  assume f: "f \<in> [{..<r}]\<^bsup>2\<^esup> \<rightarrow> {..<length [m,n]}"
  obtain V::"'a set" where "finite V" and V: "card V = r"
    by (metis assms infinite_arbitrarily_large)
  then obtain \<phi> where \<phi>: "bij_betw \<phi> V {..<r}"
    using to_nat_on_finite by blast
  define E where "E \<equiv> {e. \<exists>x\<in>V. \<exists>y\<in>V. e = {x,y} \<and> x \<noteq> y \<and> f {\<phi> x, \<phi> y} = 0}"
  obtain K where "K\<subseteq>V" and K: "clique_indep m n K E"
    by (metis r V \<open>finite V\<close> IS_RN_def nle_le)
  then consider "card K = m" "clique K E" | "card K = n" "indep K E"
    by (meson clique_indep_def)
  then show "\<exists>i<length [m, n]. \<exists>H\<in>[{..<r}]\<^bsup>([m,n] ! i)\<^esup>. f ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
  proof cases
    case 1
    have "f e = 0"
      if e: "e \<subseteq> \<phi> ` K" "finite e" "card e = 2" for e :: "nat set"
    proof -
      obtain x y where "x\<in>V" "y\<in>V" "e = {\<phi> x, \<phi> y} \<and> x \<noteq> y"
        using e \<open>K\<subseteq>V\<close> \<phi>
        apply (auto simp: subset_image_iff)
        by (metis basic_trans_rules(23) bij_betw_def bij_betw_same_card bij_betw_singletonI bij_betw_subset card_2_iff image_insert insert_subset)
      then show ?thesis
        using e 1
        apply (simp add: clique_def E_def)
        by (smt (verit, ccfv_threshold) \<phi> bij_betw_iff_bijections imageE image_insert image_is_empty)
    qed
    moreover have "\<phi> ` K \<in> [{..<r}]\<^bsup>m\<^esup>"
      apply (auto simp: nsets_def)
      using \<open>K \<subseteq> V\<close> \<phi> bij_betw_imp_surj_on apply fastforce
      using \<open>K \<subseteq> V\<close> \<open>finite V\<close> finite_subset apply blast
      by (metis "1"(1) \<open>K \<subseteq> V\<close> \<phi> bij_betw_same_card bij_betw_subset)
    ultimately show ?thesis
      apply (rule_tac x="0" in exI)
      apply (simp add: )
      by (smt (verit, best) image_subset_iff insert_iff mem_Collect_eq nsets_def)
  next
    case 2
    then show ?thesis sorry
  qed

qed

lemma partn_lst_imp_IS_RN: (*EVENTUALLY, RENAME*)
  fixes U :: "'a itself"
  assumes "partn_lst {..<r} [m,n] 2"
  shows "IS_RN U m n r"
  unfolding IS_RN_def
proof (intro strip)
  fix V::"'a set" and E ::"'a set set"
  assume V: "finite V" "r \<le> card V"
  obtain \<phi> where \<phi>: "bij_betw \<phi> {..<card V} V"
    using \<open>finite V\<close> bij_betw_from_nat_into_finite by blast
  define f :: "nat set \<Rightarrow> nat" where "f \<equiv> \<lambda>e. if \<phi>`e \<in> E then 0 else 1"
  obtain i H where "i<2" and H: "H \<subseteq> {..<r}" "finite H" "card H = [m,n] ! i" 
    and mono: "f ` (nsets H 2) \<subseteq> {i}"
    using assms unfolding partn_lst_def nsets_def
    using f_def numeral_2_eq_2
    apply-
    apply (drule_tac x="f" in bspec)
    apply (simp add: f_def)
    using numeral_2_eq_2 by auto
  have [simp]: "\<And>v w. \<lbrakk>v \<in> H; w \<in> H\<rbrakk> \<Longrightarrow> \<phi> v = \<phi> w \<longleftrightarrow> v=w"
    using bij_betw_imp_inj_on [OF \<phi>] H
    by (meson V(2) inj_on_def inj_on_subset lessThan_subset_iff)
  define K where "K \<equiv> \<phi> ` H"
  have [simp]: "\<And>v w. \<lbrakk>v \<in> K; w \<in> K\<rbrakk> \<Longrightarrow> inv_into {..<card V} \<phi> v = inv_into {..<card V} \<phi> w \<longleftrightarrow> v=w"
    using bij_betw_inv_into_right [OF \<phi>] H
    by (metis (no_types, opaque_lifting) K_def Set.basic_monos(7) V(2) \<phi> bij_betw_imp_surj_on image_mono lessThan_subset_iff)
  have "K \<subseteq> V"
    using H \<phi> V bij_betw_imp_surj_on by (fastforce simp: K_def nsets_def)
  have [simp]: "card (\<phi> ` H) = card H"
    using H by (metis V(2) \<phi> bij_betw_same_card bij_betw_subset lessThan_subset_iff)
  consider (0) "i=0" | (1) "i=1"
    using \<open>i<2\<close> by linarith
  then have "clique_indep m n K E"
  proof cases
    case 0 
    have "{v, w} \<in> E" if "v \<in> K" and "w \<in> K" and "v \<noteq> w"  for v w
    proof -
      have "{inv_into {..<card V} \<phi> v, inv_into {..<card V} \<phi> w} \<in> [H]\<^bsup>2\<^esup>"
        using that bij_betw_inv_into_left [OF \<phi>] H(1) V(2)
        by (auto simp add: nsets_def card_insert_if K_def)
      then show ?thesis
        by (smt (verit, del_insts) "0" Set.basic_monos(7) \<open>K \<subseteq> V\<close> \<phi> bij_betw_inv_into_right f_def image_empty image_insert image_subset_iff mono nat.simps(3) numeral_nat(7) singletonD that(1) that(2))
    qed
    then show ?thesis 
      unfolding clique_indep_def clique_def
      by (simp add: "0" H(3) K_def)
  next
    case 1
    have "{v, w} \<notin> E" if "v \<in> K" and "w \<in> K" and "v \<noteq> w"  for v w
    proof -
      have "{inv_into {..<card V} \<phi> v, inv_into {..<card V} \<phi> w} \<in> [H]\<^bsup>2\<^esup>"
        using that bij_betw_inv_into_left [OF \<phi>] H(1) V(2)
        by (auto simp add: nsets_def card_insert_if K_def)
      then show ?thesis
        by (smt (verit, del_insts) "1" Set.basic_monos(7) \<open>K \<subseteq> V\<close> \<phi> bij_betw_inv_into_right f_def image_empty image_insert image_subset_iff mono nat.simps(3) numeral_nat(7) singletonD that(1) that(2))
    qed
    then show ?thesis 
      unfolding clique_indep_def indep_def
      by (simp add: "1" H(3) K_def)
  qed
  with \<open>K \<subseteq> V\<close> show "\<exists>K. K \<subseteq> V \<and> clique_indep m n K E" by blast
qed



text \<open>All complete graphs of a given cardinality are the same\<close>
lemma IS_RN_any_type:
  assumes "IS_RN (U::'a itself) m n r" "infinite (UNIV::'a set)" 
  shows "IS_RN (V::'b::infinite itself) m n r"
  by (metis  partn_lst_imp_IS_RN IS_RN_imp_partn_lst assms)

lemma is_Ramsey_number_le:
  assumes "is_Ramsey_number m n r" and le: "m' \<le> m" "n' \<le> n"
  shows "is_Ramsey_number m' n' r"
  using partn_lst_less [where \<alpha> = "[m,n]" and \<alpha>' = "[m',n']"] assms
  by (force simp add: less_Suc_eq)

definition RN where
  "RN \<equiv> \<lambda>m n. LEAST r. is_Ramsey_number m n r"

lemma is_Ramsey_number_RN: "partn_lst {..< (RN m n)} [m,n] 2"
  by (metis LeastI_ex RN_def ramsey2_full)


lemma RN_le: "\<lbrakk>is_Ramsey_number m n r\<rbrakk> \<Longrightarrow> RN m n \<le> r"
  by (simp add: Least_le RN_def)

lemma RN_mono:
  assumes "m' \<le> m" "n' \<le> n"
  shows "RN m' n' \<le> RN m n"
  by (meson RN_le assms is_Ramsey_number_RN is_Ramsey_number_le)

lemma indep_iff_clique [simp]: "K \<subseteq> V \<Longrightarrow> indep K (all_edges V - E) \<longleftrightarrow> clique K E"
  by (auto simp: clique_def indep_def all_edges_def)

lemma clique_iff_indep [simp]: "K \<subseteq> V \<Longrightarrow> clique K (all_edges V - E) \<longleftrightarrow> indep K E"
  by (auto simp: clique_def indep_def all_edges_def)

lemma is_Ramsey_number_commute:
  assumes "is_Ramsey_number m n r"
  shows "is_Ramsey_number n m r"
  unfolding partn_lst_def
proof (intro strip)
  fix f 
  assume f: "f \<in> [{..<r}]\<^bsup>2\<^esup> \<rightarrow> {..<length [n, m]}"
  define f' where "f' \<equiv> \<lambda>A. 1 - f A"
  then have "f' \<in> [{..<r}]\<^bsup>2\<^esup> \<rightarrow> {..<2}"
    by (auto simp: f'_def)
  then obtain i H where "i<2" and H: "H \<in> [{..<r}]\<^bsup>([m,n] ! i)\<^esup>" "f' ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
    using assms by (auto simp: partn_lst_def numeral_2_eq_2)
  then have "H \<subseteq> {..<r}"
    by (auto simp: nsets_def)
  then have fless2: "\<forall>x\<in>[H]\<^bsup>2\<^esup>. f x < Suc (Suc 0)"
    using funcset_mem [OF f] nsets_mono by force
  show "\<exists>i<length [n, m]. \<exists>H\<in>[{..<r}]\<^bsup>([n,m] ! i)\<^esup>. f ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
  proof (intro exI bexI conjI)
    show "f ` [H]\<^bsup>2\<^esup> \<subseteq> {1-i}"
      using H fless2 by (fastforce simp: f'_def)
    show "H \<in> [{..<r}]\<^bsup>([n, m] ! (1-i))\<^esup>"
      using \<open>i<2\<close> H by (fastforce simp add: less_2_cases_iff f'_def image_subset_iff)
  qed auto
qed

lemma RN_commute_aux: "RN n m \<le> RN m n"
  using RN_le is_Ramsey_number_RN is_Ramsey_number_commute by blast

lemma RN_commute: "RN m n = RN n m"
  by (simp add: RN_commute_aux le_antisym)


lemma RN_0 [simp]: "RN 0 m = 0"
  unfolding RN_def
proof (intro Least_equality)
  show "is_Ramsey_number 0 m 0"
    by (auto simp: partn_lst_def nsets_def)
qed auto

lemma RN_1 [simp]: 
  assumes "m>0" shows "RN 1 m = 1"
  unfolding RN_def
proof (intro Least_equality)
  have [simp]: "[{..<Suc 0}]\<^bsup>2\<^esup> = {}" "[{}]\<^bsup>2\<^esup> = {}"
    by (auto simp: nsets_def card_2_iff)
  show "is_Ramsey_number 1 m 1"
    by (auto simp: partn_lst_def)
  fix i
  assume i: "is_Ramsey_number 1 m i"
  show "i \<ge> 1"
  proof (cases "i=0")
    case True
    with i assms show ?thesis
      by (auto simp: partn_lst_def nsets_empty_iff less_Suc_eq)
  qed auto
qed

lemma IS_RN_2: "IS_RN TYPE(nat) 2 m m"
  unfolding IS_RN_def
proof (intro strip)
  fix V :: "'a set" and E
  assume "finite V"
    and "m \<le> card V"
  show "\<exists>K. K \<subseteq> V \<and> clique_indep 2 m K E"
  proof (cases "\<exists>K. K \<subseteq> V \<and> card K = 2 \<and> clique K E")
    case False
    then have "indep V E"
      apply (clarsimp simp: clique_def indep_def card_2_iff)
      by (smt (verit, best) doubleton_eq_iff insert_absorb insert_iff subset_iff)
    then show ?thesis
      unfolding clique_indep_def
      by (meson \<open>m \<le> card V\<close> card_Ex_subset smaller_indep)
  qed (metis clique_indep_def)
qed

lemma RN_2 [simp]: 
  assumes "m>1"
  shows "RN 2 m = m"
  unfolding RN_def
proof (intro Least_equality)
  show "is_Ramsey_number 2 m m"
    apply (rule IS_RN_imp_partn_lst)
     apply (rule IS_RN_2)
    apply (auto simp: )
    done
  fix i
  assume "is_Ramsey_number 2 m i"
  then have i: "IS_RN TYPE(nat) 2 m i"
    using partn_lst_imp_IS_RN by blast
  obtain V :: "nat set" where V: "card V = i" "finite V"
    by force
  show "i \<ge> m"
  proof (cases "i<m")
    case True
    then have "\<not> (\<exists>K\<subseteq>V. card K = 2 \<and> clique K {})"
      by (auto simp: clique_def card_2_iff')
    with i V assms show ?thesis
      unfolding IS_RN_def clique_indep_def by (metis card_mono dual_order.refl)
  qed auto
qed

lemma RN_3plus: 
  assumes "k \<ge> 3" "m>1"
  shows "RN k m \<ge> m"
proof -
  have "RN 2 m = m"
    using assms by auto
  with RN_mono[of 2 k m m] assms show ?thesis
    by force
qed

context sgraph
begin

lemma clique_iff: "F \<subseteq> all_edges K \<Longrightarrow> clique K F \<longleftrightarrow> F = all_edges K"
  by (auto simp: clique_def all_edges_def card_2_iff)

lemma indep_iff: "F \<subseteq> all_edges K \<Longrightarrow> indep K F \<longleftrightarrow> F = {}"
  by (auto simp: indep_def all_edges_def card_2_iff)

lemma all_edges_empty_iff: "all_edges K = {} \<longleftrightarrow> (\<exists>v. K \<subseteq> {v})"
  apply (simp add: all_edges_def card_2_iff subset_iff)
  by (metis insert_iff singleton_iff)

(*the corresponding strict inequality can be proved under the assumptions  "1 < s" "s \<le> n"
  using fact_less_fact_power*)
lemma binomial_fact_pow: "(n choose s) * fact s \<le> n^s"
proof (cases "s \<le> n")
  case True
  then show ?thesis
    using fact_less_fact_power 
    by (smt (verit) binomial_fact_lemma mult.assoc mult.commute fact_div_fact_le_pow fact_nonzero nonzero_mult_div_cancel_right) 
qed (simp add: binomial_eq_0)

text \<open>The original Ramsey number lower bound, by Erdős\<close>
(* requires re-factoring to take advantage of card_Pow_diff and with a symmetric treatment of 
independent sets, and also utilising Andrew's simpler estimation *)
proposition Ramsey_number_lower:  
  fixes n s::nat
  assumes "s \<ge> 3" and n: "real n \<le> 2 powr (s/2)"
  shows "\<not> IS_RN (TYPE (nat)) s s n"
proof
  define W where "W \<equiv> {..<n}"
  assume "IS_RN (TYPE (nat)) s s n"
  then have monoc: "\<And>F. \<exists>K\<subseteq>W. clique_indep s s K F"
    by (simp add: IS_RN_def W_def)
  then have "s \<le> n"
    by (metis W_def card_lessThan card_mono clique_indep_def finite_lessThan)
  have "s > 1" using assms by arith
  have "n>0"
    using \<open>1 < s\<close> \<open>s \<le> n\<close> by linarith
  define monoset where "monoset \<equiv> \<lambda>K::nat set. {F. F \<subseteq> all_edges K \<and> clique_indep s s K F}"

  have "(n choose s) \<le> n^s / fact s"  \<comment> \<open>probability calculation\<close>
    using binomial_fact_pow[of n s]
    by (smt (verit) fact_gt_zero of_nat_fact of_nat_mono of_nat_mult pos_divide_less_eq)  
  then have "(n choose s) * (2 / 2^(s choose 2)) \<le> 2 * n^s / (fact s * 2 ^ (s * (s-1) div 2))"
    by (simp add: choose_two divide_simps)
  also have "\<dots> \<le> 2 powr (1 + s/2) / fact s" 
  proof -
    have [simp]: "real (s * (s - Suc 0) div 2) = real s * (real s - 1) / 2"
      by (subst real_of_nat_div) auto
    have "n powr s \<le> (2 powr (s/2)) powr s"
      using n by (simp add: powr_mono2)
    then have "n powr s \<le> 2 powr (s * s / 2)"
      using \<open>n>0\<close> assms by (simp add: power2_eq_square powr_powr)
    then have "2 * n powr s \<le> 2 powr ((2 + s * s) / 2)"
      by (simp add: add_divide_distrib powr_add)
    then show ?thesis
      using n \<open>n>0\<close> by (simp add: field_simps flip: powr_realpow powr_add)
  qed
  also have "\<dots> < 1"
  proof -
    have "2 powr (1 + (k+3)/2) < fact (k+3)" for k
    proof (induction k)
      case 0
      have "2 powr (5/2) = sqrt (2^5)"
        by (metis divide_inverse mult.left_neutral numeral_powr_numeral_real powr_ge_pzero powr_half_sqrt powr_powr)
      also have "\<dots> < sqrt 36"
        by (intro real_sqrt_less_mono) auto
      finally show ?case
        by (simp add: eval_nat_numeral)
    next
      case (Suc k)
      have "2 powr (1 + real (Suc k + 3) / 2) = 2 powr (1/2) * 2 powr (1 + (k+3)/2)"
        apply (simp add: powr_add powr_half_sqrt_powr real_sqrt_mult)
        apply (simp flip: real_sqrt_mult)
        done
      also have "\<dots> \<le> sqrt 2 * fact (k+3)"
        using Suc.IH by (simp add: powr_half_sqrt)
      also have "\<dots> < real(k + 4) * fact (k + 3)"
        using sqrt2_less_2 by simp
      also have "\<dots> = fact (Suc (k + 3))"
        unfolding fact_Suc by simp
      finally show ?case by simp
    qed
    then have "2 powr (1 + s/2) < fact s"
      by (metis add.commute \<open>s\<ge>3\<close> le_Suc_ex)
    then show ?thesis
      by (simp add: divide_simps)
  qed
  finally have less_1: "real (n choose s) * (2 / 2 ^ (s choose 2)) < 1" .

  define \<Omega> where "\<Omega> \<equiv> Pow (all_edges W)"  \<comment>\<open>colour the edges randomly\<close>
  have "finite W" and cardW: "card W = n"
    by (auto simp: W_def)
  moreover
  have "card (all_edges W) = n choose 2"
    by (simp add: W_def card_all_edges)
  ultimately have card\<Omega>: "card \<Omega> = 2 ^ (n choose 2)"
    by (simp add: \<Omega>_def card_Pow finite_all_edges)
  then have fin_\<Omega>: "finite \<Omega>"
    by (simp add: \<Omega>_def \<open>finite W\<close> finite_all_edges)
  define M where "M \<equiv> uniform_count_measure \<Omega>"
  have space_eq: "space M = \<Omega>"
    by (simp add: M_def space_uniform_count_measure)
  have sets_eq: "sets M = Pow \<Omega>"
    by (simp add: M_def sets_uniform_count_measure)
  interpret P: prob_space M
    using M_def fin_\<Omega> card\<Omega> prob_space_uniform_count_measure by force

  \<comment>\<open>the event to avoid: monochromatic cliques, given @{term "K \<subseteq> W"};
      we are considering edges over the entire graph @{term W}, to agree with @{text monoc}\<close>
  define A where "A \<equiv> \<lambda>K. {F \<in> \<Omega>. F \<inter> all_edges K \<in> monoset K}"
  have A_ev: "A K \<in> P.events" for K
    by (auto simp add: sets_eq A_def \<Omega>_def)
  have A_sub_\<Omega>: "A K \<subseteq> \<Omega>" for K
    by (auto simp add: sets_eq A_def \<Omega>_def)
  have UA_sub_\<Omega>: "(\<Union>K \<in> nsets W s. A K) \<subseteq> \<Omega>"
    by (auto simp: \<Omega>_def A_def nsets_def all_edges_def)
  have s_choose_le: "s choose 2 \<le> n choose 2"
    using \<open>s \<le> n\<close> by (simp add: Diagonal.binomial_mono)
  have cardA: "card (A K) = 2 * 2 ^ ((n choose 2) - (s choose 2))" 
    if "K \<in> nsets W s" for K     \<comment>\<open>the cardinality involves the edges outside the clique\<close>
  proof -
    have K: "K \<subseteq> W" "finite K" "card K = s"
      using that by (auto simp: nsets_def)
    with \<open>finite W\<close> have [simp]: "finite ([K]\<^bsup>2\<^esup>)" "finite ([W]\<^bsup>2\<^esup>)"
      by (auto simp add: finite_imp_finite_nsets)
    have "card ([K]\<^bsup>2\<^esup>) = s choose 2"
      by (simp add: K)
    have *: "all_edges K \<noteq> {}"
      using that \<open>s \<ge> 3\<close> subset_singletonD by (fastforce simp: nsets_def all_edges_empty_iff)

    define f :: "nat set set * nat set set \<Rightarrow> nat set set * nat set set" 
      where "f \<equiv> \<lambda>(EW,EA). ((EW \<inter> all_edges K) \<union> (EA - all_edges K), EA \<inter> all_edges K)"
    have "bij_betw f (Pow (nsets K 2) \<times> A K) 
                       (Pow (nsets W 2) \<times> {all_edges K, {}})"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on f (Pow ([K]\<^bsup>2\<^esup>) \<times> A K)"
        by (auto simp add: inj_on_def f_def A_def nsets2_eq_all_edges)
      have *: "\<exists>EA\<subseteq>all_edges W. EA \<inter> all_edges K \<in> monoset K
                        \<and> EW = EW \<inter> all_edges K \<union> (EA - all_edges K) \<and> F = EA \<inter> all_edges K"
        if F: "F = all_edges K \<or> F = {}" and EW: "EW \<subseteq> all_edges W" for EW F
        using F
      proof
        assume \<section>: "F = all_edges K"
        show ?thesis
        proof (intro exI conjI)
          show "EW \<union> all_edges K \<subseteq> all_edges W"
            by (simp add: \<open>K \<subseteq> W\<close> all_edges_mono EW)
          show "(EW \<union> all_edges K) \<inter> all_edges K \<in> monoset K"
            by (simp add: K clique_iff clique_indep_def monoset_def)
        qed (use \<section> in auto)
      next
        assume \<section>: "F = {}"
        show ?thesis
        proof (intro exI conjI)
          show "(EW - all_edges K) \<inter> all_edges K \<in> monoset K"
            by (simp add: Int_commute K clique_indep_def indep_iff monoset_def)
        qed (use \<section> that in auto)
      qed
      have "f ` (Pow ([K]\<^bsup>2\<^esup>) \<times> A K) \<subseteq> Pow ([W]\<^bsup>2\<^esup>) \<times> {all_edges K, {}}"
        using K all_edges_mono
        by (auto simp: f_def A_def \<Omega>_def nsets2_eq_all_edges monoset_def clique_indep_def clique_iff indep_iff)
      moreover have "Pow ([W]\<^bsup>2\<^esup>) \<times> {all_edges K, {}} \<subseteq> f ` (Pow ([K]\<^bsup>2\<^esup>) \<times> A K)"
        apply (clarsimp simp: f_def A_def \<Omega>_def image_iff nsets2_eq_all_edges)
        apply (rule_tac x="a \<inter> all_edges K" in bexI; force simp add: *)
        done
      ultimately show "f ` (Pow ([K]\<^bsup>2\<^esup>) \<times> A K) = Pow ([W]\<^bsup>2\<^esup>) \<times> {all_edges K, {}}" 
        by blast
    qed
    then
    have "card (Pow (nsets K 2) \<times> A K)  = card (Pow (nsets W 2) \<times> {all_edges K, {}})"
      using bij_betw_same_card by blast
    then have "2 ^ (s choose 2) * card (A K) = 2 * 2 ^ (n choose 2)"
      using K  * by (simp add: card_Pow card_cartesian_product cardW)
    then have "2 ^ (s choose 2) * card (A K) = 2 * 2 ^ ((s choose 2) + (n choose 2 - (s choose 2)))"
      by (simp add: s_choose_le)
    then show ?thesis
      by (simp add: power_add)
  qed
  have emeasure_eq: "emeasure M C = (if C \<subseteq> \<Omega> then card C / card \<Omega> else 0)" for C
    using M_def emeasure_neq_0_sets emeasure_uniform_count_measure fin_\<Omega> sets_eq by force
  have MA: "emeasure M (A K) = ennreal (2 / 2 ^ (s choose 2))" if "K \<in> nsets W s" for K
    using that
    apply (simp add: emeasure_eq A_sub_\<Omega> card\<Omega> cardA)
    apply (simp add: s_choose_le power_diff flip: divide_ennreal ennreal_power)
    done
  then have prob_AK: "P.prob (A K) = 2 / 2 ^ (s choose 2)" if "K \<in> nsets W s" for K
    using that by (simp add: P.emeasure_eq_measure)
  have "P.prob (\<Union> K \<in> nsets W s. A K) \<le> (\<Sum>K \<in> nsets W s. P.prob (A K))"
    by (simp add: A_ev P.finite_measure_subadditive_finite \<open>finite W\<close> nsets_def image_subset_iff)
  also have "\<dots> = real (n choose s) * (2 / 2 ^ (s choose 2))"
    by (simp add: prob_AK W_def)
  also have "\<dots> < 1" 
    using less_1 by presburger
  finally have "P.prob (\<Union> K \<in> nsets W s. A K) < 1" .
  with A_ev UA_sub_\<Omega> obtain F where "F \<in> \<Omega> - (\<Union> K \<in> nsets W s. A K)"
    by (smt (verit, best) P.prob_space Diff_iff space_eq subset_antisym subset_iff)
  then have "\<forall>K \<in> nsets W s. \<not> clique_indep s s K F"
    by (simp add: A_def monoset_def \<Omega>_def clique_indep_all_edges_iff)
  then show False
    using monoc \<open>finite W\<close> finite_subset nsets_def by (fastforce simp add: clique_indep_def)
qed

lemma powr_half_ge:
  fixes x::real
  assumes "x\<ge>4"
  shows "x \<le> 2 powr (x/2)"
proof -
  have 1: "x \<le> 2 powr (x/2)" if "x=4"
    using that by simp
  have 2: "((\<lambda>x. 2 powr (x/2) - x) has_real_derivative ln 2 * (2 powr (y/2 - 1)) - 1) (at y)" for y
    by (rule derivative_eq_intros refl | simp add: powr_diff)+
  have 3: "ln 2 * (2 powr (y/2 - 1)) - 1 \<ge> 0" if "4 \<le> y" for y::real
  proof -
    have "1 \<le> ln 2 * 2 powr ((4 - 2) / (2::real))"
      using ln2_ge_two_thirds by simp
    also have "... \<le> ln 2 * (2 powr (y/2 - 1))"
      using that by (intro mult_left_mono powr_mono) auto
    finally show ?thesis by simp
  qed
  show ?thesis
    by (rule gen_upper_bound_increasing [OF assms 2 3]) auto
qed

theorem RN_lower:
  assumes "k \<ge> 3"
  shows "RN k k > 2 powr (k/2)"                              
  using assms Ramsey_number_lower is_Ramsey_number_RN
  by (smt (verit) partn_lst_imp_IS_RN)

text \<open>and trivially, off the diagonal too (OBSOLETE?)\<close>
corollary RN_lower_nodiag:
  assumes "k \<ge> 3" "l \<ge> k"
  shows "RN k l > 2 powr (k/2)"
  by (meson RN_lower RN_mono assms less_le_trans le_refl of_nat_mono)                       

theorem RN_lower_self:
  assumes "k \<ge> 4"
  shows "RN k k > k"
proof -
  have "k \<le> 2 powr (k/2)"
    using powr_half_ge numeral_le_real_of_nat_iff assms by blast
  also have "\<dots> < RN k k"
    using assms by (intro RN_lower) auto
  finally show ?thesis
    by fastforce
qed

lemma Ramsey_number_zero: "\<not> is_Ramsey_number (Suc m) (Suc n) 0"
  by (metis RN_1 RN_le is_Ramsey_number_le not_one_le_zero Suc_le_eq One_nat_def zero_less_Suc)

(* this might work better with the other treatment of Ramsey numbers, avoiding the need to encode pairs*)
lemma Ramsey_number_times_lower: "\<not> is_Ramsey_number (Suc m) (Suc n) (m*n)"
proof
  assume \<section>: "is_Ramsey_number (Suc m) (Suc n) (m*n)"
  obtain \<phi> where \<phi>: "bij_betw \<phi> {..<m*n} ({..<m} \<times> {..<n})"
    using bij_betw_iff_card
    by (metis card_cartesian_product card_lessThan finite_cartesian_product finite_lessThan)
  define edge :: "[nat \<times> nat, nat \<times> nat] \<Rightarrow> nat" where "edge \<equiv> \<lambda>(x,y) (x',y'). if y=y' then 0 else 1"
  have edge2: "\<And>u v. edge u v < 2"
    by (simp add: edge_def split: prod.split)
  define f where "f \<equiv> upair_define (\<lambda>p q. edge (\<phi> p) (\<phi> q))"
  have edge_commute: "\<And>p q. edge (\<phi> p) (\<phi> q) = edge (\<phi> q) (\<phi> p)"
    by (simp add: edge_def split: prod.split)
  then have f_apply: "\<And>p q. f{p,q} = edge (\<phi> p) (\<phi> q)"
    by (simp add: f_def upair_define_apply)
  then have "f \<in> [{..<m * n}]\<^bsup>2\<^esup> \<rightarrow> {..<2}"
    by (auto simp add: Pi_iff nsets_def card_2_iff edge2)
  then obtain i where "i<2" and i: "monochromatic {..<m * n} ([Suc m, Suc n] ! i) 2 f i"
    using \<section> by (force simp add: partn_lst_iff eval_nat_numeral)
  have edge_apply: "\<And>u v. \<lbrakk>u \<in> {..<m}\<times>{..<n}; v \<in> {..<m}\<times>{..<n}\<rbrakk> 
               \<Longrightarrow> edge u v = f{inv_into {..<m*n} \<phi> u, inv_into {..<m*n} \<phi> v}"
    using \<phi> by (simp add: f_apply bij_betw_inv_into_right)

  have apply\<phi>: "\<And>e x H. \<lbrakk>H \<subseteq> {..<m * n}; e \<in> [H]\<^bsup>2\<^esup>; x \<in> e\<rbrakk> \<Longrightarrow> \<phi> x \<in> {..<m} \<times> {..<n}"
    using \<phi> by (auto simp: bij_betw_def ordered_nsets_2_eq)    
  consider (0) "i=0" | (1) "i=1"
    using \<open>i<2 \<close>by linarith
  then show False
  proof cases
    case 0
    then obtain H where H: "H \<subseteq> {..<m * n}" "finite H" "card H = Suc m" 
              and monoc: "\<And>u. u \<in> [H]\<^bsup>2\<^esup> \<Longrightarrow> f u = 0"
      using i by (auto simp add: monochromatic_def nsets_def image_subset_iff)
    then have inj\<phi>: "inj_on \<phi> H"
      by (meson \<phi> bij_betw_def inj_on_subset)
    define A where "A \<equiv>  \<phi> ` \<Union> ([H]\<^bsup>2\<^esup>)"
    have "edge u v = 0" if "u \<in> A" "v \<in> A" "u \<noteq> v" for u v
      using that \<open>H \<subseteq> {..<m * n}\<close>  
      apply (clarsimp simp add: A_def edge_apply apply\<phi> all_edges_def nsets2_eq_all_edges subset_iff bij_betw_inv_into_left [OF \<phi>])
      by (rule monoc) auto
    then have snd_eq: "snd u = snd v" if "u \<in> A" "v \<in> A" "u \<noteq> v" for u v
      by (smt (verit) edge_def prod.collapse prod.simps(2) zero_neq_one that)
    then have "inj_on fst A"
      by (meson inj_onI prod.expand)
    moreover have "fst ` A \<subseteq> {..<m}"
      by (force simp: A_def image_iff dest!: apply\<phi> [OF \<open>H \<subseteq> {..<m * n}\<close>])
    ultimately have "card A \<le> m"
      by (metis card_image card_lessThan card_mono finite_lessThan)
    have "card H \<ge> 2"
      using Suc_le_eq H monoc by fastforce
    have "Suc m \<le> card (\<Union> ([H]\<^bsup>2\<^esup>))"
      using H subset_nsets_2 [OF \<open>card H \<ge> 2\<close>]
      by (smt (verit) equalityI less_irrefl linorder_not_le mem_Collect_eq Union_iff nsets_def subset_iff)
    moreover
    have "inj_on \<phi> (\<Union> ([H]\<^bsup>2\<^esup>))"
      using inj\<phi> unfolding inj_on_def ordered_nsets_2_eq by blast
    then have "card A = card (\<Union> ([H]\<^bsup>2\<^esup>))"
      using A_def card_image by blast
    ultimately show False
      using \<open>card A \<le> m\<close> by linarith
  next
    case 1
    then obtain H where H: "H \<subseteq> {..<m * n}" "finite H" "card H = Suc n" 
              and monoc: "\<And>u. u \<in> [H]\<^bsup>2\<^esup> \<Longrightarrow> f u = Suc 0"
      using i by (auto simp add: monochromatic_def nsets_def image_subset_iff)
    then have inj\<phi>: "inj_on \<phi> H"
      by (meson \<phi> bij_betw_def inj_on_subset)
    define A where "A \<equiv>  \<phi> ` \<Union> ([H]\<^bsup>2\<^esup>)"
    have "edge u v = 1" if "u \<in> A" "v \<in> A" "u \<noteq> v" for u v
      using that \<open>H \<subseteq> {..<m * n}\<close>  
      apply (clarsimp simp add: A_def edge_apply apply\<phi> all_edges_def nsets2_eq_all_edges subset_iff bij_betw_inv_into_left [OF \<phi>])
      by (rule monoc) auto
    then have snd_eq: "snd u \<noteq> snd v" if "u \<in> A" "v \<in> A" "u \<noteq> v" for u v
      by (smt (verit) edge_def prod.collapse prod.simps(2) zero_neq_one that)
    then have "inj_on snd A"
      by (meson inj_onI prod.expand)
    moreover have "snd ` A \<subseteq> {..<n}"
      by (force simp: A_def image_iff dest!: apply\<phi> [OF \<open>H \<subseteq> {..<m * n}\<close>])
    ultimately have "card A \<le> n"
      by (metis card_image card_lessThan card_mono finite_lessThan)
    have "card H \<ge> 2"
      using Suc_le_eq H monoc by fastforce
    have "Suc n \<le> card (\<Union> ([H]\<^bsup>2\<^esup>))"
      using H subset_nsets_2 [OF \<open>card H \<ge> 2\<close>]
      by (smt (verit) equalityI less_irrefl linorder_not_le mem_Collect_eq Union_iff nsets_def subset_iff)
    moreover
    have "inj_on \<phi> (\<Union> ([H]\<^bsup>2\<^esup>))"
      using inj\<phi> unfolding inj_on_def ordered_nsets_2_eq by blast
    then have "card A = card (\<Union> ([H]\<^bsup>2\<^esup>))"
      using A_def card_image by blast
    ultimately show False
      using \<open>card A \<le> n\<close> by linarith
  qed
qed

theorem RN_times_lower:
  shows "RN (Suc m) (Suc n) > m*n"                              
  using  Ramsey_number_times_lower is_Ramsey_number_RN partn_lst_greater_resource
  using linorder_le_less_linear by blast

corollary RN_times_lower':
  shows "\<lbrakk>m>0; n>0\<rbrakk> \<Longrightarrow> RN m n > (m-1)*(n-1)"
  using RN_times_lower gr0_conv_Suc by force                              

lemma RN_gt1:
  assumes "2 \<le> k" "3 \<le> l" shows "k < RN k l"
    using RN_times_lower' [of k l] RN_3plus[of l] assms  
  by (smt (verit, best) Suc_1 Suc_pred less_le_trans Suc_le_eq n_less_n_mult_m nat_less_le numeral_3_eq_3 One_nat_def zero_less_diff)

lemma RN_gt2:
  assumes "2 \<le> k" "3 \<le> l" shows "k < RN l k"
  by (simp add: RN_commute assms RN_gt1)

text \<open>Andrew's calculation for the Ramsey lower bound. Symmetric, so works for both colours\<close>
lemma Ramsey_lower_calc:
  fixes s::nat and t::nat and p::real
  assumes  "s \<ge> 3" "t \<ge> 3" "n > 4"
    and n: "real n \<le> exp ((real s - 1) * (real t - 1) / (2*(s+t)))"
  defines "p \<equiv> real s / (real s + real t)"
  shows "(n choose s) * p ^ (s choose 2) < 1 / fact s"
proof -
  have p01: "0<p" "p<1"
    using assms by (auto simp: p_def)
  have "exp ((real s - 1) * (real t - 1) / (2*(s+t)))  \<le> exp (t / (s+t)) powr ((s-1)/2)"
    using \<open>s \<ge> 3\<close> by (simp add: mult_ac divide_simps of_nat_diff)
  with assms p01 have "n \<le> exp (t / (s+t)) powr ((s-1)/2)"
    by linarith
  then have "n * p powr ((s-1)/2) \<le> (exp (t / (s+t)) * p) powr ((s-1)/2)"
    using \<open>0<p\<close> by (simp add: powr_mult)
  also have "... < 1"
  proof -
    have "exp (real t / real (s+t)) * p < 1"
    proof -
      have "p = 1 - t / (s+t)"
        using assms by (simp add: p_def divide_simps)
      also have "... < exp (- real t / real (s+t))"
        using assms by (simp add: exp_minus_greater)
      finally show ?thesis
        by (simp add: exp_minus divide_simps mult.commute)
    qed
    then show ?thesis
      using Diagonal.powr_less_one assms(1) p01(1) by fastforce
  qed
  finally have "n * p powr ((s-1)/2) < 1" .
  then have "(n * p powr ((s-1)/2)) ^ s < 1"
    using \<open>s \<ge> 3\<close> by (simp add: power_less_one_iff)
  then have B: "n^s * p ^ (s choose 2) < 1"
    using \<open>0<p\<close> \<open>4 < n\<close> \<open>s \<ge> 3\<close>
    by (simp add: choose_two_real powr_powr powr_mult of_nat_diff mult.commute flip: powr_realpow)
  have "(n choose s) * p ^ (s choose 2) \<le> n^s / fact s * p ^ (s choose 2)"
  proof (intro mult_right_mono)
    show "real (n choose s) \<le> real (n ^ s) / fact s"
      using binomial_fact_pow[of n s]  
      by (simp add: divide_simps mult.commute approximation_preproc_nat(13))
  qed (use p01 in auto)
  also have "... < 1 / fact s"
    using B by (simp add: divide_simps)
  finally show ?thesis .
qed


text \<open>trying Andrew's sketch\<close> (* And the final bound can be sharpened per Andrew's suggestion*)
proposition Ramsey_number_lower_off_diag:  
  fixes n s::nat  
  assumes "s \<ge> 3" "t \<ge> 3" and n: "real n \<le> exp ((real s - 1) * (real t - 1) / (2*(s+t)))"
  shows "\<not> IS_RN (TYPE (nat)) s t n"
proof
  assume con: "IS_RN (TYPE (nat)) s t n"
  then have is_RN: "is_Ramsey_number s t n"
    by (simp add: IS_RN_imp_partn_lst)
  then have "(s - 1) * (t - 1) < n"
    using RN_times_lower' [of s t] assms by (metis RN_le numeral_3_eq_3 order_less_le_trans zero_less_Suc)
  moreover have "2*2 \<le> (s - 1) * (t - 1)"
    using assms by (intro mult_mono) auto
  ultimately have "n > 4"
    by simp
  define W where "W \<equiv> {..<n}"              \<comment>\<open>defining a probability space\<close>
  have monoc: "\<And>F. \<exists>K\<subseteq>W. clique_indep s t K F"
    using con by (simp add: IS_RN_def W_def)
  have "finite W" and cardW: "card W = n"
    by (auto simp: W_def)
  have cardEW: "card (all_edges W) = n choose 2"
    by (simp add: W_def card_all_edges)
  define p where "p \<equiv> s / (s+t)"
  have p01: "0<p" "p<1"
    using assms by (auto simp: p_def)

  \<comment> \<open>Easier to represent the state as maps from edges to colours, not sets of coloured edges\<close>
   \<comment>\<open>colour the edges randomly\<close>
  define OMEGA :: "(nat set \<Rightarrow> nat) set" where "OMEGA \<equiv> (all_edges W) \<rightarrow>\<^sub>E {..<2}"
  have cardOMEGA: "card OMEGA = 2 ^ (n choose 2)"
    by (simp add: OMEGA_def \<open>finite W\<close> cardEW card_funcsetE finite_all_edges)
  define COLORD where "COLORD \<equiv> \<lambda>F. \<lambda>f::nat set \<Rightarrow> nat. \<lambda>c. (f -` {c}) \<inter> F"
  have COLORD: "COLORD F f c = {e \<in> F. f e = c}" for f c F
    by (auto simp: COLORD_def)
  have finite_COLORD[simp]: "finite (COLORD F f c)" if "finite F" for f c F
    using COLORD_def that by blast
  define PR where "PR \<equiv> \<lambda>F f. p ^ card (COLORD F f 0) * (1-p) ^ card (COLORD F f 1)"
  have PR01: "0 < PR U f" "PR U f \<le> 1" for U f \<comment> \<open>the inequality could be strict\<close>
    using \<open>0<p\<close> \<open>p<1\<close> by (auto simp: mult_le_one power_le_one PR_def cardOMEGA)
  define M where "M \<equiv> point_measure OMEGA (PR (all_edges W))"
  have space_eq: "space M = OMEGA"
    by (simp add: M_def space_point_measure)
  have sets_eq: "sets M = Pow OMEGA"
    by (simp add: M_def sets_point_measure)
  have fin_OMEGA[simp]: "finite OMEGA"
    by (simp add: OMEGA_def finite_PiE \<open>finite W\<close> finite_all_edges)

  have COLORD_insert: "COLORD (insert e F) f c = (if f e = c then insert e (COLORD F f c) else COLORD F f c)" 
    for f e c F
    by (auto simp add: COLORD)

  have eq2: "{..<2} = {0, Suc 0}"
    by (simp add: insert_commute lessThan_Suc numeral_2_eq_2)

  have sum_PR_1 [simp]: "sum (PR U) (U \<rightarrow>\<^sub>E {..<2}) = 1" if "finite U" for U
    using that
  proof (induction U)
    case empty
    then show ?case
      by (simp add: PR_def COLORD)
  next
    case (insert e F)
    then have [simp]: "e \<notin> COLORD F f c" "COLORD F (f(e := c)) c' = COLORD F f c'" for f c c'
      by (auto simp: COLORD)
    show ?case
      using insert
      apply (simp add: PR_def COLORD_insert)
      apply (simp add: PiE_insert_eq split: prod.split)
      apply (subst sum.reindex)
       apply (fastforce simp add: inj_on_def fun_eq_iff)
      apply (simp add: Information.sum_cartesian_product' card_insert_if eq2 mult_ac flip: sum_distrib_left)
      done
  qed

  interpret P: prob_space M
  proof
    have "sum (PR (all_edges W)) OMEGA = 1"
      using OMEGA_def sum_PR_1 \<open>finite W\<close> finite_all_edges by blast
    with PR01 show "emeasure M (space M) = 1" 
      unfolding M_def
      by (metis fin_OMEGA prob_space.emeasure_space_1 prob_space_point_measure zero_le
       ennreal_1 linorder_not_less nle_le sum_ennreal)
  qed

  \<comment>\<open>the event to avoid: monochromatic cliques, given @{term "K \<subseteq> W"};
      we are considering edges over the entire graph @{term W}\<close>
  define mono where "mono \<equiv> \<lambda>c K. {f \<in> OMEGA. all_edges K \<subseteq> COLORD (all_edges W) f c}"
  have mono_ev: "mono c K \<in> P.events" if "c<2" for K c
    by (auto simp add: sets_eq mono_def OMEGA_def)
  have mono_sub_\<Omega>: "mono c K \<subseteq> OMEGA" if "c<2" for K c
    using mono_ev sets_eq that by auto

  have emeasure_eq: "emeasure M C = (if C \<subseteq> OMEGA then (\<Sum>a\<in>C. ennreal (PR (all_edges W) a)) else 0)" for C
    by (simp add: M_def emeasure_notin_sets emeasure_point_measure_finite sets_point_measure)

  define pc where "pc \<equiv> \<lambda>c::nat. if c=0 then p else 1-p"
  have COLORD_upd: "COLORD F (\<lambda>t\<in>F. if t \<in> G then c else f t) c' 
        = (if c=c' then G \<union> COLORD (F-G) f c' else COLORD (F-G) f c')" if "G \<subseteq> F" for F G f c c'
    using that by (auto simp add: COLORD)

  have prob_mono: "P.prob (mono c K) = (pc c ^ (r choose 2))"  
    if "K \<in> nsets W r" "c<2" for r K c
  proof -
    have \<section>: "K \<subseteq> W" "finite K" "card K = r"
      using that by (auto simp: nsets_def)
    have "r \<le> n"
      using "\<section>" \<open>finite W\<close> cardW card_mono by blast
    then have sn2: "(r choose 2) \<le> (n choose 2)"
      using binomial_mono by auto

    have *: "{f \<in> OMEGA. all_edges K \<subseteq> COLORD (all_edges W) f c} = 
          (\<Union>g \<in> (all_edges W - all_edges K) \<rightarrow>\<^sub>E {..<2}. {\<lambda>t \<in> all_edges W. if t \<in> all_edges K then c else g t})"
      (is "?L = ?R")
    proof
      show "?L \<subseteq> ?R"
      proof clarsimp
        fix f
        assume f: "f \<in> OMEGA" and c: "all_edges K \<subseteq> COLORD (all_edges W) f c"
        show "\<exists>g\<in>all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2}. f = (\<lambda>t\<in>all_edges W. if t \<in> all_edges K then c else g t)"
          apply (rule_tac x="restrict f (all_edges W - all_edges K)" in bexI)
           apply (rule ext)
          using c f
           apply (simp add: OMEGA_def COLORD subset_iff)
           apply blast
          using OMEGA_def f by auto
      qed
      show "?R \<subseteq> ?L"
        using that all_edges_mono[OF \<open>K \<subseteq> W\<close>]
        by (auto simp add: COLORD OMEGA_def nsets_def PiE_iff)
    qed

    have [simp]: "card (all_edges K \<union> COLORD (all_edges W - all_edges K) f c)
                = (r choose 2) + card (COLORD (all_edges W - all_edges K) f c)" for f c
      using \<section> \<open>finite W\<close>
      by (subst card_Un_disjoint) (auto simp: finite_all_edges COLORD card_all_edges)

    have **: "PR (all_edges W) (\<lambda>t \<in> all_edges W. if t \<in> all_edges K then c else f t) 
        = pc c ^ (r choose 2) * PR (all_edges W - all_edges K) f" 
      if "f \<in> all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2}" for f
      using that all_edges_mono[OF \<open>K \<subseteq> W\<close>] p01 \<open>c<2\<close> \<section>
      by (simp add: PR_def COLORD_upd pc_def power_add)

    have A: "(\<Sum>F\<in>all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2}. (pc c ^ (r choose 2) * PR (all_edges W - all_edges K) F)) 
              = (pc c ^ (r choose 2))"
      by (simp add: ** \<open>finite W\<close> finite_all_edges flip: sum_distrib_left)
    have "emeasure M (mono c K) = ennreal (pc c ^ (r choose 2))"
      using that p01
      apply (simp add: emeasure_eq mono_sub_\<Omega>)
      apply (simp add: mono_def *)
      apply (subst sum.UNION_disjoint_family)
         apply (simp add: \<open>finite W\<close> finite_PiE finite_all_edges)
        apply blast
       apply (simp add: disjoint_family_on_def)
       apply (auto simp: fun_eq_iff)[1]
       apply (metis DiffE PiE_E)
      apply (simp add: **  )
      apply (subst sum_ennreal)
       apply (simp add: PR_def pc_def)
      using A by presburger
    then show ?thesis 
      using p01 that by (simp add: measure_eq_emeasure_eq_ennreal pc_def)
  qed

  define Reds where "Reds \<equiv> (\<Union>K \<in> nsets W s. mono 0 K)"
  define Blues where "Blues \<equiv> (\<Union>K \<in> nsets W t. mono 1 K)"
  have Uev: "\<Union> (mono c ` [W]\<^bsup>r\<^esup>) \<in> P.events" for c r
    by (simp add: local.mono_def sets_eq subset_iff)
  then have "Reds \<in> P.events" "Blues \<in> P.events"
    by (auto simp: Reds_def Blues_def)
  have prob_0: "P.prob Reds < 1/2" 
  proof -
    have "P.prob Reds \<le> (\<Sum>K \<in> nsets W s. P.prob (mono 0 K))"
      by (simp add: Reds_def \<open>finite W\<close> finite_imp_finite_nsets measure_UNION_le mono_ev)
    also have "... \<le> (n choose s) * (p ^ (s choose 2))"
      by (simp add: prob_mono pc_def cardW)
    also have "... < 1 / fact s"
      using Ramsey_lower_calc \<open>4 < n\<close> assms(1) assms(2) n p_def by auto
    also have "... < 1/2"
      using \<open>s \<ge> 3\<close>
      apply (simp add: divide_simps eval_nat_numeral)
      by (metis Suc_le_lessD fact_2 fact_less_mono numerals(2) pos2)
    finally show ?thesis .
  qed
  moreover
  have prob_1: "P.prob Blues < 1/2" 
  proof -
    have "1-p = real t / (real t + real s)"
      using \<open>s \<ge> 3\<close> by (simp add: p_def divide_simps)
    with assms have *: "(n choose t) * (1-p) ^ (t choose 2) < 1 / fact t"
      by (metis Ramsey_lower_calc add.commute mult.commute \<open>4 < n\<close>) 
    have "P.prob Blues \<le> (\<Sum>K \<in> nsets W t. P.prob (mono 1 K))"
      by (simp add: Blues_def \<open>finite W\<close> finite_imp_finite_nsets measure_UNION_le mono_ev)
    also have "... \<le> (n choose t) * ((1-p) ^ (t choose 2))"
      by (simp add: prob_mono pc_def cardW)
    also have "... < 1 / fact t"
      by (simp add: "*")
    also have "... < 1/2"
      using \<open>t \<ge> 3\<close>
      apply (simp add: divide_simps eval_nat_numeral)
      by (metis Suc_le_lessD fact_2 fact_less_mono numerals(2) pos2)
    finally show ?thesis .
  qed
  ultimately have "P.prob (Reds \<union> Blues) < 1/2 + 1/2"
    using P.finite_measure_subadditive \<open>Blues \<in> P.events\<close> \<open>Reds \<in> P.events\<close> by fastforce
  then obtain F where F: "F \<in> OMEGA - (Reds \<union> Blues)"
    by (metis Blues_def Diff_iff P.prob_space Pow_iff Reds_def Un_subset_iff Uev equalityI field_sum_of_halves less_irrefl sets_eq space_eq subsetI)
  have False if "i < 2" "H \<in> [W]\<^bsup>([s, t] ! i)\<^esup>" "F ` [H]\<^bsup>2\<^esup> \<subseteq> {i}" for i H
  proof -
    have "\<not> all_edges H \<subseteq> {e \<in> all_edges W. F e = 0}" "\<not> all_edges H \<subseteq> {e \<in> all_edges W. F e = 1}"
      using F that
      by (auto simp: less_2_cases_iff nsets2_eq_all_edges OMEGA_def Reds_def Blues_def mono_def COLORD image_subset_iff)
    moreover have "H \<subseteq> W"
      using that by (auto simp: nsets_def)
    ultimately show False
      using that all_edges_mono [OF \<open>H \<subseteq> W\<close>] by (auto simp: less_2_cases_iff nsets2_eq_all_edges)
  qed
  moreover have "F \<in> [{..<n}]\<^bsup>2\<^esup> \<rightarrow> {..<2}"
    using F apply (auto simp: OMEGA_def)
    by (metis PiE_E W_def lessThan_iff nsets2_eq_all_edges)
  ultimately show False
    using is_RN \<open>finite W\<close>
    apply (simp add: W_def partn_lst_def)
    by (metis numerals(2)) 
qed

end

section \<open>Preliminary definitions\<close>

definition Neighbours :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "Neighbours \<equiv> \<lambda>E x. {y. {x,y} \<in> E}"

lemma in_Neighbours_iff: "y \<in> Neighbours E x \<longleftrightarrow> {x,y} \<in> E"
  by (simp add: Neighbours_def)

lemma (in fin_sgraph) not_own_Neighbour: "E' \<subseteq> E \<Longrightarrow> x \<notin> Neighbours E' x"
  by (force simp: Neighbours_def singleton_not_edge)

section \<open>Preliminaries on graphs\<close>

context ulgraph
begin

text \<open>The set of \emph{undirected} edges between two sets\<close>
definition all_edges_betw_un :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "all_edges_betw_un X Y \<equiv> {{x, y}| x y. x \<in> X \<and> y \<in> Y \<and> {x, y} \<in> E}"

lemma all_edges_betw_un_commute1: "all_edges_betw_un X Y \<subseteq> all_edges_betw_un Y X"
  by (smt (verit, del_insts) Collect_mono all_edges_betw_un_def insert_commute)

lemma all_edges_betw_un_commute: "all_edges_betw_un X Y = all_edges_betw_un Y X"
  by (simp add: all_edges_betw_un_commute1 subset_antisym)

lemma all_edges_betw_un_iff_mk_edge: "all_edges_betw_un X Y = mk_edge ` all_edges_between X Y"
  using all_edges_between_set all_edges_betw_un_def by presburger

lemma all_uedges_betw_subset: "all_edges_betw_un X Y \<subseteq> E"
  by (auto simp add: all_edges_betw_un_def)

lemma all_uedges_betw_I: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> {x, y} \<in> E \<Longrightarrow> {x, y} \<in> all_edges_betw_un X Y"
  by (auto simp add: all_edges_betw_un_def)

lemma all_edges_betw_un_subset: "all_edges_betw_un X Y \<subseteq> Pow (X\<union>Y)"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_rem_wf: "all_edges_betw_un X Y = all_edges_betw_un (X \<inter> V) (Y \<inter> V)"
  using wellformed by (simp add: all_edges_betw_un_def) blast 

lemma all_edges_betw_un_empty [simp]:
  "all_edges_betw_un {} Z = {}" "all_edges_betw_un Z {} = {}"
  by (auto simp: all_edges_betw_un_def)

lemma card_all_uedges_betw_le: 
  assumes "finite X" "finite Y"
  shows "card (all_edges_betw_un X Y) \<le> card (all_edges_between X Y)"
  by (simp add: all_edges_betw_un_iff_mk_edge assms card_image_le finite_all_edges_between)

lemma max_all_edges_betw_un: 
  assumes "finite X" "finite Y"
  shows "card (all_edges_betw_un X Y) \<le> card X * card Y"
  by (meson assms card_all_uedges_betw_le max_all_edges_between order_trans)

lemma all_edges_betw_un_insert1:
  "all_edges_betw_un (insert v X) Y = ({{v, y}| y. y \<in> Y} \<inter> E) \<union> all_edges_betw_un X Y"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_insert2:
  "all_edges_betw_un X (insert v Y) = ({{x, v}| x. x \<in> X} \<inter> E) \<union> all_edges_betw_un X Y"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_Un1:
  "all_edges_betw_un (X \<union> Y) Z = all_edges_betw_un X Z \<union> all_edges_betw_un Y Z"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_Un2:
  "all_edges_betw_un X (Y \<union> Z) = all_edges_betw_un X Y \<union> all_edges_betw_un X Z"
  by (auto simp: all_edges_betw_un_def)

lemma finite_all_edges_betw_un:
  assumes "finite X" "finite Y"
  shows "finite (all_edges_betw_un X Y)"
  by (simp add: all_edges_betw_un_iff_mk_edge assms finite_all_edges_between)

lemma all_edges_betw_un_Union1:
  "all_edges_betw_un (Union \<X>) Y = (\<Union>X\<in>\<X>. all_edges_betw_un X Y)"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_Union2:
  "all_edges_betw_un X (Union \<Y>) = (\<Union>Y\<in>\<Y>. all_edges_betw_un X Y)"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_mono1:
  "Y \<subseteq> Z \<Longrightarrow> all_edges_betw_un Y X \<subseteq> all_edges_betw_un Z X"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_mono2:
  "Y \<subseteq> Z \<Longrightarrow> all_edges_betw_un X Y \<subseteq> all_edges_betw_un X Z"
  by (auto simp: all_edges_betw_un_def)

text \<open>this notion, mentioned on Page 3, is a little vague: "a graph on vertex set @{term"S \<union> T"} 
that contains all edges incident to @{term"S"}"\<close>
definition book :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "book \<equiv> \<lambda>S T F. disjnt S T \<and> all_edges_betw_un S (S\<union>T) \<subseteq> F"

lemma book_empty [simp]: "book {} T F"
  by (auto simp: book_def)

lemma book_imp_disjnt: "book S T F \<Longrightarrow> disjnt S T"
  by (auto simp: book_def)

end

context sgraph
begin

declare singleton_not_edge [simp]

lemma book_insert: 
  "book (insert v S) T F \<longleftrightarrow> book S T F \<and> v \<notin> T \<and> all_edges_betw_un {v} (S \<union> T) \<subseteq> F"
  by (auto simp: book_def all_edges_betw_un_insert1 all_edges_betw_un_insert2 all_edges_betw_un_Un2 insert_commute subset_iff)

text \<open>Cliques of a given number of vertices; the definition of clique from Ramsey is used\<close>

definition size_clique :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "size_clique p K F \<equiv> card K = p \<and> clique K F \<and> K \<subseteq> V"

lemma size_clique_all_edges: "size_clique p K F \<Longrightarrow> all_edges K \<subseteq> F"
  by (auto simp: size_clique_def all_edges_def clique_def card_2_iff)

lemma indep_iff_clique: "K \<subseteq> V \<Longrightarrow> indep K F \<longleftrightarrow> clique K (all_edges V - F)"
  by (auto simp: indep_def clique_def all_edges_def)

end


section \<open>Locale for the parameters of the construction\<close>

type_synonym 'a config = "'a set \<times> 'a set \<times> 'a set \<times> 'a set"

locale Diagonal = fin_sgraph +   \<comment> \<open>finite simple graphs (no loops)\<close>
  fixes k::nat       \<comment> \<open>red limit\<close>
  fixes l::nat       \<comment> \<open>blue limit\<close>
  assumes l_large: "6 \<le> l" and lk: "l \<le> k" \<comment> \<open>they should be "sufficiently large"\<close>
      (* in particular, need l ^ (2/3) \<ge> 3*)
  assumes complete: "E \<equiv> all_edges V"
  fixes Red Blue :: "'a set set"
  assumes Red_not_Blue: "Red \<noteq> Blue"
  assumes part_RB: "partition_on E {Red,Blue}"
  assumes no_Red_clique: "\<not> (\<exists>K. size_clique k K Red)"
  assumes no_Blue_clique: "\<not> (\<exists>K. size_clique l K Blue)"
  \<comment> \<open>the following are local to the program and possibly require their own locale\<close>
  fixes X0 :: "'a set" and Y0 :: "'a set"    \<comment> \<open>initial values\<close>
  assumes XY0: "disjnt X0 Y0" "X0 \<subseteq> V" "Y0 \<subseteq> V"
  fixes \<mu>::real
  assumes \<mu>01: "0 < \<mu>" "\<mu> < 1"
  assumes infinite_UNIV: "infinite (UNIV::'a set)"
begin

abbreviation "nV \<equiv> card V"

lemma RB_nonempty: "Red \<noteq> {}" "Blue \<noteq> {}"
  using part_RB partition_onD3 by auto

lemma Red_E: "Red \<subset> E" and Blue_E: "Blue \<subset> E" 
  using part_RB Red_not_Blue by (auto simp: partition_on_def disjnt_iff pairwise_def)

lemma disjnt_Red_Blue: "disjnt Red Blue"
  by (metis Red_not_Blue pairwise_insert part_RB partition_on_def singletonI)

lemma Red_Blue_all: "Red \<union> Blue = all_edges V"
  using part_RB complete by (auto simp: partition_on_def)

lemma Blue_eq: "Blue = all_edges V - Red"
  using disjnt_Red_Blue Red_Blue_all complete wellformed
  by (auto simp: disjnt_iff)

lemma nontriv: "E \<noteq> {}"
  using Red_E bot.extremum_strict by blast

lemma kn0: "k > 0"
  using lk l_large by auto

lemma not_Red_Neighbour [simp]: "x \<notin> Neighbours Red x" and not_Blue_Neighbour [simp]: "x \<notin> Neighbours Blue x"
  using Red_E Blue_E not_own_Neighbour by auto

lemma Neighbours_Red_Blue: 
  assumes "x \<in> V" 
  shows "Neighbours Red x = V - insert x (Neighbours Blue x)"
  using Red_E assms by (auto simp: Blue_eq Neighbours_def complete all_edges_def)

lemma clique_imp_all_edges_betw_un: "clique K F \<Longrightarrow> all_edges_betw_un K K \<subseteq> F"
  by (force simp: clique_def all_edges_betw_un_def)

lemma all_edges_betw_un_iff_clique:
  assumes "K \<subseteq> V"
  shows "all_edges_betw_un K K \<subseteq> F \<longleftrightarrow> clique K F"
proof
  assume \<section>: "all_edges_betw_un K K \<subseteq> F"
  show "clique K F"
    unfolding clique_def 
  proof (intro strip)
    fix v w
    assume "v \<in> K" "w \<in> K" "v \<noteq> w"
    with assms have "{v, w} \<in> E"
      by (force simp add: complete all_edges_def)
    then show "{v, w} \<in> F"
      using "\<section>" \<open>v \<in> K\<close> \<open>w \<in> K\<close> all_uedges_betw_I by blast
  qed
qed (force simp: clique_def all_edges_betw_un_def)

lemma indep_Red_iff_clique_Blue: "K \<subseteq> V \<Longrightarrow> indep K Red \<longleftrightarrow> clique K Blue"
  using Blue_eq by auto

lemma Red_Blue_RN:
  fixes X :: "'a set"
  assumes "card X \<ge> RN m n" "X\<subseteq>V"
  shows "\<exists>K \<subseteq> X. size_clique m K Red \<or> size_clique n K Blue"
  using partn_lst_imp_IS_RN [OF is_Ramsey_number_RN [of m n]]  assms indep_Red_iff_clique_Blue 
  unfolding IS_RN_def size_clique_def clique_indep_def
  by (metis finV finite_subset subset_eq)


text \<open>for calculating the perimeter p\<close>
definition "gen_density \<equiv> \<lambda>C X Y. card (C \<inter> all_edges_betw_un X Y) / (card X * card Y)"

abbreviation "red_density X Y \<equiv> gen_density Red X Y"
abbreviation "blue_density X Y \<equiv> gen_density Blue X Y"

lemma red_density_ge0: "red_density X Y \<ge> 0"
  by (auto simp: gen_density_def)

lemma red_le_edge_density: "red_density X Y \<le> edge_density X Y"
proof (cases "finite X \<and> finite Y")
  case True
  then have "card (Red \<inter> all_edges_betw_un X Y) \<le> card (all_edges_betw_un X Y)"
    by (simp add: all_edges_betw_un_iff_mk_edge card_mono finite_all_edges_between')
  also have "\<dots> \<le> card (all_edges_between X Y)"
    by (simp add: all_edges_betw_un_iff_mk_edge card_image_le finite_all_edges_between')
  finally show ?thesis
    by (simp add: gen_density_def edge_density_def divide_right_mono)
qed (auto simp: gen_density_def edge_density_def)

lemma red_density_le1: "red_density X Y \<le> 1"
  by (meson edge_density_le1 order_trans red_le_edge_density)

definition Weight :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real" where
  "Weight \<equiv> \<lambda>X Y x y. inverse (card Y) * (card (Neighbours Red x \<inter> Neighbours Red y \<inter> Y)
                      - red_density X Y * card (Neighbours Red x \<inter> Y))"

definition weight :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> real" where
  "weight \<equiv> \<lambda>X Y x. \<Sum>y \<in> X-{x}. Weight X Y x y"

definition "p0 \<equiv> red_density X0 Y0"

definition "epsk \<equiv> k powr (-1/4)"

definition "q \<equiv> \<lambda>h. p0 + ((1 + epsk)^h - 1) / k"

definition "hgt \<equiv> \<lambda>p. LEAST h. p \<le> q h \<and> h>0"

lemma q0 [simp]: "q 0 = p0"
  by (simp add: q_def)

lemma p0_01: "0 \<le> p0" "p0 \<le> 1"
  by (simp_all add: p0_def red_density_ge0 red_density_le1)

lemma epsk_n0: "epsk > 0"
  by (auto simp: epsk_def kn0)

lemma height_exists:
  assumes "0 < p" and "p < 1"
  obtains h where "p \<le> q h"
proof -
  let ?h = "nat \<lceil>k / epsk\<rceil>"  \<comment>\<open>larger than the bound suggested in the paper\<close>
  have "k+1 \<le> (1 + epsk) ^ ?h"
    using linear_plus_1_le_power [of epsk ?h] epsk_n0
    by (smt (verit, best) mult_imp_less_div_pos of_nat_1 of_nat_add of_nat_ceiling)
  then have "p \<le> q ?h"
    unfolding q_def
    using kn0 assms p0_01
    by (smt (verit, best) le_divide_eq_1_pos of_nat_0_less_iff of_nat_1 of_nat_add)
  then show thesis ..
qed

lemma q_Suc_diff: "q(Suc h) - q h = epsk * (1 + epsk)^h / k"
  by (simp add: q_def field_split_simps)

definition "alpha \<equiv> \<lambda>h. q h - q (h-1)"

definition all_incident_edges :: "'a set \<Rightarrow> 'a set set" where
    "all_incident_edges \<equiv> \<lambda>A. \<Union>v\<in>A. incident_edges v"

lemma all_incident_edges_Un [simp]: "all_incident_edges (A\<union>B) = all_incident_edges A \<union> all_incident_edges B"
  by (auto simp: all_incident_edges_def)

subsection \<open>State invariants\<close>

definition "V_state \<equiv> \<lambda>(X,Y,A,B). X\<subseteq>V \<and> Y\<subseteq>V \<and> A\<subseteq>V \<and> B\<subseteq>V"

definition "disjoint_state \<equiv> \<lambda>(X,Y,A,B). disjnt X Y \<and> disjnt X A \<and> disjnt X B \<and> disjnt Y A \<and> disjnt Y B \<and> disjnt A B"

text \<open>previously had all edges incident to A, B\<close>
definition "RB_state \<equiv> \<lambda>(X,Y,A,B). all_edges_betw_un A A \<subseteq> Red \<and> all_edges_betw_un A (X \<union> Y) \<subseteq> Red
             \<and> all_edges_betw_un B (B \<union> X) \<subseteq> Blue"

definition "valid_state \<equiv> \<lambda>U. V_state U \<and> disjoint_state U \<and> RB_state U"

definition "termination_condition \<equiv> \<lambda>X Y. card X \<le> RN k (nat \<lceil>l powr (3/4)\<rceil>) \<or> red_density X Y \<le> 1/k"

lemma 
  assumes "V_state(X,Y,A,B)" 
  shows finX: "finite X" and finY: "finite Y" and finA: "finite A" and finB: "finite B"
  using V_state_def assms finV finite_subset by auto

subsection \<open>Degree regularisation\<close>

definition "red_dense \<equiv> \<lambda>Y p x. card (Neighbours Red x \<inter> Y) \<ge> p - epsk powr (-1/2) * alpha (hgt p) * card Y"

definition "X_degree_reg \<equiv>  \<lambda>X Y. {x \<in> X. red_dense Y (red_density X Y) x}"

definition "degree_reg \<equiv> \<lambda>(X,Y,A,B). (X_degree_reg X Y, Y, A, B)"

lemma X_degree_reg_subset: "X_degree_reg X Y \<subseteq> X"
  by (auto simp: X_degree_reg_def)

lemma degree_reg_V_state: "V_state U \<Longrightarrow> V_state (degree_reg U)"
  by (auto simp add: degree_reg_def X_degree_reg_def V_state_def)

lemma degree_reg_disjoint_state: "disjoint_state U \<Longrightarrow> disjoint_state (degree_reg U)"
  by (auto simp add: degree_reg_def X_degree_reg_def disjoint_state_def disjnt_iff)

lemma degree_reg_RB_state: "RB_state U \<Longrightarrow> RB_state (degree_reg U)"
  apply (simp add: degree_reg_def RB_state_def all_edges_betw_un_Un2 split: prod.split prod.split_asm)
  by (meson X_degree_reg_subset all_edges_betw_un_mono2 dual_order.trans)

lemma degree_reg_valid_state: "valid_state U \<Longrightarrow> valid_state (degree_reg U)"
  by (simp add: degree_reg_RB_state degree_reg_V_state degree_reg_disjoint_state valid_state_def)

subsection \<open>Big blue steps: code\<close>

definition bluish :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "bluish \<equiv> \<lambda>X x. card (Neighbours Blue x \<inter> X) \<ge> \<mu> * card X"

definition many_bluish :: "'a set \<Rightarrow> bool" where
  "many_bluish \<equiv> \<lambda>X. card {x\<in>X. bluish X x} \<ge> RN k (nat \<lceil>l powr (2/3)\<rceil>)"

definition "good_blue_book \<equiv> \<lambda>X::'a set. \<lambda>(S,T). book S T Blue \<and> S\<subseteq>X \<and> T\<subseteq>X \<and> card T \<ge> (\<mu> ^ card S) * card X / 2"

lemma lpowr23_ge3: "nat \<lceil>l powr (2/3)\<rceil> \<ge> 3"
proof -
  have "(3::real) \<le> 6 powr (2/3)"
    by (approximation 10)
  also have "\<dots> \<le> l powr (2/3)"
    by (simp add: l_large powr_mono2)
  finally show ?thesis
    by (simp add: le_natceiling_iff)
qed

lemma ex_good_blue_book: "good_blue_book X ({}, X)"
  by (simp add: good_blue_book_def)

lemma bounded_good_blue_book: "\<lbrakk>good_blue_book X (S,T); V_state(X,Y,A,B)\<rbrakk> \<Longrightarrow> card S \<le> card X"
  by (simp add: card_mono finX good_blue_book_def)

definition best_blue_book_card :: "'a set \<Rightarrow> nat" where
  "best_blue_book_card \<equiv> \<lambda>X. GREATEST s. \<exists>S T. good_blue_book X (S,T) \<and> s = card S"

lemma best_blue_book_is_best: "\<lbrakk>good_blue_book X (S,T); V_state(X,Y,A,B)\<rbrakk> \<Longrightarrow> card S \<le> best_blue_book_card X"
  unfolding best_blue_book_card_def
  by (smt (verit) Greatest_le_nat bounded_good_blue_book)

lemma ex_best_blue_book: "V_state(X,Y,A,B) \<Longrightarrow> \<exists>S T. good_blue_book X (S,T) \<and> card S = best_blue_book_card X"
  unfolding best_blue_book_card_def
  by (smt (verit, del_insts) GreatestI_ex_nat bounded_good_blue_book ex_good_blue_book)

definition "choose_blue_book \<equiv> \<lambda>(X,Y,A,B). @(S,T). good_blue_book X (S,T) \<and> card S = best_blue_book_card X"

lemma choose_blue_book_works: 
  "\<lbrakk>V_state(X,Y,A,B); (S,T) = choose_blue_book(X,Y,A,B)\<rbrakk> 
  \<Longrightarrow> good_blue_book X (S,T) \<and> card S = best_blue_book_card X"
  unfolding choose_blue_book_def
  using someI_ex [OF ex_best_blue_book]
  by (metis (mono_tags, lifting) case_prod_conv someI_ex)


lemma choose_blue_book_subset: 
  "\<lbrakk>V_state(X,Y,A,B); (S,T) = choose_blue_book(X,Y,A,B)\<rbrakk> \<Longrightarrow> T \<subseteq> X"
  using choose_blue_book_works good_blue_book_def by fastforce


text \<open>expressing the complicated preconditions inductively\<close>
inductive big_blue
  where "\<lbrakk>many_bluish X; good_blue_book X (S,T); card S = best_blue_book_card X\<rbrakk> \<Longrightarrow> big_blue (X,Y,A,B) (T, Y, A, B\<union>S)"

lemma big_blue_V_state: "\<lbrakk>big_blue U U'; V_state U\<rbrakk> \<Longrightarrow> V_state U'"
  by (force simp: good_blue_book_def V_state_def elim!: big_blue.cases)

lemma big_blue_disjoint_state: "\<lbrakk>big_blue U U'; disjoint_state U\<rbrakk> \<Longrightarrow> disjoint_state U'"
  apply (clarsimp simp add: good_blue_book_def disjoint_state_def elim!: big_blue.cases)
  by (metis book_imp_disjnt disjnt_subset1 disjnt_sym)

lemma big_blue_RB_state: "\<lbrakk>big_blue U U'; RB_state U\<rbrakk> \<Longrightarrow> RB_state U'"
  apply (clarsimp simp add: good_blue_book_def book_def RB_state_def all_edges_betw_un_Un1 all_edges_betw_un_Un2 elim!: big_blue.cases)
  by (metis all_edges_betw_un_commute all_edges_betw_un_mono1 le_supI2 sup.orderE)

lemma big_blue_valid_state: "\<lbrakk>big_blue U U'; valid_state U\<rbrakk> \<Longrightarrow> valid_state U'"
  by (meson big_blue_RB_state big_blue_V_state big_blue_disjoint_state valid_state_def)

subsection \<open>The central vertex\<close>

definition central_vertex :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "central_vertex \<equiv> \<lambda>X x. x \<in> X \<and> card (Neighbours Blue x \<inter> X) \<le> \<mu> * card X"

lemma ex_central_vertex:
  assumes "\<not> termination_condition X Y" "\<not> many_bluish X"
  shows "\<exists>x. central_vertex X x"
proof -
  have *: "real l powr (2/3) \<le> real l powr (3/4)"
    using l_large powr_mono by force
  then have "card {x \<in> X. bluish X x} < card X"
    using assms RN_mono
    unfolding termination_condition_def many_bluish_def not_le
    by (smt (verit, ccfv_SIG) linorder_not_le nat_ceiling_le_eq of_nat_le_iff)
  then obtain x where "x \<in> X" "\<not> bluish X x"
    by (metis (mono_tags, lifting) mem_Collect_eq nat_neq_iff subsetI subset_antisym)
  then show ?thesis
    by (meson bluish_def central_vertex_def linorder_linear)
qed

lemma finite_central_vertex_set: "V_state(X,Y,A,B) \<Longrightarrow> finite {x. central_vertex X x}"
  by (simp add: central_vertex_def finX)

definition max_central_vx :: "'a set \<Rightarrow> 'a set \<Rightarrow> real" where
  "max_central_vx \<equiv> \<lambda>X Y. Max (weight X Y ` {x. central_vertex X x})"

lemma central_vx_is_best: "\<lbrakk>central_vertex X x; V_state(X,Y,A,B)\<rbrakk> \<Longrightarrow> weight X Y x \<le> max_central_vx X Y"
  unfolding max_central_vx_def by (simp add: finite_central_vertex_set)

lemma ex_best_central_vx: 
  "\<lbrakk>\<not> termination_condition X Y; \<not> many_bluish X; V_state(X,Y,A,B)\<rbrakk> 
  \<Longrightarrow> \<exists>x. central_vertex X x \<and> weight X Y x = max_central_vx X Y"
  unfolding max_central_vx_def
  by (metis empty_iff ex_central_vertex finite_central_vertex_set mem_Collect_eq obtains_MAX)

text \<open>it's necessary to make a specific choice; a relational treatment might allow different vertices 
  to be chosen, making a nonsense of the choice between steps 4 and 5\<close>
definition "choose_central_vx \<equiv> \<lambda>(X,Y,A,B). @x. central_vertex X x \<and> weight X Y x = max_central_vx X Y"

lemma choose_central_vx_works: 
  "\<lbrakk>\<not> termination_condition X Y; \<not> many_bluish X; V_state(X,Y,A,B)\<rbrakk> 
  \<Longrightarrow> central_vertex X (choose_central_vx (X,Y,A,B)) \<and> weight X Y (choose_central_vx (X,Y,A,B)) = max_central_vx X Y"
  unfolding choose_central_vx_def
  using someI_ex [OF ex_best_central_vx] by force

lemma choose_central_vx_X: 
  "\<lbrakk>\<not> termination_condition X Y; \<not> many_bluish X; V_state(X,Y,A,B)\<rbrakk>  \<Longrightarrow> choose_central_vx (X,Y,A,B) \<in> X"
  using central_vertex_def choose_central_vx_works by presburger

subsection \<open>Red step\<close>

definition "reddish \<equiv> \<lambda>X Y p x. red_density (Neighbours Red x \<inter> X) (Neighbours Red x \<inter> Y) \<ge> p - alpha (hgt p)"

inductive red_step
  where "\<lbrakk>reddish X Y (red_density X Y) x; x = choose_central_vx (X,Y,A,B)\<rbrakk> 
         \<Longrightarrow> red_step (X,Y,A,B) (Neighbours Red x \<inter> X, Neighbours Red x \<inter> Y, insert x A, B)"

lemma red_step_V_state: 
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish X" "V_state (X,Y,A,B)"
  shows "V_state U'"
proof -
  have "choose_central_vx (X, Y, A, B) \<in> V"
    using assms choose_central_vx_X  by (simp add: V_state_def subset_eq)
  with assms show ?thesis
    by (auto simp add: V_state_def elim!: red_step.cases)
qed

lemma red_step_disjoint_state:
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish X" "V_state (X,Y,A,B)" "disjoint_state (X,Y,A,B)"
  shows "disjoint_state U'"
proof -
  have "choose_central_vx (X, Y, A, B) \<in> X"
    using assms choose_central_vx_X by (simp add: V_state_def)
  with assms show ?thesis
    by (auto simp add: disjoint_state_def disjnt_iff not_own_Neighbour elim!: red_step.cases)
qed

lemma red_step_RB_state: 
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish X" "V_state (X,Y,A,B)" "RB_state (X,Y,A,B)"
  shows "RB_state U'"
proof -
  define x where "x \<equiv> choose_central_vx (X, Y, A, B)"
  have "x \<in> X"
    using assms choose_central_vx_X by (simp add: x_def V_state_def)
  have A: "all_edges_betw_un (insert x A) (insert x A) \<subseteq> Red"
    if "all_edges_betw_un A A \<subseteq> Red" "all_edges_betw_un A (X \<union> Y) \<subseteq> Red"
    using that \<open>x \<in> X\<close> all_edges_betw_un_commute 
    by (auto simp: all_edges_betw_un_insert2 all_edges_betw_un_Un2 intro!: all_uedges_betw_I)
  have B1: "all_edges_betw_un (insert x A) (Neighbours Red x \<inter> X) \<subseteq> Red"
    if "all_edges_betw_un A X \<subseteq> Red"
    using that \<open>x \<in> X\<close> by (force simp:  all_edges_betw_un_def in_Neighbours_iff)
  have B2: "all_edges_betw_un (insert x A) (Neighbours Red x \<inter> Y) \<subseteq> Red"
    if "all_edges_betw_un A Y \<subseteq> Red"
    using that \<open>x \<in> X\<close> by (force simp:  all_edges_betw_un_def in_Neighbours_iff)
  from assms A B1 B2 show ?thesis
    apply (clarsimp simp: RB_state_def simp flip: x_def   elim!: red_step.cases)
    by (metis Int_Un_eq(2) Un_subset_iff all_edges_betw_un_Un2)
qed

lemma red_step_valid_state: 
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish X" "valid_state (X,Y,A,B)"
  shows "valid_state U'"
  by (meson assms red_step_RB_state red_step_V_state red_step_disjoint_state valid_state_def)

subsection \<open>Density-boost step\<close>

inductive density_boost
  where "\<lbrakk>\<not> reddish X Y (red_density X Y) x; x = choose_central_vx (X,Y,A,B)\<rbrakk> 
         \<Longrightarrow> density_boost (X,Y,A,B) (Neighbours Blue x \<inter> X, Neighbours Red x \<inter> Y, A, insert x B)"


lemma density_boost_V_state: 
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish X" "V_state (X,Y,A,B)"
  shows "V_state U'"
proof -
  have "choose_central_vx (X, Y, A, B) \<in> V"
    using assms choose_central_vx_X  by (simp add: V_state_def subset_eq)
  with assms show ?thesis
    by (auto simp add: V_state_def elim!: density_boost.cases)
qed

lemma density_boost_disjoint_state:
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish X" "V_state (X,Y,A,B)" "disjoint_state (X,Y,A,B)"
  shows "disjoint_state U'"
proof -
  have "choose_central_vx (X, Y, A, B) \<in> X"
    using assms choose_central_vx_X by (simp add: V_state_def)
  with assms show ?thesis
    by (auto simp add: disjoint_state_def disjnt_iff not_own_Neighbour elim!: density_boost.cases)
qed

lemma density_boost_RB_state: 
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish X" "V_state (X,Y,A,B)" 
    and rb: "RB_state (X,Y,A,B)"
  shows "RB_state U'"
proof -
  define x where "x \<equiv> choose_central_vx (X, Y, A, B)"
  have "x \<in> X"
    using assms choose_central_vx_X by (simp add: x_def V_state_def)
  have A: "all_edges_betw_un A (Neighbours Blue x \<inter> X \<union> Neighbours Red x \<inter> Y) \<subseteq> Red"
    if "all_edges_betw_un A (X \<union> Y) \<subseteq> Red"
    using that by (metis Int_Un_eq(4) Un_subset_iff all_edges_betw_un_Un2)
  have B: "all_edges_betw_un (insert x B) (insert x B) \<subseteq> Blue"
    if "all_edges_betw_un B (B \<union> X) \<subseteq> Blue"
    using that \<open>x \<in> X\<close> all_edges_betw_un_commute 
    by (auto simp: all_edges_betw_un_insert1 all_edges_betw_un_insert2 all_edges_betw_un_Un2 intro!: all_uedges_betw_I)
  have C: "all_edges_betw_un (insert x B) (Neighbours Blue x \<inter> X) \<subseteq> Blue"
    if "all_edges_betw_un B (B \<union> X) \<subseteq> Blue"
    using \<open>x \<in> X\<close> that  
    apply (auto simp: in_Neighbours_iff all_edges_betw_un_insert1 all_edges_betw_un_insert2 all_edges_betw_un_Un2 intro!: all_uedges_betw_I)
    by (metis Int_lower2 all_edges_betw_un_mono2 subset_iff)
  from assms A B C show ?thesis
    by (auto simp add: RB_state_def all_edges_betw_un_Un2 x_def [symmetric]  elim!: density_boost.cases)
qed

lemma density_boost_valid_state:
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish X" "valid_state (X,Y,A,B)"
  shows "valid_state U'"
  by (meson assms density_boost_RB_state density_boost_V_state density_boost_disjoint_state valid_state_def)

subsection \<open>Steps 2–5 as a function\<close>

definition next_state :: "'a config \<Rightarrow> 'a config" where
  "next_state \<equiv> \<lambda>(X,Y,A,B). 
       if many_bluish X then let (S,T) = choose_blue_book(X,Y,A,B) in (T, Y, A, B\<union>S) 
       else let x = choose_central_vx (X,Y,A,B) in
            if reddish X Y (red_density X Y) x then (Neighbours Red x \<inter> X, Neighbours Red x \<inter> Y, insert x A, B)
            else (Neighbours Blue x \<inter> X, Neighbours Red x \<inter> Y, A, insert x B)"

lemma next_state_valid:
  assumes "valid_state (X,Y,A,B)" "\<not> termination_condition X Y"
  shows "valid_state (next_state (X,Y,A,B))"
proof (cases "many_bluish X")
  case True
  then have "big_blue (X,Y,A,B) (next_state (X,Y,A,B))"
    apply (simp add: next_state_def split: prod.split)
    by (metis assms(1) big_blue.intros choose_blue_book_works valid_state_def)
  then show ?thesis
    using assms(1) big_blue_valid_state by blast
next
  case non_bluish: False
  define x where "x = choose_central_vx (X,Y,A,B)"
  show ?thesis
  proof (cases "reddish X Y (red_density X Y) x")
    case True
    with non_bluish have "red_step (X,Y,A,B) (next_state (X,Y,A,B))"
      by (simp add: next_state_def Let_def x_def red_step.intros split: prod.split)
    then show ?thesis
      using assms non_bluish red_step_valid_state by blast      
  next
    case False
    with non_bluish have "density_boost (X,Y,A,B) (next_state (X,Y,A,B))"
      by (simp add: next_state_def Let_def x_def density_boost.intros split: prod.split)
    then show ?thesis
      using assms density_boost_valid_state non_bluish by blast
  qed
qed

primrec stepper :: "nat \<Rightarrow> 'a config" where
  "stepper 0 = (X0,Y0,{},{})"
| "stepper (Suc n) = 
     (let (X,Y,A,B) = stepper n in 
      if termination_condition X Y then (X,Y,A,B) 
      else if even n then next_state (X,Y,A,B) else (degree_reg (X,Y,A,B)))"

lemma degree_reg_subset:
  assumes "degree_reg (X,Y,A,B) = (X',Y',A',B')" 
  shows "X' \<subseteq> X \<and> Y' \<subseteq> Y"
  using assms by (auto simp: degree_reg_def X_degree_reg_def)

lemma next_state_subset:
  assumes "next_state (X,Y,A,B) = (X',Y',A',B')" "valid_state (X,Y,A,B)"
  shows "X' \<subseteq> X \<and> Y' \<subseteq> Y"
  using assms choose_blue_book_subset
  by (force simp: next_state_def valid_state_def Let_def split: if_split_asm prod.split_asm)

lemma valid_state0: "valid_state (X0, Y0, {}, {})"
  using XY0 by (simp add: valid_state_def V_state_def disjoint_state_def RB_state_def)

lemma valid_state_stepper [simp]: "valid_state (stepper n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: stepper_def valid_state0)
next
  case (Suc n)
  then show ?case
    by (force simp: next_state_valid degree_reg_valid_state split: prod.split)
qed

definition "Xseq \<equiv> (\<lambda>(X,Y,A,B). X) \<circ> stepper"
definition "Yseq \<equiv> (\<lambda>(X,Y,A,B). Y) \<circ> stepper"
definition "pseq \<equiv> \<lambda>n. red_density (Xseq n) (Yseq n)"

lemma Xseq_Suc_subset: "Xseq (Suc n) \<subseteq> Xseq n"
  apply (simp add: Xseq_def split: if_split_asm prod.split)
  by (metis degree_reg_subset next_state_subset valid_state_stepper)

lemma Xseq_antimono: "m \<le> n \<Longrightarrow>Xseq n \<subseteq> Xseq m"
  by (simp add: Xseq_Suc_subset lift_Suc_antimono_le)

lemma Yseq_Suc_subset: "Yseq (Suc n) \<subseteq> Yseq n"
  apply (simp add: Yseq_def split: if_split_asm prod.split)
  by (metis degree_reg_subset next_state_subset valid_state_stepper)

lemma Yseq_antimono: "m \<le> n \<Longrightarrow>Yseq n \<subseteq> Yseq m"
  by (simp add: Yseq_Suc_subset lift_Suc_antimono_le)

lemma pseq_0: "p0 = pseq 0"
  by (simp add: p0_def pseq_def Xseq_def Yseq_def)

datatype stepkind = red_step | bblue_step | dboost_step | dreg_step

definition next_state_kind :: "'a config \<Rightarrow> stepkind" where
  "next_state_kind \<equiv> \<lambda>(X,Y,A,B). 
       if many_bluish X then bblue_step 
       else let x = choose_central_vx (X,Y,A,B) in
            if reddish X Y (red_density X Y) x then red_step
            else dboost_step"

definition stepper_kind :: "nat \<Rightarrow> stepkind" where
  "stepper_kind n = 
     (let (X,Y,A,B) = stepper n in 
      if termination_condition X Y then dreg_step 
      else if even n then next_state_kind (X,Y,A,B) else dboost_step)"

section \<open>Big blue steps: theorems\<close>

lemma Blue_4_1:
  defines "b \<equiv> l powr (1/4)"
  assumes "many_bluish X" "X\<subseteq>V"
  shows "(\<exists>K. size_clique k K Red) \<or> (\<exists>S T. good_blue_book S T \<and> real (card S) \<ge> b)"
proof -
  define W where "W \<equiv> {x\<in>X. bluish X x}"
  define m where "m \<equiv> nat\<lceil>l powr (2/3)\<rceil>"
  have Wbig: "card W \<ge> RN k m"
    using assms by (simp add: W_def m_def many_bluish_def)
  with Red_Blue_RN obtain U where "U \<subseteq> W" and U: "size_clique k U Red \<or> size_clique m U Blue"
    by (metis (no_types, lifting) W_def \<open>X\<subseteq>V\<close> mem_Collect_eq subset_eq)
  show ?thesis
    using U
  proof
    assume U_m_Blue: "size_clique m U Blue"
    then have "card U = m" and "clique U Blue" and "U \<subseteq> V"
      by (auto simp: size_clique_def)
    have "m \<ge> 3"
      using lpowr23_ge3 m_def by blast
    then have "k \<le> RN m k" and "m \<noteq> 0"
      using l_large lk by auto
    have "U \<subseteq> X"
      using W_def \<open>U \<subseteq> W\<close> by blast
    with \<open>X\<subseteq>V\<close> have cardXU: "card (X - U) = card X - card U" "card U \<le> card X"
      by (meson card_Diff_subset finV finite_subset card_mono)+
    have "k \<ge> 4"
      using l_large lk by linarith
    have "real l powr (2/3) \<le> real l powr 1"
      using l_large by (intro powr_mono) auto
    then have "m \<le> k"
      using lk by (simp add: m_def)
    then have "m < RN k m"
      using RN_commute RN_lower_self \<open>4 \<le> k\<close> \<open>k \<le> RN m k\<close> nat_less_le by force
    also have cX: "RN k m \<le> card X"
      using assms by (metis Collect_subset W_def Wbig card_mono order_trans finV finite_subset)
    finally have "card U < card X"
      using \<open>card U = m\<close> by blast
    have cXm2: "2 powr (m/2) < card X"
      using cX RN_commute RN_lower_nodiag \<open>3 \<le> m\<close> \<open>m \<le> k\<close> by fastforce
    
    have card_Blue_\<mu>: "card (Neighbours Blue u \<inter> X) \<ge> \<mu> * card X" if "u \<in> U" for u
      using W_def \<open>U \<subseteq> W\<close> bluish_def that by auto

    

    define \<sigma> where "\<sigma> \<equiv> blue_density U (X-U)"

    have "m\<ge>4"
      sorry
    then 
    have M: "m * (k / 2 * (1 - \<mu>) + 1) \<le> card X"
      using cXm2 RN_gt1[of k m] cX \<open>m\<ge>3\<close> \<open>k \<ge>4\<close> \<mu>01 powr_half_ge [of m]
      apply (simp add: field_simps)

      sorry
    have "\<mu> - 2/k \<le> (\<mu> * card X - card U) / (card X - card U)"
      using kn0 \<mu>01 M \<open>card U < card X\<close>
      by (auto simp add: \<open>card U = m\<close> field_split_simps mult_less_cancel_right1 of_nat_diff split: if_split_asm)

    have "m * (k / 2 * (1 - \<mu>) + 1) \<le> m * (k / 2 + 1)"
      using \<open>m\<ge>3\<close> \<open>k \<ge>4\<close> \<mu>01 by (simp add: divide_simps)

    then
    have "(m * (1 - \<mu>)) * k/2 \<le> (card X - card U)"
    have "(card U * (1 - \<mu>)) * k/2 \<le> (card X - card U)"
      using cardXU
      apply (simp add: algebra_simps \<open>card U = m\<close>)

      sorry
    
    have "\<mu> - 2/k \<le> (\<mu> * card X - card U) / (card X - card U)"
      using kn0 \<mu>01 M




      sorry
    also have "\<dots> \<le> \<sigma>"
      using \<open>m\<noteq>0\<close>
      apply (simp add: \<sigma>_def gen_density_def divide_simps)
      apply (auto simp: )
      apply (metis of_nat_less_0_iff of_nat_mult)
         defer
      using \<open>card U = m\<close> \<open>m \<noteq> 0\<close> apply blast
      apply (metis \<open>card U = m\<close> card.infinite card_less_sym_Diff less_nat_zero_code)
      apply (metis of_nat_less_0_iff of_nat_mult)
      apply (simp add: cardXU)


      sorry
    finally have "\<mu> - 2/k \<le> \<sigma>" .
    show ?thesis
      sorry
  qed auto
qed

section \<open>Density-boost steps\<close>

text \<open>"See observation 5.5 below"\<close>
lemma sum_Weight_ge0: "(\<Sum>x\<in>X. \<Sum>y\<in>X. Weight X Y x y) \<ge> 0"
  sorry
