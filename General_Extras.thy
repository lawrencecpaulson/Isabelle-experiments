theory General_Extras imports
  "HOL-Analysis.Analysis" 
  "HOL-ex.Sketch_and_Explore"

begin


(*the corresponding strict inequality can be proved under the assumptions  "1 < s" "s \<le> n"
  using fact_less_fact_power*)
thm binomial_fact_lemma
lemma binomial_fact_pow: "(n choose s) * fact s \<le> n^s"
proof (cases "s \<le> n")
  case True
  then show ?thesis
    by (smt (verit) binomial_fact_lemma mult.assoc mult.commute fact_div_fact_le_pow fact_nonzero nonzero_mult_div_cancel_right) 
qed (simp add: binomial_eq_0)

text \<open>useful for counting the number of edges containing a clique\<close>
lemma card_Pow_diff:
  assumes "A \<subseteq> B" "finite B"
  shows "card {X \<in> Pow B. A \<subseteq> X} = 2 ^ (card B - card A)"
proof -
  have inj: "inj_on ((\<union>) A) (Pow (B-A))"
    using assms by (auto simp: inj_on_def)
  have "\<And>C. \<lbrakk>A \<subseteq> C; C \<subseteq> B\<rbrakk> \<Longrightarrow> C \<in> (\<union>) A ` Pow (B - A)"
    by (metis Diff_mono Diff_partition PowI imageI subset_refl)
  with assms have "{X \<in> Pow B. A \<subseteq> X} = (\<union>)A ` Pow (B-A)"
    by blast
  moreover have "card \<dots> = 2 ^ (card B - card A)"
    using inj assms by (simp add: card_Diff_subset card_Pow card_image finite_subset)
  ultimately show ?thesis
    by presburger
qed

context linordered_semidom
begin

thm power_le_one_iff (*MOVE TO A BETTER PLACE AND GENERALISE THUS*)
lemma power_le_one_iff: "0 \<le> a \<Longrightarrow> a ^ n \<le> 1 \<longleftrightarrow> (n = 0 \<or> a \<le> 1)"
  by (metis (mono_tags) gr0I nle_le one_le_power power_le_one self_le_power power_0)

lemma power_less1_D: "a^n < 1 \<Longrightarrow> a < 1"
  using not_le one_le_power by blast

lemma power_less_one_iff: "0 \<le> a \<Longrightarrow> a ^ n < 1 \<longleftrightarrow> (n > 0 \<and> a < 1)"
  by (metis (mono_tags) power_one power_strict_mono power_less1_D less_le_not_le neq0_conv power_0)

end

subsection \<open>Convexity?\<close>

(* the definition of convex in the library is incorrect: 
  we speak of a convex function ONLY on a convex set*)

lemma mono_on_ident: "mono_on S (\<lambda>x. x)"
  by (simp add: mono_on_def)

lemma mono_on_const:
  fixes a :: "'a::order" shows "mono_on S (\<lambda>x. a)"
  by (simp add: mono_on_def)

lemma convex_on_iff: "convex_on S f = concave_on S (\<lambda>x. - f x)"
  by (simp add: concave_on_def)

lemma convex_on_ident: "convex_on S (\<lambda>x. x)"
  by (simp add: convex_on_def)

lemma concave_on_ident: "concave_on S (\<lambda>x. x)"
  by (simp add: concave_on_iff)

lemma convex_on_const: "convex_on S (\<lambda>x. a)"
  by (simp add: convex_on_def flip: distrib_right)

lemma concave_on_const: "concave_on S (\<lambda>x. a)"
  by (simp add: concave_on_iff flip: distrib_right)

lemma convex_on_diff:
  assumes "convex_on S f"
    and "concave_on S g"
  shows "convex_on S (\<lambda>x. f x - g x)"
  using assms concave_on_def convex_on_add by fastforce

lemma concave_on_diff:
  assumes "concave_on S f"
    and "convex_on S g"
  shows "concave_on S (\<lambda>x. f x - g x)"
  using convex_on_diff assms concave_on_def by fastforce

lemma concave_on_add:
  assumes "concave_on S f"
    and "concave_on S g"
  shows "concave_on S (\<lambda>x. f x + g x)"
  using assms convex_on_iff concave_on_diff concave_on_def by fastforce

lemma convex_on_cdiv [intro]:
  fixes c :: real
  assumes "0 \<le> c" and "convex_on S f"
  shows "convex_on S (\<lambda>x. f x / c)"
  unfolding divide_inverse
  using convex_on_cmul [of "inverse c" S f]
  by (simp add: mult.commute assms)

lemma mono_on_mul:
  fixes f::"'a::ord \<Rightarrow> 'b::ordered_semiring"
  assumes "mono_on S f" "mono_on S g"
  assumes fty: "f \<in> S \<rightarrow> {0..}" and gty: "g \<in> S \<rightarrow> {0..}"
  shows "mono_on S (\<lambda>x. f x * g x)"
  using assms by (auto simp: Pi_iff monotone_on_def intro!: mult_mono)

lemma mono_on_prod:
  fixes f::"'i \<Rightarrow> 'a::ord \<Rightarrow> 'b::linordered_idom"
  assumes "\<And>i. i \<in> I \<Longrightarrow> mono_on S (f i)" 
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> S \<rightarrow> {0..}" 
  shows "mono_on S (\<lambda>x. prod (\<lambda>i. f i x) I)"
  using assms
  by (induction I rule: infinite_finite_induct)
     (auto simp: mono_on_const Pi_iff prod_nonneg mono_on_mul)

lemma convex_on_mul:
  fixes S::"real set"
  assumes "convex_on S f" "convex_on S g" "convex S"
  assumes "mono_on S f" "mono_on S g"
  assumes fty: "f \<in> S \<rightarrow> {0..}" and gty: "g \<in> S \<rightarrow> {0..}"
  shows "convex_on S (\<lambda>x. f x*g x)"
proof (intro convex_on_linorderI)
  fix t::real and x y
  assume t: "0 < t" "t < 1" and xy: "x \<in> S" "y \<in> S"
  have "f x*g y + f y*g x \<le> f x*g x + f y*g y"
    using \<open>mono_on S f\<close> \<open>mono_on S g\<close>
    by (smt (verit, ccfv_SIG) mono_onD mult_right_mono right_diff_distrib' xy)
  then have "(1-t) * f x * g y + (1-t) * f y * g x \<le> (1-t) * f x * g x + (1-t) * f y * g y"
    using t
    by (metis (mono_tags, opaque_lifting) mult.assoc diff_gt_0_iff_gt distrib_left mult_le_cancel_left_pos)
  then have *: "t*(1-t) * f x * g y + t*(1-t) * f y * g x \<le> t*(1-t) * f x * g x + t*(1-t) * f y * g y"
    using t
    by (metis (mono_tags, opaque_lifting) mult.assoc distrib_left mult_le_cancel_left_pos)  
  have inS: "(1-t)*x + t*y \<in> S"
    using t xy \<open>convex S\<close> by (simp add: convex_alt)
  then have "f ((1-t)*x + t*y) * g ((1-t)*x + t*y) \<le> ((1-t)*f x + t*f y)*g ((1-t)*x + t*y)"
    using convex_onD [OF \<open>convex_on S f\<close>, of t x y] t xy fty gty
    by (intro mult_mono add_nonneg_nonneg) (auto simp: Pi_iff zero_le_mult_iff)
  also have "... \<le> ((1-t)*f x + t*f y) * ((1-t)*g x + t*g y)"
    using convex_onD [OF \<open>convex_on S g\<close>, of t x y] t xy fty gty inS
    by (intro mult_mono add_nonneg_nonneg) (auto simp: Pi_iff zero_le_mult_iff)
  also have "... \<le> (1-t) * (f x*g x) + t * (f y*g y)"
    using * by (simp add: algebra_simps)
  finally show "f ((1-t) *\<^sub>R x + t *\<^sub>R y) * g ((1-t) *\<^sub>R x + t *\<^sub>R y) \<le> (1-t)*(f x*g x) + t*(f y*g y)" 
    by simp
qed

lemma convex_gchoose_aux: "convex_on {k-1..} (\<lambda>a. prod (\<lambda>i. a - of_nat i) {0..<k})"
proof (induction k)
  case 0
  then show ?case 
    by (simp add: convex_on_def)
next
  case (Suc k)
  with convex_on_subset have "convex_on {real k..} (\<lambda>a. (\<Prod>i = 0..<k. a - real i) * (a - real k))"
    by (intro convex_on_mul convex_on_diff convex_on_ident convex_on_const
              concave_on_const mono_on_mul mono_on_prod;
        fastforce simp add: Pi_iff prod_nonneg mono_onI)+
  then show ?case
    by simp
qed

lemma convex_gchoose: "convex_on {k-1..} (\<lambda>x. x gchoose k)"
  by (simp add: gbinomial_prod_rev convex_on_cdiv convex_gchoose_aux)

text \<open>Mehta's binomial, convex on the entire real line and coinciding with 
gchoose under weak conditions\<close>

definition "mfact \<equiv> \<lambda>a k. if a < real k - 1 then 0 else prod (\<lambda>i. a - of_nat i) {0..<k}"

text \<open>Mehta's special rule for convexity, my proof\<close>
lemma E:
  fixes f :: "real \<Rightarrow> real"
  assumes cf: "convex_on {k..} f" and mon: "mono_on {k..} f" 
    and **: "\<And>x. x < k \<Longrightarrow> f x = f k"
  shows "convex_on UNIV f"
proof (intro convex_on_linorderI)
  fix  t x y :: real
  assume t: "0 < t" "t < 1" and "x < y"
  show "f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f x + t * f y"
  proof (cases "k \<le> x")
    case True
    with \<open>x < y\<close> t show ?thesis
      by (intro convex_onD [OF cf]) auto
  next
    case False
    then have [simp]: "x < k" "f x = f k" by (auto simp add: "**")
    show ?thesis
    proof (cases "k \<le> y")
      case True
      then have "f y \<ge> f k"
        using mon mono_onD by auto
      have fle: "f ((1 - t) *\<^sub>R k + t *\<^sub>R y) \<le> (1 - t) * f k + t * f y"
        using t True by (intro convex_onD [OF cf]) auto
      with False
      show ?thesis
      proof (cases "(1 - t) * x + t * y < k")
        case True
        then have "f ((1 - t) * x + t * y) = f k"
          by (simp add: "**")
        then show ?thesis
          using \<open>f k \<le> f y\<close> segment_bound_lemma t by auto
      next
        case False
        have "f ((1 - t) *\<^sub>R x + t *\<^sub>R y) \<le> (1 - t) * f k + t * f y"
          apply (rule order_trans [OF _ convex_onD [OF cf]])
          using t \<open>x < k\<close> apply (auto simp: )
           apply (rule mono_onD [OF mon])
          using False t \<open>x < k\<close> apply (auto simp: )
          using True segment_bound_lemma apply force
          using \<open>x < k\<close> apply linarith
          using True by auto
        then show ?thesis
          using fle by auto
      qed
    next
      case False
      with \<open>x < k\<close> show ?thesis
        by (simp add: "**" convex_bound_lt order_less_imp_le segment_bound_lemma t)
    qed
  qed
qed

lemma convex_mfact: 
  assumes "k>0"
  shows "convex_on UNIV (\<lambda>a. mfact a k)"
  using assms
  apply (simp add: mfact_def)
  apply (rule E [where k="k-1"])
  using convex_gchoose_aux apply (auto simp add: convex_on_def)[1]
    apply (metis add_diff_cancel_right' le_add_same_cancel2 linorder_not_le segment_bound_lemma)
   defer
   apply (auto simp: )
  apply (auto simp: mono_on_def)
  using \<open>k > 0\<close>
  apply (intro prod_mono)
  apply (auto simp: )
  done

definition mbinomial :: "real \<Rightarrow> nat \<Rightarrow> real"
  where "mbinomial \<equiv> \<lambda>a k. mfact a k / fact k"

lemma convex_mbinomial: "k>0 \<Longrightarrow> convex_on UNIV (\<lambda>x. mbinomial x k)"
  by (simp add: mbinomial_def convex_mfact convex_on_cdiv)

lemma mbinomial_eq_choose [simp]: "mbinomial (real n) k = n choose k"
  by (simp add: binomial_gbinomial gbinomial_prod_rev mbinomial_def mfact_def)

lemma mbinomial_eq_gchoose [simp]: "k \<le> a \<Longrightarrow> mbinomial a k = a gchoose k"
  by (simp add: gbinomial_prod_rev mbinomial_def mfact_def)

text \<open>Elementary inequalities about sums vs products\<close>

lemma add_prod_le:
  fixes f g :: "'a \<Rightarrow> 'b::linordered_idom"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> f i \<ge> 0 \<and> g i \<ge> 0" "I \<noteq> {}"
  shows "(\<Prod>i\<in>I. f i) + (\<Prod>i\<in>I. g i) \<le> (\<Prod>i\<in>I. f i + g i)"
  using assms
proof (induction I)
  case empty
  then show ?case
    by simp
next
  case (insert i I)
  show ?case
  proof (cases "I={}")
    case False
    then have "prod f I + prod g I \<le> (\<Prod>i\<in>I. f i + g i)"
      using insert by force
    moreover have "(\<Prod>i\<in>I. f i) \<le> (\<Prod>i\<in>I. f i + g i)"
      by (simp add: insert.prems prod_mono)
    moreover have "(\<Prod>i\<in>I. g i) \<le> (\<Prod>i\<in>I. f i + g i)"
      by (simp add: insert.prems prod_mono)
    ultimately show ?thesis
      by (simp add: algebra_simps insert add_mono mult_left_mono)
  qed auto
qed

lemma sum_prod_le:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::linordered_idom"
  assumes "finite I" "finite J" "J \<noteq> {}"
  and fge0: "\<And>i j. \<lbrakk>i\<in>I; j\<in>J\<rbrakk> \<Longrightarrow> f i j \<ge> 0"
  shows "(\<Sum>i\<in>I. \<Prod>j\<in>J. f i j) \<le> (\<Prod>j\<in>J. \<Sum>i\<in>I. f i j)"
  using \<open>finite I\<close> fge0
proof (induction I)
  case empty
  then show ?case by simp
next
  case (insert a I)
  have "(\<Sum>i \<in> insert a I. prod (f i) J) = (\<Sum>i\<in>I. prod (f i) J) + prod (f a) J"
    using insert.hyps by force
  also have "... \<le> (\<Prod>j\<in>J. \<Sum>i\<in>I. f i j) + prod (f a) J"
    by (simp add: insert)
  also have "... \<le> (\<Prod>j\<in>J. (\<Sum>i\<in>I. f i j) + f a j)"
    by (intro add_prod_le) (auto simp: assms insert sum_nonneg)
  also have "... = (\<Prod>j\<in>J. \<Sum>i\<in>insert a I. f i j)"
    by (simp add: add.commute insert.hyps)
  finally show ?case .
qed



lemma powr01_less_one: "0 \<le> (a::real) \<Longrightarrow> a < 1 \<Longrightarrow> e>0 \<Longrightarrow> a powr e < 1 "
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
    by (auto simp: choose_two dvd_def)
next
  case False
  then have "even (n-1)"
    by simp
  then show ?thesis
    by (auto simp: choose_two dvd_def)
qed


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

(*Binomial*)
lemma binomial_mono:
  assumes "m \<le> n" shows "m choose k \<le> n choose k"
proof -
  have "{K. K \<subseteq> {0..<m} \<and> card K = k} \<subseteq> {K. K \<subseteq> {0..<n} \<and> card K = k}"
    using assms by auto
  then show ?thesis
    by (simp add: binomial_def card_mono)
qed

lemma gbinomial_mono:
  fixes k::nat and a::real
  assumes "k \<le> a" "a \<le> b" shows "a gchoose k \<le> b gchoose k"
  using assms
  by (force simp add: gbinomial_prod_rev intro!: divide_right_mono prod_mono)

lemma gbinomial_is_prod: "(a gchoose k) = (\<Prod>i<k. (a - of_nat i) / (1 + of_nat i))"
  unfolding gbinomial_prod_rev
  by (induction k; simp add: divide_simps)

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

end

