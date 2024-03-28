theory General_Extras imports
  "HOL-Analysis.Analysis"  "Landau_Symbols.Landau_More"
  "HOL-ex.Sketch_and_Explore"

begin
    
text \<open>yet another telescope variant, with weaker promises but a different conclusion\<close>
lemma prod_lessThan_telescope_mult:
  fixes f::"nat \<Rightarrow> 'a::field"
  assumes "\<And>i. i<n \<Longrightarrow> f i \<noteq> 0" 
  shows "(\<Prod>i<n. f (Suc i) / f i) * f 0 = f n"
  using assms
by (induction n) (auto simp: divide_simps)

abbreviation set_difference :: "['a set,'a set] \<Rightarrow> 'a set" (infixl "\<setminus>" 65)
  where "A \<setminus> B \<equiv> A-B"

(* most of the remainder belongs in an AFP entry concerned with Ramsey theory*)

lemma sum_odds_even:
  fixes f :: "nat \<Rightarrow> 'a :: ab_group_add"
  assumes "even m"
  shows "(\<Sum>i \<in> {i. i<m \<and> odd i}. f (Suc i) - f (i -Suc 0)) = f m - f 0"
  using assms
proof (induction m rule: less_induct)
  case (less m)
  show ?case
  proof (cases "m<2")
    case True
    with \<open>even m\<close> have "m=0"
      using nat_dvd_not_less by blast
    then show ?thesis
      by simp
  next
    case False
    have eq: "{i. i<m \<and> odd i} = insert (m-1) {i. i<m-2 \<and> odd i}"
    proof
      show "{i. i < m \<and> odd i} \<subseteq> insert (m - 1) {i. i < m - 2 \<and> odd i}"
        using \<open>even m\<close>
        by clarify (metis Suc_lessI add_2_eq_Suc' diff_Suc_1 even_Suc_Suc_iff less_diff_conv)
    qed (use False less in auto)
    have [simp]: "\<not> (m - Suc 0 < m - 2)"
      by linarith
    show ?thesis
      using False  by (simp add: eq less flip: numeral_2_eq_2)
  qed
qed 

lemma sum_odds_odd:
  fixes f :: "nat \<Rightarrow> 'a :: ab_group_add"
  assumes "odd m"
  shows "(\<Sum>i \<in> {i. i<m \<and> odd i}. f (Suc i) - f (i -Suc 0)) = f (m-1) - f 0"
proof -
  have eq: "{i. i<m \<and> odd i} = {i. i<m-1 \<and> odd i}"
    using assms not_less_iff_gr_or_eq by fastforce
  show ?thesis
    by (simp add: sum_odds_even eq assms)
qed

text \<open>A bounded increasing sequence of finite sets eventually terminates\<close>
lemma Union_incseq_finite:
  assumes fin: "\<And>n. finite (A n)" and N: "\<And>n. card (A n) < N" and "incseq A"
  shows "\<forall>\<^sub>F k in sequentially. \<Union> (range A) = A k"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "\<forall>k. \<exists>l\<ge>k. \<Union> (range A) \<noteq> A l"
    using eventually_sequentially by force
  then have "\<forall>k. \<exists>l\<ge>k. \<exists>m\<ge>l. A m \<noteq> A l"
    by (smt (verit, ccfv_threshold) \<open>incseq A\<close> cSup_eq_maximum image_iff monotoneD nat_le_linear rangeI)
  then have "\<forall>k. \<exists>l\<ge>k. A l - A k \<noteq> {}"
    by (metis assms(3) diff_shunt_var monotoneD nat_le_linear subset_antisym)
  then obtain f where f: "\<And>k. f k \<ge> k \<and> A (f k) - A k \<noteq> {}"
    by metis
  have "card (A ((f^^i)0)) \<ge> i" for i
  proof (induction i)
    case 0
    then show ?case
      by auto
  next
    case (Suc i)
    have "card (A ((f ^^ i) 0)) < card (A (f ((f ^^ i) 0)))"
      by (metis Diff_cancel \<open>incseq A\<close> card_seteq f fin leI monotoneD)
    then show ?case
      using Suc by simp
  qed
  with N show False
    using linorder_not_less by auto
qed

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

lemma finite_countable_subset:
  assumes "finite A" and A: "A \<subseteq> (\<Union>i::nat. B i)"
  obtains n where "A \<subseteq> (\<Union>i<n. B i)"
proof -
  obtain f where f: "\<And>x. x \<in> A \<Longrightarrow> x \<in> B(f x)"
    by (metis in_mono UN_iff A)
  define n where "n = Suc (Max (f`A))"
  have "finite (f ` A)"
    by (simp add: \<open>finite A\<close>)
  then have "A \<subseteq> (\<Union>i<n. B i)"
    unfolding UN_iff f n_def subset_iff
    by (meson Max_ge f imageI le_imp_less_Suc lessThan_iff)
  then show ?thesis ..
qed

lemma finite_countable_equals:
  assumes "finite A" "A = (\<Union>i::nat. B i)"
  obtains n where "A = (\<Union>i<n. B i)"
  by (smt (verit, best) UNIV_I UN_iff finite_countable_subset assms equalityI subset_iff)


lemma integral_uniform_count_measure:
  assumes "finite A" 
  shows "integral\<^sup>L (uniform_count_measure A) f = sum f A / (card A)"
proof -
  have "integral\<^sup>L (uniform_count_measure A) f = (\<Sum>x\<in>A. f x / card A)" 
    using assms by (simp add: uniform_count_measure_def lebesgue_integral_point_measure_finite)
  with assms show ?thesis
    by (simp add: sum_divide_distrib nn_integral_count_space_finite)
qed

subsection \<open>Convexity\<close>

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
     (auto simp: mono_on_const Pi_iff prod_nonneg mono_on_mul mono_onI)

lemma convex_gchoose_aux: "convex_on {k-1..} (\<lambda>a. prod (\<lambda>i. a - of_nat i) {0..<k})"
proof (induction k)
  case 0
  then show ?case 
    by (simp add: convex_on_def)
next
  case (Suc k)
  have "convex_on {real k..} (\<lambda>a. (\<Prod>i = 0..<k. a - real i) * (a - real k))"
  proof (intro convex_on_mul convex_on_diff)
    show "convex_on {real k..} (\<lambda>x. \<Prod>i = 0..<k. x - real i)"
      using Suc convex_on_subset by fastforce
    show "mono_on {real k..} (\<lambda>x. \<Prod>i = 0..<k. x - real i)"
      by (force simp: monotone_on_def intro!: prod_mono)
  next
    show "(\<lambda>x. \<Prod>i = 0..<k. x - real i) \<in> {real k..} \<rightarrow> {0..}"
      by (auto intro!: prod_nonneg)
  qed (auto simp: convex_on_ident concave_on_const mono_onI)
  then show ?case
    by simp
qed

lemma convex_gchoose: "convex_on {k-1..} (\<lambda>x. x gchoose k)"
  by (simp add: gbinomial_prod_rev convex_on_cdiv convex_gchoose_aux)

text \<open>Mehta's binomial, convex on the entire real line and coinciding with 
gchoose under weak conditions\<close>

definition "mfact \<equiv> \<lambda>a k. if a < real k - 1 then 0 else prod (\<lambda>i. a - of_nat i) {0..<k}"

text \<open>Mehta's special rule for convexity, my proof\<close>
lemma convex_on_extend:
  fixes f :: "real \<Rightarrow> real"
  assumes cf: "convex_on {k..} f" and mon: "mono_on {k..} f" 
    and fk: "\<And>x. x<k \<Longrightarrow> f x = f k"
  shows "convex_on UNIV f"
proof (intro convex_on_linorderI)
  fix t x y :: real
  assume t: "0 < t" "t < 1" and "x < y"
  let ?u = "((1 - t) *\<^sub>R x + t *\<^sub>R y)"
  show "f ?u \<le> (1 - t) * f x + t * f y"
  proof (cases "k \<le> x")
    case True
    with \<open>x < y\<close> t show ?thesis
      by (intro convex_onD [OF cf]) auto
  next
    case False
    then have "x < k" and fxk: "f x = f k" by (auto simp add: fk)
    show ?thesis
    proof (cases "k \<le> y")
      case True
      then have "f y \<ge> f k"
        using mon mono_onD by auto
      have kle: "k \<le> (1 - t) * k + t * y"
        using True segment_bound_lemma t by auto
      have fle: "f ((1 - t) *\<^sub>R k + t *\<^sub>R y) \<le> (1 - t) * f k + t * f y"
        using t True by (intro convex_onD [OF cf]) auto
      with False
      show ?thesis
      proof (cases "?u < k")
        case True
        then show ?thesis
          using \<open>f k \<le> f y\<close> fxk fk segment_bound_lemma t by auto
      next
        case False
        have "f ?u \<le> f ((1 - t) *\<^sub>R k + t *\<^sub>R y)"
          using kle \<open>x < k\<close> False t by (intro mono_onD [OF mon]) auto
        then show ?thesis
          using fle fxk by auto
      qed
    next
      case False
      with \<open>x < k\<close> show ?thesis
        by (simp add: fk convex_bound_lt order_less_imp_le segment_bound_lemma t)
    qed
  qed
qed auto

lemma convex_mfact: 
  assumes "k>0"
  shows "convex_on UNIV (\<lambda>a. mfact a k)"
  unfolding mfact_def
proof (rule convex_on_extend)
  show "convex_on {real (k - 1)..} (\<lambda>a. if a < real k - 1 then 0 else \<Prod>i = 0..<k. a - real i)"
    using convex_gchoose_aux [of k] assms
    apply (simp add: convex_on_def)
    by (metis eq_diff_eq le_add_same_cancel2 linorder_not_le segment_bound_lemma)
  show "mono_on {real (k - 1)..} (\<lambda>a. if a < real k - 1 then 0 else \<Prod>i = 0..<k. a - real i)"
    using \<open>k > 0\<close> by (auto simp: mono_on_def intro!: prod_mono)
qed (use assms in auto)

definition mbinomial :: "real \<Rightarrow> nat \<Rightarrow> real"
  where "mbinomial \<equiv> \<lambda>a k. mfact a k / fact k"

lemma convex_mbinomial: "k>0 \<Longrightarrow> convex_on UNIV (\<lambda>x. mbinomial x k)"
  by (simp add: mbinomial_def convex_mfact convex_on_cdiv)

lemma mbinomial_eq_choose [simp]: "mbinomial (real n) k = n choose k"
  by (simp add: binomial_gbinomial gbinomial_prod_rev mbinomial_def mfact_def)

lemma mbinomial_eq_gchoose [simp]: "k \<le> a \<Longrightarrow> mbinomial a k = a gchoose k"
  by (simp add: gbinomial_prod_rev mbinomial_def mfact_def)

text \<open>Elementary inequalities about sums vs products\<close>

(*Used only for the next one*)
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

(*unused*)
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
  also have "\<dots> \<le> (\<Prod>j\<in>J. \<Sum>i\<in>I. f i j) + prod (f a) J"
    by (simp add: insert)
  also have "\<dots> \<le> (\<Prod>j\<in>J. (\<Sum>i\<in>I. f i j) + f a j)"
    by (intro add_prod_le) (auto simp: assms insert sum_nonneg)
  also have "\<dots> = (\<Prod>j\<in>J. \<Sum>i\<in>insert a I. f i j)"
    by (simp add: add.commute insert.hyps)
  finally show ?case .
qed


thm has_derivative_powr (*THIS VERSION IS SIMILAR BUT  NOT THE SAME AS A REPOSITORY VERSION*)
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


(*These can't go into Binomial because they need type "real"
They could go to an AFP entry on Ramsey bounds*)

lemma choose_two_real: "of_nat (n choose 2) = real n * (real n - 1) / 2"
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

lemma add_choose_le_power: "(n + k) choose n \<le> Suc k ^ n"
proof -
  have *: "(\<Prod>i<n. of_nat (n+k - i) / of_nat (n - i)) \<le> (\<Prod>i<n. real (Suc k))"
  proof (intro prod_mono conjI)
    fix i
    assume i: "i \<in> {..<n}"
    then have "real (n + k - i) / real (n - i) = 1 + k/real(n-i)"
      by (auto simp: divide_simps)
    also have "\<dots> \<le> 1 + real k"
      using i by (simp add: divide_inverse inverse_le_1_iff mult_left_le)
    finally show "real (n + k - i) / real (n - i) \<le> real (Suc k)" 
      by simp
  qed auto
  then have "real((n + k) choose n) \<le> real (Suc k ^ n)"
    by (simp add: binomial_altdef_of_nat lessThan_atLeast0)
  then show ?thesis
    by linarith
qed

lemma choose_le_power: "m choose k \<le> (Suc m - k) ^ k"
  by (metis Suc_diff_le add_choose_le_power add_diff_inverse_nat binomial_eq_0_iff less_le_not_le nle_le zero_le)

lemma gbinomial_mono:
  fixes k::nat and a::real
  assumes "of_nat k \<le> a" "a \<le> b" shows "a gchoose k \<le> b gchoose k"
  using assms
  by (force simp add: gbinomial_prod_rev intro!: divide_right_mono prod_mono)

lemma gbinomial_is_prod: "(a gchoose k) = (\<Prod>i<k. (a - of_nat i) / (1 + of_nat i))"
  unfolding gbinomial_prod_rev
  by (induction k; simp add: divide_simps)

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
    using assms by (intro prod_mono_strict [where i="n-1"]) auto
  also have "\<dots> = (\<Prod>i = 1..n-s. real i) * real n ^ s"
    using \<open>s \<le> n\<close> by (force simp add: prod.If_cases eq)
  also have "\<dots> = fact (n - s) * real n ^ s"
    by (simp add: fact_prod)
  finally show ?thesis .
qed

lemma smallo_multiples:
  assumes f: "f \<in> o(real)" and "k>0"
  shows "(\<lambda>n. f (k * n)) \<in> o(real)"
proof (clarsimp simp: smallo_def)
  fix c::real
  assume "c>0"
  then have "c/k > 0"
    by (simp add: assms)
  with assms have "\<forall>\<^sub>F n in sequentially. \<bar>f n\<bar> \<le> c / real k * n"
    by (force simp: smallo_def del: divide_const_simps)
  then obtain N where "\<And>n. n\<ge>N \<Longrightarrow> \<bar>f n\<bar> \<le> c/k * n"
    by (meson eventually_at_top_linorder)
  then have "\<And>m. (k*m)\<ge>N \<Longrightarrow> \<bar>f (k*m)\<bar> \<le> c/k * (k*m)"
    by blast
  with \<open>k>0\<close> have "\<forall>\<^sub>F m in sequentially. \<bar>f (k*m)\<bar> \<le> c/k * (k*m)"
    by (smt (verit, del_insts) One_nat_def Suc_leI eventually_at_top_linorderI mult_1_left mult_le_mono)
  then show "\<forall>\<^sub>F n in sequentially. \<bar>f (k * n)\<bar> \<le> c * n"
    by eventually_elim (use \<open>k>0\<close> in auto)
qed

subsection \<open>An asymptotic form for binomial coefficients via Stirling's formula\<close>

text \<open>From Appendix D.3, page 56\<close>

lemma const_smallo_real: "(\<lambda>n. x) \<in> o(real)"
  by real_asymp

lemma o_real_shift:
  assumes "f \<in> o(real)"
  shows "(\<lambda>i. f(i+j)) \<in> o(real)"
  unfolding smallo_def
proof clarify
  fix c :: real
  assume "(0::real) < c"
  then have *: "\<forall>\<^sub>F i in sequentially. norm (f i) \<le> c/2 * norm i"
    using assms half_gt_zero landau_o.smallD by blast
  have "\<forall>\<^sub>F i in sequentially. norm (f (i + j)) \<le> c/2 * norm (i + j)"
    using eventually_all_ge_at_top [OF *]
    by (metis (mono_tags, lifting) eventually_sequentially le_add1)
  then have "\<forall>\<^sub>F i in sequentially. i\<ge>j \<longrightarrow> norm (f (i + j)) \<le> c * norm i"
    apply eventually_elim
    apply clarsimp
    by (smt (verit, best) \<open>0 < c\<close> mult_left_mono nat_distrib(2) of_nat_mono)
  then show "\<forall>\<^sub>F i in sequentially. norm (f (i + j)) \<le> c * norm i"
    using eventually_mp by fastforce
qed

lemma tendsto_zero_imp_o1:
  fixes a :: "nat \<Rightarrow> real"
  assumes "a \<longlonglongrightarrow> 0"
  shows "a \<in> o(1)"
proof -
  have "\<forall>\<^sub>F n in sequentially. \<bar>a n\<bar> \<le> c" if "c>0" for c
  proof -
    have "\<forall>\<^sub>F n in sequentially. \<bar>a n\<bar> < c"
      by (metis assms order_tendstoD(2) tendsto_rabs_zero_iff that)
    then show ?thesis
      by (meson eventually_sequentially less_eq_real_def)
  qed
  then show ?thesis
    by (auto simp: smallo_def)
qed

lemma tendsto_imp_o1:
  assumes "a \<longlonglongrightarrow> x"
  shows "(\<lambda>n. norm (a n - x)) \<in> o(1)"
  by (simp add: LIM_zero assms tendsto_zero_imp_o1 tendsto_norm_zero)

end

