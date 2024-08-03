theory General_Extras imports
  "HOL-Analysis.Analysis"  "Landau_Symbols.Landau_More"

begin

(*ALMOST ALL ARE JUST FOR DIAGONAL*)

thm deriv_nonneg_imp_mono (*REPLACE [shorter proof]*)
proposition deriv_nonneg_imp_mono:
  assumes deriv: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes ab: "a \<le> b"
  shows "g a \<le> g b"
  by (meson atLeastAtMost_iff DERIV_nonneg_imp_nondecreasing [of concl: g] assms)

(*for Big Blue Steps*)
lemma integral_uniform_count_measure:
  assumes "finite A" 
  shows "integral\<^sup>L (uniform_count_measure A) f = sum f A / (card A)"
proof -
  have "integral\<^sup>L (uniform_count_measure A) f = (\<Sum>x\<in>A. f x / card A)" 
    using assms by (simp add: uniform_count_measure_def lebesgue_integral_point_measure_finite)
  with assms show ?thesis
    by (simp add: sum_divide_distrib nn_integral_count_space_finite)
qed


thm sum_in_smallo  (*for Diagonal*)
lemma maxmin_in_smallo:
  assumes "f \<in> o[F](h)" "g \<in> o[F](h)"
  shows   "(\<lambda>k. max (f k) (g k)) \<in> o[F](h)" "(\<lambda>k. min (f k) (g k)) \<in> o[F](h)"
proof -
  { fix c::real
    assume "c>0"
    with assms smallo_def
    have "\<forall>\<^sub>F x in F. norm (f x) \<le> c * norm(h x)" "\<forall>\<^sub>F x in F. norm(g x) \<le> c * norm(h x)"
      by (auto simp: smallo_def)
    then have "\<forall>\<^sub>F x in F. norm (max (f x) (g x)) \<le> c * norm(h x) \<and> norm (min (f x) (g x)) \<le> c * norm(h x)"
      by (smt (verit) eventually_elim2 max_def min_def)
  } with assms   
  show "(\<lambda>x. max (f x) (g x)) \<in> o[F](h)" "(\<lambda>x. min (f x) (g x)) \<in> o[F](h)"
    by (smt (verit) eventually_elim2 landau_o.smallI)+
qed


(*ALSO TO MIGRATE;
mono_on_mul mono_on_prod convex_gchoose gbinomial_mono gbinomial_is_prod smallo_multiples*)

(*migrated 2024-07-23. Diagonal*)
lemma (in order_topology)
  shows at_within_Ici_at_right: "at a within {a..} = at_right a"
    and at_within_Iic_at_left:  "at a within {..a} = at_left a"
  using order_tendstoD(2)[OF tendsto_ident_at [where s = "{a<..}"]]
  using order_tendstoD(1)[OF tendsto_ident_at[where s = "{..<a}"]]
  by (auto intro!: order_class.order_antisym filter_leI
      simp: eventually_at_filter less_le
      elim: eventually_elim2)

axiomatization(*NOT TO IMPORT. Diagonal*)
  where ln0 [simp]: "ln 0 = 0"

lemma log0 [simp]: "log b 0 = 0"(*NOT TO IMPORT*)
  by (simp add: log_def)

thm of_nat_le_iff
context linordered_nonzero_semiring
begin (*migrated 2024-07-23*)
    
    lemma one_of_nat_le_iff [simp]: "1 \<le> of_nat k \<longleftrightarrow> 1 \<le> k"
      using of_nat_le_iff [of 1] by simp
    
    lemma numeral_nat_le_iff [simp]: "numeral n \<le> of_nat k \<longleftrightarrow> numeral n \<le> k"
      using of_nat_le_iff [of "numeral n"] by simp
    
    lemma of_nat_le_1_iff [simp]: "of_nat k \<le> 1 \<longleftrightarrow> k \<le> 1"
      using of_nat_le_iff [of _ 1] by simp
    
    lemma of_nat_le_numeral_iff [simp]: "of_nat k \<le> numeral n \<longleftrightarrow> k \<le> numeral n"
      using of_nat_le_iff [of _ "numeral n"] by simp
    
    lemma one_of_nat_less_iff [simp]: "1 < of_nat k \<longleftrightarrow> 1 < k"
      using of_nat_less_iff [of 1] by simp
    
    lemma numeral_nat_less_iff [simp]: "numeral n < of_nat k \<longleftrightarrow> numeral n < k"
      using of_nat_less_iff [of "numeral n"] by simp
    
    lemma of_nat_less_1_iff [simp]: "of_nat k < 1 \<longleftrightarrow> k < 1"
      using of_nat_less_iff [of _ 1] by simp
    
    lemma of_nat_less_numeral_iff [simp]: "of_nat k < numeral n \<longleftrightarrow> k < numeral n"
      using of_nat_less_iff [of _ "numeral n"] by simp
    
    lemma of_nat_eq_numeral_iff [simp]: "of_nat k = numeral n \<longleftrightarrow> k = numeral n"
      using of_nat_eq_iff [of _ "numeral n"] by simp

end

    lemma DERIV_nonneg_imp_increasing_open:(*migrated 2024-07-23. Diagonal*)
      fixes a b :: real
        and f :: "real \<Rightarrow> real"
      assumes "a \<le> b"
        and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> (\<exists>y. DERIV f x :> y \<and> y \<ge> 0)"
        and con: "continuous_on {a..b} f"
      shows "f a \<le> f b"
    proof (cases "a=b")
      case False
      with \<open>a\<le>b\<close> have "a<b" by simp
      show ?thesis 
      proof (rule ccontr)
        assume f: "\<not> ?thesis"
        have "\<exists>l z. a < z \<and> z < b \<and> DERIV f z :> l \<and> f b - f a = (b - a) * l"
          by (rule MVT) (use assms \<open>a<b\<close> real_differentiable_def in \<open>force+\<close>)
        then obtain l z where z: "a < z" "z < b" "DERIV f z :> l" and "f b - f a = (b - a) * l"
          by auto
        with assms z f show False
          by (metis DERIV_unique diff_ge_0_iff_ge zero_le_mult_iff)
      qed
    qed auto
    
    lemma DERIV_nonpos_imp_decreasing_open:(*migrated 2024-07-23. Diagonal*)
      fixes a b :: real
        and f :: "real \<Rightarrow> real"
      assumes "a \<le> b"
        and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> \<exists>y. DERIV f x :> y \<and> y \<le> 0"
        and con: "continuous_on {a..b} f"
      shows "f a \<ge> f b"
    proof -
      have "(\<lambda>x. -f x) a \<le> (\<lambda>x. -f x) b"
      proof (rule DERIV_nonneg_imp_increasing_open [of a b])
        show "\<And>x. \<lbrakk>a < x; x < b\<rbrakk> \<Longrightarrow> \<exists>y. ((\<lambda>x. - f x) has_real_derivative y) (at x) \<and> 0 \<le> y"
          using assms
          by (metis Deriv.field_differentiable_minus neg_0_le_iff_le)
        show "continuous_on {a..b} (\<lambda>x. - f x)"
          using con continuous_on_minus by blast
      qed (use assms in auto)
      then show ?thesis
        by simp
    qed

  (*migrated 2024-07-23. Diagonal*)
  lemma floor_ceiling_diff_le: "0 \<le> r \<Longrightarrow> nat\<lfloor>real k - r\<rfloor> \<le> k - nat\<lceil>r\<rceil>"
    by linarith
  

thm log_exp (*RENAME EXISTING LOG_EXP TO log_power. Diagonal*)
thm log_def
    lemma log_exp [simp]: "log b (exp x) = x / ln b"(*migrated 2024-07-29*)
      by (simp add: log_def)


  lemma exp_mono:(*migrated 2024-07-29. Diagonal*)
    fixes x y :: real
    assumes "x \<le> y"
    shows "exp x \<le> exp y"
    using assms exp_le_cancel_iff by force

  (*migrated 2024-07-29*)
  lemma exp_minus': "exp (-x) = 1 / (exp x)"
    for x :: "'a::{real_normed_field,banach}"
    by (simp add: exp_minus inverse_eq_divide)

  lemma ln_strict_mono:(*migrated 2024-07-29*) "\<And>x::real. \<lbrakk>x < y; 0 < x; 0 < y\<rbrakk> \<Longrightarrow> ln x < ln y"
  using ln_less_cancel_iff by blast


(*migrated 2024-06?*)
declare eventually_frequently_const_simps [simp] of_nat_diff [simp]

(*migrated 2024-07-29*)
lemma mult_ge1_I: "\<lbrakk>x\<ge>1; y\<ge>1\<rbrakk> \<Longrightarrow> x*y \<ge> (1::real)"
  by (smt (verit, best) mult_less_cancel_right2)

thm lift_Suc_mono_le (*Generalising those in Nat*) (*migrated 2024-07-23*)
context order
begin
    
    lemma lift_Suc_mono_le:
      assumes mono: "\<And>n. n\<in>N \<Longrightarrow> f n \<le> f (Suc n)"
        and "n \<le> n'" and subN: "{n..<n'} \<subseteq> N"
      shows "f n \<le> f n'"
    proof (cases "n < n'")
      case True
      then show ?thesis
        using subN
      proof (induction n n' rule: less_Suc_induct)
        case (1 i)
        then show ?case
          by (simp add: mono subsetD) 
      next
        case (2 i j k)
        have "f i \<le> f j" "f j \<le> f k"
          using 2 by force+
        then show ?case by auto 
      qed
    next
      case False
      with \<open>n \<le> n'\<close> show ?thesis by auto
    qed
    
    lemma lift_Suc_antimono_le:
      assumes mono: "\<And>n. n\<in>N \<Longrightarrow> f n \<ge> f (Suc n)"
        and "n \<le> n'" and subN: "{n..<n'} \<subseteq> N"
      shows "f n \<ge> f n'"
    proof (cases "n < n'")
      case True
      then show ?thesis
        using subN
      proof (induction n n' rule: less_Suc_induct)
        case (1 i)
        then show ?case
          by (simp add: mono subsetD) 
      next
        case (2 i j k)
        have "f i \<ge> f j" "f j \<ge> f k"
          using 2 by force+
        then show ?case by auto 
      qed
    next
      case False
      with \<open>n \<le> n'\<close> show ?thesis by auto
    qed
    
    lemma lift_Suc_mono_less:
      assumes mono: "\<And>n. n\<in>N \<Longrightarrow> f n < f (Suc n)"
        and "n < n'" and subN: "{n..<n'} \<subseteq> N"
      shows "f n < f n'"
      using \<open>n < n'\<close>
      using subN
    proof (induction n n' rule: less_Suc_induct)
      case (1 i)
      then show ?case
        by (simp add: mono subsetD) 
    next
      case (2 i j k)
      have "f i < f j" "f j < f k"
        using 2 by force+
      then show ?case by auto 
    qed
 
end

lemma eventually_all_geI0:
  assumes "\<forall>\<^sub>F l in sequentially. P a l"  
          "\<And>l x. \<lbrakk>P a l; a\<le>x; x\<le>b; l \<ge> L\<rbrakk> \<Longrightarrow> P x l"
  shows "\<forall>\<^sub>F l in sequentially. \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> P x l"
  by (smt (verit, del_insts) assms eventually_sequentially eventually_elim2)

lemma eventually_all_geI1:
  assumes "\<forall>\<^sub>F l in sequentially. P b l"  
          "\<And>l x. \<lbrakk>P b l; a\<le>x; x\<le>b; l \<ge> L\<rbrakk> \<Longrightarrow> P x l"
  shows "\<forall>\<^sub>F l in sequentially. \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> P x l"
  by (smt (verit, del_insts) assms eventually_sequentially eventually_elim2)

    lemma prod_divide_nat_ivl: (*migrated 2024-07-23*)
      fixes f :: "nat \<Rightarrow> 'a::idom_divide"
      shows "\<lbrakk> m \<le> n; n \<le> p; prod f {m..<n} \<noteq> 0\<rbrakk> \<Longrightarrow> prod f {m..<p} div prod f {m..<n} = prod f {n..<p}"
      using prod.atLeastLessThan_concat [of m n p f,symmetric]
      by (simp add: ac_simps)
    
    lemma prod_divide_split: (*migrated 2024-07-23*)
      fixes f:: "nat \<Rightarrow> 'a::idom_divide"
      assumes "m \<le> n" "(\<Prod>i<m. f i) \<noteq> 0"
      shows "(\<Prod>i\<le>n. f i) div (\<Prod>i<m. f i) = (\<Prod>i\<le>n - m. f(n - i))"
    proof -
      have "\<And>i. i \<le> n-m \<Longrightarrow> \<exists>k\<ge>m. k \<le> n \<and> i = n-k"
        by (metis Nat.le_diff_conv2 add.commute \<open>m\<le>n\<close> diff_diff_cancel diff_le_self order.trans)
      then have eq: "{..n-m} = (-)n ` {m..n}"
        by force
      have inj: "inj_on ((-)n) {m..n}"
        by (auto simp: inj_on_def)
      have "(\<Prod>i\<le>n - m. f(n - i)) = (\<Prod>i=m..n. f i)"
        by (simp add: eq prod.reindex_cong [OF inj])
      also have "\<dots> = (\<Prod>i\<le>n. f i) div (\<Prod>i<m. f i)"
        using prod_divide_nat_ivl[of 0 "m" "Suc n" f] assms
        by (force simp: atLeast0AtMost atLeast0LessThan atLeastLessThanSuc_atLeastAtMost)
      finally show ?thesis by metis
    qed


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
    then have "x < k" and fxk: "f x = f k" by (auto simp: fk)
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
    apply (simp add: convex_on_def Ball_def)
    by (smt (verit, del_insts) distrib_right mult_cancel_right2 mult_left_mono)
  show "mono_on {real (k - 1)..} (\<lambda>a. if a < real k - 1 then 0 else \<Prod>i = 0..<k. a - real i)"
    using \<open>k > 0\<close> by (auto simp: mono_on_def intro!: prod_mono)
qed (use assms gr0_conv_Suc in force)

definition mbinomial :: "real \<Rightarrow> nat \<Rightarrow> real"
  where "mbinomial \<equiv> \<lambda>a k. mfact a k / fact k"

lemma convex_mbinomial: "k>0 \<Longrightarrow> convex_on UNIV (\<lambda>x. mbinomial x k)"
  by (simp add: mbinomial_def convex_mfact convex_on_cdiv)

lemma mbinomial_eq_choose [simp]: "mbinomial (real n) k = n choose k"
  by (simp add: binomial_gbinomial gbinomial_prod_rev mbinomial_def mfact_def)

lemma mbinomial_eq_gchoose [simp]: "k \<le> a \<Longrightarrow> mbinomial a k = a gchoose k"
  by (simp add: gbinomial_prod_rev mbinomial_def mfact_def)

(*These can't go into Binomial because they need type "real"
They could go to an AFP entry on Ramsey bounds*)

lemma gbinomial_mono:
  fixes k::nat and a::real
  assumes "of_nat k \<le> a" "a \<le> b" shows "a gchoose k \<le> b gchoose k"
  using assms
  by (force simp: gbinomial_prod_rev intro!: divide_right_mono prod_mono)

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
    using \<open>s \<le> n\<close> by (force simp: prod.If_cases eq)
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

