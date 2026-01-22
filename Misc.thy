section \<open>Misc experiments\<close>

theory Misc 
  imports "HOL-Analysis.Analysis"   "HOL-Real_Asymp.Real_Asymp" 
 "HOL-ex.Sketch_and_Explore"
   
begin

context
  includes lifting_syntax

begin

definition rel_real1 :: "real \<Rightarrow> real^1 \<Rightarrow> bool" where
  "rel_real1 x y \<equiv> y = vec x"

lemma rel_real1_set: "rel_set rel_real1 x y \<longleftrightarrow> y = vec ` x"
  by (auto simp: rel_real1_def rel_set_def)

lemma bi_unique_rel_real1 [transfer_rule]:
  "bi_unique rel_real1"
  by (simp add: rel_real1_def bi_unique_def)

lemma bi_total_rel_real1 [transfer_rule]: "bi_total rel_real1"
  unfolding rel_real1_def
  by (metis (mono_tags, lifting) bi_total_def vector_one_nth)

lemma zero_transfer [transfer_rule]: "rel_real1 0 (0::real^1)"
  unfolding rel_real1_def by simp

lemma one_transfer [transfer_rule]: "rel_real1 1 (1::real^1)"
  unfolding rel_real1_def by simp

lemma add_transfer [transfer_rule]:
  "(rel_real1 ===> rel_real1 ===> rel_real1) (+) (+)"
  by (simp add: rel_fun_def rel_real1_def vec_add)
  
lemma uminus_transfer [transfer_rule]:
  "(rel_real1 ===> rel_real1) uminus uminus"
  by (simp add: rel_fun_def rel_real1_def vec_neg)

lemma diff_transfer [transfer_rule]:
  "(rel_real1 ===> rel_real1 ===> rel_real1) (-) (-)"
  by (simp add: rel_fun_def rel_real1_def vec_sub)

lemma le_transfer [transfer_rule]:
  "(rel_real1 ===> rel_real1 ===> (=)) (\<le>) (\<le>)"
  by (simp add: rel_fun_def rel_real1_def less_eq_vec_def)

lemma less_transfer [transfer_rule]:
  "(rel_real1 ===> rel_real1 ===> (=)) (<) (<)"
  by (auto simp: rel_fun_def rel_real1_def less_eq_vec_def less_vec_def)

lemma inf_transfer [transfer_rule]:
  "(rel_real1 ===> rel_real1 ===> rel_real1) inf inf"
  by (simp add: rel_fun_def rel_real1_def vec_def inf_vec_def)

lemma sup_transfer [transfer_rule]:
  "(rel_real1 ===> rel_real1 ===> rel_real1) sup sup"
  by (simp add: rel_fun_def rel_real1_def vec_def sup_vec_def)

lemma norm_abs_transfer [transfer_rule]:
  "(rel_real1 ===> (=)) abs norm"
  by (simp add: rel_fun_def rel_real1_def norm_real)

lemma cbox_transfer [transfer_rule]:
  "(rel_real1 ===> rel_real1 ===> rel_set rel_real1) atLeastAtMost cbox"
  unfolding rel_fun_def rel_real1_def rel_set_def Bex_def
  by (auto simp: mem_box_cart less_eq_vec_def simp flip: interval_cbox)

lemma box_transfer [transfer_rule]:
  "(rel_real1 ===> rel_real1 ===> rel_set rel_real1) greaterThanLessThan box"
  unfolding rel_fun_def rel_real1_def rel_set_def Bex_def
  by (auto simp: mem_box_cart less_eq_vec_def simp flip: interval_cbox)

lemma dist_transfer [transfer_rule]:
  "(rel_real1 ===> rel_real1 ===> (=)) dist dist"
  by (simp add: rel_fun_def rel_real1_def dist_norm norm_real)

lemma ball_transfer [transfer_rule]:
  "(rel_real1 ===> (=) ===> rel_set rel_real1) ball ball"
  unfolding ball_def 
  by transfer_prover

lemma cball_transfer [transfer_rule]:
  "(rel_real1 ===> (=) ===> rel_set rel_real1) cball cball"
  unfolding cball_def 
  by transfer_prover

lemma open_transfer [transfer_rule]:
  "(rel_set rel_real1 ===> (=)) open open"
  unfolding open_dist dist_norm 
  by simp transfer_prover

lemma closed_transfer [transfer_rule]:
  "(rel_set rel_real1 ===> (=)) closed closed"
  unfolding closed_def 
  by transfer_prover

lemma nhds_transfer [transfer_rule]:
  "(rel_real1 ===> rel_filter rel_real1) nhds nhds"
  unfolding nhds_def
  by simp transfer_prover

lemma at_within_transfer [transfer_rule]:
  "(rel_real1 ===> rel_set rel_real1 ===> rel_filter rel_real1) at_within at_within"
  unfolding at_within_def  
  by transfer_prover

lemma eventually_parametric [transfer_rule]:
  "((A ===> (=)) ===> rel_filter A ===> (=)) eventually eventually"
  unfolding rel_fun_def
  by(force elim!: rel_filter.cases eventually_rev_mp simp add: eventually_map_filter_on intro: always_eventually)

lemma tendsto_parametric [transfer_rule]:
  "((B ===> A) ===> A ===> rel_filter B ===> (=)) tendsto tendsto"
  unfolding filterlim_def
  using filtermap_parametric nhds_transfer
  apply (simp add: )
  by transfer_prover
  oops
  tendsto :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b filter \<Rightarrow> bool" 

lemma "i \<ge> 0 \<Longrightarrow> sqrt (of_int i)^2 = i"
  by simp

lemma "(\<Sum>i \<in> {0..}. sqrt (of_int i)^2) = (\<Sum>i \<in> {0..}. of_int i)"
  by simp

definition "f \<equiv> \<lambda>i::nat. if prime i then 1 else 0"

lemma "(\<Sum>i \<in> Collect prime. f i) = X"
apply (simp add: f_def)
  by simp


      
lemma "((\<lambda>x. sin(x)/x^2 - cos(x)/x) has_integral 1) {0..pi}"
       (is "(?g has_integral 1) _")
proof -
  note zero_ereal_def [simp] one_ereal_def [simp] 
  define f where "f \<equiv> \<lambda>x::real. - sin x/x"
  have "(f has_real_derivative ?g x) (at x)"
    if "0 < ereal x" "ereal x < pi" for x
    unfolding f_def has_real_derivative_iff_has_vector_derivative [symmetric]
    apply (rule refl derivative_eq_intros | use that in force)+
    apply (simp add: divide_simps power2_eq_square)
    done
  moreover
  have "isCont ?g x"
    if "0 < x" for x using that by force
  moreover
  have "?g x \<ge> 0" if "x \<in> {0<..<pi}" for x
  proof -
    have "1/4 \<le> x \<and> x \<le> pi \<Longrightarrow> 0 \<le> ?g x" 
      by (approximation 12 splitting: x=12)
    moreover have "0 < x \<and> x < 1/4 \<Longrightarrow> 0 \<le> ?g x" 
      sorry
    ultimately show ?thesis
      using linorder_not_le that by auto
  qed

  moreover
  have "(f \<longlongrightarrow> -1) (at_right 0)" "(f \<longlongrightarrow> 0) (at_left pi)"
    unfolding f_def by real_asymp+
  ultimately have 
    "set_integrable lborel {0<..<pi} (\<lambda>x::real. ?g x)"
    "(LBINT x=0..pi. ?g x) = 1"
    using interval_integral_FTC_nonneg [of 0 pi f ?g]  
    by (auto simp add: ereal_tendsto_simps1)
  moreover have "einterval 0 pi = {0<..<pi}"
    by (auto simp: einterval_def)
  ultimately 
  show ?thesis
    using integral_open_interval_real [of 0 pi ?g]
    using interval_integral_eq_integral' [of 0 pi ?g]
    by (simp_all add: has_integral_iff integrable_on_Icc_iff_Ioo set_borel_integral_eq_integral(1))
qed


lemma
  fixes f :: "real \<Rightarrow> real^'n"
  assumes "\<And>i::'n. (\<lambda>x. norm (f x $ i)) integrable_on S" 
  assumes "S \<in> sets lebesgue"
  shows "(\<lambda>x. norm (f x)) integrable_on S"
proof -
  have "\<And>i. (\<lambda>x. f x $ i) integrable_on S"
    sorry
  then show ?thesis
  using absolutely_integrable_on_iff_component [of S f] assms
    unfolding absolutely_integrable_on_def
    by blast
qed


definition complex_to_vec :: "complex \<Rightarrow> real^2" where
  "complex_to_vec z = vector [Re z, Im z]"

lemma has_absolute_integral_change_of_variables_2':
  fixes f :: "real \<Rightarrow> complex" and g :: "real \<Rightarrow> real"
  assumes S: "S \<in> sets lebesgue"
    and der_g: "\<And>x. x \<in> S \<Longrightarrow> (g has_field_derivative g' x) (at x within S)"
    and inj: "inj_on g S"
  shows "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R f(g x)) = b
     \<longleftrightarrow> f absolutely_integrable_on (g ` S) \<and> integral (g ` S) f = b"
proof -
  have "(\<lambda>x. \<bar>g' x\<bar> *\<^sub>R complex_to_vec (f(g x)) :: real ^ 2) absolutely_integrable_on S \<and>
           integral S (\<lambda>x. \<bar>g' x\<bar> *\<^sub>R complex_to_vec (f(g x))) = (complex_to_vec b :: real ^ 2)
         \<longleftrightarrow> (\<lambda>x. complex_to_vec (f x) :: real ^ 2) absolutely_integrable_on (g ` S) \<and>
           integral (g ` S) (\<lambda>x. complex_to_vec (f x)) = (complex_to_vec b :: real ^ 2)"
    using assms unfolding has_real_derivative_iff_has_vector_derivative
    by (intro has_absolute_integral_change_of_variables_1 assms) auto
  thus ?thesis
    apply (intro conjI iffI)

    by (simp add: absolutely_integrable_on_1_iff integral_on_1_eq)
qed


lemma "(2 + 3 * \<i>) * (2 + 3 * \<i>) / (1 - \<i>) = -17/2 + \<i> * (7 / 2)"
  by (simp add: algebra_simps Complex_divide legacy_Complex_simps)

lemma "eventually (\<lambda>x::real. 1 - 1/x \<le> ln(x)) (at_right 0)"
  by real_asymp

lemma "eventually (\<lambda>x::real. 1 / x \<le> 1 / x\<^sup>2) (at 0)"
  by real_asymp

lemma "eventually (\<lambda>x::real. 1 / \<bar>x\<bar> \<le> 1 / x\<^sup>2) (at 0)"
  by real_asymp

lemma "eventually (\<lambda>x::real. 1 / \<bar>x\<bar> \<le> 1 / x\<^sup>2) (at_left 0)"
  by real_asymp

lemma sin_npi_numeral [simp]: "sin(Num.numeral n * pi) = 0"
  by (simp add: sin_zero_iff_int2)

lemma sin_npi2_numeral [simp]: "sin (pi * Num.numeral n) = 0"
  by (metis of_nat_numeral sin_npi2)

lemma cos_npi_numeral [simp]: "cos (Num.numeral n * pi) = (- 1) ^ Num.numeral n"
  by (metis cos_npi of_nat_numeral)

lemma cos_npi2_numeral [simp]: "cos (pi * Num.numeral n) = (- 1) ^ Num.numeral n"
  by (metis cos_npi2 of_nat_numeral)

lemma "\<exists>f'. ((\<lambda>x. exp(-x)*cos(2*pi*x)) has_real_derivative f' t) (at t) \<and> P(f' t)" for t
  apply (rule exI conjI derivative_eq_intros | force)+
  oops

(*Source: https://tutorial.math.lamar.edu/Solutions/CalcII/IntegrationByParts/Prob6.aspx*)
lemma deriv_prob6: "((\<lambda>x. x^2 * sin(4*x)/4 - sin(4*x)/32 + x * cos(4*x)/8) 
        has_real_derivative x^2 * cos(4*x)) (at x)" for x
  apply (rule exI derivative_eq_intros refl | force)+
  apply (simp add: field_simps)
  done

lemma "((\<lambda>x. x^2 * cos(4*x)) has_integral (pi/8)) {0..pi}"
proof -
  define f where "f \<equiv> \<lambda>x::real. x^2 * sin(4*x)/4 - sin(4*x)/32 + x * cos(4*x)/8"
  have derf: "(f has_vector_derivative x^2 * cos(4*x)) (at x within {0..pi})" for x
    unfolding f_def has_real_derivative_iff_has_vector_derivative [symmetric]
    by (rule exI derivative_eq_intros refl | force simp: field_simps)+
  moreover have "f pi - f 0 = pi/8"
    by (simp add: f_def mult.commute)
  ultimately show ?thesis
    using fundamental_theorem_of_calculus [OF _ derf]
    by (simp add: f_def field_simps)
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
    using assms by (intro prod_mono_strict [where i="n-1"]) auto
  also have "\<dots> = (\<Prod>i = 1..n-s. real i) * real n ^ s"
    using \<open>s \<le> n\<close> by (force simp: prod.If_cases eq)
  also have "\<dots> = fact (n - s) * real n ^ s"
    by (simp add: fact_prod)
  finally show ?thesis .
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



lemma DD: "x>(0::real) \<Longrightarrow> y>0 \<Longrightarrow> x powr (ln y) = y powr (ln x)"
  by (simp add: powr_def)

lemma
  fixes \<epsilon>::real
  assumes "\<epsilon>>0" "k > 1"
  shows "((1 + \<epsilon>) powr ((2/\<epsilon>) * ln k)) \<le> k^2"
proof -
  have "((1 + \<epsilon>) powr ((2/\<epsilon>) * ln k)) = (k powr ln(1 + \<epsilon>)) powr (2/\<epsilon>)"
    by (smt (verit, del_insts) DD assms mult.commute powr_powr)
  also have "\<dots> \<le> (k powr \<epsilon>) powr (2/\<epsilon>)"
    using ln_add_one_self_le_self2 [of \<epsilon>] assms
    by (auto intro!: powr_mono2) 
  also have "\<dots> = (k^2)"
    using assms powr_powr by auto
  finally show ?thesis .
qed


lemma
  fixes \<epsilon>::real
  assumes "\<epsilon>>0" "k > 2"
  shows "1 + 2 * ln k \<le> ((1 + \<epsilon>) powr ((2/\<epsilon>) * ln k))"
proof -
  have "1 + \<epsilon> powr k \<le> ((1 + \<epsilon>) powr k)"
    apply (simp add: powr_def)
    apply auto
    using assms(1) apply linarith

    sorry
  have "1 + \<epsilon> powr ((2/\<epsilon>) * ln k) \<le> ((1 + \<epsilon>) powr ((2/\<epsilon>) * ln k))"
    sorry
  have "((1 + \<epsilon>) powr ((2/\<epsilon>) * ln k)) = (k powr ln(1 + \<epsilon>)) powr (2/\<epsilon>)"
    by (smt (verit, del_insts) DD assms mult.commute powr_powr)
  also have "\<dots> \<le> (k powr \<epsilon>) powr (2/\<epsilon>)"
    using ln_add_one_self_le_self2 [of \<epsilon>] assms
    by (auto intro!: powr_mono2) 
  also have "\<dots> = (k^2)"
    using assms powr_powr by auto
  finally show ?thesis .
qed


lemma 
  defines "e::real \<equiv> exp 1" shows "2*e - 2 \<le> 8*(e-2)"
  unfolding assms by (approximation 5)


lemma 
  fixes c::real
  shows "c\<noteq>0 \<Longrightarrow> d\<noteq>0 \<Longrightarrow> a / (c^2+d^2) = b / (c^2+d^2) \<Longrightarrow> a=b"
apply (simp add: )

lemma cuberoot_irrational:
  defines "x \<equiv> root 3 2 + root 3 3"
  shows "x \<notin> \<rat>"
proof
  assume "x \<in> \<rat>"
  moreover
  have "root 3 8 = 2" "root 3 27 = 3"
    by auto
  then have xcubed: "x^3 = 5 + 3 * x * root 3 6"
    by (simp add: x_def algebra_simps eval_nat_numeral flip: real_root_mult)
  ultimately have Q: "5 + 3 * x * root 3 6 \<in> \<rat>"
    by (metis Rats_power \<open>x \<in> \<rat>\<close>)
  have "root 3 6 \<notin> \<rat>"
  proof 
    assume "root 3 6 \<in> \<rat>"
    then obtain a b where "a / b = root 3 6" and cop: "coprime a b" "b\<noteq>0"
      by (smt (verit, best) Rats_cases')
    then have "(a/b)^3 = 6"
      by auto
    then have eq: "a^3 = 2*3 * b^3" 
      using of_int_eq_iff by (fastforce simp: divide_simps \<open>b\<noteq>0\<close>)
    then have p: "2 dvd a"
      by (metis coprime_left_2_iff_odd coprime_power_right_iff dvd_triv_left mult.assoc)
    then obtain c where "a = 2*c"
      by blast
    with eq have "2 dvd b"
      by (simp add: eval_nat_numeral) (metis even_mult_iff even_numeral odd_numeral)
    with p and cop show False
      by fastforce
  qed
  moreover have "3*x \<in> \<rat> - {0}"
    using xcubed by (force simp: \<open>x \<in> \<rat>\<close>)
  ultimately have "3 * x * root 3 6 \<notin> \<rat>"
    using Rats_divide by force
  with Q show False
    using Rats_add_iff Rats_number_of by blast
qed


(*** COMBINING / BREAKING SEQUENCES INDEXED BY NATURAL NUMBERS (from original Szemeredi development) **)

text \<open>Some tools for combining integer-indexed sequences or splitting them into parts\<close>

lemma less_sum_nat_iff:
  fixes b::nat and k::nat
  shows "b < (\<Sum>i<k. a i) \<longleftrightarrow> (\<exists>j<k. (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"
proof (induction k arbitrary: b)
  case (Suc k)
  then show ?case
    by (simp add: less_Suc_eq) (metis not_less trans_less_add1)
qed auto

lemma less_sum_nat_iff_uniq:
  fixes b::nat and k::nat
  shows "b < (\<Sum>i<k. a i) \<longleftrightarrow> (\<exists>!j. j<k \<and> (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"
  unfolding less_sum_nat_iff by (meson leD less_sum_nat_iff nat_neq_iff)

definition part :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where "part a k b \<equiv> (THE j. j<k \<and> (\<Sum>i<j. a i) \<le> b \<and> b < (\<Sum>i<j. a i) + a j)"

lemma part: 
  "b < (\<Sum>i<k. a i) \<longleftrightarrow> (let j = part a k b in j < k \<and> (\<Sum>i < j. a i) \<le> b \<and> b < (\<Sum>i < j. a i) + a j)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding less_sum_nat_iff_uniq part_def by (metis (no_types, lifting) theI')
qed (auto simp: less_sum_nat_iff Let_def)

lemma part_Suc: "part a (Suc k) b = (if sum a {..<k} \<le> b \<and> b < sum a {..<k} + a k then k else part a k b)"
  using leD 
  by (fastforce simp: part_def less_Suc_eq less_sum_nat_iff conj_disj_distribR cong: conj_cong)

lemma part_eq:
  assumes "i < k" "d < a i"
  shows "part a k (sum a {..<i} + d) = i"
proof -
  have \<section>: "\<And>j. \<lbrakk>sum a {..<j} \<le> sum a {..<i} + d;
              sum a {..<i} + d < sum a {..<j} + a j\<rbrakk> \<Longrightarrow> j = i"
    by (meson \<open>d < a i\<close> leD le_add1 less_sum_nat_iff nat_add_left_cancel_less not_less_iff_gr_or_eq)
  show ?thesis
    unfolding part_def
    using assms
    by (intro the_equality) (auto simp: \<section>)
qed

lemma sum_layers_less:
  fixes d::nat and k::nat
  shows "\<lbrakk>i < k; d < a i\<rbrakk> \<Longrightarrow> sum a {..<i} + d < sum a {..<k}"
  by (meson le_add1 less_sum_nat_iff nat_add_left_cancel_less)


lemma whoops: "\<forall>x. P x \<longrightarrow> P (Suc x) \<Longrightarrow> P x \<Longrightarrow> P y"
  sorry
  by blast

lemma False
  using whoops [of "\<lambda>x. x\<noteq>0" 1 0]
  by auto


lemma
  fixes p::nat
  assumes "prime p"
  obtains q where "p<q" "q < p*p" "prime q"
proof -
  have "p dvd m*n \<longleftrightarrow> p dvd m \<or> p dvd n"
    by (simp add: assms prime_dvd_mult_iff)


  oops

lemma
  fixes p::nat
  assumes "prime p"
  obtains q where "p<q" "q < p*p" "prime q"
proof -
  have "p dvd m*n \<longleftrightarrow> p dvd m \<or> p dvd n" for m n
    by (simp add: assms prime_dvd_mult_iff)

  
  
  
  
  oops



lemma
  fixes p::nat
  assumes "prime p"
  obtains q where "p<q" "q < p*p" "prime q"
proof -
  have "\<And>m n. p dvd m*n \<longleftrightarrow> p dvd m \<or> p dvd n" 
    by (simp add: assms prime_dvd_mult_iff)

  oops

lemma
  assumes "prime p"
  shows "p > 2"


  sorry


lemma "\<lbrakk>0 < N; 0 \<le> x; x < 1\<rbrakk> \<Longrightarrow>  \<lfloor>x * real_of_int N\<rfloor> < N"
  by (simp add: floor_less_iff)

lemma "\<lbrakk>0 < N; 0 \<le> x; x < 1\<rbrakk> \<Longrightarrow> nat \<lfloor>x * real N\<rfloor> < N"
  by (smt (verit) mult_less_cancel_right2 mult_nonneg_nonneg of_nat_0_less_iff of_nat_floor of_nat_less_imp_less)


text \<open>Kevin Buzzard's examples\<close>
lemma
  fixes x::real
  shows "(x+y)*(x+2*y)*(x+3*y) = x^3 + 6*x^2*y + 11*x*y^2 + 6*y^3"
  by (simp add: algebra_simps eval_nat_numeral)

lemma "sqrt 2 + sqrt 3 < sqrt 10"
proof -
  have "(sqrt 2 + sqrt 3)^2 < (sqrt 10)^2"
  proof (simp add: algebra_simps eval_nat_numeral)
    have "(2 * (sqrt 2 * sqrt 3))^2 < 5 ^ 2"
      by (simp add: algebra_simps eval_nat_numeral)
    then show "2 * (sqrt 2 * sqrt 3) < 5"
      by (smt (verit, best) power_mono)
  qed
  then show ?thesis
    by (simp add: real_less_rsqrt)
qed

lemma "sqrt 2 + sqrt 3 < sqrt 10"
  by (approximation 10)

lemma "3.141592635389 < pi"
  by (approximation 30)

lemma "sqrt 2 \<notin> \<rat>"
proof
  assume "sqrt 2 \<in> \<rat>"
  then obtain q::rat where "sqrt 2 = of_rat q"
    using Rats_cases by blast
  then have "q^2 = 2"
    by (metis abs_numeral of_rat_eq_iff of_rat_numeral_eq of_rat_power power2_eq_square real_sqrt_mult_self)
  then obtain m n
    where "coprime m n" "q = of_int m / of_int n"
    by (metis Fract_of_int_quotient Rat_cases)
  then have "of_int m ^ 2 / of_int n ^ 2 = (2::rat)"
    by (metis \<open>q\<^sup>2 = 2\<close> power_divide)
  then have 2: "of_int m ^ 2 = (2::rat) * of_int n ^ 2"
    by (metis division_ring_divide_zero double_eq_0_iff mult_2_right mult_zero_right nonzero_divide_eq_eq)
  then have "2 dvd m"
    by (metis (mono_tags, lifting) even_mult_iff even_numeral of_int_eq_iff of_int_mult of_int_numeral power2_eq_square)
  then obtain r where "m = 2*r"
    by blast
  then have "2 dvd n"
    by (smt (verit) "2" \<open>even m\<close> dvdE even_mult_iff mult.left_commute mult_cancel_left of_int_1 of_int_add of_int_eq_iff of_int_mult one_add_one power2_eq_square)
  then show False
    using \<open>coprime m n\<close> \<open>m = 2 * r\<close> by simp
qed


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




lemma "\<not> (\<exists>q::rat. q^2 = 2)"
proof
  assume "\<exists>q::rat. q^2 = 2"
  then obtain q::rat and m n
    where "q^2 = 2" "coprime m n" "q = of_int m / of_int n"
    by (meson quotient_of_coprime quotient_of_div surj_pair)
  then have "of_int m ^ 2 / of_int n ^ 2 = (2::rat)"
    by (metis \<open>q\<^sup>2 = 2\<close> power_divide)
  then have 2: "of_int m ^ 2 = (2::rat) * of_int n ^ 2"
    by (metis division_ring_divide_zero double_eq_0_iff mult_2_right mult_zero_right nonzero_divide_eq_eq)
  then have "2 dvd m"
    by (metis (mono_tags, lifting) even_mult_iff even_numeral of_int_eq_iff of_int_mult of_int_numeral power2_eq_square)
  then obtain r where "m = 2*r"
    by blast
  then have "2 dvd n"
    by (smt (verit, ccfv_threshold) "2" Groups.mult_ac(3) dvd_def even_mult_iff mult_cancel_left of_int_1 of_int_add of_int_eq_of_int_power_cancel_iff of_int_mult one_add_one power2_eq_square)
  then show False
    using \<open>coprime m n\<close> \<open>m = 2 * r\<close> by simp
qed

lemma "\<nat> \<noteq> (Ints :: complex set)"
  by (smt (z3) Ints_minus Nats_altdef1 mem_Collect_eq of_int_eq_iff of_int_minus)

lemma "\<nat> \<noteq> (Ints :: real set)"
  by (smt (z3) Ints_minus Nats_altdef1 mem_Collect_eq of_int_eq_iff of_int_minus)

thm of_nat_def Int.of_int_def

lemma "\<nat> \<noteq> (Ints :: 'a::linordered_idom set)"
  by (metis Ints_1 Ints_minus Nats_induct neg_0_le_iff_le not_one_le_zero of_nat_0_le_iff)

lemma "m * 2^(2*m) \<le> 2^(2^m)"
  oops


lemma
  fixes a::real
  shows "(a*b + b * c + c*a)^3 \<le> (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c*a + a^2)"
  by sos


subsection \<open>Possible library additions\<close>

lemma mono_on_compose: "mono_on f (g ` S) \<Longrightarrow> mono_on g S \<Longrightarrow> mono_on (f \<circ> g) S"
  by (simp add: mono_on_def)

thm of_int_less_iff
context linordered_idom
begin

lemma of_nat_nat_eq_iff: "real (nat i) = of_int i \<longleftrightarrow> 0 \<le> i"
  using local.of_int_le_iff by fastforce

end



lemma inv_into_subset_eq:
  assumes "inj_on f A" "B \<subseteq> A" "b \<in> f ` B"
  shows "inv_into A f b = inv_into B f b"
  using assms inj_on_subset by fastforce


lemma B:
  fixes f :: "'a::linorder \<Rightarrow> 'b::linorder"
  assumes "strict_mono_on f S"  
  shows "bij_betw (inv_into S f) (f ` S) S"
  by (meson assms bij_betw_imageI strict_mono_on_imp_inj_on assms bij_betw_inv_into)


lemma C'':
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes "strict_mono_on f {a..b}"  "continuous_on {a..b} f"  "a \<le> b"
    and g: "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> g (f x) = x"
  shows "strict_mono_on g {f a..f b}"
  by (smt (verit, del_insts) IVT' assms atLeastAtMost_iff le_less linorder_not_le strict_mono_on_def)


lemma C:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes "strict_mono_on f {a..b}"  "continuous_on {a..b} f"  "a \<le> b"
   shows "strict_mono_on (inv_into {a..b} f) {f a..f b}"
    by (metis assms strict_mono_image_endpoints strict_mono_on_inv_into)

lemma C':
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes sm: "strict_mono_on f {a..}" and "continuous_on {a..} f" and "b \<ge> a"
  shows "strict_mono_on (inv_into {a..} f) {f a..f b}" 
  by (smt (verit, ccfv_threshold) C'' Icc_subset_Ici_iff assms(2) assms(3) atLeastAtMost_iff atLeast_iff continuous_on_subset dual_order.refl inv_into_f_f sm strict_mono_on_def strict_mono_on_imp_inj_on)

lemma X:
  fixes a::real
  assumes "strict_mono_on f {0..a}" and f: "(f has_integral I) {0..a}" 
    and "a \<ge> 0"
  shows "I \<le> a * f a"
proof -
  have "((\<lambda>x. f a) has_integral a * f a) {0..a}"
    using has_integral_const_real [of "f a" 0 a] \<open>a \<ge> 0\<close>
    by simp
  then show ?thesis
    using has_integral_le [OF f]
    by (metis assms(1) assms(3) atLeastAtMost_iff order_refl strict_mono_on_leD)
qed

thm strict_mono_inv_on_range
lemma strict_mono_on_inv_into:
  fixes f :: "'a::linorder \<Rightarrow> 'b::order"
  assumes "strict_mono_on f S"
  shows "strict_mono_on (inv_into S f) (f ` S)"
  using assms
  unfolding strict_mono_on_def
  by (metis f_inv_into_f inv_into_into less_asym' neqE)

(*DUPLICATE FROM YOUNG'S*)

lemma strict_mono_image_endpoints:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes "strict_mono_on f {a..b}" and f: "continuous_on {a..b} f" and "a \<le> b"
  shows "f ` {a..b} = {f a..f b}"
proof
  show "f ` {a..b} \<subseteq> {f a..f b}"
    using assms(1) strict_mono_on_leD by fastforce
  show "{f a..f b} \<subseteq> f ` {a..b}"
    using assms IVT'[OF _ _ _ f] by (force simp: Bex_def)
qed


lemma strict_mono_continuous_inv:
  fixes f :: "real \<Rightarrow> real"
  assumes "strict_mono_on f {a..b}" and "continuous_on {a..b} f" and "a \<le> b"
  shows "continuous_on {f a..f b} (inv_into {a..b} f)"
  by (metis strict_mono_image_endpoints assms compact_interval continuous_on_inv inv_into_f_eq strict_mono_on_imp_inj_on)


lemma BB:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes "strict_mono_on f {a..b}"  "a \<le> b"
    and g: "\<And>x. \<lbrakk>a \<le> x; x \<le> b\<rbrakk> \<Longrightarrow> g (f x) = x"
  shows "continuous_on (f ` {a..b}) g"
proof -
  have "strict_mono_on g (f ` {a..b})"
    by (smt (verit) assms(1) atLeastAtMost_iff g imageE linorder_not_le strict_mono_on_def strict_mono_on_leD)
  show ?thesis


    sorry
  by (smt (verit, del_insts) IVT' assms atLeastAtMost_iff le_less linorder_not_le strict_mono_on_def)


end
