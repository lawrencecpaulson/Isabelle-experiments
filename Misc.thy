section \<open>Misc experiments\<close>

theory Misc imports
  "HOL-Analysis.Analysis"
  "HOL-Decision_Procs.Approximation"
  "HOL-Computational_Algebra.Primes"
  "HOL-ex.Sketch_and_Explore"
   
begin

(*FOR THE LIBRARY?*)
    
    lemma wellorder_InfI:
      fixes k :: "'a::{wellorder,conditionally_complete_lattice}"
      assumes "k \<in> A" shows "Inf A \<in> A" 
      using wellorder_class.LeastI [of "\<lambda>x. x \<in> A" k]
      by (simp add: Least_le assms cInf_eq_minimum)
    
    lemma wellorder_Inf_le1:
      fixes k :: "'a::{wellorder,conditionally_complete_lattice}"
      assumes "k \<in> A" shows "Inf A \<le> k"
      by (meson Least_le assms bdd_below.I cInf_lower)
    
    lemma sum_Re_le_cmod: "(\<Sum>i\<in>I. Re (z i)) \<le> cmod (\<Sum>i\<in>I. z i)"
      by (metis Re_sum complex_Re_le_cmod)
    
    lemma sum_Im_le_cmod: "(\<Sum>i\<in>I. Im (z i)) \<le> cmod (\<Sum>i\<in>I. z i)"
      by (smt (verit, best) Im_sum abs_Im_le_cmod sum.cong)
    
    lemma cos_gt_neg1:
      assumes "(t::real) \<in> {-pi<..<pi}"
      shows   "cos t > -1"
    proof -
      have "cos t \<ge> -1"
        by simp
      moreover have "cos t \<noteq> -1"
      proof
        assume "cos t = -1"
        then obtain n where n: "t = (2 * of_int n + 1) * pi"
          by (subst (asm) cos_eq_minus1) auto
        from assms have "t / pi \<in> {-1<..<1}"
          by (auto simp: field_simps)
        also from n have "t / pi = of_int (2 * n + 1)"
          by auto
        finally show False
          by auto
      qed
      ultimately show ?thesis by linarith
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

lemma "Nats \<noteq> (Ints :: complex set)"
  by (smt (z3) Ints_minus Nats_altdef1 mem_Collect_eq of_int_eq_iff of_int_minus)

lemma "Nats \<noteq> (Ints :: real set)"
  by (smt (z3) Ints_minus Nats_altdef1 mem_Collect_eq of_int_eq_iff of_int_minus)

thm of_nat_def Int.of_int_def

lemma "Nats \<noteq> (Ints :: 'a::linordered_idom set)"
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

lemma of_nat_nat_eq_iff: "of_nat (nat i) = of_int i \<longleftrightarrow> 0 \<le> i"
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
