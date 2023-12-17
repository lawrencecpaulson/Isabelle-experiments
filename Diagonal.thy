theory Diagonal imports
  General_Extras Ramsey_Extras
  "HOL-Library.Disjoint_Sets" "Undirected_Graph_Theory.Undirected_Graph_Basics" 
  "HOL-Decision_Procs.Approximation" 
  "HOL-Library.Infinite_Set"   
  "HOL-ex.Sketch_and_Explore"

   
begin

text \<open>Mehta\<close>
lemma exp_thing:(*four_two_aux''' PROBABLY NOT NEEDED *)
  fixes x::real
  assumes "0 \<le> x" "x \<le> 1/2" shows "exp (- 2 * x) \<le> 1 - x"
proof -
  have "1 / (1-x) \<le> 1 + 2 * x"
    using assms by (simp add: mult_right_le_one_le field_simps)
  also have "... \<le> exp (2*x)"
    using exp_ge_add_one_self by blast
  finally show ?thesis
    using assms by (simp add: exp_minus divide_simps mult.commute)
qed

lemma integral_uniform_count_measure:
  assumes "finite \<Omega>" 
  shows "integral\<^sup>L (uniform_count_measure \<Omega>) f = sum f \<Omega> / (card \<Omega>)"
proof -
  have "(integral\<^sup>L (uniform_count_measure \<Omega>) f) = (\<Sum>a\<in>\<Omega>. (f a) / real (card \<Omega>))" 
    using assms by (simp add: uniform_count_measure_def lebesgue_integral_point_measure_finite)
  with assms show ?thesis
    by (simp add: sum_divide_distrib nn_integral_count_space_finite)
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

text \<open>This is fact 4.2 (page 11) as well as equation (73), page 55.\<close>
lemma Fact_D1_73:
  fixes \<sigma>::real and m b::nat  
  assumes \<sigma>: "0<\<sigma>" "\<sigma>\<le>1" and b: "real b \<le> \<sigma> * m / 2"
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
  with EQ have "\<sigma>^b * exp (- (3 * real b ^ 2) / (4*m)) \<le> ((\<sigma>*m) gchoose b) * inverse (m gchoose b)"
    by (simp add: assms)
  with \<sigma> bm show ?thesis
    by (simp add: field_split_simps flip: binomial_gbinomial)
qed


section \<open>Preliminary definitions\<close>

definition Neighbours :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "Neighbours \<equiv> \<lambda>E x. {y. {x,y} \<in> E}"

lemma in_Neighbours_iff: "y \<in> Neighbours E x \<longleftrightarrow> {x,y} \<in> E"
  by (simp add: Neighbours_def)

lemma finite_Neighbours:
  assumes "finite E"
  shows "finite (Neighbours E x)"
proof -
  have "Neighbours E x \<subseteq> Neighbours {X\<in>E. finite X} x"
    by (auto simp: Neighbours_def)
  also have "... \<subseteq> (\<Union>{X\<in>E. finite X})"
    by (meson Union_iff in_Neighbours_iff insert_iff subset_iff)
  finally show ?thesis
    using assms finite_subset by fastforce
qed

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
  by (auto simp: all_edges_betw_un_def)

lemma all_uedges_betw_I: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> {x, y} \<in> E \<Longrightarrow> {x, y} \<in> all_edges_betw_un X Y"
  by (auto simp: all_edges_betw_un_def)

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

lemma all_edges_betw_un_le: 
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

lemma all_edges_betw_un_Int1:
  "disjnt Y Z \<Longrightarrow> all_edges_betw_un (X \<inter> Y) Z = all_edges_betw_un X Z \<inter> all_edges_betw_un Y Z"
  by (fastforce simp: all_edges_betw_un_def doubleton_eq_iff disjnt_def)

lemma all_edges_betw_un_Int2:
  "disjnt Z X \<Longrightarrow> all_edges_betw_un X (Y \<inter> Z) = all_edges_betw_un X Y \<inter> all_edges_betw_un X Z"
  by (fastforce simp: all_edges_betw_un_def doubleton_eq_iff disjnt_def)

lemma all_edges_betw_un_diff1:
  "Z \<subseteq> Y \<Longrightarrow> all_edges_betw_un (X - Y) Z = all_edges_betw_un X Z - all_edges_betw_un Y Z"
  by (fastforce simp: all_edges_betw_un_def doubleton_eq_iff)

lemma all_edges_betw_un_diff2:
  "X \<subseteq> Z \<Longrightarrow> all_edges_betw_un X (Y - Z) = all_edges_betw_un X Y - all_edges_betw_un X Z"
  by (fastforce simp: all_edges_betw_un_def doubleton_eq_iff)

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

lemma all_edges_betw_un_UN1:
  "all_edges_betw_un (\<Union>i\<in>I. X i) Y = (\<Union>i\<in>I. all_edges_betw_un (X i) Y)"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_UN2:
  "all_edges_betw_un X (\<Union>i\<in>I. Y i) = (\<Union>i\<in>I. all_edges_betw_un X (Y i))"
  by (auto simp: all_edges_betw_un_def)

lemma all_edges_betw_un_INT1:
  "\<lbrakk>i\<in>I; disjnt (X i) Y\<rbrakk> \<Longrightarrow> all_edges_betw_un (\<Inter>i\<in>I. X i) Y = (\<Inter>i\<in>I. all_edges_betw_un (X i) Y)"
  by (simp add: all_edges_betw_un_def disjnt_iff set_eq_iff) (smt (verit) doubleton_eq_iff)

lemma all_edges_betw_un_INT2:
  "\<lbrakk>i\<in>I; disjnt X (Y i)\<rbrakk> \<Longrightarrow> all_edges_betw_un X (\<Inter>i\<in>I. Y i) = (\<Inter>i\<in>I. all_edges_betw_un X (Y i))"
  by (simp add: all_edges_betw_un_def disjnt_iff set_eq_iff) (smt (verit) doubleton_eq_iff)

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

lemma Neighbours_eq_all_edges_betw_un:
  "Neighbours E x = \<Union> (all_edges_betw_un V {x}) - {x}"
  using wellformed by (auto simp: Neighbours_def all_edges_betw_un_def insert_commute )

lemma Neighbours_eq_all_edges_betw_un':
  "F \<subseteq> E \<Longrightarrow> Neighbours F x = \<Union> (all_edges_betw_un V {x} \<inter> F) - {x}"
  using wellformed 
  apply (auto simp: Neighbours_def all_edges_betw_un_def insert_commute )
  apply (rule_tac x="{xa,x}" in bexI)
   apply (force simp add: insert_commute all_edges_betw_un_def)+
  done

lemma book_insert: 
  "book (insert v S) T F \<longleftrightarrow> book S T F \<and> v \<notin> T \<and> all_edges_betw_un {v} (S \<union> T) \<subseteq> F"
  by (auto simp: book_def all_edges_betw_un_insert1 all_edges_betw_un_insert2 all_edges_betw_un_Un2 insert_commute subset_iff)

text \<open>Cliques of a given number of vertices; the definition of clique from Ramsey is used\<close>

definition size_clique :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "size_clique p K F \<equiv> card K = p \<and> clique K F \<and> K \<subseteq> V"

lemma size_clique_smaller: "\<lbrakk>size_clique p K F; p' < p\<rbrakk> \<Longrightarrow> \<exists>K'. size_clique p' K' F"
  unfolding size_clique_def
  by (meson card_Ex_subset order.trans less_imp_le_nat smaller_clique)

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
  assumes l_large: "15 \<le> l" and lk: "l \<le> k" \<comment> \<open>they should be "sufficiently large"\<close>
      (* in particular, need l ^ (2/3) \<ge> 6*)
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

lemma kn0: "k > 0" and ln0: "l > 0"
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
  using partn_lst_imp_is_clique_RN [OF is_Ramsey_number_RN [of m n]]  assms indep_Red_iff_clique_Blue 
  unfolding is_clique_RN_def size_clique_def clique_indep_def
  by (metis finV finite_subset subset_eq)


text \<open>for calculating the perimeter p\<close>
definition "edge_card \<equiv> \<lambda>C X Y. card (C \<inter> all_edges_betw_un X Y)"

definition "gen_density \<equiv> \<lambda>C X Y. edge_card C X Y / (card X * card Y)"

abbreviation "red_density X Y \<equiv> gen_density Red X Y"
abbreviation "blue_density X Y \<equiv> gen_density Blue X Y"

lemma edge_card_empty [simp]: "edge_card C X {} = 0"
  by (auto simp: edge_card_def)

lemma edge_card_le: 
  assumes "finite X" "finite Y"
  shows "edge_card C X Y \<le> card X * card Y"
unfolding edge_card_def
  by (metis Int_lower2 all_edges_betw_un_le assms card_mono finite_all_edges_betw_un order_trans)

lemma gen_density_ge0: "gen_density C X Y \<ge> 0"
  by (auto simp: gen_density_def)

lemma gen_density_gt0: 
  assumes "finite X" "finite Y" "{x,y} \<in> C" "x \<in> X" "y \<in> Y" "C \<subseteq> E"
  shows "gen_density C X Y > 0"
proof -
  have xy: "{x,y} \<in> all_edges_betw_un X Y"
    using assms by (auto simp: all_edges_betw_un_def)
  moreover have "finite (all_edges_betw_un X Y)"
    by (simp add: assms finite_all_edges_betw_un)
  ultimately have "edge_card C X Y > 0"
    by (metis IntI assms(3) card_0_eq edge_card_def emptyE finite_Int gr0I)
  with xy show ?thesis
    using assms gen_density_def less_eq_real_def by fastforce
qed

lemma gen_density_le_1_minus: 
  shows "gen_density C X Y \<le> 1 - gen_density (E-C) X Y"
proof (cases "finite X \<and> finite Y")
  case True
  have "C \<inter> all_edges_betw_un X Y \<union> (E - C) \<inter> all_edges_betw_un X Y = all_edges_betw_un X Y"
    by (auto simp: all_edges_betw_un_def)
  with True have "(edge_card C X Y) + (edge_card (E - C) X Y) \<le> card (all_edges_betw_un X Y)"
    unfolding edge_card_def
    by (metis Diff_Int_distrib2 Diff_disjoint card_Un_disjoint card_Un_le finite_Int finite_all_edges_betw_un)
  with True show ?thesis
    apply (simp add: gen_density_def field_split_simps)
    by (smt (verit) all_edges_betw_un_le of_nat_add of_nat_mono of_nat_mult)
qed (auto simp: gen_density_def)

lemma gen_density_lt1: 
  assumes "{x,y} \<in> E-C" "x \<in> X" "y \<in> Y" "C \<subseteq> E"
  shows "gen_density C X Y < 1"
proof (cases "finite X \<and> finite Y")
  case True
  then have "0 < gen_density (E - C) X Y"
    using assms gen_density_gt0 by auto
  have "gen_density C X Y \<le> 1 - gen_density (E - C) X Y"
    by (intro gen_density_le_1_minus)
  then show ?thesis
    using \<open>0 < gen_density (E - C) X Y\<close> by linarith
qed (auto simp: gen_density_def)

lemma gen_density_le1: "gen_density C X Y \<le> 1"
  unfolding gen_density_def
  by (smt (verit) card.infinite divide_le_eq_1 edge_card_le mult_eq_0_iff of_nat_le_0_iff of_nat_mono)

lemma red_le_edge_density: "red_density X Y \<le> edge_density X Y"
proof (cases "finite X \<and> finite Y")
  case True
  then have "card (Red \<inter> all_edges_betw_un X Y) \<le> card (all_edges_betw_un X Y)"
    by (simp add: all_edges_betw_un_iff_mk_edge card_mono finite_all_edges_between')
  also have "\<dots> \<le> card (all_edges_between X Y)"
    by (simp add: all_edges_betw_un_iff_mk_edge card_image_le finite_all_edges_between')
  finally show ?thesis
    by (simp add: gen_density_def edge_card_def edge_density_def divide_right_mono)
qed (auto simp: gen_density_def edge_density_def)


lemma edge_card_eq_sum_Neighbours:
  assumes "C \<subseteq> E" and B: "finite B" "disjnt A B"
  shows "edge_card C A B = (\<Sum>i\<in>B. card (Neighbours C i \<inter> A))"
  using B
proof (induction B)
  case empty
  then show ?case
    by (auto simp: edge_card_def)
next
  case (insert b B)
  have "finite C"
    using assms(1) fin_edges finite_subset by blast
  have bij: "bij_betw (\<lambda>e. the_elem(e-{b})) (C \<inter> {{x, b} |x. x \<in> A}) (Neighbours C b \<inter> A)"
    unfolding bij_betw_def
  proof
    have [simp]: "the_elem ({x, b} - {b}) = x" if "x \<in> A" for x
      using insert.prems by (simp add: disjnt_iff insert_Diff_if that)
    show "inj_on (\<lambda>e. the_elem (e - {b})) (C \<inter> {{x, b} |x. x \<in> A})"
      by (auto simp: inj_on_def)
    show "(\<lambda>e. the_elem (e - {b})) ` (C \<inter> {{x, b} |x. x \<in> A}) = Neighbours C b \<inter> A"
      by (fastforce simp: Neighbours_def insert_commute image_iff Bex_def)
  qed
  have "edge_card C A (insert b B) = card (C \<inter> ({{x,b} |x. x \<in> A} \<union> all_edges_betw_un A B))"
    using \<open>C \<subseteq> E\<close> 
    apply (simp add: edge_card_def all_edges_betw_un_insert2 Int_Un_distrib Int_ac)
    by (metis (no_types, lifting) Int_absorb2 Int_assoc Un_commute)
  also have "... = card ((C \<inter> ({{x,b} |x. x \<in> A}) \<union> (C \<inter> all_edges_betw_un A B)))"
    by (simp add: Int_Un_distrib)
  also have "... = card (C \<inter> {{x,b} |x. x \<in> A}) + card (C \<inter> all_edges_betw_un A B)"
  proof (rule card_Un_disjnt)
    show "disjnt (C \<inter> {{x, b} |x. x \<in> A}) (C \<inter> all_edges_betw_un A B)"
      using insert by (auto simp add: disjnt_iff all_edges_betw_un_def doubleton_eq_iff)
  qed (use \<open>finite C\<close> in auto)
  also have "... = card (Neighbours C b \<inter> A) + card (C \<inter> all_edges_betw_un A B)"
    using bij_betw_same_card [OF bij] by simp
  also have "... = (\<Sum>i\<in>insert b B. card (Neighbours C i \<inter> A))"
    using insert by (simp add: edge_card_def)
  finally show ?case .
qed


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
  by (simp_all add: p0_def gen_density_ge0 gen_density_le1)

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

lemma finite_Red [simp]: "finite Red"
  by (metis Red_Blue_all complete fin_edges finite_Un)

lemma finite_Blue [simp]: "finite Blue"
  using Blue_E fin_edges finite_subset by blast


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
  by (auto simp: degree_reg_def X_degree_reg_def V_state_def)

lemma degree_reg_disjoint_state: "disjoint_state U \<Longrightarrow> disjoint_state (degree_reg U)"
  by (auto simp: degree_reg_def X_degree_reg_def disjoint_state_def disjnt_iff)

lemma degree_reg_RB_state: "RB_state U \<Longrightarrow> RB_state (degree_reg U)"
  apply (simp add: degree_reg_def RB_state_def all_edges_betw_un_Un2 split: prod.split prod.split_asm)
  by (meson X_degree_reg_subset all_edges_betw_un_mono2 dual_order.trans)

lemma degree_reg_valid_state: "valid_state U \<Longrightarrow> valid_state (degree_reg U)"
  by (simp add: degree_reg_RB_state degree_reg_V_state degree_reg_disjoint_state valid_state_def)

subsection \<open>Big blue steps: code\<close>

definition bluish :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "bluish \<equiv> \<lambda>X x. card (Neighbours Blue x \<inter> X) \<ge> \<mu> * card X"

definition many_bluish :: "[nat,'a set] \<Rightarrow> bool" where
  "many_bluish \<equiv> \<lambda>l X. card {x\<in>X. bluish X x} \<ge> RN k (nat \<lceil>l powr (2/3)\<rceil>)"

definition "good_blue_book \<equiv> \<lambda>X::'a set. \<lambda>(S,T). book S T Blue \<and> S\<subseteq>X \<and> T\<subseteq>X \<and> card T \<ge> (\<mu> ^ card S) * card X / 2"

lemma l_powr_23_ge6: "nat \<lceil>l powr (2/3)\<rceil> \<ge> 6"
proof -
  have "(6::real) \<le> 15 powr (2/3)"
    by (approximation 12)
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
  where "\<lbrakk>many_bluish l X; good_blue_book X (S,T); card S = best_blue_book_card X\<rbrakk> \<Longrightarrow> big_blue (X,Y,A,B) (T, Y, A, B\<union>S)"

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
  assumes "\<not> termination_condition X Y" "\<not> many_bluish l X"
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
  "\<lbrakk>\<not> termination_condition X Y; \<not> many_bluish l X; V_state(X,Y,A,B)\<rbrakk> 
  \<Longrightarrow> \<exists>x. central_vertex X x \<and> weight X Y x = max_central_vx X Y"
  unfolding max_central_vx_def
  by (metis empty_iff ex_central_vertex finite_central_vertex_set mem_Collect_eq obtains_MAX)

text \<open>it's necessary to make a specific choice; a relational treatment might allow different vertices 
  to be chosen, making a nonsense of the choice between steps 4 and 5\<close>
definition "choose_central_vx \<equiv> \<lambda>(X,Y,A,B). @x. central_vertex X x \<and> weight X Y x = max_central_vx X Y"

lemma choose_central_vx_works: 
  "\<lbrakk>\<not> termination_condition X Y; \<not> many_bluish l X; V_state(X,Y,A,B)\<rbrakk> 
  \<Longrightarrow> central_vertex X (choose_central_vx (X,Y,A,B)) \<and> weight X Y (choose_central_vx (X,Y,A,B)) = max_central_vx X Y"
  unfolding choose_central_vx_def
  using someI_ex [OF ex_best_central_vx] by force

lemma choose_central_vx_X: 
  "\<lbrakk>\<not> termination_condition X Y; \<not> many_bluish l X; V_state(X,Y,A,B)\<rbrakk>  \<Longrightarrow> choose_central_vx (X,Y,A,B) \<in> X"
  using central_vertex_def choose_central_vx_works by presburger

subsection \<open>Red step\<close>

definition "reddish \<equiv> \<lambda>X Y p x. red_density (Neighbours Red x \<inter> X) (Neighbours Red x \<inter> Y) \<ge> p - alpha (hgt p)"

inductive red_step
  where "\<lbrakk>reddish X Y (red_density X Y) x; x = choose_central_vx (X,Y,A,B)\<rbrakk> 
         \<Longrightarrow> red_step (X,Y,A,B) (Neighbours Red x \<inter> X, Neighbours Red x \<inter> Y, insert x A, B)"

lemma red_step_V_state: 
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish l X" "V_state (X,Y,A,B)"
  shows "V_state U'"
proof -
  have "choose_central_vx (X, Y, A, B) \<in> V"
    using assms choose_central_vx_X  by (simp add: V_state_def subset_eq)
  with assms show ?thesis
    by (auto simp: V_state_def elim!: red_step.cases)
qed

lemma red_step_disjoint_state:
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish l X" "V_state (X,Y,A,B)" "disjoint_state (X,Y,A,B)"
  shows "disjoint_state U'"
proof -
  have "choose_central_vx (X, Y, A, B) \<in> X"
    using assms choose_central_vx_X by (simp add: V_state_def)
  with assms show ?thesis
    by (auto simp: disjoint_state_def disjnt_iff not_own_Neighbour elim!: red_step.cases)
qed

lemma red_step_RB_state: 
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish l X" "V_state (X,Y,A,B)" "RB_state (X,Y,A,B)"
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
  assumes "red_step (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish l X" "valid_state (X,Y,A,B)"
  shows "valid_state U'"
  by (meson assms red_step_RB_state red_step_V_state red_step_disjoint_state valid_state_def)

subsection \<open>Density-boost step\<close>

inductive density_boost
  where "\<lbrakk>\<not> reddish X Y (red_density X Y) x; x = choose_central_vx (X,Y,A,B)\<rbrakk> 
         \<Longrightarrow> density_boost (X,Y,A,B) (Neighbours Blue x \<inter> X, Neighbours Red x \<inter> Y, A, insert x B)"


lemma density_boost_V_state: 
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish l X" "V_state (X,Y,A,B)"
  shows "V_state U'"
proof -
  have "choose_central_vx (X, Y, A, B) \<in> V"
    using assms choose_central_vx_X  by (simp add: V_state_def subset_eq)
  with assms show ?thesis
    by (auto simp: V_state_def elim!: density_boost.cases)
qed

lemma density_boost_disjoint_state:
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish l X" "V_state (X,Y,A,B)" "disjoint_state (X,Y,A,B)"
  shows "disjoint_state U'"
proof -
  have "choose_central_vx (X, Y, A, B) \<in> X"
    using assms choose_central_vx_X by (simp add: V_state_def)
  with assms show ?thesis
    by (auto simp: disjoint_state_def disjnt_iff not_own_Neighbour elim!: density_boost.cases)
qed

lemma density_boost_RB_state: 
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish l X" "V_state (X,Y,A,B)" 
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
    by (auto simp: RB_state_def all_edges_betw_un_Un2 x_def [symmetric]  elim!: density_boost.cases)
qed

lemma density_boost_valid_state:
  assumes "density_boost (X,Y,A,B) U'" "\<not> termination_condition X Y" "\<not> many_bluish l X" "valid_state (X,Y,A,B)"
  shows "valid_state U'"
  by (meson assms density_boost_RB_state density_boost_V_state density_boost_disjoint_state valid_state_def)

subsection \<open>Steps 2–5 as a function\<close>

definition next_state :: "'a config \<Rightarrow> 'a config" where
  "next_state \<equiv> \<lambda>(X,Y,A,B). 
       if many_bluish l X then let (S,T) = choose_blue_book(X,Y,A,B) in (T, Y, A, B\<union>S) 
       else let x = choose_central_vx (X,Y,A,B) in
            if reddish X Y (red_density X Y) x then (Neighbours Red x \<inter> X, Neighbours Red x \<inter> Y, insert x A, B)
            else (Neighbours Blue x \<inter> X, Neighbours Red x \<inter> Y, A, insert x B)"

lemma next_state_valid:
  assumes "valid_state (X,Y,A,B)" "\<not> termination_condition X Y"
  shows "valid_state (next_state (X,Y,A,B))"
proof (cases "many_bluish l X")
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
       if many_bluish l X then bblue_step 
       else let x = choose_central_vx (X,Y,A,B) in
            if reddish X Y (red_density X Y) x then red_step
            else dboost_step"

definition stepper_kind :: "nat \<Rightarrow> stepkind" where
  "stepper_kind n = 
     (let (X,Y,A,B) = stepper n in 
      if termination_condition X Y then dreg_step 
      else if even n then next_state_kind (X,Y,A,B) else dboost_step)"

section \<open>Big blue steps: theorems\<close>


lemma 
  fixes e::real
  assumes "e > 0"
  shows "\<forall>\<^sup>\<infinity>n. 1 / real n < e"
proof
  show "1 / real n < e"
    if "nat (ceiling (1 + inverse e)) \<le> n" for n :: nat
    using that assms
    by (simp add: divide_simps mult_of_nat_commute)
qed




lemma Blue_4_1:
  defines "b \<equiv> nat (ceiling (l powr (1/4)))"
  assumes "many_bluish l X" "X\<subseteq>V"
  shows "(\<exists>K. size_clique k K Red) \<or> (\<exists>S T. good_blue_book X (S,T) \<and> real (card S) \<ge> b)"
proof -
  have l_super: "l \<ge> (6/\<mu>) powr (12/5)" (* ultimately the Lemma must be restated to use a limiting argument:
      we can choose a sufficiently large l*)
    sorry
  have lpowr0[simp]: "0 \<le> \<lceil>l powr r\<rceil>" for r
    by (metis ceiling_mono ceiling_zero powr_ge_pzero)
  define W where "W \<equiv> {x\<in>X. bluish X x}"
  define m where "m \<equiv> nat\<lceil>l powr (2/3)\<rceil>"
  have "m>0"
    using l_powr_23_ge6 m_def by linarith
  have "b>0"
    by (simp add: assms(1) ln0)
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
    then have "finite U"
      using finV infinite_super by blast
    have "m \<ge> 6"
      using l_powr_23_ge6 m_def by blast
    then have "k \<le> RN m k" and "m \<noteq> 0"
      using l_large lk RN_3plus \<open>6 \<le> m\<close> by force+
    then have "card X \<ge> l"
      by (metis Collect_subset RN_commute W_def Wbig \<open>X\<subseteq>V\<close> card_mono order.trans finV finite_subset lk)
    have "U \<noteq> X"
      by (metis U_m_Blue \<open>card U = m\<close> \<open>l \<le> card X\<close> order.order_iff_strict no_Blue_clique size_clique_smaller)
    then have "U \<subset> X"
      using W_def \<open>U \<subseteq> W\<close> by blast
    then have cardU_less_X: "card U < card X"
      by (meson \<open>X\<subseteq>V\<close> finV finite_subset psubset_card_mono)
    with \<open>X\<subseteq>V\<close> have cardXU: "card (X-U) = card X - card U"
      by (meson \<open>U \<subset> X\<close> card_Diff_subset finV finite_subset psubset_imp_subset)
    then have real_cardXU[simp]: "real (card (X-U)) = real (card X) - m"
      using \<open>card U = m\<close> cardU_less_X by linarith
    have [simp]: "m \<le> card X"
      using \<open>card U = m\<close> cardU_less_X nless_le by blast
    have "k \<ge> 4"
      using l_large lk by linarith
    have lpowr23: "real l powr (2/3) \<le> real l powr 1"
      using l_large by (intro powr_mono) auto
    then have "m \<le> l"
      by (simp add: m_def)
    then have "m \<le> k"
      using lk by auto
    then have "m < RN k m"
      using RN_commute RN_lower_self \<open>4 \<le> k\<close> \<open>k \<le> RN m k\<close> nat_less_le by force
    also have cX: "RN k m \<le> card X"
      using assms by (metis Collect_subset W_def Wbig card_mono order_trans finV finite_subset)
    finally have "card U < card X"
      using \<open>card U = m\<close> by blast
    text \<open>First part of (10)\<close>
    have "card U * (\<mu> * card X - card U) = m * (\<mu> * (card X - card U)) - (1-\<mu>) * m\<^sup>2"
      using cardU_less_X by (simp add: \<open>card U = m\<close> algebra_simps of_nat_diff numeral_2_eq_2)
    also have "... \<le> real (card (Blue \<inter> all_edges_betw_un U (X-U)))"
    proof -
      have dfam: "disjoint_family_on (\<lambda>u. Blue \<inter> all_edges_betw_un {u} (X-U)) U"
        by (auto simp add: disjoint_family_on_def all_edges_betw_un_def)
      have "\<mu> * (card X - card U) \<le> card (Blue \<inter> all_edges_betw_un {u} (X-U)) + (1-\<mu>) * m" 
        if "u \<in> U" for u
      proof -
        have NBU: "Neighbours Blue u \<inter> U = U - {u}"
          using \<open>clique U Blue\<close> Red_Blue_all singleton_not_edge that 
          by (force simp: Neighbours_def clique_def)
        then have NBX_split: "(Neighbours Blue u \<inter> X) = (Neighbours Blue u \<inter> (X-U)) \<union> (U - {u})"
          using \<open>U \<subset> X\<close> by blast
        moreover have "Neighbours Blue u \<inter> (X-U) \<inter> (U - {u}) = {}"
          by blast
        ultimately have "card(Neighbours Blue u \<inter> X) = card(Neighbours Blue u \<inter> (X-U)) + (m - Suc 0)"
          by (simp add: card_Un_disjoint finite_Neighbours \<open>finite U\<close> \<open>card U = m\<close> that)
        then have "\<mu> * (card X) \<le> real (card (Neighbours Blue u \<inter> (X-U))) + real (m - Suc 0)"
          using W_def \<open>U \<subseteq> W\<close> bluish_def that by force
        then have "\<mu> * (card X - card U) 
                \<le> real (card (Neighbours Blue u \<inter> (X-U))) + real (m - Suc 0) - \<mu> *card U"
          by (smt (verit) cardU_less_X nless_le of_nat_diff right_diff_distrib')
        then have *: "\<mu> * (card X - card U) \<le> real (card (Neighbours Blue u \<inter> (X-U))) + (1-\<mu>)*m"
          using \<mu>01 by (simp add: \<open>card U = m\<close> left_diff_distrib)
        have "inj_on (\<lambda>x. {u,x}) (Neighbours Blue u \<inter> X)"
          by (simp add: doubleton_eq_iff inj_on_def)
        moreover have "(\<lambda>x. {u,x}) ` (Neighbours Blue u \<inter> (X-U)) \<subseteq> Blue \<inter> all_edges_betw_un {u} (X-U)"
          using Blue_E by (auto simp: Neighbours_def all_edges_betw_un_def)
        ultimately have "card (Neighbours Blue u \<inter> (X-U)) \<le> card (Blue \<inter> all_edges_betw_un {u} (X-U))"
          by (metis NBX_split Blue_eq card_image card_mono complete fin_edges finite_Diff finite_Int inj_on_Un)
        with * show ?thesis
          by auto
      qed
      then have "(card U) * (\<mu> * real (card X - card U))
             \<le> (\<Sum>x\<in>U. card (Blue \<inter> all_edges_betw_un {x} (X-U)) + (1-\<mu>) * m)"
        by (meson sum_bounded_below)
      then have "m * (\<mu> * (card X - card U))
             \<le> (\<Sum>x\<in>U. card (Blue \<inter> all_edges_betw_un {x} (X-U))) + (1-\<mu>) * m\<^sup>2"
        apply (simp add: sum.distrib power2_eq_square \<open>card U = m\<close>)
        by (smt (verit) mult.assoc mult_of_nat_commute)
      also have "... \<le> card (\<Union>u\<in>U. Blue \<inter> all_edges_betw_un {u} (X-U)) + (1-\<mu>) * m\<^sup>2"
        by (simp add: dfam card_UN_disjoint' \<open>finite U\<close> flip: UN_simps)
      finally have "m * (\<mu> * (card X - card U)) 
                \<le> card (\<Union>u\<in>U. Blue \<inter> all_edges_betw_un {u} (X-U)) + (1 - \<mu>) * m\<^sup>2" .
      moreover have "(\<Union>u\<in>U. Blue \<inter> all_edges_betw_un {u} (X-U)) = (Blue \<inter> all_edges_betw_un U (X-U))"
        by (auto simp: all_edges_betw_un_def)
      ultimately show ?thesis
        by simp
    qed
    also have "... \<le> edge_card Blue U (X-U)"
      by (simp add: edge_card_def)
    finally have DD: "edge_card Blue U (X-U) \<ge> card U * (\<mu> * card X - card U)" .
    define \<sigma> where "\<sigma> \<equiv> blue_density U (X-U)"
    then have "\<sigma> \<ge> 0" by (simp add: gen_density_ge0)
    have "\<sigma> \<le> 1"
      by (simp add: \<sigma>_def gen_density_le1)
    have 6: "real (6*k) \<le> real (2 + k*m)"
      by (metis \<open>m\<ge>6\<close> mult.commute mult_le_mono of_nat_mono order.refl trans_le_add2)
    then have km: "k + m \<le> Suc (k * m)"
      using l_large lk \<open>m \<le> l\<close> by linarith

    have "real m / 2 * (2 + real k * (1 - \<mu>)) \<le> real m / 2 * (2 + real k)"
      using \<mu>01 by (simp add: algebra_simps)
    also have "\<dots> \<le> (k - 1) * (m - 1)"
      using l_large lk 6 \<open>m \<le> k\<close> by (simp add: algebra_simps of_nat_diff km)
    finally  have "(m/2) * (2 + k * (1-\<mu>)) \<le> RN k m"
      using RN_times_lower' [of k m] by linarith
    then have "\<mu> - 2/k \<le> (\<mu> * card X - card U) / (card X - card U)"
      using kn0 \<mu>01 cardU_less_X \<open>card U = m\<close> cX by (simp add: of_nat_diff field_simps)
    also have "\<dots> \<le> \<sigma>"
      using \<open>m\<noteq>0\<close> \<open>card U = m\<close> cardU_less_X cardXU DD
      by (simp add: \<sigma>_def gen_density_def field_simps mult_less_0_iff zero_less_mult_iff)
    finally have eq10: "\<mu> - 2/k \<le> \<sigma>" .
    have B: "2 * b / m \<le> \<mu> - 2/k"
    proof -
      have 512: "5/12 \<le> (1::real)"
        by simp
      with l_super have "l powr (5/12) \<ge> ((6/\<mu>) powr (12/5)) powr (5/12)"
        by (simp add: powr_mono2)
      then have lge: "l powr (5/12) \<ge> 6/\<mu>"
        using \<mu>01(1) powr_powr by force
      have "2 * b \<le> 2 * (l powr (1 / 4) + 1)"
        by (simp add: b_def del: zero_le_ceiling distrib_left_numeral)
      then have "2*b / m + 2/l \<le> 2 * (l powr (1/4) + 1) / l powr (2/3) + 2/l"
        by (simp add: b_def m_def frac_le ln0 del: zero_le_ceiling distrib_left_numeral)
      also have "... \<le> (2 * l powr (1/4) + 4) / l powr (2/3)"
        using ln0 lpowr23 by (simp add: pos_le_divide_eq pos_divide_le_eq algebra_simps)
      also have "... \<le> (2 * l powr (1/4) + 4 * l powr (1/4)) / l powr (2/3)"
        by (smt (verit, ccfv_SIG) Num.of_nat_simps(2) diff_divide_distrib divide_pos_pos gr_one_powr l_large numeral_Bit1 numeral_One numeral_le_real_of_nat_iff of_nat_numeral)
      also have "... = 6 / l powr (5/12)"
        by (simp add: divide_simps flip: powr_add)
      also have "... \<le> \<mu>"
        using lge \<mu>01 by (simp add: divide_le_eq mult.commute)
      finally have "2*b / m + 2/l \<le> \<mu>" .
      then show ?thesis
        using lk \<open>m\<noteq>0\<close> ln0 by (smt (verit, best) frac_le of_nat_0_less_iff of_nat_mono)
    qed
    with eq10 have "2 / (m/b) \<le> \<sigma>"
      by simp
    moreover have "l powr (2/3) \<le> nat \<lceil>real l powr (2/3)\<rceil>"
      using of_nat_ceiling by blast
    ultimately have ble: "b \<le> \<sigma> * m / 2"
      using mult_left_mono \<open>\<sigma> \<ge> 0\<close> l_large kn0 lk unfolding b_def m_def powr_diff
      by (simp add: divide_simps)
    then have "\<sigma> > 0"
      using \<open>0 \<le> \<sigma>\<close> \<open>6 \<le> m\<close> \<open>m \<le> l\<close> powr_gt_zero by (fastforce simp add: b_def)

    text \<open>now for the material between (10) and (11)\<close>
    have "\<sigma> * real m / 2 \<le> m"
      using \<open>\<sigma> \<le> 1\<close> \<open>m \<noteq> 0\<close> by auto
    with ble have "b \<le> m"
      by linarith

    have "card X > 2 powr (m/2)"
      by (metis RN_commute RN_lower_nodiag \<open>6 \<le> m\<close> \<open>m \<le> k\<close> add_leE less_le_trans cX numeral_Bit0 of_nat_mono)

    text \<open>Mehta\<close> (*four_two_aux''' PROBABLY NOT NEEDED *)
    have "exp (- 2 * (i / (\<sigma> * m))) \<le> 1 - i / (\<sigma> * m)" if "i<b" for i
      using ble \<open>0 \<le> \<sigma>\<close> that
      by (intro order_trans [OF exp_thing]) auto

    have "card X > 2*m"
      using cX 
      sorry
    have "b\<^sup>2 / (\<sigma>*m) \<le> b/2"
      using ble \<open>b>0\<close>
      by (simp add: power2_eq_square divide_simps)

    have "m/b \<ge> l powr (5/12)"
      apply (simp add: m_def b_def divide_simps)

    sorry

    have "\<mu>/2 \<le> \<sigma>"
      using eq10 B \<open>0 < b\<close> \<open>m \<le> k\<close> \<open>0 < m\<close>
      by (smt (verit, ccfv_SIG) of_nat_add field_sum_of_halves frac_le mult_2 nat_less_real_le of_nat_0 of_nat_mono)

    define \<Phi> where "\<Phi> \<equiv> \<Sum>v \<in> X-U. card (Neighbours Blue v \<inter> U) choose b"

    have "\<mu>^b/2 * card X \<le> (1 - b\<^sup>2 / (\<sigma>*m)) * \<sigma>^b * card (X-U)"
      using \<open>\<sigma> > 0\<close> \<open>m \<noteq> 0\<close> cX
      apply (simp add: divide_simps)
      apply (auto simp: algebra_simps)

      using eq10
      apply (simp add: )
      using real_cardXU
      unfolding b_def m_def
      apply (simp add: cardXU cardU_less_X )
      sorry
    also have "... \<le> exp (- (of_nat (b\<^sup>2) / (\<sigma>*m))) * \<sigma>^b * card (X-U)"
      unfolding divide_inverse
      using \<open>0 \<le> \<sigma>\<close> \<open>card U = m\<close> cardU_less_X
      by (intro mult_right_mono exp_minus_ge order_refl) auto
    also have "\<dots> = \<sigma>^b * exp (- of_nat (b\<^sup>2) / (\<sigma>*m)) * card (X-U)"
      by (simp add: mult.commute) 
    also have "\<dots> \<le> 1/(m choose b) * ((\<sigma>*m) gchoose b) * card (X-U)"
    proof (intro mult_right_mono)
      have "0 < real m gchoose b"
        by (metis \<open>b \<le> m\<close> binomial_gbinomial of_nat_0_less_iff zero_less_binomial_iff)
      then have "\<sigma> ^ b * ((real m gchoose b) * exp (- ((real b)\<^sup>2 / (\<sigma> * real m)))) \<le> \<sigma> * real m gchoose b"
        using Fact_D1_73 [OF \<open>\<sigma>>0\<close> \<open>\<sigma>\<le>1\<close> ble] \<open>b\<le>m\<close> cardU_less_X \<open>0 < \<sigma>\<close>
        by (simp add: field_split_simps binomial_gbinomial)
      then show "\<sigma>^b * exp (- real (b\<^sup>2) / (\<sigma> * m)) \<le> 1/(m choose b) * (\<sigma> * m gchoose b)"
        using \<open>b\<le>m\<close> cardU_less_X \<open>0 < \<sigma>\<close> \<open>0 < m gchoose b\<close>
        by (simp add: field_split_simps binomial_gbinomial)
    qed auto
    also have "... = 1/(m choose b) * (((\<sigma>*m) gchoose b) * card (X-U))"
      by (simp add: mult.assoc)
    also have "\<dots> \<le> 1/(m choose b) * \<Phi>"
    proof (intro mult_left_mono)
      have eeq: "edge_card Blue U (X-U) = (\<Sum>i\<in>X-U. card (Neighbours Blue i \<inter> U))"
      proof (intro edge_card_eq_sum_Neighbours)
        show "finite (X-U)"
          by (meson \<open>X\<subseteq>V\<close> finV finite_Diff finite_subset)
      qed (use disjnt_def Blue_E in auto)
      have "(\<Sum>i\<in>X - U. card (Neighbours Blue i \<inter> U)) / (real (card X) - m) 
          = blue_density U (X-U) * m"
        using \<open>m>0\<close> by (simp add: gen_density_def \<open>card U = m\<close> eeq divide_simps)
      then have *: "(\<Sum>i\<in>X - U. real (card (Neighbours Blue i \<inter> U)) /\<^sub>R real (card (X-U))) = \<sigma> * m"
        by (simp add: \<sigma>_def divide_inverse_commute flip: sum_distrib_left)
      have "mbinomial (\<Sum>i\<in>X - U. real (card (Neighbours Blue i \<inter> U)) /\<^sub>R (card (X-U))) b 
         \<le> (\<Sum>i\<in>X - U. inverse (real (card (X-U))) * mbinomial (card (Neighbours Blue i \<inter> U)) b)"
      proof (rule convex_on_sum)
        show "finite (X-U)"
          using cardU_less_X zero_less_diff by fastforce
        show "convex_on UNIV (\<lambda>a. mbinomial a b)"
          using assms(1) convex_mbinomial ln0 by auto
        show "(\<Sum>i\<in>X - U. inverse (card (X-U))) = 1"
          using cardU_less_X cardXU by force
      qed (use \<open>U \<subset> X\<close> in auto)
      with ble 
      show "(\<sigma>*m gchoose b) * card (X-U) \<le> \<Phi>"
        unfolding * \<Phi>_def 
        by (simp add: cardU_less_X cardXU binomial_gbinomial divide_simps  flip: sum_distrib_left sum_divide_distrib)
    qed auto
    finally have F: "\<mu>^b/2 * card X \<le> 1/(m choose b) * \<Phi>" .

    define \<Omega> where "\<Omega> \<equiv> nsets U b"  \<comment>\<open>Choose a random subset of size @{term b}\<close>
    have card\<Omega>: "card \<Omega> = m choose b"
      by (simp add: \<Omega>_def \<open>card U = m\<close>)
    then have fin\<Omega>: "finite \<Omega>" and "\<Omega> \<noteq> {}"
      using \<open>b \<le> m\<close> not_less by fastforce+
    then have "card \<Omega> > 0"
      by (simp add: card_gt_0_iff)
    define M where "M \<equiv> uniform_count_measure \<Omega>"
    have space_eq: "space M = \<Omega>"
      by (simp add: M_def space_uniform_count_measure)
    have sets_eq: "sets M = Pow \<Omega>"
      by (simp add: M_def sets_uniform_count_measure)
    interpret P: prob_space M
      using M_def \<open>b \<le> m\<close> card\<Omega> fin\<Omega> prob_space_uniform_count_measure by force
    have measure_eq: "measure M C = (if C \<subseteq> \<Omega> then card C / card \<Omega> else 0)" for C
      by (simp add: M_def fin\<Omega> measure_uniform_count_measure_if) 

    define Int_NB where "Int_NB \<equiv> \<lambda>S. \<Inter>v\<in>S. Neighbours Blue v \<inter> (X-U)"
    have sum_card_NB: 
      "(\<Sum>A\<in>\<Omega>. card (\<Inter>(Neighbours Blue ` A) \<inter> Y)) = (\<Sum>v\<in>Y. card (Neighbours Blue v \<inter> U) choose b)"
      if "finite Y" "Y \<subseteq> X-U" for Y
      using that
    proof (induction Y)
      case (insert y Y)
      have *: "\<Omega> \<inter> {A. \<forall>x\<in>A. y \<in> Neighbours Blue x} = nsets (Neighbours Blue y \<inter> U) b"
              "\<Omega> \<inter> - {A. \<forall>x\<in>A. y \<in> Neighbours Blue x} = \<Omega> - nsets (Neighbours Blue y \<inter> U) b"
        using insert.prems by (auto simp: \<Omega>_def nsets_def in_Neighbours_iff insert_commute)
      then show ?case
        using insert fin\<Omega>
        apply (simp add: Int_insert_right sum_Suc sum.If_cases if_distrib [of card] flip: insert.IH)
        by (smt (verit, best) Int_lower1 add.commute sum.subset_diff)
    qed auto
    have "(\<Sum>x\<in>\<Omega>. card (if x = {} then UNIV else \<Inter> (Neighbours Blue ` x) \<inter> (X-U))) 
        = (\<Sum>x\<in>\<Omega>. card (\<Inter> (Neighbours Blue ` x) \<inter> (X-U)))"
      unfolding \<Omega>_def nsets_def using \<open>0 < b\<close>
      by (force simp add: intro: sum.cong)
    also have "\<dots> = (\<Sum>v\<in>X - U. card (Neighbours Blue v \<inter> U) choose b)"
      by (metis sum_card_NB \<open>X\<subseteq>V\<close> dual_order.refl finV finite_Diff rev_finite_subset)
    finally have "sum (card o Int_NB) \<Omega> = \<Phi>"
      by (simp add: \<Omega>_def \<Phi>_def Int_NB_def)
    moreover
    have "ennreal (P.expectation (\<lambda>S. card (Int_NB S))) = sum (card o Int_NB) \<Omega> / (card \<Omega>)"
      using integral_uniform_count_measure M_def fin\<Omega> by fastforce
    ultimately have P: "P.expectation (\<lambda>S. card (Int_NB S)) = \<Phi> / (m choose b)"
      by (metis Bochner_Integration.integral_nonneg card\<Omega> divide_nonneg_nonneg ennreal_inj of_nat_0_le_iff)
    have False if "\<And>S. S \<in> \<Omega> \<Longrightarrow> card (Int_NB S) < \<Phi> / (m choose b)"
    proof -
      define L where "L \<equiv> (\<lambda>S. \<Phi> / real (m choose b) - card (Int_NB S)) ` \<Omega>"
      have "finite L" "L \<noteq> {}"
        using L_def fin\<Omega>  \<open>\<Omega>\<noteq>{}\<close> by blast+
      define \<epsilon> where "\<epsilon> \<equiv> Min L"
      have "\<epsilon> > 0"
        using that fin\<Omega> \<open>\<Omega> \<noteq> {}\<close> by (simp add: L_def \<epsilon>_def)
      then have "\<And>S. S \<in> \<Omega> \<Longrightarrow> card (Int_NB S) \<le> \<Phi> / (m choose b) - \<epsilon>"
        using linorder_class.Min_le [OF \<open>finite L\<close>]
        by (fastforce simp add: algebra_simps \<epsilon>_def L_def)
      then have "P.expectation (\<lambda>S. card (Int_NB S)) \<le> \<Phi> / (m choose b) - \<epsilon>"
        using M_def P P.not_empty not_integrable_integral_eq space_eq \<open>\<epsilon> > 0\<close>
        by (intro P.integral_le_const) fastforce+
      then show False
        using P \<open>0 < \<epsilon>\<close> by auto
    qed
    then obtain S where "S \<in> \<Omega>" and Sge: "card (Int_NB S) \<ge> \<Phi> / (m choose b)"
      using linorder_not_le by blast
    then have "S \<subseteq> U"
      by (simp add: \<Omega>_def nsets_def subset_iff)
    have "card S = b" "clique S Blue"
      using \<open>S \<in> \<Omega>\<close> \<open>U \<subseteq> V\<close> \<open>clique U Blue\<close> smaller_clique 
      unfolding \<Omega>_def nsets_def size_clique_def by auto
    have "\<Phi> / (m choose b) \<ge> \<mu>^b * card X / 2"
      using F by simp
    then have S: "card (Int_NB S) \<ge> \<mu>^b * card X / 2"
      using Sge by linarith
    obtain v where "v \<in> S"
      using \<open>0 < b\<close> \<open>card S = b\<close> by fastforce
    have "all_edges_betw_un S (S \<union> Int_NB S) \<subseteq> Blue"
      using \<open>clique S Blue\<close> unfolding all_edges_betw_un_def Neighbours_def clique_def Int_NB_def
      by fastforce
    then have "good_blue_book X (S, Int_NB S)"
      using \<open>S\<subseteq>U\<close> \<open>v \<in> S\<close> \<open>U \<subset> X\<close> S \<open>card S = b\<close>
      unfolding good_blue_book_def book_def size_clique_def Int_NB_def disjnt_iff
      by blast
    then show ?thesis
      using \<open>card S = b\<close> by blast
  qed auto
qed

section \<open>Density-boost steps\<close>

text \<open>"See observation 5.5 below"\<close>
lemma sum_Weight_ge0: "(\<Sum>x\<in>X. \<Sum>y\<in>X. Weight X Y x y) \<ge> 0"
  sorry
