theory Diagonal imports
  "HOL-Library.Disjoint_Sets" "HOL-Library.Ramsey" "Undirected_Graph_Theory.Undirected_Graph_Basics" 
  "Special_Function_Bounds.Exp_Bounds"
  "HOL-ex.Sketch_and_Explore"
   
begin

text \<open>not actually used but possibly interesting\<close>
lemma gbinomial_is_prod: "(a gchoose k) = (\<Prod>i<k. (a - of_nat i) / (1 + of_nat i))"
  unfolding gbinomial_prod_rev
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  show ?case
    by (simp add: divide_simps flip: Suc)
qed

section \<open>Appendix D\<close>

subsection \<open>Fact D1\<close>

text \<open>from appendix D, page 55\<close>
lemma Fact_D1_73_aux:
  fixes \<sigma>::real and m b::nat  
  assumes \<sigma>: "0<\<sigma>" and bm: "real b < real m"
  shows  "((\<sigma>*m) gchoose b) * inverse (m gchoose b) = \<sigma>^b * (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))"
proof -
  have "((\<sigma>*m) gchoose b) * inverse (m gchoose b) = (\<Prod>i<b. (\<sigma>*m - i) / (real m - real i))"
    using bm by (simp add: gbinomial_prod_rev prod_dividef atLeast0LessThan)
  also have "... = \<sigma>^b * (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))"
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
  then have "\<sigma> * m / 2 \<le> real m"
    using \<sigma> by auto
  with b \<sigma> False have bm: "real b < real m"
    by (smt (verit, best) divide_eq_1_iff mult_cancel_right2 of_nat_eq_0_iff times_divide_eq_left)
  have nonz: "m gchoose b \<noteq> 0"
    by (metis binomial_gbinomial bm less_le_not_le of_nat_eq_0_iff of_nat_le_iff zero_less_binomial_iff)
  have EQ: "((\<sigma>*m) gchoose b) * inverse (m gchoose b) = \<sigma>^b * (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))" 
    using Fact_D1_73_aux \<open>0<\<sigma>\<close> bm by blast
  also have "... \<le> \<sigma> ^ b * 1"
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
      also have "... \<le> inverse (1 + 2*x)"
        using exp_ge_add_one_self that by auto
      also have "... \<le> 1-x"
        using that by (simp add: mult_left_le field_simps)
      finally show ?thesis .
    qed
    have "exp (-2 * real i / (\<sigma>*m)) = exp (-2 * (i / (\<sigma>*m)))"
      by simp
    also have "\<dots> \<le> 1 - i/(\<sigma> * m)"
    proof (intro exp_le)
      show "0 \<le> real i / (\<sigma> * real m)"
        using \<sigma> by auto
      show "real i / (\<sigma> * real m) \<le> 1/2"
        using b that by auto
    qed
    also have "... \<le> 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i))"
      using \<sigma> b that 
      apply (simp add: field_split_simps)
      using bm by linarith
    finally show ?thesis .
  qed
  have "sum real {..<b} \<le> real b ^ 2 / 2"
    by (induction b) (auto simp: power2_eq_square algebra_simps)
  with \<sigma> have "exp (- (real b ^ 2) / (\<sigma>*m)) \<le> exp (- (2 * (\<Sum>i<b. i) / (\<sigma>*m)))"
    by (simp add: mult_less_0_iff divide_simps)
  also have "... = exp (\<Sum>i<b. -2 * real i / (\<sigma>*m))"
    by (simp add: sum_negf sum_distrib_left sum_divide_distrib)
  also have "... = (\<Prod>i<b. exp (-2 * real i / (\<sigma>*m)))"
    using exp_sum by blast
  also have "... \<le> (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))"
    using * by (force intro: prod_mono)
  finally have "exp (- (real b)\<^sup>2 / (\<sigma> * real m)) \<le> (\<Prod>i<b. 1 - (1 - \<sigma>) * real i / (\<sigma> * (real m - real i)))" .
  with EQ have "\<sigma>^b * exp (- (real b ^ 2) / (\<sigma>*m)) \<le> ((\<sigma>*m) gchoose b) * inverse (real m gchoose b)"
    by (simp add: assms(1))
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
  also have "... \<le> inverse (1 + 3*x/2 + (1/2)*(3*x/2)^2 + (1/6)*(3*x/2)^3)"
    apply (intro le_imp_inverse_le exp_lower_taylor_2)
    by (smt (verit) divide_nonneg_nonneg mult_nonneg_nonneg \<open>0 \<le> x\<close> zero_le_power)
  also have "... \<le> 1 - 4*x/3"
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
    also have "... \<le> 1 - 8*i / (7 * (real m - real b))"
    proof -
      have "real i * (real b * 7) \<le> real i * real m"
        using b' by (simp add: mult_left_mono)
      then show ?thesis
        using b' by (simp add: field_split_simps)
    qed
    also have "... \<le> 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i))"
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
  also have "... = exp (\<Sum>i<b. -3 * real i / (2*m))"
    by (simp add: sum_negf sum_distrib_left sum_divide_distrib)
  also have "... = (\<Prod>i<b. exp (-3 * real i / (2*m)))"
    using exp_sum by blast
  also have "... \<le> (\<Prod>i<b. 1 - ((1-\<sigma>)*i) / (\<sigma> * (real m - real i)))"
    using * by (force intro: prod_mono)
  finally have "exp (- (3 * real b ^ 2) / (4*m)) \<le> (\<Prod>i<b. 1 - (1 - \<sigma>) * real i / (\<sigma> * (real m - real i)))" .
  with EQ have "\<sigma>^b * exp (- (3 * real b ^ 2) / (4*m)) \<le> ((\<sigma>*m) gchoose b) * inverse (real m gchoose b)"
    by (simp add: assms(1))
  with \<sigma> bm show ?thesis
    by (simp add: field_split_simps flip: binomial_gbinomial)
qed

section \<open>Lemmas relating to Ramsey's theorem\<close>

class infinite =
  assumes infinite_UNIV: "infinite (UNIV::'a set)"

instance nat :: infinite
  by (intro_classes) simp
instance prod :: (infinite, type) infinite
  by intro_classes (simp add: finite_prod infinite_UNIV)
instance list :: (type) infinite
  by intro_classes (simp add: infinite_UNIV_listI)

lemma smaller_clique: "\<lbrakk>clique R E; R' \<subseteq> R\<rbrakk> \<Longrightarrow> clique R' E"
  by (auto simp: clique_def)

lemma smaller_indep: "\<lbrakk>indep R E; R' \<subseteq> R\<rbrakk> \<Longrightarrow> indep R' E"
  by (auto simp: indep_def)

text \<open>identifying Ramsey numbers (not the minimum) for a given type and pair of integers\<close>
definition is_Ramsey_number where
  "is_Ramsey_number \<equiv> \<lambda>U::'a itself. \<lambda>m n r. r \<ge> 1 \<and> (\<forall>V::'a set. \<forall>E. finite V \<and> card V \<ge> r \<longrightarrow>
    (\<exists>K \<subseteq> V. card K = m \<and> clique K E \<or> card K = n \<and> indep K E))"

text \<open>All complete graphs of a given cardinality are the same\<close>
lemma 
  assumes "is_Ramsey_number (U::'a::infinite itself) m n r"
  shows "is_Ramsey_number (V::'b itself) m n r"
  unfolding is_Ramsey_number_def
  proof (intro conjI strip)
  show "1 \<le> r"
    by (meson assms is_Ramsey_number_def)
next
  fix V :: "'b set" and E :: "'b set set"
  assume V: "finite V \<and> r \<le> card V"
  obtain W::"'a set" where "finite W" and W: "card W = card V"
    by (metis infinite_UNIV infinite_arbitrarily_large)
  with V obtain f where f: "bij_betw f V W"
    by (metis finite_same_card_bij)
  define F where "F \<equiv> (\<lambda>e. f ` e) ` (E \<inter> Pow V)"
  obtain R where "R\<subseteq>W" and R: "card R = m \<and> clique R F \<or> card R = n \<and> indep R F"
    using assms V W \<open>finite W\<close> unfolding is_Ramsey_number_def by metis
  define S where "S \<equiv> inv_into V f ` R"
  have eq_iff: "\<forall>v\<in>R. \<forall>w\<in>R. inv_into V f v = inv_into V f w \<longleftrightarrow> v=w"
    by (metis \<open>R \<subseteq> W\<close> bij_betw_inv_into_right f subset_iff)
  have *: "\<And>v w x. \<lbrakk>{v, w} = f ` x; x \<subseteq> V\<rbrakk> \<Longrightarrow> {inv_into V f v, inv_into V f w} = x"
    by (metis bij_betw_def f image_empty image_insert inv_into_image_cancel)
  have "card S = card R"
    by (metis S_def \<open>R \<subseteq> W\<close> f bij_betw_inv_into bij_betw_same_card bij_betw_subset)
  moreover have "clique S E" if "clique R F"
    using that * by (force simp: S_def clique_def image_iff eq_iff F_def)
  moreover have "indep S E" if "indep R F"
    unfolding S_def indep_def
  proof clarify
    fix x y
    assume xy: "x \<in> R" "y \<in> R"
      and "inv_into V f x \<noteq> inv_into V f y"
      and E: "{inv_into V f x, inv_into V f y} \<in> E"
    then have "x \<noteq> y"
      by blast
    then have *: "\<not> (\<exists>e\<in>E \<inter> Pow V. {x,y} = f ` e)"
      by (metis F_def image_eqI indep_def that xy)
    have "inv_into V f x \<in> V \<and> inv_into V f y \<in> V"
      by (metis \<open>R \<subseteq> W\<close> bij_betw_imp_surj_on f inv_into_into subsetD xy)
    then have "{x, y} \<noteq> f ` {inv_into V f x, inv_into V f y}"
      using * E by blast
    with f \<open>R \<subseteq> W\<close> xy have "{x,y} \<in> F"
      by (auto simp: bij_betw_def doubleton_eq_iff)
    with * show False
      by (simp add: F_def image_iff)
  qed
  ultimately show "\<exists>R. (R::'b set) \<subseteq> V \<and> (card R = m \<and> clique R E \<or> card R = n \<and> indep R E)"
    by (metis R S_def \<open>R \<subseteq> W\<close> bij_betw_def bij_betw_inv_into f image_mono)
qed

lemma is_Ramsey_number_le:
  assumes "is_Ramsey_number U m n r" "m' \<le> m" "n' \<le> n"
  shows "is_Ramsey_number U m' n' r"
  using assms
  apply (clarsimp simp: is_Ramsey_number_def)
  apply (drule_tac x="V" in spec)
  apply (simp add: )
  apply (drule_tac x="E" in spec)
  using smaller_clique smaller_indep
  by (metis (no_types, opaque_lifting) dual_order.trans obtain_subset_with_card_n)

lemma is_Ramsey_number_ge:
  assumes "is_Ramsey_number U m n r'" "r' \<le> r"
  shows "is_Ramsey_number U m n r"
  using assms by (auto simp: is_Ramsey_number_def)

lemma ex_Ramsey_number: "\<exists>r. is_Ramsey_number U m n r"
  using ramsey2 [of m n] by (simp add: is_Ramsey_number_def)

definition RN where
  "RN \<equiv> \<lambda>U::'a itself. \<lambda>m n. LEAST r. is_Ramsey_number U m n r"

lemma is_Ramsey_number_RN: "is_Ramsey_number U m n (RN U m n)"
  by (simp add: LeastI_ex RN_def ex_Ramsey_number)

lemma RN_le: "is_Ramsey_number U m n r \<Longrightarrow> RN U m n \<le> r"
  by (simp add: Least_le RN_def)

lemma Ramsey_RN:
  fixes U :: "'a itself" and V :: "'a set"
  assumes "card V \<ge> RN U m n" "finite V"
  shows "\<exists>K \<subseteq> V. card K = m \<and> clique K E \<or> card K = n \<and> indep K E"
  using is_Ramsey_number_RN [of U m n] assms
  unfolding is_Ramsey_number_def by blast

lemma RN_mono:
  assumes "m' \<le> m" "n' \<le> n"
  shows "RN U m' n' \<le> RN U m n"
  by (meson RN_le assms is_Ramsey_number_RN is_Ramsey_number_le)


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
  assumes ln0: "0 < l" and lk: "l \<le> k" 
  assumes complete: "E \<equiv> all_edges V"
  fixes Red Blue
  assumes Red_not_Blue: "Red \<noteq> Blue"
  assumes part_RB: "partition_on E {Red,Blue}"
  assumes no_Red_clique: "\<not> (\<exists>K. size_clique k K Red)"
  assumes no_Blue_clique: "\<not> (\<exists>K. size_clique l K Blue)"
  \<comment> \<open>the following are local to the program and possibly require their own locale\<close>
  fixes X0 :: "'a set" and Y0 :: "'a set"    \<comment> \<open>initial values\<close>
  assumes XY0: "disjnt X0 Y0" "X0 \<subseteq> V" "Y0 \<subseteq> V"
  fixes \<mu>::real
  assumes "0 < \<mu>" "\<mu> < 1"
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
  using lk ln0 by auto

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

lemma indep_Red_iff_clique_Bllue: "K \<subseteq> V \<Longrightarrow> indep K Red \<longleftrightarrow> clique K Blue"
  by (simp add: Blue_eq indep_iff_clique)

lemma Red_Blue_RN:
  fixes X :: "'a set"
  assumes "card X \<ge> RN (TYPE('a)) m n" "X\<subseteq>V"
  shows "\<exists>K \<subseteq> X. size_clique m K Red \<or> size_clique n K Blue"
  using is_Ramsey_number_RN [of "TYPE('a)" m n] assms indep_Red_iff_clique_Bllue
  unfolding is_Ramsey_number_def size_clique_def
  by (metis finV finite_subset subset_eq)


text \<open>for calculating the perimeter p\<close>
definition "density C X Y \<equiv> card (C \<inter> all_edges_betw_un X Y) / (card X * card Y)"

abbreviation "red_density X Y \<equiv> density Red X Y"
abbreviation "blue_density X Y \<equiv> density Blue X Y"

lemma red_density_ge0: "red_density X Y \<ge> 0"
  by (auto simp: density_def)

lemma red_le_edge_density: "red_density X Y \<le> edge_density X Y"
proof (cases "finite X \<and> finite Y")
  case True
  then have "card (Red \<inter> all_edges_betw_un X Y) \<le> card (all_edges_betw_un X Y)"
    by (simp add: all_edges_betw_un_iff_mk_edge card_mono finite_all_edges_between')
  also have "... \<le> card (all_edges_between X Y)"
    by (simp add: all_edges_betw_un_iff_mk_edge card_image_le finite_all_edges_between')
  finally show ?thesis
    by (simp add: density_def edge_density_def divide_right_mono)
qed (auto simp: density_def edge_density_def)

lemma red_density_le1: "red_density X Y \<le> 1"
  by (meson edge_density_le1 order_trans red_le_edge_density)

definition Weight :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real" where
  "Weight \<equiv> \<lambda>X Y x y. inverse (card Y) * (card (Neighbours Red x \<inter> Neighbours Red y \<inter> Y)
                      - red_density X Y * card (Neighbours Red x \<inter> Y))"

definition weight :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> real" where
  "weight \<equiv> \<lambda>X Y x. \<Sum>y \<in> X-{x}. Weight X Y x y"

text \<open>"See observation 5.5 below"\<close>
lemma sum_Weight_ge0: "(\<Sum>x\<in>X. \<Sum>y\<in>X. Weight X Y x y) \<ge> 0"
  sorry

definition "p0 \<equiv> red_density X0 Y0"

definition "epsk \<equiv> k powr (-1/4)"

definition "q \<equiv> \<lambda>h. p0 + ((1 + epsk)^h - 1) / k"

definition "height \<equiv> \<lambda>p. LEAST h. p \<le> q h \<and> h>0"

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

definition "termination_condition \<equiv> \<lambda>X Y. card X \<le> RN (TYPE('a)) k (nat \<lceil>l powr (3/4)\<rceil>) \<or> red_density X Y \<le> 1/k"

lemma 
  assumes "V_state(X,Y,A,B)" 
  shows finX: "finite X" and finY: "finite Y" and finA: "finite A" and finB: "finite B"
  using V_state_def assms finV finite_subset by auto

subsection \<open>Degree regularisation\<close>

definition "red_dense \<equiv> \<lambda>Y p x. card (Neighbours Red x \<inter> Y) \<ge> p - epsk powr (-1/2) * alpha (height p) * card Y"

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
  "many_bluish \<equiv> \<lambda>X. card {x\<in>X. bluish X x} \<ge> RN (TYPE('a)) k (nat \<lceil>l powr (2/3)\<rceil>)"

definition "good_blue_book \<equiv> \<lambda>X::'a set. \<lambda>(S,T). book S T Blue \<and> S\<subseteq>X \<and> T\<subseteq>X \<and> card T \<ge> (\<mu> ^ card S) * card X / 2"

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
    using ln0 powr_mono by force
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

definition "reddish \<equiv> \<lambda>X Y p x. red_density (Neighbours Red x \<inter> X) (Neighbours Red x \<inter> Y) \<ge> p - alpha (height p)"

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

definition "Xseq \<equiv> (\<lambda>(X,Y,A,B). X) o stepper"
definition "Yseq \<equiv> (\<lambda>(X,Y,A,B). Y) o stepper"
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
  have Wbig: "card W \<ge> RN (TYPE('a)) k m"
    using assms by (simp add: W_def m_def many_bluish_def)
  with Red_Blue_RN obtain U where "U \<subseteq> W" and U: "size_clique k U Red \<or> size_clique m U Blue"
    by (metis (no_types, lifting) W_def \<open>X\<subseteq>V\<close> mem_Collect_eq subset_eq)
  show ?thesis
    using U
  proof
    assume "size_clique m U Blue"
    have "card U = m"
      using \<open>size_clique m U Blue\<close> size_clique_def by auto
    have "m\<noteq>0"
      by (simp add: ln0 m_def)
    have "U \<subseteq> X"
      using W_def \<open>U \<subseteq> W\<close> by blast
    with \<open>X\<subseteq>V\<close> have cardXU: "card (X - U) = card X - card U" "card U \<le> card X"
      by (meson card_Diff_subset finV finite_subset card_mono)+
    have cX: "card X \<ge> RN (TYPE('a)) k (nat \<lceil>l powr (2/3)\<rceil>)"
      using assms
      apply (simp add: many_bluish_def)
      by (metis (full_types) Collect_subset card_mono finV order_trans finite_subset)
    then have "card U < card X"
      apply (simp add: \<open>card U = m\<close> m_def)

        sorry
    define \<sigma> where "\<sigma> \<equiv> blue_density U (X-U)"
    have "\<mu> - 1/k \<le> (\<mu> * card X - card U) / (card X - card U)"
      using kn0 \<open>U \<subseteq> X\<close> cardXU cX
      apply (simp add: field_split_simps of_nat_diff)
      apply (auto simp: \<open>card U = m\<close> simp flip: m_def)
      defer
      sorry
    also have "... \<le> \<sigma>"
      using \<open>m\<noteq>0\<close>
      apply (simp add: \<sigma>_def density_def divide_simps)
      apply (auto simp: )
      apply (metis of_nat_less_0_iff of_nat_mult)
         defer
      using \<open>card U = m\<close> \<open>m \<noteq> 0\<close> apply blast
      apply (metis \<open>card U = m\<close> card.infinite card_less_sym_Diff less_nat_zero_code)
      apply (metis of_nat_less_0_iff of_nat_mult)
      apply (simp add: cardXU)


      sorry
    finally have "\<mu> - 1/k \<le> \<sigma>" .
    show ?thesis
      sorry
  qed auto
qed