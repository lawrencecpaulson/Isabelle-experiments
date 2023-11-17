theory Diagonal imports
  "HOL-Library.Disjoint_Sets" "HOL-Library.Ramsey" "Undirected_Graph_Theory.Undirected_Graph_Basics" "HOL-ex.Sketch_and_Explore"
   
begin

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
  "is_Ramsey_number \<equiv> \<lambda>U::'a itself. \<lambda>m n r. r \<ge> 1 \<and> (\<forall>V::'a set. \<forall>Red. finite V \<and> card V \<ge> r \<longrightarrow>
    (\<exists>R \<subseteq> V. card R = m \<and> clique R Red \<or> card R = n \<and> indep R Red))"

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
    then have **: "\<not> (\<exists>e\<in>E \<inter> Pow V. {x,y} = f ` e)"
      by (metis F_def image_eqI indep_def that xy)
    with E f have "{x,y} \<in> F"
      apply (clarsimp simp: Bex_def bij_betw_def)
      by (smt (verit, best) \<open>R \<subseteq> W\<close> empty_subsetI f_inv_into_f image_empty image_insert in_mono insert_subset inv_into_into xy)
    with ** show False
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
  apply (drule_tac x="Red" in spec)
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
  shows "\<exists>R \<subseteq> V. card R = m \<and> clique R Red \<or> card R = n \<and> indep R Red"
  using is_Ramsey_number_RN [of U m n] assms
  unfolding is_Ramsey_number_def by blast

lemma RN_mono:
  assumes "m' \<le> m" "n' \<le> n"
  shows "RN U m' n' \<le> RN U m n"
  by (meson RN_le assms is_Ramsey_number_RN is_Ramsey_number_le)


text \<open>cliques of a given size; the definition of clique from Ramsay is used\<close>

definition size_clique :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "size_clique p K E \<equiv> card K = p \<and> clique K E"

lemma size_clique_all_edges: "size_clique p K E \<Longrightarrow> all_edges K \<subseteq> E"
  by (auto simp: size_clique_def all_edges_def clique_def card_2_iff)

lemma indep_iff_clique: "indep V E \<longleftrightarrow> clique V (all_edges V - E)"
  by (auto simp: indep_def clique_def all_edges_def)

definition Neighbours :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "Neighbours \<equiv> \<lambda>E x. {y. {x,y} \<in> E}"

context ulgraph
begin

text \<open>The set of \emph{undirected} edges between two sets\<close>
definition all_uedges_between :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "all_uedges_between X Y \<equiv> {{x, y}| x y. x \<in> X \<and> y \<in> Y \<and> {x, y} \<in> E}"

lemma all_uedges_between_commute1: "all_uedges_between X Y \<subseteq> all_uedges_between Y X"
  by (smt (verit, del_insts) Collect_mono all_uedges_between_def insert_commute)

lemma all_uedges_between_commute: "all_uedges_between X Y = all_uedges_between Y X"
  by (simp add: all_uedges_between_commute1 subset_antisym)

lemma all_uedges_between_iff_mk_edge: "all_uedges_between X Y = mk_edge ` all_edges_between X Y"
  using all_edges_between_set all_uedges_between_def by presburger

lemma all_uedges_betw_subset: "all_uedges_between X Y \<subseteq> E"
  by (auto simp add: all_uedges_between_def)

lemma all_uedges_betw_I: "x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> {x, y} \<in> E \<Longrightarrow> {x, y} \<in> all_uedges_between X Y"
  by (auto simp add: all_uedges_between_def)

lemma all_uedges_between_subset: "all_uedges_between X Y \<subseteq> Pow (X\<union>Y)"
  by (auto simp: all_uedges_between_def)

lemma all_uedges_between_rem_wf: "all_uedges_between X Y = all_uedges_between (X \<inter> V) (Y \<inter> V)"
  using wellformed by (simp add: all_uedges_between_def) blast 

lemma all_uedges_between_empty [simp]:
  "all_uedges_between {} Z = {}" "all_uedges_between Z {} = {}"
  by (auto simp: all_uedges_between_def)

lemma card_all_uedges_betw_le: 
  assumes "finite X" "finite Y"
  shows "card (all_uedges_between X Y) \<le> card (all_edges_between X Y)"
  by (simp add: all_uedges_between_iff_mk_edge assms card_image_le finite_all_edges_between)

lemma max_all_uedges_between: 
  assumes "finite X" "finite Y"
  shows "card (all_uedges_between X Y) \<le> card X * card Y"
  by (meson assms card_all_uedges_betw_le max_all_edges_between order_trans)

lemma all_uedges_between_Un1:
  "all_uedges_between (X \<union> Y) Z = all_uedges_between X Z \<union> all_uedges_between Y Z"
  by (auto simp: all_uedges_between_def)

lemma all_uedges_between_Un2:
  "all_uedges_between X (Y \<union> Z) = all_uedges_between X Y \<union> all_uedges_between X Z"
  by (auto simp: all_uedges_between_def)

lemma finite_all_uedges_between:
  assumes "finite X" "finite Y"
  shows "finite (all_uedges_between X Y)"
  by (simp add: all_uedges_between_iff_mk_edge assms finite_all_edges_between)

lemma all_uedges_between_Union1:
  "all_uedges_between (Union \<X>) Y = (\<Union>X\<in>\<X>. all_uedges_between X Y)"
  by (auto simp: all_uedges_between_def)

lemma all_uedges_between_Union2:
  "all_uedges_between X (Union \<Y>) = (\<Union>Y\<in>\<Y>. all_uedges_between X Y)"
  by (auto simp: all_uedges_between_def)

lemma all_uedges_between_mono1:
  "Y \<subseteq> Z \<Longrightarrow> all_uedges_between Y X \<subseteq> all_uedges_between Z X"
  by (auto simp: all_uedges_between_def)

lemma all_uedges_between_mono2:
  "Y \<subseteq> Z \<Longrightarrow> all_uedges_between X Y \<subseteq> all_uedges_between X Z"
  by (auto simp: all_uedges_between_def)

text \<open>this notion, mentioned on Page 3, is a little vague: "a graph on vertex set @{term"S \<union> T"} 
that contains all edges incident to @{term"S"}"\<close>
definition book :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "book \<equiv> \<lambda>S T F. disjnt S T \<and> all_uedges_between S (S\<union>T) \<subseteq> F"

lemma book_empty [simp]: "book {} T F"
  by (auto simp: book_def)

lemma book_imp_disjnt: "book S T F \<Longrightarrow> disjnt S T"
  by (auto simp: book_def)

lemma (in fin_sgraph) book_insert: "book (insert v S) T F \<longleftrightarrow> book S T F \<and> v \<notin> T \<and> all_uedges_between {v} (S \<union> T) \<subseteq> F"
  apply (auto simp: book_def)
  using all_uedges_between_def apply auto[1]
  using all_uedges_between_def apply auto[1]
  apply (simp add: all_uedges_between_def)
  by (smt (verit, best) insert_is_Un mem_Collect_eq singleton_insert_inj_eq singleton_not_edge subset_iff sup_commute)

end

section \<open>Locale for the parameters of the construction\<close>

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

lemma nontriv: "E \<noteq> {}"
  using Red_E bot.extremum_strict by blast

lemma kn0: "k > 0"
  using lk ln0 by auto

text \<open>for calculating the perimeter p\<close>
definition "red_density X Y \<equiv> card (Red \<inter> all_uedges_between X Y) / (card X * card Y)"

lemma red_density_ge0: "red_density X Y \<ge> 0"
  by (auto simp: red_density_def)

lemma red_le_edge_density: "red_density X Y \<le> edge_density X Y"
proof (cases "finite X \<and> finite Y")
  case True
  then have "card (Red \<inter> all_uedges_between X Y) \<le> card (all_uedges_between X Y)"
    by (simp add: all_uedges_between_iff_mk_edge card_mono finite_all_edges_between')
  also have "... \<le> card (all_edges_between X Y)"
    by (simp add: all_uedges_between_iff_mk_edge card_image_le finite_all_edges_between')
  finally show ?thesis
    by (simp add: red_density_def edge_density_def divide_right_mono)
qed (auto simp: red_density_def edge_density_def)

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

definition "disjoint_state \<equiv> \<lambda>(X,Y,A,B). disjnt X Y \<and> disjnt X A \<and> disjnt X B \<and> disjnt Y A \<and> disjnt Y B \<and> disjnt A B"

text \<open>previously had all edges incident to A, B\<close>
definition "RB_state \<equiv> \<lambda>(X,Y,A,B). all_uedges_between A A \<subseteq> Red \<and> all_uedges_between A (X \<union> Y) \<subseteq> Red
             \<and> all_uedges_between B B \<subseteq> Blue \<and> all_uedges_between B X \<subseteq> Blue"

definition "valid_state \<equiv> \<lambda>U. disjoint_state U \<and> RB_state U"

subsection \<open>Degree regularisation\<close>

definition "X_degree_reg \<equiv> \<lambda>X Y. {x \<in> X. card (Neighbours Red x \<inter> Y) \<ge> 
                                   (let p = red_density X Y in p - epsk powr (-1/2) * alpha (height p)) * card Y}"

definition "degree_reg \<equiv> \<lambda>(X,Y,A,B). (X_degree_reg X Y, Y, A, B)"

lemma X_degree_reg_subset: "X_degree_reg X Y \<subseteq> X"
  by (auto simp: X_degree_reg_def)

lemma degree_reg_disjoint_state: "disjoint_state U \<Longrightarrow> disjoint_state (degree_reg U)"
  by (auto simp add: degree_reg_def X_degree_reg_def disjoint_state_def disjnt_iff)

lemma degree_reg_RB_state: "RB_state U \<Longrightarrow> RB_state (degree_reg U)"
  apply (simp add: degree_reg_def RB_state_def all_uedges_between_Un2 split: prod.split prod.split_asm)
  by (meson X_degree_reg_subset all_uedges_between_mono2 dual_order.trans)

lemma degree_reg_valid_state: "valid_state U \<Longrightarrow> valid_state (degree_reg U)"
  by (meson degree_reg_RB_state degree_reg_disjoint_state valid_state_def)

subsection \<open>Big blue steps\<close>

definition bluish :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "bluish \<equiv> \<lambda>x X. card (Neighbours Blue x \<inter> X) \<ge> \<mu> * card X"

definition many_bluish :: "'a set \<Rightarrow> bool" where
  "many_bluish \<equiv> \<lambda>X. card {x\<in>X. bluish x X} \<ge> RN (TYPE('a)) k (nat \<lceil>l powr (2/3)\<rceil>)"

definition "good_blue_book \<equiv> \<lambda>X::'a set. \<lambda>(S,T). book S T Blue \<and> S\<subseteq>X \<and> T\<subseteq>X \<and> card T \<ge> (\<mu> ^ card S) * card X / 2"

lemma ex_good_blue_book: "\<exists>S T. good_blue_book X (S,T)"
  apply (rule_tac x="{}" in exI)
  apply (rule_tac x="X" in exI)
  apply (simp add: good_blue_book_def)
  done

lemma bounded_good_blue_book: "\<lbrakk>good_blue_book X (S,T); finite X\<rbrakk> \<Longrightarrow> card S \<le> card X"
  by (simp add: card_mono good_blue_book_def)

definition "best_blue_book \<equiv> \<lambda>X. GREATEST s. \<exists>S T. good_blue_book X (S,T) \<and> s = card S"

lemma best_blue_book_is_best: "\<lbrakk>good_blue_book X (S,T); finite X\<rbrakk> \<Longrightarrow> card S \<le> best_blue_book X"
  unfolding best_blue_book_def
  by (smt (verit) Greatest_le_nat bounded_good_blue_book)

lemma ex_best_blue_book: "finite X \<Longrightarrow> \<exists>S T. good_blue_book X (S,T) \<and> card S = best_blue_book X"
  unfolding best_blue_book_def
  by (smt (verit, ccfv_threshold) GreatestI_nat bounded_good_blue_book ex_good_blue_book)

text \<open>expressing the complicated preconditions inductively\<close>
inductive big_blue
  where "\<lbrakk>many_bluish X; good_blue_book X (S,T); card S = best_blue_book X\<rbrakk> \<Longrightarrow> big_blue (X,Y,A,B) (T, Y, A, B\<union>S)"

lemma big_blue_disjoint_state: "\<lbrakk>big_blue U U'; disjoint_state U\<rbrakk> \<Longrightarrow> disjoint_state U'"
  apply (clarsimp simp add: good_blue_book_def disjoint_state_def elim!: big_blue.cases)
  by (metis book_imp_disjnt disjnt_subset1 disjnt_sym)

lemma big_blue_RB_state: "\<lbrakk>big_blue U U'; RB_state U\<rbrakk> \<Longrightarrow> RB_state U'"
  apply (clarsimp simp add: good_blue_book_def book_def RB_state_def all_uedges_between_Un1 all_uedges_between_Un2 elim!: big_blue.cases)
  by (metis all_uedges_between_commute all_uedges_between_mono1 le_supI2 sup.orderE)



datatype book = Degree_reg
