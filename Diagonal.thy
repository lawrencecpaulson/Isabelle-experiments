theory Diagonal imports
  "HOL-Library.Disjoint_Sets" "HOL-Library.Ramsey" "Undirected_Graph_Theory.Undirected_Graph_Basics" "HOL-ex.Sketch_and_Explore"
   
begin

lemma smaller_clique: "\<lbrakk>clique R E; R' \<subseteq> R\<rbrakk> \<Longrightarrow> clique R' E"
  by (auto simp: clique_def)

lemma smaller_indep: "\<lbrakk>indep R E; R' \<subseteq> R\<rbrakk> \<Longrightarrow> indep R' E"
  by (auto simp: indep_def)

text \<open>All complete graphs of a given cardinality are the same, but to avoid technical complications
  it seems simpler to make the following definitions pointlessly polymorphic.\<close>

text \<open>identifying Ramsey numbers (not the minimum) for a given time and pair of integers\<close>
definition is_Ramsey_number where
  "is_Ramsey_number \<equiv> \<lambda>U::'a itself. \<lambda>m n r. r \<ge> 1 \<and> (\<forall>V::'a set. \<forall>Red. finite V \<and> card V \<ge> r \<longrightarrow>
    (\<exists>R \<subseteq> V. card R = m \<and> clique R Red \<or> card R = n \<and> indep R Red))"

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
definition "book \<equiv> \<lambda>S T F. disjnt S T \<and> all_edges_between S S \<subseteq> F \<and> F \<subseteq> all_edges_between (S\<union>T) (S\<union>T)"

end

context fin_sgraph
begin

end

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
  fixes X0 :: "'a set" and Y0 :: "'a set"    \<comment> \<open>initial values\<close>
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

definition "disjoint_state \<equiv> \<lambda>(X,Y,A,B). disjnt X Y \<and> disjnt X A \<and> disjnt X B \<and> disjnt Y A \<and> disjnt Y B \<and> disjnt A B"

definition "RB_state \<equiv> \<lambda>(X,Y,A,B). all_incident_edges A \<subseteq> Red \<and> all_uedges_between A (X \<union> Y) \<subseteq> Red
             \<and> all_incident_edges B \<subseteq> Blue \<and> all_uedges_between B X \<subseteq> Blue"

definition "valid_state \<equiv> \<lambda>U. disjoint_state U \<and> RB_state U"

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


datatype book = Degree_reg
