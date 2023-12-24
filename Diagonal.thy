theory Diagonal imports
  Neighbours
  "HOL-Library.Disjoint_Sets"  "HOL-Decision_Procs.Approximation" 
  "HOL-Library.Infinite_Set"   "HOL-Real_Asymp.Real_Asymp" 
  "HOL-ex.Sketch_and_Explore"

begin

section \<open>Locale for the parameters of the construction\<close>

type_synonym 'a config = "'a set \<times> 'a set \<times> 'a set \<times> 'a set"

(*NOT CLEAR WHETHER \<mu> CAN BE FIXED HERE OR NOT*)

locale Diagonal = fin_sgraph +   \<comment> \<open>finite simple graphs (no loops)\<close>
  assumes complete: "E \<equiv> all_edges V"
  fixes Red Blue :: "'a set set"
  assumes Red_not_Blue: "Red \<noteq> Blue"
  assumes part_RB: "partition_on E {Red,Blue}"
  \<comment> \<open>the following are local to the program and possibly require their own locale\<close>
  fixes X0 :: "'a set" and Y0 :: "'a set"    \<comment> \<open>initial values\<close>
  assumes XY0: "disjnt X0 Y0" "X0 \<subseteq> V" "Y0 \<subseteq> V"
  assumes infinite_UNIV: "infinite (UNIV::'a set)"

context Diagonal
begin

(*This wants to be a locale. But nested locales don't seem to work, and having separate
locales for different parts of the development gets confusing here.*)
  \<comment> \<open>l: blue limit, and k: red limit\<close>
definition "Colours \<equiv> \<lambda>l k. l \<le> k \<and> \<not> (\<exists>K. size_clique k K Red) \<and> \<not> (\<exists>K. size_clique l K Blue)"

lemma Colours_ln0: "Colours l k \<Longrightarrow> l>0"
  by (force simp: Colours_def size_clique_def clique_def)

lemma Colours_kn0: "Colours l k \<Longrightarrow> k>0"
  using Colours_def Colours_ln0 not_le by auto

(*
locale Colours = Diagonal + 
  fixes l::nat       \<comment> \<open>blue limit\<close>
  fixes k::nat       \<comment> \<open>red limit\<close>
  assumes lk: "l \<le> k" \<comment> \<open>they should be "sufficiently large"\<close>
  assumes no_Red_clique: "\<not> (\<exists>K. size_clique k K Red)"
  assumes no_Blue_clique: "\<not> (\<exists>K. size_clique l K Blue)"
begin

lemma ln0: "l>0"
  using no_Blue_clique by (force simp: size_clique_def clique_def)

lemma kn0: "k > 0"
  using  lk ln0 by auto

end
*)

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

lemma in_E_iff [iff]: "{v,w} \<in> E \<longleftrightarrow> v\<in>V \<and> w\<in>V \<and> v\<noteq>w"
  by (auto simp: complete all_edges_alt doubleton_eq_iff)

lemma not_Red_Neighbour [simp]: "x \<notin> Neighbours Red x" and not_Blue_Neighbour [simp]: "x \<notin> Neighbours Blue x"
  using Red_E Blue_E not_own_Neighbour by auto

lemma Neighbours_Red_Blue: 
  assumes "x \<in> V" 
  shows "Neighbours Red x = V - insert x (Neighbours Blue x)"
  using Red_E assms by (auto simp: Blue_eq Neighbours_def complete all_edges_def)

lemma clique_imp_all_edges_betw_un: "clique K F \<Longrightarrow> all_edges_betw_un K K \<subseteq> F"
  by (force simp: clique_def all_edges_betw_un_def)

lemma all_edges_betw_un_iff_clique: "K \<subseteq> V \<Longrightarrow> all_edges_betw_un K K \<subseteq> F \<longleftrightarrow> clique K F"
  unfolding clique_def all_edges_betw_un_def doubleton_eq_iff subset_iff
  by blast

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
    using assms by (force simp: all_edges_betw_un_def)
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
  also have "\<dots> = card ((C \<inter> ({{x,b} |x. x \<in> A}) \<union> (C \<inter> all_edges_betw_un A B)))"
    by (simp add: Int_Un_distrib)
  also have "\<dots> = card (C \<inter> {{x,b} |x. x \<in> A}) + card (C \<inter> all_edges_betw_un A B)"
  proof (rule card_Un_disjnt)
    show "disjnt (C \<inter> {{x, b} |x. x \<in> A}) (C \<inter> all_edges_betw_un A B)"
      using insert by (auto simp: disjnt_iff all_edges_betw_un_def doubleton_eq_iff)
  qed (use \<open>finite C\<close> in auto)
  also have "\<dots> = card (Neighbours C b \<inter> A) + card (C \<inter> all_edges_betw_un A B)"
    using bij_betw_same_card [OF bij] by simp
  also have "\<dots> = (\<Sum>i\<in>insert b B. card (Neighbours C i \<inter> A))"
    using insert by (simp add: edge_card_def)
  finally show ?case .
qed


definition Weight :: "['a set, 'a set, 'a, 'a] \<Rightarrow> real" where
  "Weight \<equiv> \<lambda>X Y x y. inverse (card Y) * (card (Neighbours Red x \<inter> Neighbours Red y \<inter> Y)
                      - red_density X Y * card (Neighbours Red x \<inter> Y))"

definition weight :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> real" where
  "weight \<equiv> \<lambda>X Y x. \<Sum>y \<in> X-{x}. Weight X Y x y"

definition "p0 \<equiv> red_density X0 Y0"

definition "eps \<equiv> \<lambda>k. real k powr (-1/4)"

definition "q \<equiv> \<lambda>k h. p0 + ((1 + eps k)^h - 1) / k"

definition "hgt \<equiv> \<lambda>k p. LEAST h. p \<le> q k h \<and> h>0"

lemma q0 [simp]: "q k 0 = p0"
  by (simp add: q_def)

lemma p0_01: "0 \<le> p0" "p0 \<le> 1"
  by (simp_all add: p0_def gen_density_ge0 gen_density_le1)

lemma epsk_n0: "k>0 \<Longrightarrow> eps k > 0"
  by (simp add: eps_def)

lemma height_exists:
  assumes "0 < p" and "p < 1" and "k>0"
  obtains h where "p \<le> q k h"
proof -
  let ?h = "nat \<lceil>k / eps k\<rceil>"  \<comment>\<open>larger than the bound suggested in the paper\<close>
  have "k+1 \<le> (1 + eps k) ^ ?h"
    using linear_plus_1_le_power [of "eps k" ?h] epsk_n0 \<open>k>0\<close>
    by (smt (verit, best) mult_imp_less_div_pos of_nat_1 of_nat_add of_nat_ceiling)
  then have "p \<le> q k ?h"
    unfolding q_def
    using assms p0_01
    by (smt (verit, best) le_divide_eq_1_pos of_nat_0_less_iff of_nat_1 of_nat_add)
  then show thesis ..
qed

lemma q_Suc_diff: "q k (Suc h) - q k h = eps k * (1 + eps k)^h / k"
  by (simp add: q_def field_split_simps)

lemma finite_Red [simp]: "finite Red"
  by (metis Red_Blue_all complete fin_edges finite_Un)

lemma finite_Blue [simp]: "finite Blue"
  using Blue_E fin_edges finite_subset by blast


definition "alpha \<equiv> \<lambda>k h. q k h - q k (h-1)"

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

definition "termination_condition \<equiv> \<lambda>l k X Y. card X \<le> RN k (nat \<lceil>real l powr (3/4)\<rceil>) \<or> red_density X Y \<le> 1/k"

lemma 
  assumes "V_state(X,Y,A,B)" 
  shows finX: "finite X" and finY: "finite Y" and finA: "finite A" and finB: "finite B"
  using V_state_def assms finV finite_subset by auto

subsection \<open>Degree regularisation\<close>

definition "red_dense \<equiv> \<lambda>k Y p x. card (Neighbours Red x \<inter> Y) \<ge> p - eps k powr (-1/2) * alpha k (hgt k p) * card Y"

definition "X_degree_reg \<equiv>  \<lambda>k X Y. {x \<in> X. red_dense k Y (red_density X Y) x}"

definition "degree_reg \<equiv> \<lambda>k (X,Y,A,B). (X_degree_reg k X Y, Y, A, B)"

lemma X_degree_reg_subset: "X_degree_reg k X Y \<subseteq> X"
  by (auto simp: X_degree_reg_def)

lemma degree_reg_V_state: "V_state U \<Longrightarrow> V_state (degree_reg k U)"
  by (auto simp: degree_reg_def X_degree_reg_def V_state_def)

lemma degree_reg_disjoint_state: "disjoint_state U \<Longrightarrow> disjoint_state (degree_reg k U)"
  by (auto simp: degree_reg_def X_degree_reg_def disjoint_state_def disjnt_iff)

lemma degree_reg_RB_state: "RB_state U \<Longrightarrow> RB_state (degree_reg k U)"
  apply (simp add: degree_reg_def RB_state_def all_edges_betw_un_Un2 split: prod.split prod.split_asm)
  by (meson X_degree_reg_subset all_edges_betw_un_mono2 dual_order.trans)

lemma degree_reg_valid_state: "valid_state U \<Longrightarrow> valid_state (degree_reg k U)"
  by (simp add: degree_reg_RB_state degree_reg_V_state degree_reg_disjoint_state valid_state_def)

subsection \<open>Big blue steps: code\<close>

definition bluish :: "[real,'a set,'a] \<Rightarrow> bool" where
  "bluish \<equiv> \<lambda>\<mu> X x. card (Neighbours Blue x \<inter> X) \<ge> \<mu> * real (card X)"

definition many_bluish :: "[real, nat,nat,'a set] \<Rightarrow> bool" where
  "many_bluish \<equiv> \<lambda>\<mu> l k X. card {x\<in>X. bluish \<mu> X x} \<ge> RN k (nat \<lceil>l powr (2/3)\<rceil>)"

definition good_blue_book :: "[real, 'a set, 'a set \<times> 'a set] \<Rightarrow> bool" where
 "good_blue_book \<equiv> \<lambda>\<mu> X. \<lambda>(S,T). book S T Blue \<and> S\<subseteq>X \<and> T\<subseteq>X 
                               \<and> card T \<ge> (\<mu> ^ card S) * real (card X) / 2"

lemma ex_good_blue_book: "good_blue_book \<mu> X ({}, X)"
  by (simp add: good_blue_book_def)

lemma bounded_good_blue_book: "\<lbrakk>good_blue_book \<mu> X (S,T); V_state(X,Y,A,B)\<rbrakk> \<Longrightarrow> card S \<le> card X"
  by (simp add: card_mono finX good_blue_book_def)

definition best_blue_book_card :: "[real,'a set] \<Rightarrow> nat" where
  "best_blue_book_card \<equiv> \<lambda>\<mu> X. GREATEST s. \<exists>S T. good_blue_book \<mu> X (S,T) \<and> s = card S"

lemma best_blue_book_is_best: "\<lbrakk>good_blue_book \<mu> X (S,T); V_state(X,Y,A,B)\<rbrakk> \<Longrightarrow> card S \<le> best_blue_book_card \<mu> X"
  unfolding best_blue_book_card_def
  by (smt (verit) Greatest_le_nat bounded_good_blue_book)

lemma ex_best_blue_book: "V_state(X,Y,A,B) \<Longrightarrow> \<exists>S T. good_blue_book \<mu> X (S,T) \<and> card S = best_blue_book_card \<mu> X"
  unfolding best_blue_book_card_def
  by (smt (verit, del_insts) GreatestI_ex_nat bounded_good_blue_book ex_good_blue_book)

definition "choose_blue_book \<equiv> \<lambda>\<mu> (X,Y,A,B). @(S,T). good_blue_book \<mu> X (S,T) \<and> card S = best_blue_book_card \<mu> X"

lemma choose_blue_book_works: 
  "\<lbrakk>V_state(X,Y,A,B); (S,T) = choose_blue_book \<mu> (X,Y,A,B)\<rbrakk> 
  \<Longrightarrow> good_blue_book \<mu> X (S,T) \<and> card S = best_blue_book_card \<mu> X"
  unfolding choose_blue_book_def
  using someI_ex [OF ex_best_blue_book]
  by (metis (mono_tags, lifting) case_prod_conv someI_ex)


lemma choose_blue_book_subset: 
  "\<lbrakk>V_state(X,Y,A,B); (S,T) = choose_blue_book \<mu> (X,Y,A,B)\<rbrakk> \<Longrightarrow> S \<subseteq> X \<and> T \<subseteq> X \<and> disjnt S T"
  using choose_blue_book_works good_blue_book_def book_def by fastforce


text \<open>expressing the complicated preconditions inductively\<close>
inductive big_blue
  where "\<lbrakk>many_bluish \<mu> l k X; good_blue_book \<mu> X (S,T); card S = best_blue_book_card \<mu> X\<rbrakk> \<Longrightarrow> big_blue \<mu> (X,Y,A,B) (T, Y, A, B\<union>S)"

lemma big_blue_V_state: "\<lbrakk>big_blue \<mu> U U'; V_state U\<rbrakk> \<Longrightarrow> V_state U'"
  by (force simp: good_blue_book_def V_state_def elim!: big_blue.cases)

lemma big_blue_disjoint_state: "\<lbrakk>big_blue \<mu> U U'; disjoint_state U\<rbrakk> \<Longrightarrow> disjoint_state U'"
  apply (clarsimp simp add: good_blue_book_def disjoint_state_def elim!: big_blue.cases)
  by (metis book_imp_disjnt disjnt_subset1 disjnt_sym)

lemma big_blue_RB_state: "\<lbrakk>big_blue \<mu> U U'; RB_state U\<rbrakk> \<Longrightarrow> RB_state U'"
  apply (clarsimp simp add: good_blue_book_def book_def RB_state_def all_edges_betw_un_Un1 all_edges_betw_un_Un2 elim!: big_blue.cases)
  by (metis all_edges_betw_un_commute all_edges_betw_un_mono1 le_supI2 sup.orderE)

lemma big_blue_valid_state: "\<lbrakk>big_blue \<mu> U U'; valid_state U\<rbrakk> \<Longrightarrow> valid_state U'"
  by (meson big_blue_RB_state big_blue_V_state big_blue_disjoint_state valid_state_def)

subsection \<open>The central vertex\<close>

definition central_vertex :: "[real,'a set,'a] \<Rightarrow> bool" where
  "central_vertex \<equiv> \<lambda>\<mu> X x. x \<in> X \<and> card (Neighbours Blue x \<inter> X) \<le> \<mu> * real (card X)"

lemma ex_central_vertex:
  assumes "\<not> termination_condition l k X Y" "\<not> many_bluish \<mu> l k X"
  shows "\<exists>x. central_vertex \<mu> X x"
proof -
  have "l \<noteq> 0"
    using linorder_not_less assms unfolding many_bluish_def by force
  then have *: "real l powr (2/3) \<le> real l powr (3/4)"
    using powr_mono by force
  then have "card {x \<in> X. bluish \<mu> X x} < card X"
    using assms RN_mono
    unfolding termination_condition_def many_bluish_def not_le
    by (smt (verit, ccfv_SIG) linorder_not_le nat_ceiling_le_eq of_nat_le_iff)
  then obtain x where "x \<in> X" "\<not> bluish \<mu> X x"
    by (metis (mono_tags, lifting) mem_Collect_eq nat_neq_iff subsetI subset_antisym)
  then show ?thesis
    by (meson bluish_def central_vertex_def linorder_linear)
qed

lemma finite_central_vertex_set: "V_state(X,Y,A,B) \<Longrightarrow> finite {x. central_vertex \<mu> X x}"
  by (simp add: central_vertex_def finX)

definition max_central_vx :: "[real,'a set,'a set] \<Rightarrow> real" where
  "max_central_vx \<equiv> \<lambda>\<mu> X Y. Max (weight X Y ` {x. central_vertex \<mu> X x})"

lemma central_vx_is_best: 
  "\<lbrakk>central_vertex \<mu> X x; V_state(X,Y,A,B)\<rbrakk> \<Longrightarrow> weight X Y x \<le> max_central_vx \<mu> X Y"
  unfolding max_central_vx_def by (simp add: finite_central_vertex_set)

lemma ex_best_central_vx: 
  "\<lbrakk>\<not> termination_condition l k X Y; \<not> many_bluish \<mu> l k X; V_state(X,Y,A,B)\<rbrakk> 
  \<Longrightarrow> \<exists>x. central_vertex \<mu> X x \<and> weight X Y x = max_central_vx \<mu> X Y"
  unfolding max_central_vx_def
  by (metis empty_iff ex_central_vertex finite_central_vertex_set mem_Collect_eq obtains_MAX)

text \<open>it's necessary to make a specific choice; a relational treatment might allow different vertices 
  to be chosen, making a nonsense of the choice between steps 4 and 5\<close>
definition "choose_central_vx \<equiv> \<lambda>\<mu> (X,Y,A,B). @x. central_vertex \<mu> X x \<and> weight X Y x = max_central_vx \<mu> X Y"

lemma choose_central_vx_works: 
  "\<lbrakk>\<not> termination_condition l k X Y; \<not> many_bluish \<mu> l k X; V_state(X,Y,A,B)\<rbrakk> 
  \<Longrightarrow> central_vertex \<mu> X (choose_central_vx \<mu> (X,Y,A,B)) \<and> weight X Y (choose_central_vx \<mu> (X,Y,A,B)) = max_central_vx \<mu> X Y"
  unfolding choose_central_vx_def
  using someI_ex [OF ex_best_central_vx] by force

lemma choose_central_vx_X: 
  "\<lbrakk>\<not> termination_condition l k X Y; \<not> many_bluish \<mu> l k X; V_state(X,Y,A,B)\<rbrakk> \<Longrightarrow> choose_central_vx \<mu> (X,Y,A,B) \<in> X"
  using central_vertex_def choose_central_vx_works by presburger

subsection \<open>Red step\<close>

definition "reddish \<equiv> \<lambda>k X Y p x. red_density (Neighbours Red x \<inter> X) (Neighbours Red x \<inter> Y) \<ge> p - alpha k (hgt k p)"

inductive red_step 
  where "\<lbrakk>reddish k X Y (red_density X Y) x; x = choose_central_vx \<mu> (X,Y,A,B)\<rbrakk> 
         \<Longrightarrow> red_step \<mu> (X,Y,A,B) (Neighbours Red x \<inter> X, Neighbours Red x \<inter> Y, insert x A, B)"

lemma red_step_V_state: 
  assumes "red_step \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)"
  shows "V_state U'"
proof -
  have "choose_central_vx \<mu> (X, Y, A, B) \<in> V"
    using assms choose_central_vx_X  by (simp add: V_state_def subset_eq)
  with assms show ?thesis
    by (auto simp: V_state_def elim!: red_step.cases)
qed

lemma red_step_disjoint_state:
  assumes "red_step \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)" "disjoint_state (X,Y,A,B)"
  shows "disjoint_state U'"
proof -
  have "choose_central_vx \<mu> (X, Y, A, B) \<in> X"
    using assms choose_central_vx_X by (simp add: V_state_def)
  with assms show ?thesis
    by (auto simp: disjoint_state_def disjnt_iff not_own_Neighbour elim!: red_step.cases)
qed

lemma red_step_RB_state: 
  assumes "red_step \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)" "RB_state (X,Y,A,B)"
  shows "RB_state U'"
proof -
  define x where "x \<equiv> choose_central_vx \<mu> (X, Y, A, B)"
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
  assumes "red_step \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" "\<not> many_bluish \<mu> l k X" "valid_state (X,Y,A,B)"
  shows "valid_state U'"
  by (meson assms red_step_RB_state red_step_V_state red_step_disjoint_state valid_state_def)

subsection \<open>Density-boost step\<close>

inductive density_boost
  where "\<lbrakk>\<not> reddish k X Y (red_density X Y) x; x = choose_central_vx \<mu> (X,Y,A,B)\<rbrakk> 
         \<Longrightarrow> density_boost \<mu> (X,Y,A,B) (Neighbours Blue x \<inter> X, Neighbours Red x \<inter> Y, A, insert x B)"


lemma density_boost_V_state: 
  assumes "density_boost \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)"
  shows "V_state U'"
proof -
  have "choose_central_vx \<mu> (X, Y, A, B) \<in> V"
    using assms choose_central_vx_X  by (simp add: V_state_def subset_eq)
  with assms show ?thesis
    by (auto simp: V_state_def elim!: density_boost.cases)
qed

lemma density_boost_disjoint_state:
  assumes "density_boost \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)" "disjoint_state (X,Y,A,B)"
  shows "disjoint_state U'"
proof -
  have "choose_central_vx \<mu> (X, Y, A, B) \<in> X"
    using assms choose_central_vx_X by (simp add: V_state_def)
  with assms show ?thesis
    by (auto simp: disjoint_state_def disjnt_iff not_own_Neighbour elim!: density_boost.cases)
qed

lemma density_boost_RB_state: 
  assumes "density_boost \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)" 
    and rb: "RB_state (X,Y,A,B)"
  shows "RB_state U'"
proof -
  define x where "x \<equiv> choose_central_vx \<mu> (X, Y, A, B)"
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
  assumes "density_boost \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" "\<not> many_bluish \<mu> l k X" "valid_state (X,Y,A,B)"
  shows "valid_state U'"
  by (meson assms density_boost_RB_state density_boost_V_state density_boost_disjoint_state valid_state_def)

subsection \<open>Steps 2–5 as a function\<close>

definition next_state :: "[real,nat,nat,'a config] \<Rightarrow> 'a config" where
  "next_state \<equiv> \<lambda>\<mu> l k (X,Y,A,B). 
       if many_bluish \<mu> l k X then let (S,T) = choose_blue_book \<mu> (X,Y,A,B) in (T, Y, A, B\<union>S) 
       else let x = choose_central_vx \<mu> (X,Y,A,B) in
            if reddish k X Y (red_density X Y) x then (Neighbours Red x \<inter> X, Neighbours Red x \<inter> Y, insert x A, B)
            else (Neighbours Blue x \<inter> X, Neighbours Red x \<inter> Y, A, insert x B)"

lemma next_state_valid:
  assumes "valid_state (X,Y,A,B)" "\<not> termination_condition l k X Y"
  shows "valid_state (next_state \<mu> l k (X,Y,A,B))"
proof (cases "many_bluish \<mu> l k X")
  case True
  then have "big_blue \<mu> (X,Y,A,B) (next_state \<mu> l k (X,Y,A,B))"
    apply (simp add: next_state_def split: prod.split)
    by (metis assms(1) big_blue.intros choose_blue_book_works valid_state_def)
  then show ?thesis
    using assms(1) big_blue_valid_state by blast
next
  case non_bluish: False
  define x where "x = choose_central_vx \<mu> (X,Y,A,B)"
  show ?thesis
  proof (cases "reddish k X Y (red_density X Y) x")
    case True
    with non_bluish have "red_step \<mu> (X,Y,A,B) (next_state \<mu> l k (X,Y,A,B))"
      by (simp add: next_state_def Let_def x_def red_step.intros split: prod.split)
    then show ?thesis
      using assms non_bluish red_step_valid_state by blast      
  next
    case False
    with non_bluish have "density_boost \<mu> (X,Y,A,B) (next_state \<mu> l k (X,Y,A,B))"
      by (simp add: next_state_def Let_def x_def density_boost.intros split: prod.split)
    then show ?thesis
      using assms density_boost_valid_state non_bluish by blast
  qed
qed

primrec stepper :: "[real,nat,nat,nat] \<Rightarrow> 'a config" where
  "stepper \<mu> l k 0 = (X0,Y0,{},{})"
| "stepper \<mu> l k (Suc n) = 
     (let (X,Y,A,B) = stepper \<mu> l k n in 
      if termination_condition l k X Y then (X,Y,A,B) 
      else if even n then next_state \<mu> l k (X,Y,A,B) else (degree_reg k (X,Y,A,B)))"

lemma degree_reg_subset:
  assumes "degree_reg k (X,Y,A,B) = (X',Y',A',B')" 
  shows "X' \<subseteq> X \<and> Y' \<subseteq> Y"
  using assms by (auto simp: degree_reg_def X_degree_reg_def)

lemma next_state_subset:
  assumes "next_state \<mu> l k (X,Y,A,B) = (X',Y',A',B')" "valid_state (X,Y,A,B)"
  shows "X' \<subseteq> X \<and> Y' \<subseteq> Y"
  using assms choose_blue_book_subset
  apply (auto simp: next_state_def valid_state_def Let_def split: if_split_asm prod.split_asm)
  by (metis insert_absorb insert_subset)

lemma valid_state0: "valid_state (X0, Y0, {}, {})"
  using XY0 by (simp add: valid_state_def V_state_def disjoint_state_def RB_state_def)

lemma valid_state_stepper [simp]: "valid_state (stepper \<mu> l k n)"
proof (induction n)
  case 0
  then show ?case
    by (simp add: stepper_def valid_state0)
next
  case (Suc n)
  then show ?case
    by (force simp: next_state_valid degree_reg_valid_state split: prod.split)
qed

lemma V_state [simp]: "V_state (stepper \<mu> l k n)"
  using valid_state_def valid_state_stepper by force

lemma disjoint_state_stepper [simp]: "disjoint_state (stepper \<mu> l k n)"
  using valid_state_def valid_state_stepper by force

lemma RB_state_stepper [simp]: "RB_state (stepper \<mu> l k n)"
  using valid_state_def valid_state_stepper by force

lemma stepper_A:
  assumes \<section>: "stepper \<mu> l k n = (X,Y,A,B)"
  shows "clique A Red \<and> A\<subseteq>V"
proof -
  have "A\<subseteq>V"
    using V_state[of \<mu> l k n] assms by (auto simp: V_state_def)
  moreover
  have "all_edges_betw_un A A \<subseteq> Red"
    using RB_state_stepper[of \<mu> l k n] assms by (auto simp: RB_state_def)
  ultimately show ?thesis
    using all_edges_betw_un_iff_clique by simp
qed

lemma card_A_limit:
  assumes "stepper \<mu> l k n = (X,Y,A,B)" "Colours l k" shows  "card A < k"
proof -
  have "clique A Red"
    using stepper_A assms by auto
  then show "card A < k"
    using assms unfolding Colours_def
    by (metis linorder_neqE_nat size_clique_def size_clique_smaller stepper_A) 
qed

lemma stepper_B:
  assumes "stepper \<mu> l k n = (X,Y,A,B)"
  shows "clique B Blue \<and> B\<subseteq>V"
proof -
  have "B\<subseteq>V"
    using V_state[of \<mu> l k n] assms by (auto simp: V_state_def)
  moreover
  have "all_edges_betw_un B B \<subseteq> Blue"
    using RB_state_stepper[of \<mu> l k n] assms by (auto simp: RB_state_def all_edges_betw_un_Un2)
  ultimately show ?thesis
    using all_edges_betw_un_iff_clique by simp
qed

lemma card_B_limit:
  assumes "stepper \<mu> l k n = (X,Y,A,B)" "Colours l k" shows "card B < l"
proof -
  have "clique B Blue"
    using stepper_B assms by auto
  then show "card B < l"
    using assms unfolding Colours_def
    by (metis linorder_neqE_nat size_clique_def size_clique_smaller stepper_B) 
qed



definition "Xseq \<mu> l k \<equiv> (\<lambda>(X,Y,A,B). X) \<circ> stepper \<mu> l k"
definition "Yseq \<mu> l k \<equiv> (\<lambda>(X,Y,A,B). Y) \<circ> stepper \<mu> l k"
definition "pseq \<mu> l k \<equiv> \<lambda>n. red_density (Xseq \<mu> l k n) (Yseq \<mu> l k n)"

lemma Xseq_0 [simp]: "Xseq \<mu> l k 0 = X0"
  by (simp add: Xseq_def)

lemma Xseq_Suc_subset: "Xseq \<mu> l k (Suc n) \<subseteq> Xseq \<mu> l k n"
  apply (simp add: Xseq_def split: if_split_asm prod.split)
  by (metis degree_reg_subset next_state_subset valid_state_stepper)

lemma Xseq_antimono: "m \<le> n \<Longrightarrow>Xseq \<mu> l k n \<subseteq> Xseq \<mu> l k m"
  by (simp add: Xseq_Suc_subset lift_Suc_antimono_le)

lemma Yseq_0 [simp]: "Yseq \<mu> l k 0 = Y0"
  by (simp add: Yseq_def)

lemma Yseq_Suc_subset: "Yseq \<mu> l k (Suc n) \<subseteq> Yseq \<mu> l k n"
  apply (simp add: Yseq_def split: if_split_asm prod.split)
  by (metis degree_reg_subset next_state_subset valid_state_stepper)

lemma Yseq_antimono: "m \<le> n \<Longrightarrow>Yseq \<mu> l k n \<subseteq> Yseq \<mu> l k m"
  by (simp add: Yseq_Suc_subset lift_Suc_antimono_le)

lemma pseq_0: "p0 = pseq \<mu> l k 0"
  by (simp add: p0_def pseq_def Xseq_def Yseq_def)

text \<open>The central vertex at each step (though only defined in some cases), 
  @{term "x_i"} in the paper\<close>
definition cvx :: "[real,nat,nat,nat] \<Rightarrow> 'a" where
  "cvx \<equiv> \<lambda>\<mu> l k i. choose_central_vx \<mu> (stepper \<mu> l k i)"

definition 
  "beta \<equiv> \<lambda>\<mu> l k i. 
    (let (X,Y,A,B) = stepper \<mu> l k i in card(Neighbours Blue (cvx \<mu> l k i) \<inter> X) / card X)"


subsection \<open>The classes of execution steps\<close>

text \<open>For R, B, S, D\<close>
datatype stepkind = red_step | bblue_step | dboost_step | dreg_step

definition next_state_kind :: "[real,nat,nat,'a config] \<Rightarrow> stepkind" where
  "next_state_kind \<equiv> \<lambda>\<mu> l k (X,Y,A,B). 
       if many_bluish \<mu> l k X then bblue_step 
       else let x = choose_central_vx \<mu> (X,Y,A,B) in
            if reddish k X Y (red_density X Y) x then red_step
            else dboost_step"

definition stepper_kind :: "[real,nat,nat,nat] \<Rightarrow> stepkind" where
  "stepper_kind \<mu> l k i = 
     (let (X,Y,A,B) = stepper \<mu> l k i in 
      if termination_condition l k X Y then dreg_step 
      else if even i then next_state_kind \<mu> l k (X,Y,A,B) else dreg_step)"

definition "Step_class \<equiv> \<lambda>\<mu> l k knd. {n. stepper_kind \<mu> l k n = knd}"

lemma disjnt_Step_class: 
  "knd \<noteq> knd' \<Longrightarrow> disjnt (Step_class \<mu> l k knd) (Step_class \<mu> l k knd')"
  by (auto simp: Step_class_def disjnt_iff)

lemma finite_Step_class:
  assumes "\<And>n. finite {m. m<n \<and> stepper_kind \<mu> l k m = knd}"
  assumes "\<And>n. card {m. m<n \<and> stepper_kind \<mu> l k m = knd} < N"
  shows "finite (Step_class \<mu> l k knd)"
proof -
  have "incseq (\<lambda>n. {m. m<n \<and> stepper_kind \<mu> l k m = knd})"
    by (auto simp: incseq_def)
  moreover have "(\<Union>n. {m. m<n \<and> stepper_kind \<mu> l k m = knd}) = (Step_class \<mu> l k knd)"
    by (auto simp: Step_class_def)
  ultimately show ?thesis
    by (smt (verit) eventually_sequentially order.refl Union_incseq_finite assms)
qed

lemma Step_class_iterates:
  assumes "finite (Step_class \<mu> l k knd)"
  obtains n where "Step_class \<mu> l k knd = {m. m<n \<and> stepper_kind \<mu> l k m = knd}"
proof -
  have eq: "(Step_class \<mu> l k knd) = (\<Union>i. {m. m<i \<and> stepper_kind \<mu> l k m = knd})"
    by (auto simp: Step_class_def)
  then obtain n where n: "(Step_class \<mu> l k knd) = (\<Union>i<n. {m. m<i \<and> stepper_kind \<mu> l k m = knd})"
    using finite_countable_equals[OF assms] by blast
  with Step_class_def 
  have "{m. m<n \<and> stepper_kind \<mu> l k m = knd} = (\<Union>i<n. {m. m<i \<and> stepper_kind \<mu> l k m = knd})"
    by auto
  then show ?thesis
    by (metis n that)
qed

lemma "0 \<le> beta \<mu> l k i"
  by (simp add: beta_def split: prod.split)

lemma red_dboost_non_terminating:
  assumes "i \<in> Step_class \<mu> l k red_step \<union> Step_class \<mu> l k dboost_step"
  shows "\<not> termination_condition l k (Xseq \<mu> l k i) (Yseq \<mu> l k i)"
  using assms
  by (simp add: Step_class_def stepper_kind_def Xseq_def Yseq_def split: if_split_asm prod.split_asm)

lemma red_dboost_not_many_bluish:
  assumes "i \<in> Step_class \<mu> l k red_step \<union> Step_class \<mu> l k dboost_step"
  shows "\<not> many_bluish \<mu> l k (Xseq \<mu> l k i)"
  using assms
  by (simp add: Step_class_def stepper_kind_def next_state_kind_def Xseq_def split: if_split_asm prod.split_asm)

lemma stepper_XYseq: "stepper \<mu> l k i = (X,Y,A,B) \<Longrightarrow> X = Xseq \<mu> l k i \<and> Y = Yseq \<mu> l k i"
  using Xseq_def Yseq_def by fastforce

lemma cvx_works:
  assumes "i \<in> Step_class \<mu> l k red_step \<union> Step_class \<mu> l k dboost_step"
  shows "central_vertex \<mu> (Xseq \<mu> l k i) (cvx \<mu> l k i)
       \<and> weight (Xseq \<mu> l k i) (Yseq \<mu> l k i) (cvx \<mu> l k i) = max_central_vx \<mu> (Xseq \<mu> l k i) (Yseq \<mu> l k i)"
  apply (simp add: Xseq_def cvx_def Yseq_def split: prod.split)
  by (metis choose_central_vx_works V_state assms red_dboost_non_terminating red_dboost_not_many_bluish stepper_XYseq)

lemma cvx_in_Xseq:
  assumes "i \<in> Step_class \<mu> l k red_step \<union> Step_class \<mu> l k dboost_step"
  shows "cvx \<mu> l k i \<in> Xseq \<mu> l k i"
  apply (simp add: Xseq_def cvx_def Yseq_def split: prod.split)
  by (metis V_state assms choose_central_vx_X red_dboost_non_terminating red_dboost_not_many_bluish stepper_XYseq)

lemma beta_le:
  assumes "\<mu> > 0" and i: "i \<in> Step_class \<mu> l k red_step \<union> Step_class \<mu> l k dboost_step"
  shows "beta \<mu> l k i \<le> \<mu>"
  using \<open>\<mu> > 0\<close>
  apply (simp add: beta_def divide_simps split: prod.split)
  by (metis i central_vertex_def cvx_works stepper_XYseq)

end

end
