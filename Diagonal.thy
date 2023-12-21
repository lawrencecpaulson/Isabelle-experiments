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
      using insert by (auto simp add: disjnt_iff all_edges_betw_un_def doubleton_eq_iff)
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

definition "termination_condition \<equiv> \<lambda>l k X Y. card X \<le> RN k (nat \<lceil>l powr (3/4)\<rceil>) \<or> red_density X Y \<le> 1/k"

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
  assumes \<section>: "stepper \<mu> l k n = (X,Y,A,B)"
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
  assumes "stepper \<mu> l l n = (X,Y,B,B)" "Colours l k" shows  "card B < l"
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

lemma Xseq_Suc_subset: "Xseq \<mu> l k (Suc n) \<subseteq> Xseq \<mu> l k n"
  apply (simp add: Xseq_def split: if_split_asm prod.split)
  by (metis degree_reg_subset next_state_subset valid_state_stepper)

lemma Xseq_antimono: "m \<le> n \<Longrightarrow>Xseq \<mu> l k n \<subseteq> Xseq \<mu> l k m"
  by (simp add: Xseq_Suc_subset lift_Suc_antimono_le)

lemma Yseq_Suc_subset: "Yseq \<mu> l k (Suc n) \<subseteq> Yseq \<mu> l k n"
  apply (simp add: Yseq_def split: if_split_asm prod.split)
  by (metis degree_reg_subset next_state_subset valid_state_stepper)

lemma Yseq_antimono: "m \<le> n \<Longrightarrow>Yseq \<mu> l k n \<subseteq> Yseq \<mu> l k m"
  by (simp add: Yseq_Suc_subset lift_Suc_antimono_le)

lemma pseq_0: "p0 = pseq \<mu> l k 0"
  by (simp add: p0_def pseq_def Xseq_def Yseq_def)

datatype stepkind = red_step | bblue_step | dboost_step | dreg_step

definition next_state_kind :: "[real,nat,nat,'a config] \<Rightarrow> stepkind" where
  "next_state_kind \<equiv> \<lambda>\<mu> l k (X,Y,A,B). 
       if many_bluish \<mu> l k X then bblue_step 
       else let x = choose_central_vx \<mu> (X,Y,A,B) in
            if reddish k X Y (red_density X Y) x then red_step
            else dboost_step"

definition stepper_kind :: "[real,nat,nat,nat] \<Rightarrow> stepkind" where
  "stepper_kind \<mu> l k n = 
     (let (X,Y,A,B) = stepper \<mu> l k n in 
      if termination_condition l k X Y then dreg_step 
      else if even n then next_state_kind \<mu> l k (X,Y,A,B) else dboost_step)"

definition "Step_class \<equiv> \<lambda>\<mu> l k knd. {n. stepper_kind \<mu> l k n = knd}"

lemma Step_class_iterates:
  assumes "finite (Step_class \<mu> l k knd)"
  obtains n where "Step_class \<mu> l k knd = {m. m<n \<and> stepper_kind \<mu> l k m = knd}"
proof -
  have eq: "(Step_class \<mu> l k knd) = (\<Union>i. {m. m<i \<and> stepper_kind \<mu> l k m = knd})"
    by (auto simp: Step_class_def)
  then obtain n where n: "(Step_class \<mu> l k knd) = (\<Union>i<n. {m. m<i \<and> stepper_kind \<mu> l k m = knd})"
    using finite_countable_equals[OF assms] by presburger
  with Step_class_def 
  have "{m. m<n \<and> stepper_kind \<mu> l k m = knd} = (\<Union>i<n. {m. m<i \<and> stepper_kind \<mu> l k m = knd})"
    by auto
  then show ?thesis
    by (metis n that)
qed

section \<open>Big blue steps: theorems\<close>

lemma power2_12: "m \<ge> 12 \<Longrightarrow> 25 * m^2 \<le> 2^m"
proof (induction m)
  case 0
  then show ?case by auto
next
  case (Suc m)
  then consider "m=11" | "m\<ge>12"
    by linarith
  then show ?case
  proof cases
    case 1
    then show ?thesis
      by auto
  next
    case 2
    then have "1+m+m \<le> 3*m"
      by auto
    moreover have "m\<ge>3"
      using Suc by simp
    ultimately  have "25 * Suc (m+m) \<le> 25 * (m*m)"
      by (metis Groups.mult_ac(2) dual_order.trans mult_le_mono2 plus_1_eq_Suc semiring_norm(163))
    with Suc show ?thesis
      by (auto simp: power2_eq_square algebra_simps 2)
  qed
qed

lemma Colours_ln0: "Colours l k \<Longrightarrow> l>0"
  by (force simp: Colours_def size_clique_def clique_def)

lemma Colours_kn0: "Colours l k \<Longrightarrow> k>0"
  using Colours_def Colours_ln0 not_le by auto

text \<open>How @{term b} and @{term m} are obtained from @{term l}\<close>
definition b_of where "b_of \<equiv> \<lambda>l::nat. nat\<lceil>l powr (1/4)\<rceil>"
definition m_of where "m_of \<equiv> \<lambda>l::nat. nat\<lceil>l powr (2/3)\<rceil>"

proposition Blue_4_1:
  assumes "0 < \<mu>"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. \<forall>X. X\<subseteq>V \<longrightarrow> many_bluish \<mu> l k X \<longrightarrow> Colours l k \<longrightarrow>
                  (\<exists>S T. good_blue_book \<mu> X (S,T) \<and> card S \<ge> l powr (1/4))"
proof -
  have m_ge: "\<forall>\<^sup>\<infinity>l. m_of l \<ge> i" for i
    unfolding m_of_def by real_asymp
  have real_l_ge: "\<forall>\<^sup>\<infinity>l. real l \<ge> r" for r
    by real_asymp
  have A: "\<forall>\<^sup>\<infinity>l. 1 \<le> 5/4 * exp (- ((b_of l)^2) / ((\<mu> - 2/l) * m_of l))"
    using assms unfolding b_of_def m_of_def by real_asymp
  have B: "\<forall>\<^sup>\<infinity>l. \<mu> - 2/l > 0"
    using assms by real_asymp
  have C: "\<forall>\<^sup>\<infinity>l. 2/l \<le> (\<mu> - 2/l) * ((5/4) powr (1/b_of l) - 1)"
    using assms unfolding b_of_def by real_asymp
  let ?Big = "\<lambda>l. m_of l \<ge> 12 \<and> real l \<ge> (6/\<mu>) powr (12/5) \<and> real l \<ge> 15
                    \<and> 1 \<le> 5/4 * exp (- ((b_of l)^2) / ((\<mu> - 2/l) * m_of l)) \<and> \<mu> - 2/l > 0
                    \<and> 2/l \<le> (\<mu> - 2/l) * ((5/4) powr (1/b_of l) - 1)"
  have big_enough_l: "\<forall>\<^sup>\<infinity>l. ?Big l"
    by (intro eventually_conj m_ge real_l_ge A B C)

  have "\<exists>S T. good_blue_book \<mu> X (S, T) \<and> l powr (1/4) \<le> card S"
    if l: "?Big l" and "X\<subseteq>V" and manyb: "many_bluish \<mu> l k X" and "Colours l k" for l k X
  proof -
    obtain ln0: "l>0" and kn0: "k>0"
      using \<open>Colours l k\<close> Colours_kn0 Colours_ln0 by blast
    obtain "l\<le>k" and no_Red_clique: "\<not> (\<exists>K. size_clique k K Red)" and no_Blue_clique: "\<not> (\<exists>K. size_clique l K Blue)"
      using \<open>Colours l k\<close> by (auto simp: Colours_def)
    have lpowr0[simp]: "0 \<le> \<lceil>l powr r\<rceil>" for r
      by (metis ceiling_mono ceiling_zero powr_ge_pzero)
    define b where "b \<equiv> b_of l"
    define W where "W \<equiv> {x\<in>X. bluish \<mu> X x}"
    define m where "m \<equiv> m_of l"
    have "m \<ge> 6" "m \<ge> 12"
      using l by (auto simp: m_def)
    then have "m>0"
      by simp
    have "b>0"
      using l by (simp add: b_def b_of_def)
    have Wbig: "card W \<ge> RN k m"
      using manyb by (simp add: W_def m_def m_of_def many_bluish_def)
    with Red_Blue_RN obtain U where "U \<subseteq> W" and U_m_Blue: "size_clique m U Blue"
      by (metis W_def \<open>X \<subseteq> V\<close> mem_Collect_eq no_Red_clique subset_eq)
    then have "card U = m" and "clique U Blue" and "U \<subseteq> V"
      by (auto simp: size_clique_def)
    then have "finite U"
      using finV infinite_super by blast
    have "k \<le> RN m k"
      using \<open>m\<ge>12\<close>
      by (metis (no_types) One_nat_def RN_1 RN_3plus RN_commute \<open>0 < m\<close> add_leE kn0 less_one nat_less_le numeral_Bit0 not_le) 
    then have "card X \<ge> l"
      by (metis Collect_subset RN_commute W_def Wbig \<open>X\<subseteq>V\<close> card_mono order.trans finV finite_subset \<open>l\<le>k\<close>)
    have "U \<noteq> X"
      by (metis U_m_Blue \<open>card U = m\<close> \<open>l \<le> card X\<close> order.order_iff_strict no_Blue_clique size_clique_smaller)
    then have "U \<subset> X"
      using W_def \<open>U \<subseteq> W\<close> by blast
    then have cardU_less_X: "card U < card X"
      by (meson \<open>X\<subseteq>V\<close> finV finite_subset psubset_card_mono)
    with \<open>X\<subseteq>V\<close> have cardXU: "card (X-U) = card X - card U"
      by (meson \<open>U \<subset> X\<close> card_Diff_subset finV finite_subset psubset_imp_subset)
    then have real_cardXU: "real (card (X-U)) = real (card X) - m"
      using \<open>card U = m\<close> cardU_less_X by linarith
    have [simp]: "m \<le> card X"
      using \<open>card U = m\<close> cardU_less_X nless_le by blast
    have lpowr23: "real l powr (2/3) \<le> real l powr 1"
      using l by (intro powr_mono) auto
    then have "m \<le> l"
      by (simp add: m_def m_of_def)
    then have "m \<le> k"
      using \<open>l \<le> k\<close> by auto
    then have "m < RN k m"
      using \<open>12 \<le> m\<close> comp_sgraph.RN_gt2 by auto
    also have cX: "RN k m \<le> card X"
      using manyb \<open>X\<subseteq>V\<close> by (metis Collect_subset W_def Wbig card_mono order_trans finV finite_subset)
    finally have "card U < card X"
      using \<open>card U = m\<close> by blast
    text \<open>First part of (10)\<close>
    have "card U * (\<mu> * card X - card U) = m * (\<mu> * (card X - card U)) - (1-\<mu>) * m\<^sup>2"
      using cardU_less_X by (simp add: \<open>card U = m\<close> algebra_simps of_nat_diff numeral_2_eq_2)
    also have "\<dots> \<le> real (card (Blue \<inter> all_edges_betw_un U (X-U)))"
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
          using assms by (simp add: \<open>card U = m\<close> left_diff_distrib)
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
      also have "\<dots> \<le> card (\<Union>u\<in>U. Blue \<inter> all_edges_betw_un {u} (X-U)) + (1-\<mu>) * m\<^sup>2"
        by (simp add: dfam card_UN_disjoint' \<open>finite U\<close> flip: UN_simps)
      finally have "m * (\<mu> * (card X - card U)) 
                \<le> card (\<Union>u\<in>U. Blue \<inter> all_edges_betw_un {u} (X-U)) + (1-\<mu>) * m\<^sup>2" .
      moreover have "(\<Union>u\<in>U. Blue \<inter> all_edges_betw_un {u} (X-U)) = (Blue \<inter> all_edges_betw_un U (X-U))"
        by (auto simp: all_edges_betw_un_def)
      ultimately show ?thesis
        by simp
    qed
    also have "\<dots> \<le> edge_card Blue U (X-U)"
      by (simp add: edge_card_def)
    finally have edge_card_XU: "edge_card Blue U (X-U) \<ge> card U * (\<mu> * card X - card U)" .
    define \<sigma> where "\<sigma> \<equiv> blue_density U (X-U)"
    then have "\<sigma> \<ge> 0" by (simp add: gen_density_ge0)
    have "\<sigma> \<le> 1"
      by (simp add: \<sigma>_def gen_density_le1)
    have 6: "real (6*k) \<le> real (2 + k*m)"
      by (metis mult.commute \<open>12\<le>m\<close> mult_le_mono nle_le numeral_Bit0 of_nat_mono trans_le_add2)
    then have km: "k + m \<le> Suc (k * m)"
      using l \<open>l \<le> k\<close> \<open>m \<le> l\<close> by linarith
    have "m/2 * (2 + real k * (1-\<mu>)) \<le> m/2 * (2 + real k)"
      using assms by (simp add: algebra_simps)
    also have "\<dots> \<le> (k - 1) * (m - 1)"
      using l \<open>l \<le> k\<close> 6 \<open>m \<le> k\<close> by (simp add: algebra_simps of_nat_diff km)
    finally  have "(m/2) * (2 + k * (1-\<mu>)) \<le> RN k m"
      using RN_times_lower' [of k m] by linarith
    then have "\<mu> - 2/k \<le> (\<mu> * card X - card U) / (card X - card U)"
      using kn0 assms cardU_less_X \<open>card U = m\<close> cX by (simp add: of_nat_diff field_simps)
    also have "\<dots> \<le> \<sigma>"
      using \<open>m>0\<close> \<open>card U = m\<close> cardU_less_X cardXU edge_card_XU
      by (simp add: \<sigma>_def gen_density_def field_simps mult_less_0_iff zero_less_mult_iff)
    finally have eq10: "\<mu> - 2/k \<le> \<sigma>" .
    have "2 * b / m \<le> \<mu> - 2/k"
    proof -
      have 512: "5/12 \<le> (1::real)"
        by simp
      with l have "l powr (5/12) \<ge> ((6/\<mu>) powr (12/5)) powr (5/12)"
        by (simp add: powr_mono2)
      then have lge: "l powr (5/12) \<ge> 6/\<mu>"
        using assms powr_powr by force
      have "2 * b \<le> 2 * (l powr (1/4) + 1)"
        by (simp add: b_def b_of_def del: zero_le_ceiling distrib_left_numeral)
      then have "2*b / m + 2/l \<le> 2 * (l powr (1/4) + 1) / l powr (2/3) + 2/l"
        by (simp add: m_def m_of_def frac_le ln0 del: zero_le_ceiling distrib_left_numeral)
      also have "\<dots> \<le> (2 * l powr (1/4) + 4) / l powr (2/3)"
        using ln0 lpowr23 by (simp add: pos_le_divide_eq pos_divide_le_eq algebra_simps)
      also have "\<dots> \<le> (2 * l powr (1/4) + 4 * l powr (1/4)) / l powr (2/3)"
        using l by (simp add: divide_right_mono ge_one_powr_ge_zero)
      also have "\<dots> = 6 / l powr (5/12)"
        by (simp add: divide_simps flip: powr_add)
      also have "\<dots> \<le> \<mu>"
        using lge assms by (simp add: divide_le_eq mult.commute)
      finally have "2*b / m + 2/l \<le> \<mu>" .
      then show ?thesis
        using \<open>l \<le> k\<close> \<open>m>0\<close> ln0 by (smt (verit, best) frac_le of_nat_0_less_iff of_nat_mono)
    qed
    with eq10 have "2 / (m/b) \<le> \<sigma>"
      by simp
    moreover have "l powr (2/3) \<le> nat \<lceil>real l powr (2/3)\<rceil>"
      using of_nat_ceiling by blast
    ultimately have ble: "b \<le> \<sigma> * m / 2"
      using mult_left_mono \<open>\<sigma> \<ge> 0\<close> l kn0 \<open>l \<le> k\<close> unfolding b_def m_def powr_diff
      by (simp add: divide_simps)
    then have "\<sigma> > 0"
      using \<open>0 < b\<close> \<open>0 \<le> \<sigma>\<close> less_eq_real_def by force

    define \<Phi> where "\<Phi> \<equiv> \<Sum>v \<in> X-U. card (Neighbours Blue v \<inter> U) choose b"
    text \<open>now for the material between (10) and (11)\<close>
    have "\<sigma> * real m / 2 \<le> m"
      using \<open>\<sigma> \<le> 1\<close> \<open>m>0\<close> by auto
    with ble have "b \<le> m"
      by linarith
    have "\<mu>^b * 1 * card X \<le> (5/4 * \<sigma>^b) * (5/4 * exp(- of_nat (b\<^sup>2) / (\<sigma>*m))) * (5/4 * (card X - m))"
    proof (intro mult_mono)
      have 2: "2/k \<le> 2/l"
        by (simp add: \<open>l \<le> k\<close> frac_le ln0)
      also have "\<dots> \<le> (\<mu> - 2/l) * ((5/4) powr (1/b) - 1)"
        using l by (simp add: b_def)
      also have "\<dots> \<le> \<sigma> * ((5/4) powr (1/b) - 1)"
      proof (intro mult_right_mono)
        show "\<mu> - 2 / real l \<le> \<sigma>"
          using "2" eq10 by auto
        show "0 \<le> (5 / 4) powr (1/b) - 1"
          by (simp add: ge_one_powr_ge_zero)
      qed
      finally have "2 / real k \<le> \<sigma> * ((5/4) powr (1/b) - 1)" .
      then have 1: "\<mu> \<le> (5/4)powr(1/b) * \<sigma>"
        using eq10 \<open>b>0\<close> by (simp add: algebra_simps)
      show "\<mu> ^ b \<le> 5/4 * \<sigma> ^ b"
        using power_mono[OF 1, of b] assms \<open>\<sigma>>0\<close> \<open>b>0\<close>
        by (simp add: powr_mult powr_powr flip: powr_realpow)
      have "\<mu> - 2/l \<le> \<sigma>"
        by (smt (verit, ccfv_SIG) \<open>l \<le> k\<close> eq10 frac_le ln0 of_nat_0_less_iff of_nat_mono)
      moreover
      have "2/l < \<mu>"
        using l by auto
      ultimately have "exp (- (b^2) / ((\<mu> - 2/l) * m)) \<le> exp (- real (b\<^sup>2) / (\<sigma> * real m))"
        using \<open>\<sigma>>0\<close> \<open>m>0\<close> by (simp add: frac_le)
      then show "1 \<le> 5/4 * exp (- of_nat (b\<^sup>2) / (\<sigma> * real m))"
        by (smt (verit, best) b_def divide_minus_left frac_le l m_def mult_left_mono)
      have "25 * (real m * real m) \<le> 2 powr real m"
        using of_nat_mono [OF power2_12 [OF \<open>12 \<le> m\<close>]] by (simp add: power2_eq_square powr_realpow)
      then have "real (5 * m) \<le>  2 powr (real m / 2)"
        by (simp add: powr_half_sqrt_powr power2_eq_square real_le_rsqrt)
      moreover
      have "card X > 2 powr (m/2)"
        by (metis RN_commute RN_lower_nodiag \<open>6 \<le> m\<close> \<open>m \<le> k\<close> add_leE less_le_trans cX numeral_Bit0 of_nat_mono)
      ultimately have "5 * m \<le> real (card X)"
        by linarith
      then show "real (card X) \<le> 5/4 * real (card X - m)"
        using \<open>card U = m\<close> cardU_less_X by simp
    qed (use \<open>0 \<le> \<sigma>\<close> in auto)
    also have "\<dots> \<le> 2 * (\<sigma>^b) * exp(- b\<^sup>2 / (\<sigma>*m)) * ((card X - m))"
      by (simp add: \<open>0 \<le> \<sigma>\<close>)
    finally have "\<mu>^b/2 * card X \<le> \<sigma>^b * exp(- of_nat (b\<^sup>2) / (\<sigma>*m)) * card (X-U)"
      by (simp add: \<open>card U = m\<close> cardXU real_cardXU)
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
    also have "\<dots> = 1/(m choose b) * (((\<sigma>*m) gchoose b) * card (X-U))"
      by (simp add: mult.assoc)
    also have "\<dots> \<le> 1/(m choose b) * \<Phi>"
    proof (intro mult_left_mono)
      have eeq: "edge_card Blue U (X-U) = (\<Sum>i\<in>X-U. card (Neighbours Blue i \<inter> U))"
      proof (intro edge_card_eq_sum_Neighbours)
        show "finite (X-U)"
          by (meson \<open>X\<subseteq>V\<close> finV finite_Diff finite_subset)
      qed (use disjnt_def Blue_E in auto)
      have "(\<Sum>i\<in>X - U. card (Neighbours Blue i \<inter> U)) / (real (card X) - m) = blue_density U (X-U) * m"
        using \<open>m>0\<close> by (simp add: gen_density_def real_cardXU \<open>card U = m\<close> eeq divide_simps)
      then have *: "(\<Sum>i\<in>X - U. real (card (Neighbours Blue i \<inter> U)) /\<^sub>R real (card (X-U))) = \<sigma> * m"
        by (simp add: \<sigma>_def divide_inverse_commute real_cardXU flip: sum_distrib_left)
      have "mbinomial (\<Sum>i\<in>X - U. real (card (Neighbours Blue i \<inter> U)) /\<^sub>R (card (X-U))) b 
         \<le> (\<Sum>i\<in>X - U. inverse (real (card (X-U))) * mbinomial (card (Neighbours Blue i \<inter> U)) b)"
      proof (rule convex_on_sum)
        show "finite (X-U)"
          using cardU_less_X zero_less_diff by fastforce
        show "convex_on UNIV (\<lambda>a. mbinomial a b)"
          by (simp add: \<open>0 < b\<close> convex_mbinomial)
        show "(\<Sum>i\<in>X - U. inverse (card (X-U))) = 1"
          using cardU_less_X cardXU by force
      qed (use \<open>U \<subset> X\<close> in auto)
      with ble 
      show "(\<sigma>*m gchoose b) * card (X-U) \<le> \<Phi>"
        unfolding * \<Phi>_def 
        by (simp add: cardU_less_X cardXU binomial_gbinomial divide_simps  flip: sum_distrib_left sum_divide_distrib)
    qed auto
    finally have 11: "\<mu>^b / 2 * card X \<le> \<Phi> / (m choose b)"
      by simp 
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
      using 11 by simp
    then have S: "card (Int_NB S) \<ge> \<mu>^b * card X / 2"
      using Sge by linarith
    obtain v where "v \<in> S"
      using \<open>0 < b\<close> \<open>card S = b\<close> by fastforce
    have "all_edges_betw_un S (S \<union> Int_NB S) \<subseteq> Blue"
      using \<open>clique S Blue\<close> unfolding all_edges_betw_un_def Neighbours_def clique_def Int_NB_def
      by fastforce
    then have "good_blue_book \<mu> X (S, Int_NB S)"
      using \<open>S\<subseteq>U\<close> \<open>v \<in> S\<close> \<open>U \<subset> X\<close> S \<open>card S = b\<close>
      unfolding good_blue_book_def book_def size_clique_def Int_NB_def disjnt_iff
      by blast
    then show ?thesis
      by (metis \<open>card S = b\<close> b_def b_of_def of_nat_ceiling)
  qed
  with eventually_mono [OF big_enough_l] show ?thesis
    by presburger 
qed

text \<open>Lemma 4.3\<close>
corollary bblue_step_limit:
  assumes "\<mu>>0"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> card (Step_class \<mu> l k bblue_step) \<le> l powr (3/4)"
proof -
  have "card (Step_class \<mu> l k bblue_step) \<le> l powr (3/4)"
    if 41: "\<And>X. many_bluish \<mu> l k X \<Longrightarrow> X\<subseteq>V \<Longrightarrow> \<exists>S T. good_blue_book \<mu> X (S,T) \<and> card S \<ge> l powr (1/4)"
      and "Colours l k" for l k
  proof -
    have cardB_ge:
      "card B \<ge> b_of l * card{m. m<n \<and> stepper_kind \<mu> l k m = bblue_step}"
      if  "stepper \<mu> l k n = (X,Y,A,B)" for n X Y A B
      using that
    proof (induction n arbitrary: X Y A B)
      case 0
      then show ?case
        by auto
    next
      case (Suc n)
      obtain X' Y' A' B' where step_n: "stepper \<mu> l k n = (X',Y',A',B')"
        by (metis surj_pair)
      then have "valid_state (X',Y',A',B')"
        by (metis valid_state_stepper)
      have "B' \<subseteq> B"
        using Suc by (auto simp add: next_state_def Let_def degree_reg_def step_n split: prod.split_asm if_split_asm)
      define Blues where "Blues \<equiv> \<lambda>r. {m. m < r \<and> stepper_kind \<mu> l k m = bblue_step}"
      show ?case
      proof (cases "stepper_kind \<mu> l k n = bblue_step")
        case True
        have [simp]: "card (insert n (Blues n)) = Suc (card (Blues n))"
          by (simp add: Blues_def)
        have card_B': "card B' \<ge> b_of l * card (Blues n)"
          using step_n Blues_def Suc.IH by blast
        obtain S where "A' = A" "Y' = Y" and manyb: "many_bluish \<mu> l k X'" 
          and cbb: "choose_blue_book \<mu> (X',Y,A,B') = (S,X)" and le_cardB: "card (B' \<union> S) \<le> card B"
          using Suc.prems True
          by (auto simp: stepper_kind_def next_state_kind_def next_state_def step_n split: prod.split_asm if_split_asm)     
        then have VS: "V_state (X',Y,A,B')" and ds: "disjoint_state (X',Y,A,B')"
          using \<open>valid_state (X',Y',A',B')\<close> by (auto simp: valid_state_def)
        then have "X' \<subseteq> V"
          by (simp add: V_state_def)
        then have l14: "l powr (1/4) \<le> real (card S)"
          using \<open>Colours l k\<close> 41 [OF manyb]
          by (smt (verit, best) VS best_blue_book_is_best cbb choose_blue_book_works of_nat_mono)
        then have ble: "b_of l \<le> card S"
          using b_of_def nat_ceiling_le_eq by presburger
        have S: "good_blue_book \<mu> X' (S,X)"
          by (metis VS cbb choose_blue_book_works)
        have "card S \<le> best_blue_book_card \<mu> X'"
          using choose_blue_book_works best_blue_book_is_best S VS by blast
        have fin: "finite B'" "finite S"
          using Colours_ln0 \<open>Colours l k\<close> l14 VS finB by force+
        have "disjnt B' S"
          using ds S by (force simp: disjoint_state_def good_blue_book_def disjnt_iff)
        have eq: "Blues(Suc n) = insert n (Blues n)"
          using less_Suc_eq True unfolding Blues_def by blast
        then have "b_of l * card (Blues (Suc n)) = b_of l + b_of l * card (Blues n)"
          by auto
        also have "\<dots> \<le> card B' + card S"
          using ble card_B' by linarith
        also have "... \<le> card (B' \<union> S)"
          using ble \<open>disjnt B' S\<close> fin by (simp add: card_Un_disjnt)
        finally have **: "b_of l * card (Blues (Suc n)) \<le> card B"
          using dual_order.trans le_cardB by blast 
        then show ?thesis
          by (simp add: Blues_def)
      next
        case False
        then have "{m. m < Suc n \<and> stepper_kind \<mu> l k m = bblue_step} = {m. m < n \<and> stepper_kind \<mu> l k m = bblue_step}"
          using less_Suc_eq by blast
        with \<open>B' \<subseteq> B\<close> show ?thesis
          by (smt (verit, best) Suc V_state card_seteq dual_order.trans finB nat_le_linear step_n)
      qed
    qed
    { assume \<section>: "card (Step_class \<mu> l k bblue_step) > l powr (3/4)"
      then have fin: "finite (Step_class \<mu> l k bblue_step)"
        using card.infinite by fastforce
      then obtain n where n: "(Step_class \<mu> l k bblue_step) = {m. m<n \<and> stepper_kind \<mu> l k m = bblue_step}"
        using Step_class_iterates by blast
      with \<section> have card_gt: "card{m. m<n \<and> stepper_kind \<mu> l k m = bblue_step} > l powr (3/4)"
        by (simp add: n)
      obtain X Y A B where step: "stepper \<mu> l k n = (X,Y,A,B)"
        using prod_cases4 by blast
      have "l = l powr (1 / 4) * l powr (3 / 4)"
        by (simp flip: powr_add)
      also have "\<dots> \<le> b_of l * l powr (3/4)"
        by (simp add: b_of_def mult_mono real_nat_ceiling_ge)
      also have "\<dots> \<le> b_of l * card{m. m<n \<and> stepper_kind \<mu> l k m = bblue_step}"
        using card_gt less_eq_real_def by fastforce
      also have "... \<le> card B"
        using cardB_ge step of_nat_mono by blast
      also have "... < l"
        using stepper_B[OF step] \<open>\<mu>>0\<close> \<open>Colours l k\<close>
        by (metis Colours_def linorder_neqE_nat of_nat_less_iff size_clique_def size_clique_smaller)
      finally have False
        by simp
    } then show ?thesis by force
  qed
  with eventually_mono [OF Blue_4_1] \<open>\<mu>>0\<close> show ?thesis
    by presburger 
qed

corollary red_step_limit:
  assumes "\<mu>>0"  "Colours l k"
  shows "card (Step_class \<mu> l k red_step) \<le> k"
proof -
  have *: "card{m. m<n \<and> stepper_kind \<mu> l k m = red_step} \<le> card A"
    if "stepper \<mu> l k n = (X,Y,A,B)" for n X Y A B
    using that
  proof (induction n arbitrary: X Y A B)
    case 0
    then show ?case
      by auto
  next
    case (Suc n)
    obtain X' Y' A' B' where step_n: "stepper \<mu> l k n = (X',Y',A',B')"
      by (metis surj_pair)
    then have vs: "valid_state (X',Y',A',B')"
      by (metis valid_state_stepper)
    then have "finite A'"
      using finA valid_state_def by auto
    have "A' \<subseteq> A"
      using Suc.prems by (auto simp add: next_state_def Let_def degree_reg_def step_n split: prod.split_asm if_split_asm)
    define Reds where "Reds \<equiv> \<lambda>r. {m. m < r \<and> stepper_kind \<mu> l k m = red_step}"
    show ?case
    proof (cases "stepper_kind \<mu> l k n = red_step")
      case True
      then have "Reds (Suc n) = insert n (Reds n)"
        by (auto simp add: Reds_def)
      moreover have "card (insert n (Reds n)) = Suc (card (Reds n))"
        by (simp add: Reds_def)
      ultimately have [simp]: "card (Reds (Suc n)) = Suc (card (Reds n))"
        by presburger
      have card_A': "card (Reds n) \<le> card A'"
        using step_n Reds_def Suc.IH by blast
      have Aeq: "A = insert (choose_central_vx \<mu> (X',Y',A',B')) A'"
        using Suc.prems True
        by (auto simp: stepper_kind_def next_state_kind_def next_state_def Let_def step_n split: if_split_asm)
      have "choose_central_vx \<mu> (X',Y',A',B') \<in> X'"
        using True
        apply (clarsimp simp: stepper_kind_def next_state_kind_def step_n split: if_split_asm)
        by (metis V_state choose_central_vx_X step_n)
      moreover
      have "disjnt X' A'"
        using vs by (simp add: valid_state_def disjoint_state_def)
      ultimately have "choose_central_vx \<mu> (X',Y',A',B') \<notin> A'"
        by (simp add: disjnt_iff)
      then have "card (Reds (Suc n)) \<le> card A"
        by (simp add: Aeq \<open>finite A'\<close> card_A')
      then show ?thesis
        by (simp add: Reds_def)
    next
      case False
      then have "{m. m < Suc n \<and> stepper_kind \<mu> l k m = red_step} = {m. m < n \<and> stepper_kind \<mu> l k m = red_step}"
        using less_Suc_eq by blast
      with \<open>A' \<subseteq> A\<close> show ?thesis
        by (smt (verit, best) Suc V_state card_seteq order.trans finA nat_le_linear step_n)
    qed
  qed
  { assume \<section>: "card (Step_class \<mu> l k red_step) \<ge> k"
    then have fin: "finite (Step_class \<mu> l k red_step)"
      using card.infinite by (metis Colours_kn0 assms(2) linorder_not_less)
    then obtain n where n: "(Step_class \<mu> l k red_step) = {m. m<n \<and> stepper_kind \<mu> l k m = red_step}"
      using Step_class_iterates by meson
    with \<section> have card_gt: "card{m. m<n \<and> stepper_kind \<mu> l k m = red_step} \<ge> k"
      by auto
    obtain X Y A B where step: "stepper \<mu> l k n = (X,Y,A,B)"
      using prod_cases4 by blast
    with *[OF step] \<section> have False
      using assms(2) card_A_limit card_gt by fastforce
  } then show ?thesis by force
qed

section \<open>Density-boost steps\<close>

text \<open>"See observation 5.5 below"\<close>
lemma sum_Weight_ge0: "(\<Sum>x\<in>X. \<Sum>y\<in>X. Weight X Y x y) \<ge> 0"
  sorry

end