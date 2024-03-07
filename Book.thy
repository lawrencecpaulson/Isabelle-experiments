theory Book imports
  Neighbours
  "HOL-Library.Disjoint_Sets"  "HOL-Decision_Procs.Approximation" 
  "HOL-Library.Infinite_Set"   "HOL-Real_Asymp.Real_Asymp" 
  "HOL-ex.Sketch_and_Explore"

begin

hide_const Bseq

section \<open>Locale for the parameters of the construction\<close>

type_synonym 'a config = "'a set \<times> 'a set \<times> 'a set \<times> 'a set"

(*NOT CLEAR WHETHER \<mu> CAN BE FIXED HERE OR NOT*)

locale Diagonal = fin_sgraph +   \<comment> \<open>finite simple graphs (no loops)\<close>
  assumes complete: "E \<equiv> all_edges V"
  fixes Red Blue :: "'a set set"
  assumes Red_not_Blue: "Red \<noteq> Blue"
  assumes part_RB: "partition_on E {Red,Blue}"
  \<comment> \<open>the following are local to the program\<close>
  fixes X0 :: "'a set" and Y0 :: "'a set"    \<comment> \<open>initial values\<close>
  assumes XY0: "disjnt X0 Y0" "X0 \<subseteq> V" "Y0 \<subseteq> V"
  assumes infinite_UNIV: "infinite (UNIV::'a set)"
  assumes Red_edges_XY0: "Red \<inter> all_edges_betw_un X0 Y0 \<noteq> {}"  \<comment> \<open>initial Red density is not 0\<close>
  assumes Blue_edges_XY0: "Blue \<inter> all_edges_betw_un X0 Y0 \<noteq> {}"  \<comment> \<open>initial Red density is not 1\<close>

context Diagonal
begin

lemma finite_X0: "finite X0" and finite_Y0: "finite Y0"
  using XY0 finV finite_subset by blast+

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

lemma Red_E: "Red \<subset> E" "Red \<subseteq> E" and Blue_E: "Blue \<subset> E" "Blue \<subseteq> E" 
  using part_RB Red_not_Blue by (auto simp: partition_on_def disjnt_iff pairwise_def)

lemma disjnt_Red_Blue: "disjnt Red Blue"
  by (metis Red_not_Blue pairwise_insert part_RB partition_on_def singletonI)

lemma Red_Blue_all: "Red \<union> Blue = all_edges V"
  using part_RB complete by (auto simp: partition_on_def)

lemma Blue_eq: "Blue = all_edges V - Red"
  using disjnt_Red_Blue Red_Blue_all complete wellformed
  by (auto simp: disjnt_iff)

lemma Red_eq: "Red = all_edges V - Blue"
  using Blue_eq Red_Blue_all by blast

lemma nontriv: "E \<noteq> {}"
  using Red_E bot.extremum_strict by blast

lemma in_E_iff [iff]: "{v,w} \<in> E \<longleftrightarrow> v\<in>V \<and> w\<in>V \<and> v\<noteq>w"
  by (auto simp: complete all_edges_alt doubleton_eq_iff)

lemma no_singleton_Blue [simp]: "{a} \<notin> Blue"
  using Blue_E by auto

lemma no_singleton_Red [simp]: "{a} \<notin> Red"
  using Red_E by auto

lemma not_Red_Neighbour [simp]: "x \<notin> Neighbours Red x" and not_Blue_Neighbour [simp]: "x \<notin> Neighbours Blue x"
  using Red_E Blue_E not_own_Neighbour by auto

lemma Neighbours_RB:
  assumes "a \<in> V" "X\<subseteq>V"
  shows "Neighbours Red a \<inter> X \<union> Neighbours Blue a \<inter> X = X - {a}"
  using assms Red_Blue_all complete singleton_not_edge
  by (fastforce simp: Neighbours_def)

lemma Neighbours_Red_Blue: 
  assumes "x \<in> V" 
  shows "Neighbours Red x = V - insert x (Neighbours Blue x)"
  using Red_E assms by (auto simp: Blue_eq Neighbours_def complete all_edges_def)

lemma disjnt_Red_Blue_Neighbours: "disjnt (Neighbours Red x \<inter> X) (Neighbours Blue x \<inter> X')"
  using disjnt_Red_Blue by (auto simp: disjnt_def Neighbours_def)

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

lemma edge_card_empty [simp]: "edge_card C {} X = 0" "edge_card C X {} = 0"
  by (auto simp: edge_card_def)

lemma edge_card_commute: "edge_card C X Y = edge_card C Y X"
  using all_edges_betw_un_commute edge_card_def by presburger

lemma edge_card_le: 
  assumes "finite X" "finite Y"
  shows "edge_card C X Y \<le> card X * card Y"
unfolding edge_card_def
  by (metis Int_lower2 all_edges_betw_un_le assms card_mono finite_all_edges_betw_un order_trans)

text \<open>the assumption that @{term Z} is disjoint from @{term X} (or else @{term Y}) is necessary\<close>
lemma edge_card_Un:
  assumes "disjnt X Y" "disjnt X Z" "finite X" "finite Y"
  shows "edge_card C (X \<union> Y) Z = edge_card C X Z + edge_card C Y Z"
proof -
  have "disjnt (C \<inter> all_edges_betw_un X Z) (C \<inter> all_edges_betw_un Y Z)"
    using assms by (meson Int_iff disjnt_all_edges_betw_un disjnt_iff)
  then show ?thesis
    unfolding edge_card_def
    by (metis Int_Un_distrib all_uedges_betw_subset card_Un_disjnt fin_edges finite_Int 
            finite_subset all_edges_betw_un_Un1)
qed

lemma edge_card_diff:
  assumes "Y\<subseteq>X" "disjnt X Z" "finite X" 
  shows "edge_card C (X-Y) Z = edge_card C X Z - edge_card C Y Z"
  by (metis Diff_disjoint Diff_partition Diff_subset assms diff_add_inverse disjnt_def disjnt_subset1 edge_card_Un finite_subset)

lemma edge_card_mono:
  assumes "Y\<subseteq>X" shows "edge_card C Y Z \<le> edge_card C X Z"
  unfolding edge_card_def
proof (intro card_mono)
  show "finite (C \<inter> all_edges_betw_un X Z)"
    by (meson all_uedges_betw_subset fin_edges finite_Int finite_subset)
  show "C \<inter> all_edges_betw_un Y Z \<subseteq> C \<inter> all_edges_betw_un X Z"
    by (meson Int_mono all_edges_betw_un_mono1 assms subset_refl)
qed

lemma edge_card_eq_sum_Neighbours:
  assumes "C\<subseteq>E" and B: "finite B" "disjnt A B"
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

lemma gen_density_empty [simp]: "gen_density C {} X = 0" "gen_density C X {} = 0"
  by (auto simp: gen_density_def)

lemma gen_density_commute: "gen_density C X Y = gen_density C Y X"
  by (simp add: edge_card_commute gen_density_def)

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

lemma gen_density_Un_le:
  assumes "disjnt X Y" "disjnt X Z" "finite X" "finite Y"
  shows "gen_density C (X\<union>Y) Z \<le> gen_density C X Z + gen_density C Y Z"
proof (cases "X={} \<or> Y={} \<or> Z={}")
  case True
  then show ?thesis
    by (auto simp: gen_density_def)
next
  case False
  with assms show ?thesis
    apply (simp add: gen_density_def edge_card_Un card_Un_disjnt add_divide_distrib field_simps)
    by (smt (verit, best) card_0_eq frac_le mult_eq_0_iff mult_pos_pos of_nat_0_eq_iff of_nat_le_0_iff)
qed

lemma gen_density_diff_ge:
  assumes "disjnt X Z" "finite X" "Y\<subseteq>X"
  shows "gen_density C (X-Y) Z \<ge> gen_density C X Z - gen_density C Y Z"
  using assms
  by (smt (verit, del_insts) Diff_disjoint Diff_partition Diff_subset disjnt_def disjnt_subset1
          gen_density_Un_le finite_subset)

lemma gen_density_le_iff:
  assumes "disjnt X Z" "finite X" "Y\<subseteq>X" "Y \<noteq> {}" "finite Z"
  shows "gen_density C X Z \<le> gen_density C Y Z \<longleftrightarrow> 
        edge_card C X Z / card X \<le> edge_card C Y Z / card Y"
  using assms by (simp add: gen_density_def divide_simps mult_less_0_iff zero_less_mult_iff)

text \<open>"Removing vertices whose degree is less than the average can only increase the density 
from the remaining set" (page 17) \<close>
lemma gen_density_below_avg_ge:
  assumes "disjnt X Z" "finite X" "Y\<subset>X" "finite Z" 
    and genY: "gen_density C Y Z \<le> gen_density C X Z"
  shows "gen_density C (X-Y) Z \<ge> gen_density C X Z"
proof -
  have "real (edge_card C Y Z) / card Y \<le> real (edge_card C X Z) / card X"
    using assms
    by (force simp add: gen_density_def divide_simps zero_less_mult_iff split: if_split_asm)
  have "card Y < card X"
    by (simp add: assms psubset_card_mono)
  have *: "finite Y" "Y \<subseteq> X" "X\<noteq>{}"
    using assms finite_subset by blast+
  then
  have "card X * edge_card C Y Z \<le> card Y * edge_card C X Z"
    using genY assms
    by (simp add: gen_density_def field_split_simps card_eq_0_iff flip: of_nat_mult split: if_split_asm)
  with assms * \<open>card Y < card X\<close> show ?thesis
    by (simp add: gen_density_le_iff field_split_simps edge_card_diff card_Diff_subset of_nat_diff 
        edge_card_mono flip: of_nat_mult)
qed

(*UNUSED 29-02-24*)
lemma gen_le_edge_density: "gen_density C X Y \<le> edge_density X Y"
proof (cases "finite X \<and> finite Y")
  case True
  then have "card (C \<inter> all_edges_betw_un X Y) \<le> card (all_edges_betw_un X Y)"
    by (simp add: all_edges_betw_un_iff_mk_edge card_mono finite_all_edges_between')
  also have "\<dots> \<le> card (all_edges_between X Y)"
    by (simp add: all_edges_betw_un_iff_mk_edge card_image_le finite_all_edges_between')
  finally show ?thesis
    by (simp add: gen_density_def edge_card_def edge_density_def divide_right_mono)
qed (auto simp: gen_density_def edge_density_def)


definition Weight :: "['a set, 'a set, 'a, 'a] \<Rightarrow> real" where
  "Weight \<equiv> \<lambda>X Y x y. inverse (card Y) * (card (Neighbours Red x \<inter> Neighbours Red y \<inter> Y)
                      - red_density X Y * card (Neighbours Red x \<inter> Y))"

definition weight :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> real" where
  "weight \<equiv> \<lambda>X Y x. \<Sum>y \<in> X-{x}. Weight X Y x y"

definition p0 :: "real"
  where "p0 \<equiv> red_density X0 Y0"

definition eps :: "nat \<Rightarrow> real"
  where "eps \<equiv> \<lambda>k. real k powr (-1/4)"

definition qfun :: "[nat, nat] \<Rightarrow> real"
  where "qfun \<equiv> \<lambda>k h. p0 + ((1 + eps k)^h - 1) / k"

definition hgt :: "[nat, real] \<Rightarrow> nat"
  where "hgt \<equiv> \<lambda>k p. if k=0 then 1 else (LEAST h. p \<le> qfun k h \<and> h>0)"

lemma q0 [simp]: "qfun k 0 = p0"
  by (simp add: qfun_def)

lemma card_XY0: "card X0 > 0" "card Y0 > 0"
  using Red_edges_XY0 finite_X0 finite_Y0 by force+

lemma finite_Red [simp]: "finite Red"
  by (metis Red_Blue_all complete fin_edges finite_Un)

lemma finite_Blue [simp]: "finite Blue"
  using Blue_E fin_edges finite_subset by blast

lemma Red_edges_nonzero: "edge_card Red X0 Y0 > 0"
  using Red_edges_XY0
  using Red_E edge_card_def fin_edges finite_subset by fastforce

lemma Blue_edges_nonzero: "edge_card Blue X0 Y0 > 0"
  using Blue_edges_XY0
  using Blue_E edge_card_def fin_edges finite_subset by fastforce

lemma Blue_edges_less: "edge_card Red X0 Y0 < card X0 * card Y0"
proof -
  have "edge_card Red X0 Y0 \<noteq> card X0 * card Y0"
    using Blue_edges_XY0 Blue_eq Diff_Int_distrib2
    by (metis Diff_eq_empty_iff Int_lower2 all_edges_betw_un_le card_seteq edge_card_def
        finite_X0 finite_Y0 finite_all_edges_betw_un) 
  then show ?thesis
    by (meson edge_card_le finite_X0 finite_Y0 le_eq_less_or_eq)
qed

lemma p0_01: "0 < p0" "p0 < 1"
proof -
  show "0 < p0"
    using Red_edges_nonzero card_XY0
    by (auto simp: p0_def gen_density_def divide_simps mult_less_0_iff)
  show "p0 < 1"
    using Blue_edges_less card_XY0 less_imp_of_nat_less
    by (fastforce simp: p0_def gen_density_def divide_simps mult_less_0_iff)
qed

lemma eps_eq_sqrt: "eps k = 1 / sqrt (sqrt (real k))"
  by (simp add: eps_def powr_minus_divide powr_powr flip: powr_half_sqrt)

lemma eps_ge0: "eps k \<ge> 0"
  by (simp add: eps_def)

lemma eps_gt0: "k>0 \<Longrightarrow> eps k > 0"
  by (simp add: eps_def)

lemma eps_le1:
  assumes "k>0" shows "eps k \<le> 1"
proof -
  have "eps 1 = 1"
    by (simp add: eps_def)
  moreover have "eps n \<le> eps m" if "0<m" "m \<le> n" for m n
    using that by (simp add: eps_def powr_minus powr_mono2 divide_simps)
  ultimately show ?thesis
    using assms by (metis less_one nat_neq_iff not_le)
qed

lemma eps_less1:
  assumes "k>1" shows "eps k < 1"
  by (smt (verit) assms eps_def less_imp_of_nat_less of_nat_1 powr_less_one zero_le_divide_iff)

lemma qfun_strict_mono: "\<lbrakk>k>0; h'<h\<rbrakk> \<Longrightarrow> qfun k h' < qfun k h"
  by (simp add: qfun_def eps_gt0 power_strict_increasing divide_strict_right_mono)

lemma qfun_mono: "\<lbrakk>k>0; h'\<le>h\<rbrakk> \<Longrightarrow> qfun k h' \<le> qfun k h"
  by (simp add: qfun_def eps_ge0 frac_le power_increasing)

lemma q_Suc_diff: "qfun k (Suc h) - qfun k h = eps k * (1 + eps k)^h / k"
  by (simp add: qfun_def field_split_simps)

lemma height_exists:
  assumes "k>0"
  obtains h where "p \<le> qfun k h \<and> h>0"
proof -
  have 1: "1 + eps k \<ge> 1"
    by (auto simp: eps_def)
  have "\<forall>\<^sup>\<infinity>h. p \<le> p0 + real h * eps k / real k"
    using assms p0_01 unfolding eps_def by real_asymp
  then obtain h where "p \<le> p0 + real h * eps k / real k"
    by (meson eventually_sequentially order.refl)
  also have "... \<le> p0 + ((1 + eps k) ^ h - 1) / real k"
    using linear_plus_1_le_power [of "eps k" h]
    by (intro divide_right_mono add_mono) (auto simp: eps_def add_ac)
  also have "... \<le> p0 + ((1 + eps k) ^ Suc h - 1) / real k"
    using power_increasing [OF le_SucI [OF order_refl] 1]
    by (simp add: divide_right_mono)
  finally have "p \<le> qfun k (Suc h)"
    unfolding qfun_def using assms p0_01
    by blast
  then show thesis
    using that by blast 
qed

lemma hgt_gt0: "hgt k p > 0"
  by (smt (verit, best) LeastI_ex gr0I height_exists hgt_def zero_less_one)

lemma hgt_works:
  assumes "k>0" 
  shows "p \<le> qfun k (hgt k p)"
  using assms by (metis (no_types, lifting) LeastI_ex height_exists hgt_def not_gr0)

lemma hgt_Least:
  assumes "0<h" "p \<le> qfun k h"
  shows "hgt k p \<le> h"
  by (simp add: Suc_leI assms hgt_def Least_le)

lemma real_hgt_Least:
  assumes "real h \<le> r" "0<h" "p \<le> qfun k h"
  shows "real (hgt k p) \<le> r"
  using assms
  by (meson assms order.trans hgt_Least of_nat_mono)

lemma hgt_greater:
  assumes "0<k" "p > qfun k h"
  shows "hgt k p > h"
  by (smt (verit) assms linorder_le_less_linear qfun_mono height_exists hgt_works)

lemma hgt_less_imp_qfun_less:
  assumes "0<h" "h < hgt k p"
  shows "p > qfun k h"
  by (metis assms hgt_Least not_le)  

lemma hgt_le_imp_qfun_ge:
  assumes "hgt k p \<le> h" "0<k"
  shows "p \<le> qfun k h"
  by (meson assms hgt_greater not_less)

text \<open>This gives us an upper bound for heights, namely @{term "hgt k 1"}, but it's not explicit.\<close>
lemma hgt_mono:
  assumes "p \<le> q" "0<k"
  shows "hgt k p \<le> hgt k q"
  by (meson assms order.trans hgt_Least hgt_gt0 hgt_works)

lemma hgt_mono':
  assumes "hgt k p < hgt k q" "0<k"
  shows "p < q"
  by (smt (verit) assms hgt_mono leD)

lemma qfun_ge1:
  defines "f \<equiv> \<lambda>k. 2 * ln k / eps k"
  shows "\<forall>\<^sup>\<infinity>k. qfun k (nat \<lfloor>f k\<rfloor>) \<ge> 1"
proof -
  have "\<forall>\<^sup>\<infinity>k. 1 \<le> p0 + ((1 + eps k) powr (f k - 1) - 1) / k" "\<forall>\<^sup>\<infinity>k. k>0 "
    using p0_01 unfolding eps_def f_def by real_asymp+
  then have *: "\<forall>\<^sup>\<infinity>k. k>0 \<and> 1 \<le> p0 + ((1 + eps k) powr (f k - 1) - 1) / k"
    using eventually_conj by blast  
  show ?thesis
  proof (rule eventually_mono [OF *])
    fix k
    assume \<section>: "0 < k \<and> 1 \<le> p0 + ((1 + eps k) powr (f k - 1) - 1) / real k"
    then have "(1 + eps k) powr (f k - 1) \<le> (1 + eps k) ^ nat \<lfloor>f k\<rfloor>"
      using eps_gt0 [of k] by (simp flip: powr_realpow) linarith
    with \<section> show "1 \<le> qfun k (nat \<lfloor>f k\<rfloor>)"
      by (smt (verit) divide_right_mono of_nat_0_le_iff qfun_def)
  qed
qed

definition "Lemma_height_upper_bound \<equiv> \<lambda>k. \<forall>p. p \<le> 1 \<longrightarrow> hgt k p \<le> 2 * ln k / eps k"

text \<open>Height_upper_bound given just below (5) on page 9.
  Although we can bound all Heights by monotonicity (since @{term "p\<le>1"}), 
  we need to exhibit a specific $o(k)$ function.\<close>
lemma height_upper_bound: "\<forall>\<^sup>\<infinity>k. Lemma_height_upper_bound k"
  unfolding Lemma_height_upper_bound_def
  using real_hgt_Least eventually_mono [OF qfun_ge1] p0_01
  by (smt (verit, best) nat_floor_neg of_nat_0_less_iff of_nat_floor of_nat_le_0_iff q0)


definition alpha :: "nat \<Rightarrow> nat \<Rightarrow> real" where "alpha \<equiv> \<lambda>k h. qfun k h - qfun k (h-1)"

lemma alpha_0 [simp]: "alpha 0 h = 0" and alpha_0' [simp]: "alpha k 0 = 0"
  by (auto simp add: alpha_def qfun_def)

lemma alpha_ge0: "alpha k h \<ge> 0"
  by (simp add: alpha_def qfun_def divide_le_cancel eps_gt0)

lemma alpha_Suc_ge: "alpha k (Suc h) \<ge> eps k / k"
proof -
  have "(1 + eps k) ^ h \<ge> 1"
    by (simp add: eps_def)
  then show ?thesis
    by (simp add: alpha_def qfun_def eps_gt0 field_split_simps)
qed

lemma alpha_ge: "h>0 \<Longrightarrow> alpha k h \<ge> eps k / k"
  by (metis Suc_pred alpha_Suc_ge)

lemma alpha_gt0: "\<lbrakk>k>0; h>0\<rbrakk> \<Longrightarrow> alpha k h > 0"
  by (smt (verit) alpha_ge divide_pos_pos eps_gt0 of_nat_0_less_iff)

lemma alpha_Suc_eq: "alpha k (Suc h) = eps k * (1 + eps k) ^ h / k"
  by (simp add: alpha_def q_Suc_diff)

lemma alpha_eq: 
  assumes "h>0" shows "alpha k h = eps k * (1 + eps k) ^ (h-1) / k"
  by (metis Suc_pred' alpha_Suc_eq assms)

lemma alpha_hgt_ge: "alpha k (hgt k p) \<ge> eps k / k"
  by (simp add: alpha_ge hgt_gt0)

lemma alpha_hgt_eq: "alpha k (hgt k p) = eps k * (1 + eps k) ^ (hgt k p -1) / k"
  using alpha_eq hgt_gt0 by presburger

lemma alpha_mono: "\<lbrakk>h' \<le> h; 0 < h'\<rbrakk> \<Longrightarrow> alpha k h' \<le> alpha k h"
  by (simp add: alpha_eq eps_ge0 divide_right_mono mult_left_mono power_increasing)

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

(*This wants to be a locale. But nested locales don't seem to work, and having separate
locales for different parts of the development gets confusing here.*)
  \<comment> \<open>l: blue limit, and k: red limit\<close>

text \<open>Basic conditions for the book algorithm.\<close>
text\<open>We also don't want it to terminate without executing even one step [NOT ACTUALLY NEEDED]\<close>
definition "Colours \<equiv> \<lambda>l k. l \<le> k \<and> \<not> (\<exists>K. size_clique k K Red) \<and> \<not> (\<exists>K. size_clique l K Blue)
        \<and> \<not> termination_condition l k X0 Y0"

lemma Colours_ln0: "Colours l k \<Longrightarrow> l>0"
  by (force simp: Colours_def size_clique_def clique_def)

lemma Colours_kn0: "Colours l k \<Longrightarrow> k>0"
  using Colours_def Colours_ln0 not_le by auto

lemma 
  assumes "V_state(X,Y,A,B)" 
  shows finX: "finite X" and finY: "finite Y" and finA: "finite A" and finB: "finite B"
  using V_state_def assms finV finite_subset by auto

lemma 
  assumes "valid_state(X,Y,A,B)" 
  shows A_Red_clique: "clique A Red" and B_Blue_clique: "clique B Blue"
  using assms
  by (auto simp: valid_state_def V_state_def RB_state_def all_edges_betw_un_iff_clique all_edges_betw_un_Un2)

lemma A_less_k:
  assumes valid: "valid_state(X,Y,A,B)" and "Colours l k"
  shows "card A < k"
  using assms A_Red_clique[OF valid] unfolding Colours_def size_clique_def valid_state_def V_state_def
  by (smt (verit) card_Ex_subset case_prod_conv order.trans linorder_not_less smaller_clique)

lemma B_less_l:
  assumes valid: "valid_state(X,Y,A,B)" and "Colours l k"
  shows "card B < l"
  using assms B_Blue_clique[OF valid] unfolding Colours_def size_clique_def valid_state_def V_state_def
  by (smt (verit) card_Ex_subset case_prod_conv order.trans linorder_not_less smaller_clique)


subsection \<open>Degree regularisation\<close>

definition "red_dense \<equiv> \<lambda>k Y p x. card (Neighbours Red x \<inter> Y) \<ge> (p - eps k powr (-1/2) * alpha k (hgt k p)) * card Y"

definition "X_degree_reg \<equiv> \<lambda>k X Y. {x \<in> X. red_dense k Y (red_density X Y) x}"

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

lemma not_red_dense_sum_less:
  assumes "\<And>x. x \<in> X \<Longrightarrow> \<not> red_dense k Y p x" and "X\<noteq>{}" "finite X"
  shows "(\<Sum>x\<in>X. card (Neighbours Red x \<inter> Y)) < p * real (card Y) * card X"
proof -
  have "\<And>x. x \<in> X \<Longrightarrow> card (Neighbours Red x \<inter> Y) < p * real (card Y)"
    using assms
    unfolding red_dense_def
    by (smt (verit, ccfv_SIG) alpha_ge0 distrib_right mult_minus_left of_nat_0_le_iff powr_ge_pzero zero_less_mult_iff)
  with \<open>X\<noteq>{}\<close> show ?thesis
    by (smt (verit) \<open>finite X\<close> of_nat_sum sum_strict_mono mult_of_nat_commute sum_constant)
qed

lemma red_density_X_degree_reg_ge:
  assumes "disjnt X Y"
  shows "red_density (X_degree_reg k X Y) Y \<ge> red_density X Y"
proof (cases "X={} \<or> infinite X \<or> infinite Y")
  case True
  then show ?thesis
    by (force simp add: gen_density_def X_degree_reg_def)
next
  case False
  then have "finite X" "finite Y"
    by auto
  { assume "\<And>x. x \<in> X \<Longrightarrow> \<not> red_dense k Y (red_density X Y) x"
    with False have "(\<Sum>x\<in>X. card (Neighbours Red x \<inter> Y)) < red_density X Y * real (card Y) * card X"
      using \<open>finite X\<close> not_red_dense_sum_less by blast
    with Red_E have "edge_card Red Y X < (red_density X Y * real (card Y)) * card X"
      by (metis False assms disjnt_sym edge_card_eq_sum_Neighbours)
    then have False
      by (simp add: gen_density_def edge_card_commute split: if_split_asm)
  }
  then obtain x where x: "x \<in> X" "red_dense k Y (red_density X Y) x"
    by blast
  define X' where "X' \<equiv> {x \<in> X. \<not> red_dense k Y (red_density X Y) x}"
  have X': "finite X'" "disjnt Y X'"
    using assms \<open>finite X\<close> by (auto simp: X'_def disjnt_iff)
  have eq: "X_degree_reg k X Y = X - X'"
    by (auto simp: X_degree_reg_def X'_def)
  show ?thesis
  proof (cases "X'={}")
    case True
    then show ?thesis
      by (simp add: eq)
  next
    case False
    show ?thesis 
      unfolding eq
    proof (rule gen_density_below_avg_ge)
      have "(\<Sum>x\<in>X'. card (Neighbours Red x \<inter> Y)) < red_density X Y * real (card Y) * card X'"
      proof (intro not_red_dense_sum_less)
        fix x
        assume "x \<in> X'"
        show "\<not> red_dense k Y (red_density X Y) x"
          using \<open>x \<in> X'\<close> by (simp add: X'_def)
      qed (use False X' in auto)
      then have "card X * (\<Sum>x\<in>X'. card (Neighbours Red x \<inter> Y)) < card X' * edge_card Red Y X"
        by (simp add: gen_density_def mult.commute divide_simps edge_card_commute
            flip: of_nat_sum of_nat_mult split: if_split_asm)
      then have "card X * (\<Sum>x\<in>X'. card (Neighbours Red x \<inter> Y)) \<le> card X' * (\<Sum>x\<in>X. card (Neighbours Red x \<inter> Y))"
        using assms Red_E
        by (metis \<open>finite X\<close> disjnt_sym edge_card_eq_sum_Neighbours nless_le)
      then have "red_density Y X' \<le> red_density Y X"
        using assms X' False \<open>finite X\<close>
        apply (simp add: gen_density_def edge_card_eq_sum_Neighbours disjnt_commute Red_E)
        apply (simp add: X'_def field_split_simps flip: of_nat_sum of_nat_mult)
        done
      then show "red_density X' Y \<le> red_density X Y"
        by (simp add: X'_def gen_density_commute)
    qed (use assms x \<open>finite X\<close> \<open>finite Y\<close> X'_def in auto)
  qed
qed

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

lemma bounded_good_blue_book: "\<lbrakk>good_blue_book \<mu> X (S,T); finite X\<rbrakk> \<Longrightarrow> card S \<le> card X"
  by (simp add: card_mono finX good_blue_book_def)

definition best_blue_book_card :: "[real,'a set] \<Rightarrow> nat" where
  "best_blue_book_card \<equiv> \<lambda>\<mu> X. GREATEST s. \<exists>S T. good_blue_book \<mu> X (S,T) \<and> s = card S"

lemma best_blue_book_is_best: "\<lbrakk>good_blue_book \<mu> X (S,T); finite X\<rbrakk> \<Longrightarrow> card S \<le> best_blue_book_card \<mu> X"
  unfolding best_blue_book_card_def
  by (smt (verit) Greatest_le_nat bounded_good_blue_book)

lemma ex_best_blue_book: "finite X \<Longrightarrow> \<exists>S T. good_blue_book \<mu> X (S,T) \<and> card S = best_blue_book_card \<mu> X"
  unfolding best_blue_book_card_def
  by (smt (verit, del_insts) GreatestI_ex_nat bounded_good_blue_book ex_good_blue_book)

definition "choose_blue_book \<equiv> \<lambda>\<mu> (X,Y,A,B). @(S,T). good_blue_book \<mu> X (S,T) \<and> card S = best_blue_book_card \<mu> X"

lemma choose_blue_book_works: 
  "\<lbrakk>finite X; (S,T) = choose_blue_book \<mu> (X,Y,A,B)\<rbrakk> 
  \<Longrightarrow> good_blue_book \<mu> X (S,T) \<and> card S = best_blue_book_card \<mu> X"
  unfolding choose_blue_book_def
  using someI_ex [OF ex_best_blue_book]
  by (metis (mono_tags, lifting) case_prod_conv someI_ex)

lemma choose_blue_book_subset: 
  "\<lbrakk>finite X; (S,T) = choose_blue_book \<mu> (X,Y,A,B)\<rbrakk> \<Longrightarrow> S \<subseteq> X \<and> T \<subseteq> X \<and> disjnt S T"
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

lemma finite_central_vertex_set: "finite X \<Longrightarrow> finite {x. central_vertex \<mu> X x}"
  by (simp add: central_vertex_def)

definition max_central_vx :: "[real,'a set,'a set] \<Rightarrow> real" where
  "max_central_vx \<equiv> \<lambda>\<mu> X Y. Max (weight X Y ` {x. central_vertex \<mu> X x})"

lemma central_vx_is_best: 
  "\<lbrakk>central_vertex \<mu> X x; finite X\<rbrakk> \<Longrightarrow> weight X Y x \<le> max_central_vx \<mu> X Y"
  unfolding max_central_vx_def by (simp add: finite_central_vertex_set)

lemma ex_best_central_vx: 
  "\<lbrakk>\<not> termination_condition l k X Y; \<not> many_bluish \<mu> l k X; finite X\<rbrakk> 
  \<Longrightarrow> \<exists>x. central_vertex \<mu> X x \<and> weight X Y x = max_central_vx \<mu> X Y"
  unfolding max_central_vx_def
  by (metis empty_iff ex_central_vertex finite_central_vertex_set mem_Collect_eq obtains_MAX)

text \<open>it's necessary to make a specific choice; a relational treatment might allow different vertices 
  to be chosen, making a nonsense of the choice between steps 4 and 5\<close>
definition "choose_central_vx \<equiv> \<lambda>\<mu> (X,Y,A,B). @x. central_vertex \<mu> X x \<and> weight X Y x = max_central_vx \<mu> X Y"

lemma choose_central_vx_works: 
  "\<lbrakk>\<not> termination_condition l k X Y; \<not> many_bluish \<mu> l k X; finite X\<rbrakk> 
  \<Longrightarrow> central_vertex \<mu> X (choose_central_vx \<mu> (X,Y,A,B)) \<and> weight X Y (choose_central_vx \<mu> (X,Y,A,B)) = max_central_vx \<mu> X Y"
  unfolding choose_central_vx_def
  using someI_ex [OF ex_best_central_vx] by force

lemma choose_central_vx_X: 
  "\<lbrakk>\<not> many_bluish \<mu> l k X; \<not> termination_condition l k X Y; finite X\<rbrakk> \<Longrightarrow> choose_central_vx \<mu> (X,Y,A,B) \<in> X"
  using central_vertex_def choose_central_vx_works by fastforce

subsection \<open>Red step\<close>

definition "reddish \<equiv> \<lambda>k X Y p x. red_density (Neighbours Red x \<inter> X) (Neighbours Red x \<inter> Y) \<ge> p - alpha k (hgt k p)"

inductive red_step 
  where "\<lbrakk>reddish k X Y (red_density X Y) x; x = choose_central_vx \<mu> (X,Y,A,B)\<rbrakk> 
         \<Longrightarrow> red_step \<mu> (X,Y,A,B) (Neighbours Red x \<inter> X, Neighbours Red x \<inter> Y, insert x A, B)"

lemma red_step_V_state: 
  assumes "red_step \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" 
          "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)"
  shows "V_state U'"
proof -
  have "X \<subseteq> V"
    using assms by (auto simp: V_state_def)
  then have "choose_central_vx \<mu> (X, Y, A, B) \<in> V"
    using assms choose_central_vx_X by (fastforce simp: finX)
  with assms show ?thesis
    by (auto simp: V_state_def elim!: red_step.cases)
qed

lemma red_step_disjoint_state:
  assumes "red_step \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" 
          "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)" "disjoint_state (X,Y,A,B)"
  shows "disjoint_state U'"
proof -
  have "choose_central_vx \<mu> (X, Y, A, B) \<in> X"
    using assms by (metis choose_central_vx_X finX)
  with assms show ?thesis
    by (auto simp: disjoint_state_def disjnt_iff not_own_Neighbour elim!: red_step.cases)
qed

lemma red_step_RB_state: 
  assumes "red_step \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y"
          "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)" "RB_state (X,Y,A,B)"
  shows "RB_state U'"
proof -
  define x where "x \<equiv> choose_central_vx \<mu> (X, Y, A, B)"
  have [simp]: "finite X"
    using assms by (simp add: finX)
  have "x \<in> X"
    using assms choose_central_vx_X by (metis \<open>finite X\<close> x_def)
  have A: "all_edges_betw_un (insert x A) (insert x A) \<subseteq> Red"
    if "all_edges_betw_un A A \<subseteq> Red" "all_edges_betw_un A (X \<union> Y) \<subseteq> Red"
    using that \<open>x \<in> X\<close> all_edges_betw_un_commute 
    by (auto simp: all_edges_betw_un_insert2 all_edges_betw_un_Un2 intro!: all_uedges_betw_I)
  have B1: "all_edges_betw_un (insert x A) (Neighbours Red x \<inter> X) \<subseteq> Red"
    if "all_edges_betw_un A X \<subseteq> Red"
    using that \<open>x \<in> X\<close> by (force simp: all_edges_betw_un_def in_Neighbours_iff)
  have B2: "all_edges_betw_un (insert x A) (Neighbours Red x \<inter> Y) \<subseteq> Red"
    if "all_edges_betw_un A Y \<subseteq> Red"
    using that \<open>x \<in> X\<close> by (force simp: all_edges_betw_un_def in_Neighbours_iff)
  from assms A B1 B2 show ?thesis
    apply (clarsimp simp: RB_state_def simp flip: x_def elim!: red_step.cases)
    by (metis Int_Un_eq(2) Un_subset_iff all_edges_betw_un_Un2)
qed

lemma red_step_valid_state: 
  assumes "red_step \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" 
          "\<not> many_bluish \<mu> l k X" "valid_state (X,Y,A,B)"
  shows "valid_state U'"
  by (meson assms red_step_RB_state red_step_V_state red_step_disjoint_state valid_state_def)

subsection \<open>Density-boost step\<close>

inductive density_boost
  where "\<lbrakk>\<not> reddish k X Y (red_density X Y) x; x = choose_central_vx \<mu> (X,Y,A,B)\<rbrakk> 
         \<Longrightarrow> density_boost \<mu> (X,Y,A,B) (Neighbours Blue x \<inter> X, Neighbours Red x \<inter> Y, A, insert x B)"

lemma density_boost_V_state: 
  assumes "density_boost \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" 
          "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)"
  shows "V_state U'"
proof -
  have "X \<subseteq> V"
    using assms by (auto simp: V_state_def)
  then have "choose_central_vx \<mu> (X, Y, A, B) \<in> V"
    using assms choose_central_vx_X finX by fastforce 
  with assms show ?thesis
    by (auto simp: V_state_def elim!: density_boost.cases)
qed

lemma density_boost_disjoint_state:
  assumes "density_boost \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y"  
          "\<not> many_bluish \<mu> l k X" "V_state (X,Y,A,B)" "disjoint_state (X,Y,A,B)"
  shows "disjoint_state U'"
proof -
  have "X \<subseteq> V"
    using assms by (auto simp: V_state_def)
  then have "choose_central_vx \<mu> (X, Y, A, B) \<in> X"
    using assms by (metis choose_central_vx_X finX)
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
    using assms by (metis choose_central_vx_X finX x_def)
  have "all_edges_betw_un A (Neighbours Blue x \<inter> X \<union> Neighbours Red x \<inter> Y) \<subseteq> Red"
    if "all_edges_betw_un A (X \<union> Y) \<subseteq> Red"
    using that by (metis Int_Un_eq(4) Un_subset_iff all_edges_betw_un_Un2)
  moreover
  have "all_edges_betw_un (insert x B) (insert x B) \<subseteq> Blue"
    if "all_edges_betw_un B (B \<union> X) \<subseteq> Blue"
    using that \<open>x \<in> X\<close> by (auto simp add: subset_iff set_eq_iff all_edges_betw_un_def)
  moreover
  have "all_edges_betw_un (insert x B) (Neighbours Blue x \<inter> X) \<subseteq> Blue"
    if "all_edges_betw_un B (B \<union> X) \<subseteq> Blue"
    using \<open>x \<in> X\<close> that  by (auto simp: all_edges_betw_un_def subset_iff in_Neighbours_iff)
  ultimately show ?thesis
    using assms
    by (auto simp: RB_state_def all_edges_betw_un_Un2 x_def [symmetric]  elim!: density_boost.cases)
qed

lemma density_boost_valid_state:
  assumes "density_boost \<mu> (X,Y,A,B) U'" "\<not> termination_condition l k X Y" "\<not> many_bluish \<mu> l k X" "valid_state (X,Y,A,B)"
  shows "valid_state U'"
  by (meson assms density_boost_RB_state density_boost_V_state density_boost_disjoint_state valid_state_def)

subsection \<open>Steps 2–5 as a function\<close>

definition next_state :: "[real,nat,nat,'a config] \<Rightarrow> 'a config" where
  "next_state \<equiv> \<lambda>\<mu> l k (X,Y,A,B). 
       if many_bluish \<mu> l k X 
       then let (S,T) = choose_blue_book \<mu> (X,Y,A,B) in (T, Y, A, B\<union>S) 
       else let x = choose_central_vx \<mu> (X,Y,A,B) in
            if reddish k X Y (red_density X Y) x 
            then (Neighbours Red x \<inter> X, Neighbours Red x \<inter> Y, insert x A, B)
            else (Neighbours Blue x \<inter> X, Neighbours Red x \<inter> Y, A, insert x B)"

lemma next_state_valid:
  assumes "valid_state (X,Y,A,B)" "\<not> termination_condition l k X Y"
  shows "valid_state (next_state \<mu> l k (X,Y,A,B))"
proof (cases "many_bluish \<mu> l k X")
  case True
  with finX have "big_blue \<mu> (X,Y,A,B) (next_state \<mu> l k (X,Y,A,B))"
    apply (simp add: next_state_def split: prod.split)
    by (metis assms(1) big_blue.intros choose_blue_book_works valid_state_def)
  then show ?thesis
    using assms big_blue_valid_state by blast
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
      else if even n then degree_reg k (X,Y,A,B) else next_state \<mu> l k (X,Y,A,B))"

lemma degree_reg_subset:
  assumes "degree_reg k (X,Y,A,B) = (X',Y',A',B')" 
  shows "X' \<subseteq> X \<and> Y' \<subseteq> Y"
  using assms by (auto simp: degree_reg_def X_degree_reg_def)

lemma next_state_subset:
  assumes "next_state \<mu> l k (X,Y,A,B) = (X',Y',A',B')" "finite X"
  shows "X' \<subseteq> X \<and> Y' \<subseteq> Y"
  using assms choose_blue_book_subset
  apply (clarsimp simp: next_state_def valid_state_def Let_def split: if_split_asm prod.split_asm)
  by (smt (verit) choose_blue_book_subset subset_eq)

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

lemma V_state_stepper: "V_state (stepper \<mu> l k n)"
  using valid_state_def valid_state_stepper by force

lemma disjoint_state_stepper: "disjoint_state (stepper \<mu> l k n)"
  using valid_state_def valid_state_stepper by force

lemma RB_state_stepper: "RB_state (stepper \<mu> l k n)"
  using valid_state_def valid_state_stepper by force

lemma stepper_A:
  assumes \<section>: "stepper \<mu> l k n = (X,Y,A,B)"
  shows "clique A Red \<and> A\<subseteq>V"
proof -
  have "A\<subseteq>V"
    using V_state_stepper[of \<mu> l k n] assms by (auto simp: V_state_def)
  moreover
  have "all_edges_betw_un A A \<subseteq> Red"
    using RB_state_stepper[of \<mu> l k n] assms by (auto simp: RB_state_def)
  ultimately show ?thesis
    using all_edges_betw_un_iff_clique by simp
qed

lemma card_A_limit:
  assumes "stepper \<mu> l k n = (X,Y,A,B)" "Colours l k" shows "card A < k"
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
    using V_state_stepper[of \<mu> l k n] assms by (auto simp: V_state_def)
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
definition "Aseq \<mu> l k \<equiv> (\<lambda>(X,Y,A,B). A) \<circ> stepper \<mu> l k"
definition "Bseq \<mu> l k \<equiv> (\<lambda>(X,Y,A,B). B) \<circ> stepper \<mu> l k"
definition "pseq \<mu> l k \<equiv> \<lambda>n. red_density (Xseq \<mu> l k n) (Yseq \<mu> l k n)"

definition "pee \<equiv> \<lambda>\<mu> l k i. red_density (Xseq \<mu> l k i) (Yseq \<mu> l k i)"

lemma Xseq_0 [simp]: "Xseq \<mu> l k 0 = X0"
  by (simp add: Xseq_def)

lemma Xseq_Suc_subset: "Xseq \<mu> l k (Suc i) \<subseteq> Xseq \<mu> l k i"
  apply (simp add: Xseq_def split: if_split_asm prod.split)
  by (metis V_state_stepper degree_reg_subset finX next_state_subset)

lemma Xseq_antimono: "j \<le> i \<Longrightarrow> Xseq \<mu> l k i \<subseteq> Xseq \<mu> l k j"
  by (simp add: Xseq_Suc_subset lift_Suc_antimono_le)

lemma Xseq_subset_V: "Xseq \<mu> l k i \<subseteq> V"
  using XY0 Xseq_0 Xseq_antimono by blast

lemma finite_Xseq: "finite (Xseq \<mu> l k i)"
  by (meson Xseq_subset_V finV finite_subset)

lemma Yseq_0 [simp]: "Yseq \<mu> l k 0 = Y0"
  by (simp add: Yseq_def)

lemma Yseq_Suc_subset: "Yseq \<mu> l k (Suc i) \<subseteq> Yseq \<mu> l k i"
  apply (simp add: Yseq_def split: if_split_asm prod.split)
  by (metis V_state_stepper degree_reg_subset finX next_state_subset)

lemma Yseq_antimono: "j \<le> i \<Longrightarrow> Yseq \<mu> l k i \<subseteq> Yseq \<mu> l k j"
  by (simp add: Yseq_Suc_subset lift_Suc_antimono_le)

lemma Yseq_subset_V: "Yseq \<mu> l k i \<subseteq> V"
  using XY0 Yseq_0 Yseq_antimono by blast

lemma finite_Yseq: "finite (Yseq \<mu> l k i)"
  by (meson Yseq_subset_V finV finite_subset)

lemma Xseq_Yseq_disjnt: "disjnt (Xseq \<mu> l k i) (Yseq \<mu> l k i)"
  by (metis (no_types, opaque_lifting) XY0(1) Xseq_0 Xseq_antimono Yseq_0 Yseq_antimono disjnt_iff le0 subset_eq)

lemma edge_card_eq_pee: 
  "edge_card Red (Xseq \<mu> l k i) (Yseq \<mu> l k i) = pee \<mu> l k i * card (Xseq \<mu> l k i) * card (Yseq \<mu> l k i)"
  by (simp add: pee_def gen_density_def finite_Xseq finite_Yseq)

lemma valid_state_seq: "valid_state(Xseq \<mu> l k i, Yseq \<mu> l k i, Aseq \<mu> l k i, Bseq \<mu> l k i)"
  using valid_state_stepper[of \<mu> l k i]
  by (force simp add: Xseq_def Yseq_def Aseq_def Bseq_def simp del: valid_state_stepper split: prod.split)

lemma Aseq_less_k:
  assumes "Colours l k"
  shows "card (Aseq \<mu> l k i) < k"
  by (meson A_less_k assms valid_state_seq)

lemma Aseq_0 [simp]: "Aseq \<mu> l k 0 = {}"
  by (simp add: Aseq_def)

lemma Aseq_Suc_subset: "Aseq \<mu> l k i \<subseteq> Aseq \<mu> l k (Suc i)"
  by (fastforce simp: Aseq_def next_state_def degree_reg_def Let_def split: prod.split)

lemma Aseq_mono: "j \<le> i \<Longrightarrow> Aseq \<mu> l k j \<subseteq> Aseq \<mu> l k i"
  by (simp add: Aseq_Suc_subset lift_Suc_mono_le)

lemma Aseq_subset_V: "Aseq \<mu> l k i \<subseteq> V"
  using stepper_A[of \<mu> l k i] by (simp add: Aseq_def split: prod.split) 

lemma finite_Aseq: "finite (Aseq \<mu> l k i)"
  by (meson Aseq_subset_V finV finite_subset)

lemma Bseq_less_l:
  assumes "Colours l k"
  shows "card (Bseq \<mu> l k i) < l"
  by (meson B_less_l assms valid_state_seq)

lemma Bseq_0 [simp]: "Bseq \<mu> l k 0 = {}"
  by (simp add: Bseq_def)

lemma Bseq_Suc_subset: "Bseq \<mu> l k i \<subseteq> Bseq \<mu> l k (Suc i)"
  by (fastforce simp: Bseq_def next_state_def degree_reg_def Let_def split: prod.split)

lemma Bseq_mono: "j \<le> i \<Longrightarrow> Bseq \<mu> l k j \<subseteq> Bseq \<mu> l k i"
  by (simp add: Bseq_Suc_subset lift_Suc_mono_le)

lemma Bseq_subset_V: "Bseq \<mu> l k i \<subseteq> V"
  using stepper_B[of \<mu> l k i] by (simp add: Bseq_def split: prod.split) 

lemma finite_Bseq: "finite (Bseq \<mu> l k i)"
  by (meson Bseq_subset_V finV finite_subset)

lemma pee_eq_p0: "pee \<mu> l k 0 = p0"
  by (simp add: pee_def p0_def)

lemma pee_ge0: "pee \<mu> l k i \<ge> 0"
  by (simp add: gen_density_ge0 pee_def)

lemma pee_le1: "pee \<mu> l k i \<le> 1"
  using gen_density_le1 pee_def by presburger

lemma pseq_0: "p0 = pseq \<mu> l k 0"
  by (simp add: p0_def pseq_def Xseq_def Yseq_def)

text \<open>The central vertex at each step (though only defined in some cases), 
  @{term "x_i"} in the paper\<close>
definition cvx :: "[real,nat,nat,nat] \<Rightarrow> 'a" where
  "cvx \<equiv> \<lambda>\<mu> l k i. choose_central_vx \<mu> (stepper \<mu> l k i)"

text \<open>the indexing of @{term beta} is as in the paper --- and different from that of @{term Xseq}\<close>
definition 
  "beta \<equiv> \<lambda>\<mu> l k i. 
    (let (X,Y,A,B) = stepper \<mu> l k i in card(Neighbours Blue (cvx \<mu> l k i) \<inter> X) / card X)"

lemma beta_eq: "beta \<mu> l k i = card(Neighbours Blue (cvx \<mu> l k i) \<inter> Xseq \<mu> l k i) / card (Xseq \<mu> l k i)"
  by (simp add: beta_def cvx_def Xseq_def split: prod.split)

lemma beta_ge0: "beta \<mu> l k i \<ge> 0"
  by (simp add: beta_eq)


subsection \<open>The classes of execution steps\<close>

text \<open>For R, B, S, D\<close>
datatype stepkind = red_step | bblue_step | dboost_step | dreg_step | halted

definition next_state_kind :: "[real,nat,nat,'a config] \<Rightarrow> stepkind" where
  "next_state_kind \<equiv> \<lambda>\<mu> l k (X,Y,A,B). 
       if many_bluish \<mu> l k X then bblue_step 
       else let x = choose_central_vx \<mu> (X,Y,A,B) in
            if reddish k X Y (red_density X Y) x then red_step
            else dboost_step"

definition stepper_kind :: "[real,nat,nat,nat] \<Rightarrow> stepkind" where
  "stepper_kind \<mu> l k i = 
     (let (X,Y,A,B) = stepper \<mu> l k i in 
      if termination_condition l k X Y then halted 
      else if even i then dreg_step else next_state_kind \<mu> l k (X,Y,A,B))"

definition "Step_class \<equiv> \<lambda>\<mu> l k knd. {n. stepper_kind \<mu> l k n \<in> knd}"

lemma subset_Step_class: "\<lbrakk>i \<in> Step_class \<mu> l k K'; K' \<subseteq> K\<rbrakk> \<Longrightarrow> i \<in> Step_class \<mu> l k K"
  by (auto simp: Step_class_def)

lemma Step_class_Un: "Step_class \<mu> l k (K' \<union> K) = Step_class \<mu> l k K' \<union> Step_class \<mu> l k K"
  by (auto simp: Step_class_def)

lemma Step_class_insert: "Step_class \<mu> l k (insert knd K) = (Step_class \<mu> l k {knd}) \<union> (Step_class \<mu> l k K)"
  by (auto simp: Step_class_def)

lemma Step_class_insert_NO_MATCH:
  "NO_MATCH {} K \<Longrightarrow> Step_class \<mu> l k (insert knd K) = (Step_class \<mu> l k {knd}) \<union> (Step_class \<mu> l k K)"
  by (auto simp: Step_class_def)

lemma Step_class_UNIV: "Step_class \<mu> l k {red_step,bblue_step,dboost_step,dreg_step,halted} = UNIV"
  using Step_class_def stepkind.exhaust by auto

lemma Step_class_cases:
   "i \<in> Step_class \<mu> l k {stepkind.red_step} \<or> i \<in> Step_class \<mu> l k {bblue_step} \<or>
    i \<in> Step_class \<mu> l k {dboost_step} \<or> i \<in> Step_class \<mu> l k {dreg_step} \<or>
    i \<in> Step_class \<mu> l k {halted}"
  using Step_class_def stepkind.exhaust by auto

lemmas step_kind_defs = Step_class_def stepper_kind_def next_state_kind_def Xseq_def Yseq_def

lemma disjnt_Step_class: 
  "disjnt knd knd' \<Longrightarrow> disjnt (Step_class \<mu> l k knd) (Step_class \<mu> l k knd')"
  by (auto simp: Step_class_def disjnt_iff)

lemma halted_imp_next_halted: "stepper_kind \<mu> l k i = halted \<Longrightarrow> stepper_kind \<mu> l k (Suc i) = halted"
  by (auto simp add: step_kind_defs split: prod.split if_split_asm)

lemma halted_imp_ge_halted: "stepper_kind \<mu> l k i = halted \<Longrightarrow> stepper_kind \<mu> l k (i+n) = halted"
  by (induction n) (auto simp: halted_imp_next_halted)

lemma Step_class_halted_forever: "\<lbrakk>i \<in> Step_class \<mu> l k {halted}; i\<le>j\<rbrakk> \<Longrightarrow> j \<in> Step_class \<mu> l k {halted}"
  by (simp add: Step_class_def) (metis halted_imp_ge_halted le_iff_add)

lemma Step_class_not_halted: "\<lbrakk>i \<notin> Step_class \<mu> l k {halted}; i\<ge>j\<rbrakk> \<Longrightarrow> j \<notin> Step_class \<mu> l k {halted}"
  using Step_class_halted_forever by blast

lemma
  assumes "i \<notin> Step_class \<mu> l k {halted}" 
  shows not_halted_pee_gt: "pee \<mu> l k i > 1/k"
    and Xseq_gt0: "card (Xseq \<mu> l k i) > 0"
    and Xseq_gt_RN: "card (Xseq \<mu> l k i) > RN k (nat \<lceil>real l powr (3/4)\<rceil>)"
    and not_termination_condition: "\<not> termination_condition l k (Xseq \<mu> l k i) (Yseq \<mu> l k i)"
  using assms
  by (auto simp: step_kind_defs termination_condition_def pee_def split: if_split_asm prod.split_asm)

lemma not_halted_pee_gt0:
  assumes "i \<notin> Step_class \<mu> l k {halted}" 
  shows "pee \<mu> l k i > 0" 
  using not_halted_pee_gt [OF assms] linorder_not_le order_less_le_trans by fastforce

lemma Xseq_gt_0:
  assumes "i \<notin> Step_class \<mu> l k {halted}"
  shows "card (Xseq \<mu> l k i) > 0"
  by (metis Xseq_gt_RN assms gr0I less_zeroE) 

lemma Yseq_gt_0:
  assumes "i \<notin> Step_class \<mu> l k {halted}"
  shows "card (Yseq \<mu> l k i) > 0"
  using not_halted_pee_gt [OF assms] 
  by (auto simp: pee_def gen_density_def divide_simps mult_less_0_iff zero_less_mult_iff split: if_split_asm)

lemma dreg_step_0: "\<not> termination_condition l k X0 Y0 \<Longrightarrow> 0 \<in> Step_class \<mu> l k {dreg_step}"
  by (auto simp: Step_class_def stepper_kind_def)

lemma step_odd: "i \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step} \<Longrightarrow> odd i" 
  by (auto simp: Step_class_def stepper_kind_def split: if_split_asm prod.split_asm)

lemma step_even: "i \<in> Step_class \<mu> l k {dreg_step} \<Longrightarrow> even i" 
  by (auto simp: Step_class_def stepper_kind_def next_state_kind_def split: if_split_asm prod.split_asm)

lemma not_halted_odd_RBS: "\<lbrakk>i \<notin> Step_class \<mu> l k {halted}; odd i\<rbrakk> \<Longrightarrow> i \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}" 
  by (auto simp: Step_class_def stepper_kind_def next_state_kind_def split: prod.split_asm)

lemma not_halted_even_dreg: "\<lbrakk>i \<notin> Step_class \<mu> l k {halted}; even i\<rbrakk> \<Longrightarrow> i \<in> Step_class \<mu> l k {dreg_step}" 
  by (auto simp: Step_class_def stepper_kind_def next_state_kind_def split: prod.split_asm)

lemma step_before_dreg:
  assumes "Suc i \<in> Step_class \<mu> l k {dreg_step}"
  shows "i \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}"
  using assms by (auto simp: step_kind_defs split: if_split_asm prod.split_asm)

lemma step_before_dreg':
  assumes "i \<in> Step_class \<mu> l k {dreg_step}" "i>0"
  shows "i - Suc 0 \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}"
  by (simp add: assms step_before_dreg)

lemma dreg_before_step:
  assumes "Suc i \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}" 
  shows "i \<in> Step_class \<mu> l k {dreg_step}"
  using assms by (auto simp: Step_class_def stepper_kind_def split: if_split_asm prod.split_asm)

lemma dreg_before_step':
  assumes "i \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}" 
  shows "i - Suc 0 \<in> Step_class \<mu> l k {dreg_step}" and "i>0"
proof -
  show "i>0"
    using assms step_odd by force
  then show "i - Suc 0 \<in> Step_class \<mu> l k {dreg_step}"
    using assms dreg_before_step Suc_pred by force
qed

lemma dreg_before_step1:
  assumes "i \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}" 
  shows "i-1 \<in> Step_class \<mu> l k {dreg_step}" "i > 0"
  using dreg_before_step' [OF assms] by auto

lemma step_odd_minus2: 
  assumes "i \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}" "i>1"
  shows "i-2 \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}" 
proof -
  have "odd (i-2)"
    using assms step_odd by auto
  then have "i-2 \<notin> Step_class \<mu> l k {dreg_step}"
    using step_even by blast
  moreover have "i \<notin> Step_class \<mu> l k {halted}"
    using assms by (auto simp: Step_class_def)
  then have "i-2 \<notin> Step_class \<mu> l k {halted}"
    using Step_class_not_halted diff_le_self by blast
  ultimately show ?thesis
    using stepkind.exhaust by (auto simp: Step_class_def)
qed

lemma finite_Step_class:
  assumes "\<And>n. finite {m. m<n \<and> stepper_kind \<mu> l k m = knd}"
  assumes "\<And>n. card {m. m<n \<and> stepper_kind \<mu> l k m = knd} < N"
  shows "finite (Step_class \<mu> l k {knd})"
proof -
  have "incseq (\<lambda>n. {m. m<n \<and> stepper_kind \<mu> l k m = knd})"
    by (auto simp: incseq_def)
  moreover have "(\<Union>n. {m. m<n \<and> stepper_kind \<mu> l k m = knd}) = (Step_class \<mu> l k {knd})"
    by (auto simp: Step_class_def)
  ultimately show ?thesis
    by (smt (verit) eventually_sequentially order.refl Union_incseq_finite assms)
qed

lemma Step_class_iterates:
  assumes "finite (Step_class \<mu> l k {knd})"
  obtains n where "Step_class \<mu> l k {knd} = {m. m<n \<and> stepper_kind \<mu> l k m = knd}"
proof -
  have eq: "(Step_class \<mu> l k {knd}) = (\<Union>i. {m. m<i \<and> stepper_kind \<mu> l k m = knd})"
    by (auto simp: Step_class_def)
  then obtain n where n: "(Step_class \<mu> l k {knd}) = (\<Union>i<n. {m. m<i \<and> stepper_kind \<mu> l k m = knd})"
    using finite_countable_equals[OF assms] by blast
  with Step_class_def 
  have "{m. m<n \<and> stepper_kind \<mu> l k m = knd} = (\<Union>i<n. {m. m<i \<and> stepper_kind \<mu> l k m = knd})"
    by auto
  then show ?thesis
    by (metis n that)
qed

lemma step_non_terminating:
  assumes "i \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step,dreg_step}"
  shows "\<not> termination_condition l k (Xseq \<mu> l k i) (Yseq \<mu> l k i)"
  using assms
  by (simp add: step_kind_defs split: if_split_asm prod.split_asm)

lemma not_many_bluish:
  assumes "i \<in> Step_class \<mu> l k {red_step,dboost_step}"
  shows "\<not> many_bluish \<mu> l k (Xseq \<mu> l k i)"
  using assms
  by (simp add: step_kind_defs split: if_split_asm prod.split_asm)

lemma stepper_XYseq: "stepper \<mu> l k i = (X,Y,A,B) \<Longrightarrow> X = Xseq \<mu> l k i \<and> Y = Yseq \<mu> l k i"
  using Xseq_def Yseq_def by fastforce

lemma cvx_works:
  assumes "i \<in> Step_class \<mu> l k {red_step,dboost_step}"
  shows "central_vertex \<mu> (Xseq \<mu> l k i) (cvx \<mu> l k i)
       \<and> weight (Xseq \<mu> l k i) (Yseq \<mu> l k i) (cvx \<mu> l k i) = max_central_vx \<mu> (Xseq \<mu> l k i) (Yseq \<mu> l k i)"
proof -
  have "\<not> termination_condition l k (Xseq \<mu> l k i) (Yseq \<mu> l k i)"
    using Step_class_def assms step_non_terminating by fastforce
  then show ?thesis
    using assms not_many_bluish[OF assms] 
    apply (simp add: Step_class_def Xseq_def cvx_def Yseq_def split: prod.split prod.split_asm)
    by (metis V_state_stepper choose_central_vx_works finX)
qed

lemma cvx_in_Xseq:
  assumes "i \<in> Step_class \<mu> l k {red_step,dboost_step}"
  shows "cvx \<mu> l k i \<in> Xseq \<mu> l k i"
  using assms cvx_works[OF assms] 
  by (simp add: Xseq_def central_vertex_def cvx_def split: prod.split_asm)

lemma card_Xseq_pos:
  assumes "i \<in> Step_class \<mu> l k {red_step,dboost_step}"
  shows "card (Xseq \<mu> l k i) > 0"
  by (metis assms card_0_eq cvx_in_Xseq empty_iff finite_Xseq gr0I)

lemma beta_le:
  assumes "\<mu> > 0" and i: "i \<in> Step_class \<mu> l k {red_step,dboost_step}"
  shows "beta \<mu> l k i \<le> \<mu>"
  using assms cvx_works[OF i] 
  by (simp add: beta_def central_vertex_def Xseq_def divide_simps split: prod.split_asm)

subsection \<open>Termination proof\<close>

text \<open>Each step decreases the size of @{term X}\<close>

lemma ex_nonempty_blue_book:
  assumes mb: "many_bluish \<mu> l k X" and "Colours l k"
    shows "\<exists>x\<in>X. good_blue_book \<mu> X ({x}, Neighbours Blue x \<inter> X)"
proof -
  obtain "l > 0" "k > 0"
    using \<open>Colours l k\<close> Colours_kn0 Colours_ln0 by auto
  then have "RN k (nat \<lceil>real l powr (2 / 3)\<rceil>) > 0"
    by (metis RN_eq_0_iff gr0I of_nat_ceiling of_nat_eq_0_iff powr_nonneg_iff)
  then obtain x where "x\<in>X" and x: "bluish \<mu> X x"
    using mb unfolding many_bluish_def
    by (smt (verit) card_eq_0_iff empty_iff equalityI less_le_not_le mem_Collect_eq subset_iff)
  have "book {x} (Neighbours Blue x \<inter> X) Blue"
    by (force simp add: book_def all_edges_betw_un_def in_Neighbours_iff)
  with x show ?thesis
    by (auto simp: bluish_def good_blue_book_def \<open>x \<in> X\<close>)
qed

lemma choose_blue_book_psubset: 
  assumes "many_bluish \<mu> l k X" and ST: "choose_blue_book \<mu> (X,Y,A,B) = (S,T)"
    and "\<mu>>0" "Colours l k" "finite X"
    shows "T \<noteq> X"
proof -
  obtain x where "x\<in>X" and x: "good_blue_book \<mu> X ({x}, Neighbours Blue x \<inter> X)"
    using ex_nonempty_blue_book Diagonal_axioms assms by blast
  with \<open>finite X\<close> have "best_blue_book_card \<mu> X \<noteq> 0"
    unfolding valid_state_def
    by (metis best_blue_book_is_best card.empty card_seteq empty_not_insert finite.intros singleton_insert_inj_eq)
  then have "S \<noteq> {}"
    by (metis \<open>finite X\<close> ST choose_blue_book_works card.empty)
  with \<open>finite X\<close> ST show ?thesis
    by (metis (no_types, opaque_lifting) choose_blue_book_subset disjnt_iff empty_subsetI equalityI subset_eq)
qed

lemma next_state_smaller:
  assumes "\<mu>>0"  "Colours l k" "next_state \<mu> l k (X,Y,A,B) = (X',Y',A',B')" 
    and "finite X" and nont: "\<not> termination_condition l k X Y"  
  shows "X' \<subset> X"
proof -
  have "X' \<subseteq> X"
    using assms next_state_subset by auto
  moreover have "X' \<noteq> X"
  proof -
    have *: "\<not> X \<subseteq> Neighbours rb x \<inter> X" if "x \<in> X" "rb \<subseteq> E" for x rb
      using that by (auto simp: Neighbours_def subset_iff)
    show ?thesis
    proof (cases "many_bluish \<mu> l k X")
      case True
      with assms show ?thesis 
        by (auto simp add: next_state_def split: if_split_asm prod.split_asm
            dest!:  choose_blue_book_psubset [OF True])
    next
      case False
      then have "choose_central_vx \<mu> (X,Y,A,B) \<in> X"
        by (simp add: assms(4) choose_central_vx_X nont)
      with assms *[of _ Red] *[of _ Blue] \<open>X' \<subseteq> X\<close> Red_E Blue_E False
      choose_central_vx_X [OF False nont]
      show ?thesis
        by (fastforce simp add: next_state_def Let_def split: if_split_asm prod.split_asm)
    qed
  qed
  ultimately show ?thesis
    by auto
qed

lemma do_next_state:
  assumes "odd i" "\<not> termination_condition l k (Xseq \<mu> l k i) (Yseq \<mu> l k i)"
  obtains A B A' B' where "next_state \<mu> l k (Xseq \<mu> l k i, Yseq \<mu> l k i, A, B) 
                        = (Xseq \<mu> l k (Suc i), Yseq \<mu> l k (Suc i), A',B')"
  using assms
  by (force simp: Xseq_def Yseq_def split: if_split_asm prod.split_asm prod.split)

lemma step_bound: 
  assumes "\<mu>>0" "Colours l k"
    and i: "Suc (2*i) \<in> Step_class \<mu> l k {red_step,bblue_step,dboost_step}"
  shows "card (Xseq \<mu> l k (Suc (2*i))) + i \<le> card X0"
  using i
proof (induction i)
  case 0
  then show ?case
    apply (auto simp: )
    by (metis Xseq_0 Xseq_Suc_subset card_mono finite_X0)
next
  case (Suc i)
  then have nt: "\<not> termination_condition l k (Xseq \<mu> l k (Suc (2*i))) (Yseq \<mu> l k (Suc (2*i)))"  
    apply (intro step_non_terminating)
    by (metis Step_class_insert Suc_1 Un_iff dreg_before_step mult_Suc_right plus_1_eq_Suc plus_nat.simps(2) step_before_dreg)
  obtain A B A' B' where 2:
    "next_state \<mu> l k (Xseq \<mu> l k (Suc (2*i)), Yseq \<mu> l k (Suc (2*i)), A, B) = (Xseq \<mu> l k (Suc (Suc (2*i))), Yseq \<mu> l k (Suc (Suc (2*i))), A',B')"
    by (meson "nt" Suc_double_not_eq_double do_next_state evenE)
  have "Xseq \<mu> l k (Suc (Suc (2*i))) \<subset> Xseq \<mu> l k (Suc (2*i))"
    apply (intro next_state_smaller [OF \<open>\<mu>>0\<close> \<open>Colours l k\<close> 2])
     apply (simp add: finite_Xseq)
    by (simp add: "nt")
  then have "card (Xseq \<mu> l k (Suc (Suc (Suc (2*i))))) < card (Xseq \<mu> l k (Suc (2*i)))"
    by (smt (verit, best) Xseq_Suc_subset card_seteq order.trans finite_Xseq leD not_le)
  moreover have "card (Xseq \<mu> l k (Suc (2*i))) + i \<le> card X0"
    using Suc dreg_before_step step_before_dreg by force
  ultimately show ?case by auto
qed

lemma Step_class_halted_nonempty:
  assumes "\<mu>>0" "Colours l k"
  shows "Step_class \<mu> l k {halted} \<noteq> {}"
proof -
  define i where "i \<equiv> Suc (2 * Suc (card X0))" 
  have "odd i"
    by (auto simp: i_def)
  then have "i \<notin> Step_class \<mu> l k {dreg_step}"
    using step_even by blast
  moreover have "i \<notin> Step_class \<mu> l k {red_step,bblue_step,dboost_step}"
    unfolding i_def using step_bound [OF assms] le_add2 not_less_eq_eq by blast
  ultimately have "i \<in> Step_class \<mu> l k {halted}"
    using \<open>odd i\<close> not_halted_odd_RBS by blast
  then show ?thesis
    by blast
qed

definition "halted_point \<equiv> \<lambda>\<mu> l k. Inf (Step_class \<mu> l k {halted})"

lemma halted_point_halted:
  assumes "\<mu>>0" "Colours l k"
  shows "halted_point \<mu> l k \<in> Step_class \<mu> l k {halted}"
  using Step_class_halted_nonempty [OF assms] Inf_nat_def1 
  by (auto simp: halted_point_def)

lemma halted_point_minimal:
  assumes "\<mu>>0" "Colours l k"
  shows "i \<notin> Step_class \<mu> l k {halted} \<longleftrightarrow> i < halted_point \<mu> l k"
  using Step_class_halted_nonempty [OF assms] 
  by (metis wellorder_Inf_le1 Inf_nat_def1 Step_class_not_halted halted_point_def less_le_not_le nle_le) 

lemma halted_eq_Compl:
  "Step_class \<mu> l k {dreg_step,red_step,bblue_step,dboost_step} = - Step_class \<mu> l k {halted}"
  using Step_class_UNIV [of \<mu> l k] by (auto simp: Step_class_def)

lemma before_halted_eq:
  assumes "\<mu>>0" "Colours l k"
  shows "{..<halted_point \<mu> l k} = Step_class \<mu> l k {dreg_step,red_step,bblue_step,dboost_step}"
  using halted_point_minimal [OF assms] by (force simp add: halted_eq_Compl)

lemma halted_stepper_add_eq:
  assumes "\<mu>>0" "Colours l k"
  shows "stepper \<mu> l k (halted_point \<mu> l k + i) = stepper \<mu> l k (halted_point \<mu> l k)"
proof (induction i)
  case 0
  then show ?case
    by auto
next
  case (Suc i)
  have hlt: "stepper_kind \<mu> l k (halted_point \<mu> l k) = halted"
    using Step_class_def assms halted_point_halted by force
  obtain X Y A B where *: "stepper \<mu> l k (halted_point \<mu> l k) = (X, Y, A, B)"
    by (metis surj_pair)
  with hlt have "termination_condition l k X Y"
    by (simp add: stepper_kind_def next_state_kind_def split: if_split_asm)
  with * show ?case
    by (simp add: Suc)
qed

lemma halted_stepper_eq:
  assumes \<section>: "\<mu>>0" "Colours l k" and i: "i \<ge> halted_point \<mu> l k"
  shows "stepper \<mu> l k i = stepper \<mu> l k (halted_point \<mu> l k)"
  by (metis le_iff_add halted_stepper_add_eq[OF \<section>] i)

lemma below_halted_point_nontermination:
  assumes "i < halted_point \<mu> l k" "\<mu>>0" "Colours l k"
  shows  "\<not> termination_condition l k (Xseq \<mu> l k i) (Yseq \<mu> l k i)"
  by (simp add: assms halted_point_minimal not_termination_condition)

lemma below_halted_point_cardX:
  assumes "i < halted_point \<mu> l k" "\<mu>>0" "Colours l k"
  shows  "card (Xseq \<mu> l k i) > 0"
  using Xseq_gt_0 assms halted_point_minimal halted_stepper_eq
  by blast

lemma halted_point_nonzero:
  assumes "\<mu>>0" "Colours l k"
  shows  "halted_point \<mu> l k > 0"
proof -
  have "stepper_kind \<mu> l k 0 \<noteq> halted"
    using assms by (simp add: stepper_kind_def Colours_def)
  with halted_point_minimal [OF assms] show ?thesis
    by (simp add: Step_class_def)
qed

end
                                               
end
