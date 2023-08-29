chapter \<open>Euler's Polyhedron Formula\<close>

text \<open>One of the Famous 100 Theorems, ported from HOL Light\<close>
text\<open> Formalization of Jim Lawrence's proof of Euler's relation.                \<close>

theory Euler_Formula
  imports "HOL-Analysis.Analysis" "Inclusion_Exclusion" "HOL-ex.Sketch_and_Explore"
begin


text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Interpret which "side" of a hyperplane a point is on.                     \<close>
text\<open> ------------------------------------------------------------------------- \<close>

definition hyperplane_side
  where "hyperplane_side \<equiv> \<lambda>(a,b). \<lambda>x. sgn (a \<bullet> x - b)"

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Equivalence relation imposed by a hyperplane arrangement.                 \<close>
text\<open> ------------------------------------------------------------------------- \<close>

definition hyperplane_equiv
 where "hyperplane_equiv \<equiv> \<lambda>A x y. \<forall>h \<in> A. hyperplane_side h x = hyperplane_side h y"

lemma hyperplane_equiv_refl [iff]: "hyperplane_equiv A x x"
  by (simp add: hyperplane_equiv_def)

lemma hyperplane_equiv_sym:
   "hyperplane_equiv A x y \<longleftrightarrow> hyperplane_equiv A y x"
  by (auto simp: hyperplane_equiv_def)

lemma hyperplane_equiv_trans:
   "\<lbrakk>hyperplane_equiv A x y; hyperplane_equiv A y z\<rbrakk> \<Longrightarrow> hyperplane_equiv A x z"
  by (auto simp: hyperplane_equiv_def)

lemma hyperplane_equiv_Un:
   "hyperplane_equiv (A \<union> B) x y \<longleftrightarrow> hyperplane_equiv A x y \<and> hyperplane_equiv B x y"
  by (meson Un_iff hyperplane_equiv_def)

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Cells of a hyperplane arrangement.                                        \<close>
text\<open> ------------------------------------------------------------------------- \<close>

definition hyperplane_cell :: "('a::real_inner \<times> real) set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "hyperplane_cell \<equiv> \<lambda>A C. \<exists>x. C = Collect (hyperplane_equiv A x)"

lemma hyperplane_cell: "hyperplane_cell A C \<longleftrightarrow> (\<exists>x. C = {y. hyperplane_equiv A x y})"
  by (simp add: hyperplane_cell_def)

lemma not_hyperplane_cell_empty [simp]: "\<not> hyperplane_cell A {}"
  using hyperplane_cell by auto

lemma nonempty_hyperplane_cell: "hyperplane_cell A C \<Longrightarrow> (C \<noteq> {})"
  by auto

lemma Union_hyperplane_cells: "\<Union> {C. hyperplane_cell A C} = UNIV"
  using hyperplane_cell by blast

lemma disjoint_hyperplane_cells:
   "\<lbrakk>hyperplane_cell A C1; hyperplane_cell A C2; C1 \<noteq> C2\<rbrakk> \<Longrightarrow> disjnt C1 C2"
  by (force simp add: hyperplane_cell_def disjnt_iff hyperplane_equiv_def)

lemma disjoint_hyperplane_cells_eq:
   "\<lbrakk>hyperplane_cell A C1; hyperplane_cell A C2\<rbrakk> \<Longrightarrow> (disjnt C1 C2 \<longleftrightarrow> (C1 \<noteq> C2))"
  using disjoint_hyperplane_cells by auto

lemma hyperplane_cell_empty [iff]: "hyperplane_cell {} C \<longleftrightarrow> C = UNIV"
  by (simp add: hyperplane_cell hyperplane_equiv_def)

lemma hyperplane_cell_singleton_cases:
  assumes "hyperplane_cell {(a,b)} C"
  shows "C = {x. a \<bullet> x = b} \<or> C = {x. a \<bullet> x < b} \<or> C = {x. a \<bullet> x > b}"
proof -
  obtain x where x: "C = {y. hyperplane_side (a, b) x = hyperplane_side (a, b) y}"
    using assms by (auto simp add: hyperplane_equiv_def hyperplane_cell)
  then show ?thesis
    by (auto simp: hyperplane_side_def sgn_if split: if_split_asm)
qed

lemma hyperplane_cell_singleton:
   "hyperplane_cell {(a,b)} C \<longleftrightarrow>
    (if a = 0 then C = UNIV else C = {x. a \<bullet> x = b} \<or> C = {x. a \<bullet> x < b} \<or> C = {x. a \<bullet> x > b})"
  apply (simp add: hyperplane_cell_def hyperplane_equiv_def hyperplane_side_def sgn_if split: if_split_asm)
  by (smt (verit) Collect_cong gt_ex hyperplane_eq_Ex lt_ex)

lemma hyperplane_cell_Un:
   "hyperplane_cell (A \<union> B) C \<longleftrightarrow>
        C \<noteq> {} \<and>
        (\<exists>C1 C2. hyperplane_cell A C1 \<and> hyperplane_cell B C2 \<and> C = C1 \<inter> C2)"
  by (auto simp add: hyperplane_cell hyperplane_equiv_def)

lemma finite_hyperplane_cells:
   "finite A \<Longrightarrow> finite {C. hyperplane_cell A C}"
proof (induction rule: finite_induct)
  case (insert p A)
  obtain a b where peq: "p = (a,b)"
    by fastforce
  have "Collect (hyperplane_cell {p}) \<subseteq> {{x. a \<bullet> x = b},{x. a \<bullet> x < b},{x. a \<bullet> x > b}}"
    using hyperplane_cell_singleton_cases
    by (auto simp: peq)
  then have *: "finite (Collect (hyperplane_cell {p}))"
    by (simp add: finite_subset)
  define \<C> where "\<C> \<equiv> (\<Union>C1 \<in> {C. hyperplane_cell A C}.  \<Union>C2 \<in> {C. hyperplane_cell {p} C}. {C1 \<inter> C2})"
  have "{a. hyperplane_cell (insert p A) a} \<subseteq>  \<C>"
    using hyperplane_cell_Un [of "{p}" A] by (auto simp: \<C>_def)
  moreover have "finite \<C>"
    using * \<C>_def insert.IH by blast
  ultimately show ?case
    using finite_subset by blast
qed auto

lemma finite_restrict_hyperplane_cells:
   "finite A \<Longrightarrow> finite {C. hyperplane_cell A C \<and> P C}"
  by (simp add: finite_hyperplane_cells)

lemma finite_set_of_hyperplane_cells:
   "\<lbrakk>finite A; \<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C\<rbrakk> \<Longrightarrow> finite \<C>"
  by (metis finite_hyperplane_cells finite_subset mem_Collect_eq subsetI)

lemma pairwise_disjoint_hyperplane_cells:
   "(\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C) \<Longrightarrow> pairwise disjnt \<C>"
  by (metis disjoint_hyperplane_cells pairwiseI)

lemma hyperplane_cell_Int_open_affine:
  assumes "finite A" "hyperplane_cell A C"
  obtains S T where "open S" "affine T" "C = S \<inter> T"
  using assms
proof (induction arbitrary: thesis C rule: finite_induct)
  case empty
  then show ?case
    by auto 
next
  case (insert p A thesis C')
  obtain a b where peq: "p = (a,b)"
    by fastforce
  obtain C C1 where C1: "hyperplane_cell {(a,b)} C1" and C: "hyperplane_cell A C" 
              and "C' \<noteq> {}" and C': "C' = C1 \<inter> C"
    by (metis hyperplane_cell_Un insert.prems(2) insert_is_Un peq)
  then obtain S T where ST: "open S" "affine T" "C = S \<inter> T"
    by (meson insert.IH)
  show ?case
  proof (cases "a=0")
    case True
    with insert.prems show ?thesis
      by (metis C1 Int_commute ST \<open>C' = C1 \<inter> C\<close> hyperplane_cell_singleton inf_top.right_neutral) 
  next
    case False
    then consider "C1 = {x. a \<bullet> x = b}" | "C1 = {x. a \<bullet> x < b}" | "C1 = {x. b < a \<bullet> x}"
      by (metis C1 hyperplane_cell_singleton)
    then show ?thesis
    proof cases
      case 1
      then show thesis
        by (metis C' ST affine_Int affine_hyperplane inf_left_commute insert.prems(1))
    next
      case 2
      with ST show thesis
          by (metis Int_assoc C' insert.prems(1) open_Int open_halfspace_lt)
    next
      case 3
      with ST show thesis
        by (metis Int_assoc C' insert.prems(1) open_Int open_halfspace_gt)
    qed
  qed
qed

lemma hyperplane_cell_relatively_open:
  assumes "finite A" "hyperplane_cell A C"
  shows "openin (subtopology euclidean (affine hull C)) C"
proof -
  obtain S T where "open S" "affine T" "C = S \<inter> T"
    by (meson assms hyperplane_cell_Int_open_affine)
  show ?thesis
  proof (cases "S \<inter> T = {}")
    case True
    then show ?thesis
      by (simp add: \<open>C = S \<inter> T\<close>)
  next
    case False
    then have "affine hull (S \<inter> T) = T"
      by (metis \<open>affine T\<close> \<open>open S\<close> affine_hull_affine_Int_open hull_same inf_commute)
    then show ?thesis
      using \<open>C = S \<inter> T\<close> \<open>open S\<close> openin_subtopology by fastforce
  qed
qed

lemma hyperplane_cell_relative_interior:
   "\<lbrakk>finite A; hyperplane_cell A C\<rbrakk> \<Longrightarrow> rel_interior C = C"
  by (simp add: hyperplane_cell_relatively_open rel_interior_openin)

lemma hyperplane_cell_convex:
  assumes "hyperplane_cell A C"
  shows "convex C"
proof -
  obtain c where c: "C = {y. hyperplane_equiv A c y}"
    by (meson assms hyperplane_cell)
  have "convex (\<Inter>h\<in>A. {y. hyperplane_side h c = hyperplane_side h y})"
  proof (rule convex_INT)
    fix h :: "'a \<times> real"
    assume "h \<in> A"
    obtain a b where heq: "h = (a,b)"
      by fastforce
    have [simp]: "{y. \<not> a \<bullet> c < a \<bullet> y \<and> a \<bullet> y = a \<bullet> c} = {y. a \<bullet> y = a \<bullet> c}"
                 "{y. \<not> b < a \<bullet> y \<and> a \<bullet> y \<noteq> b} = {y. b > a \<bullet> y}"
      by auto
    then show "convex {y. hyperplane_side h c = hyperplane_side h y}"
      by (fastforce simp add: heq hyperplane_side_def sgn_if convex_halfspace_gt convex_halfspace_lt convex_hyperplane cong: conj_cong)
  qed
  with c show ?thesis
    by (simp add: hyperplane_equiv_def INTER_eq)
qed

lemma hyperplane_cell_Inter:
  assumes "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C"
    and "\<C> \<noteq> {}" and INT: "\<Inter>\<C> \<noteq> {}"
  shows "hyperplane_cell A (\<Inter>\<C>)"
proof -
  have "\<Inter>\<C> = {y. hyperplane_equiv A z y}" 
    if "z \<in> \<Inter>\<C>" for z
      using assms that by (force simp add: hyperplane_cell hyperplane_equiv_def)
  with INT hyperplane_cell show ?thesis
    by fastforce
qed


lemma hyperplane_cell_Int:
   "\<lbrakk>hyperplane_cell A S; hyperplane_cell A T; S \<inter> T \<noteq> {}\<rbrakk> \<Longrightarrow> hyperplane_cell A (S \<inter> T)"
  by (metis hyperplane_cell_Un sup.idem)

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> A cell complex is considered to be a union of such cells.                 \<close>
text\<open> ------------------------------------------------------------------------- \<close>

definition hyperplane_cellcomplex 
  where "hyperplane_cellcomplex A S \<equiv>
        \<exists>\<T>. (\<forall>C \<in> \<T>. hyperplane_cell A C) \<and> S = \<Union>\<T>"

lemma hyperplane_cellcomplex_empty [simp]: "hyperplane_cellcomplex A {}"
  using hyperplane_cellcomplex_def by auto

lemma hyperplane_cell_cellcomplex:
   "hyperplane_cell A C \<Longrightarrow> hyperplane_cellcomplex A C"
  by (auto simp: hyperplane_cellcomplex_def)

lemma hyperplane_cellcomplex_Union:
  assumes "\<And>S. S \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A S"
  shows "hyperplane_cellcomplex A (\<Union> \<C>)"
proof -
  obtain \<F> where \<F>: "\<And>S. S \<in> \<C> \<Longrightarrow> (\<forall>C \<in> \<F> S. hyperplane_cell A C) \<and> S = \<Union>(\<F> S)"
    by (metis assms hyperplane_cellcomplex_def)
  show ?thesis
    unfolding hyperplane_cellcomplex_def
    using \<F> by (fastforce intro: exI [where x="\<Union> (\<F> ` \<C>)"])
qed

lemma hyperplane_cellcomplex_Un:
   "\<lbrakk>hyperplane_cellcomplex A S; hyperplane_cellcomplex A T\<rbrakk>
        \<Longrightarrow> hyperplane_cellcomplex A (S \<union> T)"
  by (smt (verit) Un_iff Union_Un_distrib hyperplane_cellcomplex_def)

lemma hyperplane_cellcomplex_UNIV [simp]: "hyperplane_cellcomplex A UNIV"
  by (metis Union_hyperplane_cells hyperplane_cellcomplex_def mem_Collect_eq)

lemma hyperplane_cellcomplex_Inter:
  assumes "\<And>S. S \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A S"
  shows "hyperplane_cellcomplex A (\<Inter>\<C>)"
proof (cases "\<C> = {}")
  case True
  then show ?thesis
    by simp
next
  case False
  obtain \<F> where \<F>: "\<And>S. S \<in> \<C> \<Longrightarrow> (\<forall>C \<in> \<F> S. hyperplane_cell A C) \<and> S = \<Union>(\<F> S)"
    by (metis assms hyperplane_cellcomplex_def)
  have *: "\<C> = (\<lambda>S. \<Union>(\<F> S)) ` \<C>"
    using \<F> by force
  define U where "U \<equiv> \<Union> {T \<in> {\<Inter> (g ` \<C>) |g. \<forall>S\<in>\<C>. g S \<in> \<F> S}. T \<noteq> {}}"
  have "\<Inter>\<C> = \<Union>{\<Inter> (g ` \<C>) |g. \<forall>S\<in>\<C>. g S \<in> \<F> S}"
    using False \<F> unfolding Inter_over_Union [symmetric]
    by blast
  also have "... = U"
    unfolding U_def
    by blast
  finally have "\<Inter>\<C> = U" .
  have "hyperplane_cellcomplex A U"
    using False \<F> unfolding U_def
    apply (intro hyperplane_cellcomplex_Union hyperplane_cell_cellcomplex)
    by (auto simp: intro!: hyperplane_cell_Inter)
  then show ?thesis
     by (simp add: \<open>\<Inter> \<C> = U\<close>)
qed

lemma hyperplane_cellcomplex_Int:
   "\<lbrakk>hyperplane_cellcomplex A S; hyperplane_cellcomplex A T\<rbrakk>
        \<Longrightarrow> hyperplane_cellcomplex A (S \<inter> T)"
  using hyperplane_cellcomplex_Inter [of "{S,T}"] by force

lemma hyperplane_cellcomplex_Compl:
  assumes "hyperplane_cellcomplex A S"
  shows "hyperplane_cellcomplex A (- S)"
proof -
  obtain \<C> where \<C>: "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C" and "S = \<Union>\<C>"
    by (meson assms hyperplane_cellcomplex_def)
  have "hyperplane_cellcomplex A (\<Inter>T \<in> \<C>. -T)"
  proof (intro hyperplane_cellcomplex_Inter)
    fix C0
    assume "C0 \<in> uminus ` \<C>"
    then obtain C where C: "C0 = -C" "C \<in> \<C>"
      by auto
    have *: "-C = \<Union> {D. hyperplane_cell A D \<and> D \<noteq> C}"  (is "_ = ?rhs")
    proof
      show "- C \<subseteq> ?rhs"
        using hyperplane_cell by blast
      show "?rhs \<subseteq> - C"
        by clarify (meson \<open>C \<in> \<C>\<close> \<C> disjnt_iff disjoint_hyperplane_cells)
    qed
    then show "hyperplane_cellcomplex A C0"
      by (metis (no_types, lifting) C(1) hyperplane_cell_cellcomplex hyperplane_cellcomplex_Union mem_Collect_eq)
  qed
  then show ?thesis
    by (simp add: \<open>S = \<Union> \<C>\<close> uminus_Sup)
qed

lemma hyperplane_cellcomplex_diff:
   "\<lbrakk>hyperplane_cellcomplex A S; hyperplane_cellcomplex A T\<rbrakk>
        \<Longrightarrow> hyperplane_cellcomplex A (S - T)"
  using hyperplane_cellcomplex_Inter [of "{S,-T}"] 
  by (force simp add: Diff_eq hyperplane_cellcomplex_Compl)

lemma hyperplane_cellcomplex_mono:
  assumes "hyperplane_cellcomplex A S" "A \<subseteq> B"
  shows "hyperplane_cellcomplex B S"
proof -
  obtain \<C> where \<C>: "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C" and eq: "S = \<Union>\<C>"
    by (meson assms hyperplane_cellcomplex_def)
  show ?thesis
    unfolding eq
  proof (intro hyperplane_cellcomplex_Union)
    fix C
    assume "C \<in> \<C>"
    have "\<And>x. x \<in> C \<Longrightarrow> \<exists>D'. (\<exists>D. D' = D \<inter> C \<and> hyperplane_cell (B - A) D \<and> D \<inter> C \<noteq> {}) \<and> x \<in> D'"
      unfolding hyperplane_cell_def by blast
    then
    have "hyperplane_cellcomplex (A \<union> (B - A)) C"
      unfolding hyperplane_cellcomplex_def hyperplane_cell_Un
      using \<C> \<open>C \<in> \<C>\<close> by (fastforce intro!: exI [where x=" {D \<inter> C |D. hyperplane_cell (B - A) D \<and> D \<inter> C \<noteq> {}}"])
    moreover have "B = A \<union> (B - A)"
      using \<open>A \<subseteq> B\<close> by auto
    ultimately show "hyperplane_cellcomplex B C" by simp
  qed
qed

lemma finite_hyperplane_cellcomplexes:
  assumes "finite A"
  shows "finite {C. hyperplane_cellcomplex A C}"
proof -
  have "{C. hyperplane_cellcomplex A C} \<subseteq> image \<Union> {T. T \<subseteq> {C. hyperplane_cell A C}}"
    by (force simp add: hyperplane_cellcomplex_def subset_eq)
  with finite_hyperplane_cells show ?thesis
    by (metis assms finite_Collect_subsets finite_surj)
qed

lemma finite_restrict_hyperplane_cellcomplexes:
   "finite A \<Longrightarrow> finite {C. hyperplane_cellcomplex A C \<and> P C}"
  by (simp add: finite_hyperplane_cellcomplexes)

lemma finite_set_of_hyperplane_cellcomplex:
  assumes "finite A" "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A C"
  shows "finite \<C>"
  by (metis assms finite_hyperplane_cellcomplexes mem_Collect_eq rev_finite_subset subsetI)

lemma cell_subset_cellcomplex:
   "\<lbrakk>hyperplane_cell A C; hyperplane_cellcomplex A S\<rbrakk> \<Longrightarrow> C \<subseteq> S \<longleftrightarrow> ~ disjnt C S"
  by (smt (verit) Union_iff disjnt_iff disjnt_subset1 disjoint_hyperplane_cells_eq hyperplane_cellcomplex_def subsetI)

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Euler characteristic.                                                     \<close>
text\<open> ------------------------------------------------------------------------- \<close>

definition Euler_characteristic :: "('a::euclidean_space \<times> real) set \<Rightarrow> 'a set \<Rightarrow> real"
  where "Euler_characteristic A S \<equiv>
        sum (\<lambda>C. (-1) ^ (nat(aff_dim C))) {C. hyperplane_cell A C \<and> C \<subseteq> S}"

lemma Euler_characteristic_empty [simp]: "Euler_characteristic A {} = 0"
  by (simp add: sum.neutral Euler_characteristic_def)

lemma Euler_characteristic_cell_Union:
  assumes "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C"
  shows "Euler_characteristic A (\<Union> \<C>) = sum (\<lambda>C. (-1) ^ (nat(aff_dim C))) \<C>"
proof -
  have "\<And>x. \<lbrakk>hyperplane_cell A x; x \<subseteq> \<Union> \<C>\<rbrakk> \<Longrightarrow> x \<in> \<C>"
    by (metis assms disjnt_Union1 disjnt_subset1 disjoint_hyperplane_cells_eq)
  then have "{C. hyperplane_cell A C \<and> C \<subseteq> \<Union> \<C>} = \<C>"
    by (auto simp add: assms)
  then show ?thesis
    by (auto simp: Euler_characteristic_def)
qed

lemma Euler_characteristic_cell:
   "hyperplane_cell A C
         \<Longrightarrow> Euler_characteristic A C =  (-1) ^ (nat(aff_dim C))"
  using Euler_characteristic_cell_Union [of "{C}"] by force

lemma Euler_characteristic_cellcomplex_Un:
  assumes "finite A" "hyperplane_cellcomplex A S" 
    and AT: "hyperplane_cellcomplex A T" and "disjnt S T"
  shows "Euler_characteristic A (S \<union> T) =
         Euler_characteristic A S + Euler_characteristic A T"
proof -
  have *: "{C. hyperplane_cell A C \<and> C \<subseteq> S \<union> T} =
        {C. hyperplane_cell A C \<and> C \<subseteq> S} \<union> {C. hyperplane_cell A C \<and> C \<subseteq> T}"
    using cell_subset_cellcomplex [OF _ AT] by (auto simp: disjnt_iff)
  have **: "{C. hyperplane_cell A C \<and> C \<subseteq> S} \<inter> {C. hyperplane_cell A C \<and> C \<subseteq> T} = {}"
    using assms cell_subset_cellcomplex disjnt_subset1 by fastforce
  show ?thesis
  unfolding Euler_characteristic_def
    by (simp add: finite_restrict_hyperplane_cells assms * ** flip: sum.union_disjoint)
qed

lemma Euler_characteristic_cellcomplex_Union:
  assumes "finite A" 
    and \<C>: "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A C" "pairwise disjnt \<C>"
  shows "Euler_characteristic A (\<Union> \<C>) = sum (Euler_characteristic A) \<C>"
proof -
  have "finite \<C>"
    using assms finite_set_of_hyperplane_cellcomplex by blast
  then show ?thesis
    using \<C>
  proof (induction rule: finite_induct)
    case empty
    then show ?case
      by auto
  next
    case (insert C \<C>)
    then obtain "disjoint \<C>" "disjnt C (\<Union> \<C>)"
      by (metis disjnt_Union2 pairwise_insert)
    with insert show ?case
      by (simp add: Euler_characteristic_cellcomplex_Un hyperplane_cellcomplex_Union \<open>finite A\<close>)
  qed
qed

lemma Euler_characteristic:
  fixes A :: "('n::euclidean_space * real) set"
  assumes "finite A"
  shows "Euler_characteristic A S =
        (\<Sum>d = 0..DIM('n). (-1) ^ d * real (card {C. hyperplane_cell A C \<and> C \<subseteq> S \<and> aff_dim C = int d}))"
        (is "_ = ?rhs")
proof -
  have "\<And>T. \<lbrakk>hyperplane_cell A T; T \<subseteq> S\<rbrakk> \<Longrightarrow> aff_dim T \<in> {0..DIM('n)}"
    by (metis atLeastAtMost_iff nle_le order.strict_iff_not aff_dim_negative_iff 
        nonempty_hyperplane_cell aff_dim_le_DIM)
  then have *: "aff_dim ` {C. hyperplane_cell A C \<and> C \<subseteq> S} \<subseteq> int ` {0..DIM('n)}"
    by (auto simp: image_int_atLeastAtMost)
  have "Euler_characteristic A  S = (\<Sum>y\<in>int ` {0..DIM('n)}.
       \<Sum>C\<in>{x. hyperplane_cell A x \<and> x \<subseteq> S \<and> aff_dim x = y}. (- 1) ^ nat y) "
    using sum.group [of "{C. hyperplane_cell A C \<and> C \<subseteq> S}" "int ` {0..DIM('n)}" aff_dim "\<lambda>C. (-1::real) ^ nat(aff_dim C)", symmetric]
    by (simp add: assms Euler_characteristic_def finite_restrict_hyperplane_cells *)
  also have "... = ?rhs"
    by (simp add: sum.reindex mult_of_nat_commute)
  finally show ?thesis .
qed

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Show that the characteristic is invariant w.r.t. hyperplane arrangement.  \<close>
text\<open> ------------------------------------------------------------------------- \<close>

lemma hyperplane_cells_distinct_lemma:
   "{x. a \<bullet> x = b} \<inter> {x. a \<bullet> x < b} = {} \<and>
         {x. a \<bullet> x = b} \<inter> {x. a \<bullet> x > b} = {} \<and>
         {x. a \<bullet> x < b} \<inter> {x. a \<bullet> x = b} = {} \<and>
         {x. a \<bullet> x < b} \<inter> {x. a \<bullet> x > b} = {} \<and>
         {x. a \<bullet> x > b} \<inter> {x. a \<bullet> x = b} = {} \<and>
         {x. a \<bullet> x > b} \<inter> {x. a \<bullet> x < b} = {}"
  by auto

proposition Euler_characterstic_lemma:
  assumes "finite A" and "hyperplane_cellcomplex A S"
  shows "Euler_characteristic (insert h A) S = Euler_characteristic A S"
proof -
  obtain \<C> where \<C>: "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C" and "S = \<Union>\<C>"
              and "pairwise disjnt \<C>"
    by (meson assms hyperplane_cellcomplex_def pairwise_disjoint_hyperplane_cells)
  obtain a b where "h = (a,b)"
    by fastforce
  have "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cellcomplex A C \<and> hyperplane_cellcomplex (insert (a,b) A) C"
    by (meson \<C> hyperplane_cell_cellcomplex hyperplane_cellcomplex_mono subset_insertI)
  moreover
  have "sum (Euler_characteristic (insert (a,b) A)) \<C> = sum (Euler_characteristic A) \<C>"
  proof (rule sum.cong [OF refl])
    fix C
    assume "C \<in> \<C>"
    have "Euler_characteristic (insert (a, b) A) C = (-1) ^ nat(aff_dim C)"
    proof (cases "hyperplane_cell (insert (a,b) A) C")
      case True
      then show ?thesis
        using Euler_characteristic_cell by blast
    next
      case False
      with \<C>[OF \<open>C \<in> \<C>\<close>] have "a \<noteq> 0"
        by (smt (verit, ccfv_threshold) hyperplane_cell_Un hyperplane_cell_empty hyperplane_cell_singleton insert_is_Un sup_bot_left)
      have "convex C"
        using \<open>hyperplane_cell A C\<close> hyperplane_cell_convex by blast
      define r where "r \<equiv> (\<Sum>D\<in>{C' \<inter> C |C'. hyperplane_cell {(a, b)} C' \<and> C' \<inter> C \<noteq> {}}. (-1::real) ^ nat (aff_dim D))"
      have "Euler_characteristic (insert (a, b) A) C 
           = (\<Sum>D | (D \<noteq> {} \<and>
                     (\<exists>C1 C2. hyperplane_cell {(a, b)} C1 \<and> hyperplane_cell A C2 \<and> D = C1 \<inter> C2)) \<and> D \<subseteq> C.
              (- 1) ^ nat (aff_dim D))"
        unfolding r_def Euler_characteristic_def insert_is_Un [of _ A] hyperplane_cell_Un ..
      also have "\<dots> = r"
        unfolding r_def
        apply (rule sum.cong [OF _ refl])
        using \<open>hyperplane_cell A C\<close> disjoint_hyperplane_cells disjnt_iff
        by (smt (verit, ccfv_SIG) Collect_cong Int_iff disjoint_iff subsetD subsetI)
      also have "... = (-1) ^ nat(aff_dim C)"
      proof -
        have "C \<noteq> {}"
          using \<open>hyperplane_cell A C\<close> by auto
        show ?thesis
        proof (cases "C \<subseteq> {x. a \<bullet> x < b} \<or> C \<subseteq> {x. a \<bullet> x > b} \<or> C \<subseteq> {x. a \<bullet> x = b}")
          case Csub: True
          with \<open>C \<noteq> {}\<close> have "r = sum (\<lambda>c. (-1) ^ nat (aff_dim c)) {C}"
            unfolding r_def
            apply (intro sum.cong [OF _ refl])
            by (auto simp add: \<open>a \<noteq> 0\<close> hyperplane_cell_singleton)
          also have "... = (-1) ^ nat(aff_dim C)"
            by simp
          finally show ?thesis .
        next
          case False
          then obtain u v where uv: "u \<in> C" "\<not> a \<bullet> u < b" "v \<in> C" "\<not> a \<bullet> v > b"
            by blast
          have CInt_ne: "C \<inter> {x. a \<bullet> x = b} \<noteq> {}"
          proof (cases "a \<bullet> u = b \<or> a \<bullet> v = b")
            case True
            with uv show ?thesis
              by blast
          next
            case False
            have "a \<bullet> v < a \<bullet> u"
              using False uv by auto
            define w where "w \<equiv> v + ((b - a \<bullet> v) / (a \<bullet> u - a \<bullet> v)) *\<^sub>R (u - v)"
            have **: "v + a *\<^sub>R (u - v) = (1 - a) *\<^sub>R v + a *\<^sub>R u" for a
              by (simp add: algebra_simps)
            have "w \<in> C"
              unfolding w_def **
            proof (intro convexD_alt)
            qed (use \<open>a \<bullet> v < a \<bullet> u\<close> \<open>convex C\<close> uv in auto)
            moreover have "w \<in> {x. a \<bullet> x = b}"
              using \<open>a \<bullet> v < a \<bullet> u\<close> by (simp add: w_def inner_add_right inner_diff_right)
            ultimately show ?thesis
              by blast
          qed
          have Cab: "C \<inter> {x. a \<bullet> x < b} \<noteq> {} \<and> C \<inter> {x. b < a \<bullet> x} \<noteq> {}"
          proof -
            obtain u v where "u \<in> C" "a \<bullet> u = b" "v \<in> C" "a \<bullet> v \<noteq> b" "u\<noteq>v"
              using False \<open>C \<inter> {x. a \<bullet> x = b} \<noteq> {}\<close> by blast
            have "openin (subtopology euclidean (affine hull C)) C"
              using \<open>hyperplane_cell A C\<close> \<open>finite A\<close> hyperplane_cell_relatively_open by blast
            then obtain \<epsilon> where "0 < \<epsilon>"
                  and \<epsilon>: "\<And>x'. \<lbrakk>x' \<in> affine hull C; dist x' u < \<epsilon>\<rbrakk> \<Longrightarrow> x' \<in> C"
              by (meson \<open>u \<in> C\<close> openin_euclidean_subtopology_iff)
            define \<xi> where "\<xi> \<equiv> u - (\<epsilon> / 2 / norm (v - u)) *\<^sub>R (v - u)"
            have "\<xi> \<in> C"
            proof (rule \<epsilon>)
              show "\<xi> \<in> affine hull C"
                by (simp add: \<xi>_def \<open>u \<in> C\<close> \<open>v \<in> C\<close> hull_inc mem_affine_3_minus2)
            qed (use \<xi>_def \<open>0 < \<epsilon>\<close> in force)
            consider "a \<bullet> v < b" | "a \<bullet> v > b"
              using \<open>a \<bullet> v \<noteq> b\<close> by linarith
            then show ?thesis
            proof cases
              case 1
              moreover have "\<xi> \<in> {x. b < a \<bullet> x}"
                using "1" \<open>0 < \<epsilon>\<close> \<open>a \<bullet> u = b\<close> divide_less_cancel 
                by (fastforce simp add: \<xi>_def algebra_simps)
              ultimately show ?thesis
                using \<open>v \<in> C\<close> \<open>\<xi> \<in> C\<close> by blast
            next
              case 2
              moreover have "\<xi> \<in> {x. b > a \<bullet> x}"
                using "2" \<open>0 < \<epsilon>\<close> \<open>a \<bullet> u = b\<close> divide_less_cancel 
                by (fastforce simp add: \<xi>_def algebra_simps)
              ultimately show ?thesis
                using \<open>v \<in> C\<close> \<open>\<xi> \<in> C\<close> by blast
            qed
          qed
          have "r = (\<Sum>C\<in>{{x. a \<bullet> x = b} \<inter> C, {x. b < a \<bullet> x} \<inter> C, {x. a \<bullet> x < b} \<inter> C}.
                     (- 1) ^ nat (aff_dim C))"
            unfolding r_def 
            apply (intro sum.cong [OF _ refl] equalityI)
            subgoal using \<open>a \<noteq> 0\<close> 
              by (auto simp: hyperplane_cell_singleton)
            subgoal
              apply clarsimp
              using Cab Int_commute \<open>C \<inter> {x. a \<bullet> x = b} \<noteq> {}\<close> hyperplane_cell_singleton \<open>a \<noteq> 0\<close>
              by metis
            done
          also have "... = (-1) ^ nat (aff_dim (C \<inter> {x. a \<bullet> x = b})) 
                         + (-1) ^ nat (aff_dim (C \<inter> {x. b < a \<bullet> x})) 
                         + (-1) ^ nat (aff_dim (C \<inter> {x. a \<bullet> x < b}))"
            using hyperplane_cells_distinct_lemma [of a b] Cab
            by (auto simp add: sum.insert_if Int_commute Int_left_commute)
          also have "... = (- 1) ^ nat (aff_dim C)"
          proof -
            have *: "aff_dim (C \<inter> {x. a \<bullet> x < b}) = aff_dim C \<and> aff_dim (C \<inter> {x. a \<bullet> x > b}) = aff_dim C"
              by (metis Cab open_halfspace_lt open_halfspace_gt aff_dim_affine_hull 
                        affine_hull_convex_Int_open[OF \<open>convex C\<close>])
            obtain S T where "open S" "affine T" and Ceq: "C = S \<inter> T"
              by (meson \<open>hyperplane_cell A C\<close> \<open>finite A\<close> hyperplane_cell_Int_open_affine)
            have "affine hull C = affine hull T"
              by (metis Ceq \<open>C \<noteq> {}\<close> \<open>affine T\<close> \<open>open S\<close> affine_hull_affine_Int_open inf_commute)
            moreover
            have "T \<inter> ({x. a \<bullet> x = b} \<inter> S) \<noteq> {}"
              using Ceq \<open>C \<inter> {x. a \<bullet> x = b} \<noteq> {}\<close> by blast
            then have "affine hull (C \<inter> {x. a \<bullet> x = b}) = affine hull (T \<inter> {x. a \<bullet> x = b})"
              using affine_hull_affine_Int_open[of "T \<inter> {x. a \<bullet> x = b}" S] 
              by (simp add: Ceq Int_ac \<open>affine T\<close> \<open>open S\<close> affine_Int affine_hyperplane)
            ultimately have "aff_dim (affine hull C) = aff_dim(affine hull (C \<inter> {x. a \<bullet> x = b})) + 1"
              using CInt_ne False Ceq
              by (auto simp add: aff_dim_affine_Int_hyperplane \<open>affine T\<close>)
            moreover have "0 \<le> aff_dim (C \<inter> {x. a \<bullet> x = b})"
              by (metis CInt_ne aff_dim_negative_iff linorder_not_le)
            ultimately show ?thesis
              by (simp add: * nat_add_distrib)
          qed
          finally show ?thesis .
        qed
      qed
      finally show "Euler_characteristic (insert (a, b) A) C = (-1) ^ nat(aff_dim C)" .
    qed
    then show "Euler_characteristic (insert (a, b) A) C = (Euler_characteristic A C)"
      by (simp add: Euler_characteristic_cell \<C> \<open>C \<in> \<C>\<close>)
  qed
  ultimately show ?thesis
    by (simp add: Euler_characteristic_cellcomplex_Union \<open>S = \<Union> \<C>\<close> \<open>disjoint \<C>\<close> \<open>h = (a, b)\<close> assms(1))
qed



lemma Euler_characterstic_invariant_aux:
  assumes "finite B" "finite A" "hyperplane_cellcomplex A S" 
  shows "Euler_characteristic (A \<union> B) S = Euler_characteristic A S"
  using assms
  by (induction rule: finite_induct) (auto simp add: Euler_characterstic_lemma hyperplane_cellcomplex_mono)

lemma Euler_characterstic_invariant:
  assumes "finite A" "finite B" "hyperplane_cellcomplex A S" "hyperplane_cellcomplex B S"
  shows "Euler_characteristic A S = Euler_characteristic B S"
  by (metis Euler_characterstic_invariant_aux assms sup_commute)

lemma Euler_characteristic_inclusion_exclusion:
  assumes "finite A" "finite \<S>" "\<And>K. K \<in> \<S> \<Longrightarrow> hyperplane_cellcomplex A K"
  shows "Euler_characteristic A (\<Union> \<S>) = (\<Sum>\<T> | \<T> \<subseteq> \<S> \<and> \<T> \<noteq> {}. (- 1) ^ (card \<T> + 1) * Euler_characteristic A (\<Inter>\<T>))"
proof -
  interpret Incl_Excl "hyperplane_cellcomplex A" "Euler_characteristic A"
    proof
  show "Euler_characteristic A (S \<union> T) = Euler_characteristic A S + Euler_characteristic A T"
    if "hyperplane_cellcomplex A S" and "hyperplane_cellcomplex A T" and "disjnt S T" for S T
    using that Euler_characteristic_cellcomplex_Un assms(1) by blast 
  qed (use hyperplane_cellcomplex_Int hyperplane_cellcomplex_Un hyperplane_cellcomplex_diff in auto)
  show ?thesis
    using restricted assms by blast
qed


text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Euler-type relation for full-dimensional proper polyhedral cones.         \<close>
text\<open> ------------------------------------------------------------------------- \<close>

lemma Euler_polyhedral_cone:
   "polyhedron S \<and> conic S \<and> ~(interior S = {}) \<and> (S \<noteq> UNIV)
       \<Longrightarrow> sum (0..DIM('N))
               (\<lambda>d. (-1) ^ d *
                    (card {f. f face_of S \<and> aff_dim f = d })) = 0"
oops 
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `affine hull S = UNIV` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `\<forall>S. S = UNIV \<and> S \<subseteq> t \<Longrightarrow> t = UNIV`) THEN
    EXISTS_TAC `affine hull (interior S::real^N=>bool)` THEN
    SIMP_TAC[INTERIOR_SUBSET; HULL_MONO] THEN
    MATCH_MP_TAC AFFINE_HULL_OPEN THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
    ALL_TAC] THEN
  FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE id [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
  ASM_REWRITE_TAC[INTER_UNIV; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `H:(real^N=>bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(0::real^N) \<in> S` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN
    ASM_MESON_TAC[SUBSET_EMPTY; INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `\<forall>h::real^N=>bool. h \<in> H \<Longrightarrow> \<exists>a. (a \<noteq> 0) \<and> h = {x. a \<bullet> x \<le> 0}`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `h::real^N=>bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MATCH_MP_TAC MONO_EXISTS]  THEN
    X_GEN_TAC `a::real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `b::real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `b = 0` SUBST_ALL_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(REAL_ARITH `0 \<le> b \<and> ~(0 < b) \<Longrightarrow> b = 0`) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(0::real^N) \<in> \<Inter> H` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[IN_INTERS]] THEN
      DISCH_THEN(MP_TAC o SPEC `h::real^N=>bool`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_ELIM_THM; DOT_RZERO];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `H DELETE (h::real^N=>bool)`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[PSUBSET_ALT]] THEN
      DISCH_THEN(X_CHOOSE_THEN `x::real^N` STRIP_ASSUME_TAC o CONJUNCT2) THEN
      SUBGOAL_THEN `\<exists>e. 0 < e \<and> e < 1 \<and>
                        (e *\<^sub>R x::real^N) \<in> h` STRIP_ASSUME_TAC THENL
       [EXISTS_TAC `min (1 / 2) (b / ((a::real^N) \<bullet> x))` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; DOT_RMUL] THEN
        SUBGOAL_THEN `0 < (a::real^N) \<bullet> x` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `b::real` THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `~((x::real^N) \<in> S)` THEN EXPAND_TAC "S" THEN
          ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
          REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
          SUBGOAL_THEN `H:(real^N=>bool)->bool = h insert (H - {h})`
          SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          REWRITE_TAC[INTERS_INSERT; IN_INTER] THEN
          ASM_REWRITE_TAC[IN_ELIM_THM];
          ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_MIN_LT] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN
          ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC];
        UNDISCH_TAC `~((x::real^N) \<in> S)` THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `x::real^N = inverse e *\<^sub>R e *\<^sub>R x` SUBST1_TAC THENL
         [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                       VECTOR_MUL_LID];
          ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[conic]) THEN
        FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_INV_EQ] THEN
        EXPAND_TAC "S" THEN
        SUBGOAL_THEN `H:(real^N=>bool)->bool = h insert (H - {h})`
        SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[INTERS_INSERT; IN_INTER] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(x::real^N) \<in> \<Inter> (H - {h})` THEN
        REWRITE_TAC[IN_INTERS] THEN MATCH_MP_TAC MONO_FORALL THEN
        X_GEN_TAC `k::real^N=>bool` THEN REWRITE_TAC[IN_DELETE] THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k::real^N=>bool`) THEN
        ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`a':real^N`; `b':real`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC(REAL_ARITH
         `(0 \<le> x \<Longrightarrow> y \<le> x) \<and> (0 \<le>-x \<Longrightarrow> 0 \<le>-y) \<and> 0 \<le> b
          \<Longrightarrow> x \<le> b \<Longrightarrow> y \<le> b`) THEN
        REWRITE_TAC[DOT_RMUL; GSYM REAL_MUL_RNEG] THEN
        REWRITE_TAC[REAL_ARITH `e * x \<le> x \<longleftrightarrow> 0 \<le> x * (1 - e)`] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
        SUBGOAL_THEN `(0::real^N) \<in> \<Inter> H` MP_TAC THENL
         [ASM SET_TAC[]; REWRITE_TAC[IN_INTERS]] THEN
        DISCH_THEN(MP_TAC o SPEC `k::real^N=>bool`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[IN_ELIM_THM; DOT_RZERO]]];
    FIRST_X_ASSUM(K ALL_TAC o SPEC `h::real^N=>bool`)] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `fa:(real^N=>bool)->real^N` THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o funpow 2 RAND_CONV)
   [EQ_SYM_EQ] THEN
  DISCH_TAC THEN ABBREV_TAC
   `A = image (\<lambda>h. (fa:(real^N=>bool)->real^N) h,0) H` THEN
  SUBGOAL_THEN `finite(A::real^N#real=>bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `Euler_characteristic A (S::real^N=>bool)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[EULER_CHARACTERISTIC] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `d::num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
    ASM_SIMP_TAC[FINITE_RESTRICT_HYPERPLANE_CELLS] THEN
    EXISTS_TAC `rel_interior:(real^N=>bool)->(real^N=>bool)` THEN
    EXISTS_TAC `closure:(real^N=>bool)->(real^N=>bool)` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `f::real^N=>bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `closure(rel_interior f):real^N=>bool = f`
      ASSUME_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `closure f::real^N=>bool` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CLOSURE_RELATIVE_INTERIOR THEN
          ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
          REWRITE_TAC[CLOSURE_EQ] THEN MATCH_MP_TAC FACE_OF_IMP_CLOSED THEN
          ASM_MESON_TAC[POLYHEDRON_IMP_CLOSED; POLYHEDRON_IMP_CONVEX]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ALL_TAC;
        ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
        ONCE_REWRITE_TAC[GSYM AFFINE_HULL_CLOSURE] THEN
        ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET_TRANS;
                      FACE_OF_IMP_SUBSET]] THEN
      SUBGOAL_THEN `~(f::real^N=>bool = {})` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[GSYM AFF_DIM_POS_LE; INT_POS]; ALL_TAC] THEN
      SUBGOAL_THEN
       `\<exists>J. J \<subseteq> H \<and>
            f = \<Inter> {{x. fa h \<bullet> x \<le> 0} | h \<in> H} \<inter>
                \<Inter> {{x. fa(h::real^N=>bool) \<bullet> x = 0} | h \<in> J}`
      ASSUME_TAC THENL
       [ASM_CASES_TAC `f::real^N=>bool = S` THENL
         [EXISTS_TAC `{}:(real^N=>bool)->bool` THEN
          REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY; INTERS_0; INTER_UNIV;
                      SET_RULE `{f x | x | False} = {}`] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SYM(ASSUME `\<Inter> H = (S::real^N=>bool)`)] THEN
          AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
           `(\<forall>x. x \<in> S \<Longrightarrow> f x = x) \<Longrightarrow> S = {f x | x \<in> S}`) THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        EXISTS_TAC
        `{h::real^N=>bool | h \<in> H \<and>
                     f \<subseteq> S \<inter> {x. fa h \<bullet> x = 0}}` THEN
        CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`S::real^N=>bool`; `H:(real^N=>bool)->bool`;
                       `fa:(real^N=>bool)->real^N`;
                       `\<lambda>h::real^N=>bool. 0`]
          FACE_OF_POLYHEDRON_EXPLICIT) THEN
        ASM_SIMP_TAC[INTER_UNIV] THEN
        DISCH_THEN(MP_TAC o SPEC `f::real^N=>bool`) THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `\<Inter> {{x. fa(h::real^N=>bool) \<bullet> x \<le> 0} | h \<in> H} = S`
        ASSUME_TAC THENL
         [EXPAND_TAC "S" THEN AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
           `(\<forall>x. x \<in> S \<Longrightarrow> f x = x) \<Longrightarrow> {f x | x \<in> S} = S`) THEN
          ASM_SIMP_TAC[];
         ALL_TAC] THEN
        ASM_CASES_TAC `{h::real^N=>bool | h \<in> H \<and>
                           f \<subseteq> S \<inter> {x. fa h \<bullet> x = 0}} =
                       {}`
        THENL
         [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          ASM_REWRITE_TAC[IMAGE_CLAUSES; INTERS_0] THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
          ASM SET_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
        ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC id [EXTENSION] THEN
        X_GEN_TAC `y::real^N` THEN REWRITE_TAC[IN_INTER; IN_INTERS] THEN
        REWRITE_TAC[FORALL_IN_GSPEC; IN_INTER] THEN
        ASM_CASES_TAC `(y::real^N) \<in> S` THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      ABBREV_TAC
       `H' = image (\<lambda>h::real^N=>bool. {x. --(fa h) \<bullet> x \<le> 0}) H` THEN
      SUBGOAL_THEN
       `\<exists>J. finite J \<and>
            J \<subseteq> (H \<union> H') \<and>
            f::real^N=>bool = affine hull f \<inter> \<Inter> J`
      MP_TAC THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `J:(real^N=>bool)->bool`
          STRIP_ASSUME_TAC) THEN
        EXISTS_TAC
         `H \<union> image (\<lambda>h::real^N=>bool.
             {x. --(fa h) \<bullet> x \<le> 0}) J` THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[FINITE_UNION] THEN MATCH_MP_TAC FINITE_IMAGE THEN
          ASM_MESON_TAC[FINITE_SUBSET];
          EXPAND_TAC "H'" THEN ASM SET_TAC[];
          MATCH_MP_TAC(SET_RULE `S \<subseteq> f \<and> S = t \<Longrightarrow> S = f \<inter> t`) THEN
          REWRITE_TAC[HULL_SUBSET] THEN
          FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
          REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
          REWRITE_TAC[INTERS_UNION] THEN MATCH_MP_TAC(SET_RULE
           `S = s' \<and> (\<forall>x. x \<in> S \<Longrightarrow> (x \<in> t \<longleftrightarrow> x \<in> t'))
            \<Longrightarrow> S \<inter> t = s' \<inter> t'`) THEN
          CONJ_TAC THENL
           [AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
             `(\<forall>x. x \<in> S \<Longrightarrow> f x = x) \<Longrightarrow> {f x | x \<in> S} = S`) THEN
            ASM_SIMP_TAC[];
            ALL_TAC] THEN
          X_GEN_TAC `y::real^N` THEN REWRITE_TAC[IN_INTERS] THEN
          REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
          REWRITE_TAC[IN_ELIM_THM; DOT_LNEG] THEN
          REWRITE_TAC[REAL_ARITH `-x \<le> 0 \<longleftrightarrow> 0 \<le> x`] THEN
          ASM SET_TAC[]];
        ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV
         [MESON[HAS_SIZE]
           `(\<exists>f. finite f \<and> P f) \<longleftrightarrow> (\<exists>n f. f HAS_SIZE n \<and> P f)`] THEN
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
      DISCH_THEN(X_CHOOSE_THEN `nn::num`
        (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `J:(real^N=>bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `!J'. J' \<subset> J
             \<Longrightarrow> (f::real^N=>bool) \<subset> (affine hull f \<inter> \<Inter> J')`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `card(J':(real^N=>bool)->bool)`) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[CARD_PSUBSET; HAS_SIZE]; ALL_TAC] THEN
        REWRITE_TAC[NOT_EXISTS_THM; HAS_SIZE] THEN
        DISCH_THEN(MP_TAC o SPEC `J':(real^N=>bool)->bool`) THEN
        MATCH_MP_TAC(TAUT `a \<and> b \<and> (~c \<Longrightarrow> d) \<Longrightarrow> ~(a \<and> b \<and> c) \<Longrightarrow> d`) THEN
        CONJ_TAC THENL
         [ASM_MESON_TAC[\<subset>; FINITE_SUBSET; HAS_SIZE]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE
         `S \<subseteq> t \<Longrightarrow> (S \<noteq> t) \<Longrightarrow> S \<subset> t`) THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `\<forall>h::real^N=>bool. h \<in> J
          \<Longrightarrow> \<exists>a. {x. a \<bullet> x \<le> 0} = h \<and>
                  (h \<in> H \<and> a = fa h \<or> ?h'. h' \<in> H \<and> a = --(fa h'))`
      MP_TAC THENL
       [X_GEN_TAC `h::real^N=>bool` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(h::real^N=>bool) \<in> (H \<union> H')` MP_TAC THENL
         [ASM SET_TAC[]; EXPAND_TAC "H'"] THEN
        UNDISCH_THEN `(h::real^N=>bool) \<in> J` (K ALL_TAC) THEN
        SPEC_TAC(`h::real^N=>bool`,`h::real^N=>bool`) THEN
        REWRITE_TAC[IN_UNION; TAUT `(a \<or> b \<Longrightarrow> c) \<longleftrightarrow> (a \<Longrightarrow> c) \<and> (b \<Longrightarrow> c)`;
                    FORALL_AND_THM; FORALL_IN_IMAGE] THEN
        CONJ_TAC THEN X_GEN_TAC `h::real^N=>bool` THEN DISCH_TAC THENL
         [EXISTS_TAC `(fa:(real^N=>bool)->real^N) h` THEN
          ASM_SIMP_TAC[];
          EXISTS_TAC `--((fa:(real^N=>bool)->real^N) h)` THEN
          REWRITE_TAC[] THEN DISJ2_TAC THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `ga:(real^N=>bool)->real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL
       [`f::real^N=>bool`; `J:(real^N=>bool)->bool`;
        `ga:(real^N=>bool)->real^N`; `\<lambda>h::real^N=>bool. 0`]
       RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[HAS_SIZE];
          ASM_MESON_TAC[];
          ASM_SIMP_TAC[] THEN ASM_MESON_TAC[VECTOR_NEG_EQ_0; \<subseteq>]];
        DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
      SUBGOAL_THEN
       `\<forall>h::real^N=>bool. h \<in> J \<Longrightarrow> h \<in> H \<and> ga h::real^N = fa h`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `~(rel_interior f::real^N=>bool = {})` MP_TAC THENL
         [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; FACE_OF_IMP_CONVEX];
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY]] THEN
        DISCH_THEN(X_CHOOSE_TAC `z::real^N`) THEN
        SUBGOAL_THEN `(z::real^N) \<in> f \<and> z \<in> S` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[\<subseteq>; FACE_OF_IMP_SUBSET; RELATIVE_INTERIOR_SUBSET];
          ALL_TAC] THEN
        X_GEN_TAC `h::real^N=>bool` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h::real^N=>bool`) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `h':real^N=>bool` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `(z::real^N) \<in> rel_interior f` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `h::real^N=>bool`) THEN
        ASM_REWRITE_TAC[DOT_LNEG] THEN
        UNDISCH_TAC `(z::real^N) \<in> S` THEN EXPAND_TAC "S" THEN
        REWRITE_TAC[IN_INTERS] THEN
        DISCH_THEN(MP_TAC o SPEC `h':real^N=>bool`) THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h':real^N=>bool`) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
          GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM(CONJUNCT2 th)]) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN
        MP_TAC(SYM th)) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `K:(real^N=>bool)->bool` MP_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(fun th -> ASSUME_TAC(SYM th) THEN
        GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
      REWRITE_TAC[IN_INTER; IN_INTERS; FORALL_IN_GSPEC; GSYM CONJ_ASSOC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(rel_interior f::real^N=>bool = {})` ASSUME_TAC THENL
       [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; FACE_OF_IMP_CONVEX];
        ALL_TAC] THEN
      SUBGOAL_THEN `disjnt (J:(real^N=>bool)->bool) K` ASSUME_TAC THENL
       [UNDISCH_TAC `~(rel_interior f::real^N=>bool = {})` THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
         (LAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
        REWRITE_TAC[IN_DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        ASM_MESON_TAC[REAL_LT_REFL];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `rel_interior f =
          \<Inter> {(if (h::real^N=>bool) \<in> J then {x. fa h \<bullet> x < 0}
                   else if h \<in> K then {x. fa h \<bullet> x = 0}
                   else if rel_interior f \<subseteq> {x. fa h \<bullet> x = 0}
                   then {x. fa h \<bullet> x = 0}
                   else {x. fa h \<bullet> x < 0}) | h \<in> H}`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [ALL_TAC;
          FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
          GEN_REWRITE_TAC id [\<subseteq>] THEN
          REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; AND_FORALL_THM] THEN
          X_GEN_TAC `x::real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
          MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `h::real^N=>bool` THEN
          ASM_CASES_TAC `(h::real^N=>bool) \<in> H` THENL
           [ALL_TAC; DISCH_THEN(K ALL_TAC) THEN ASM SET_TAC[]] THEN
          ASM_REWRITE_TAC[] THEN
          ASM_CASES_TAC `(h::real^N=>bool) \<in> J` THEN
          ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_LE] THENL
           [ASM SET_TAC[]; ALL_TAC] THEN
          ASM_CASES_TAC `(h::real^N=>bool) \<in> K` THEN
          ASM_SIMP_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
          COND_CASES_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
          REAL_ARITH_TAC] THEN
        GEN_REWRITE_TAC id [\<subseteq>] THEN X_GEN_TAC `x::real^N` THEN
        DISCH_TAC THEN REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC] THEN
        X_GEN_TAC `h::real^N=>bool` THEN DISCH_TAC THEN
        REPEAT(COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
        REWRITE_TAC[IN_ELIM_THM; REAL_LT_LE] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; DISCH_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE id
         [SET_RULE `~(S \<subseteq> t) \<longleftrightarrow> \<exists>y. y \<in> S \<and> (y \<notin> t)`]) THEN
        REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
        X_GEN_TAC `y::real^N` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
         `~(x::real = 0) \<Longrightarrow> ~(x \<le> 0) \<or> x < 0`))
        THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(ASSUME `(x::real^N) \<in> rel_interior f`) THEN
        REWRITE_TAC[IN_RELATIVE_INTERIOR_CBALL] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `e::real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        REWRITE_TAC[\<subseteq>; IN_INTER; IN_CBALL] THEN
        SUBGOAL_THEN `~(y::real^N = x)` ASSUME_TAC THENL
         [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o SPEC `x + e / norm(y - x) *\<^sub>R (x - y):real^N`) THEN
        SUBGOAL_THEN
         `(x::real^N) \<in> affine hull f \<and> y \<in> affine hull f`
        STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; \<subseteq>; HULL_SUBSET];
          ASM_SIMP_TAC[IN_AFFINE_ADD_MUL_DIFF; AFFINE_AFFINE_HULL]] THEN
        REWRITE_TAC[NORM_ARITH `dist (x::real^N) (x + r) = norm r`] THEN
        REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; NORM_SUB;
                       REAL_DIV_RMUL; NORM_EQ_0; VECTOR_SUB_EQ] THEN
          ASM_REAL_ARITH_TAC;
          DISCH_TAC] THEN
        SUBGOAL_THEN `(x + e / norm(y - x) *\<^sub>R (x - y):real^N) \<in> S` MP_TAC THENL
         [ASM_MESON_TAC[\<subseteq>; FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
        EXPAND_TAC "S" THEN REWRITE_TAC[IN_INTERS] THEN
        DISCH_THEN(MP_TAC o SPEC `h::real^N=>bool`) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
         [SYM(CONJUNCT2(MATCH_MP th (ASSUME `(h::real^N=>bool) \<in> H`)))]) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; DOT_RADD; REAL_ADD_LID; DOT_RMUL] THEN
        ASM_REWRITE_TAC[DOT_RSUB; REAL_SUB_LZERO; REAL_NOT_LE] THEN
        MATCH_MP_TAC REAL_LT_MUL THEN
        ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `~(rel_interior f::real^N=>bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; hyperplane_cell] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z::real^N` THEN
      GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
      ONCE_ASM_REWRITE_TAC[] THEN EXPAND_TAC "A" THEN
      REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `x::real^N` THEN MP_TAC th) THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [\<in>] THEN
      REWRITE_TAC[hyperplane_equiv; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC(MESON[]
       `(\<forall>h. P h \<Longrightarrow> (Q h \<longleftrightarrow> R h))
        \<Longrightarrow> (\<forall>h. P h) \<Longrightarrow> ((\<forall>h. Q h) \<longleftrightarrow> (\<forall>h. R h))`) THEN
      X_GEN_TAC `h::real^N=>bool` THEN
      ASM_CASES_TAC `(h::real^N=>bool) \<in> H` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[hyperplane_side; REAL_SUB_RZERO] THEN
      REPEAT(COND_CASES_TAC THEN
        SIMP_TAC[IN_ELIM_THM] THENL [MESON_TAC[REAL_SGN_EQ]; ALL_TAC]) THEN
      MESON_TAC[REAL_SGN_EQ];
      X_GEN_TAC `c::real^N=>bool` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
      REWRITE_TAC[AFFINE_HULL_CLOSURE] THEN
      ASM_REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `rel_interior c::real^N=>bool` THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR_CLOSURE THEN
          ASM_MESON_TAC[HYPERPLANE_CELL_CONVEX];
          ASM_MESON_TAC[HYPERPLANE_CELL_RELATIVE_INTERIOR]]] THEN
      SUBGOAL_THEN
       `\<exists>J. J \<subseteq> H \<and>
            c = \<Inter> {{x. (fa(h::real^N=>bool)) \<bullet> x < 0} | h \<in> J} \<inter>
                \<Inter> {{x. (fa h) \<bullet> x = 0} | h \<in> (H - J)}`
      MP_TAC THENL
       [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE id [HYPERPLANE_CELL]) THEN
        EXPAND_TAC "A" THEN REWRITE_TAC[hyperplane_equiv; FORALL_IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z::real^N` MP_TAC) THEN
        REWRITE_TAC[hyperplane_side; REAL_SUB_RZERO] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
         [EQ_SYM_EQ] THEN
        DISCH_THEN(ASSUME_TAC o SYM) THEN EXISTS_TAC
         `{h::real^N=>bool | h \<in> H \<and>
                            sgn(fa h \<bullet> (z::real^N)) =-1}` THEN
        REWRITE_TAC[SET_RULE `{x. x \<in> S \<and> P x} \<subseteq> S`] THEN
        REWRITE_TAC[GSYM INTERS_UNION] THEN EXPAND_TAC "c" THEN
        GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC `y::real^N` THEN
        REWRITE_TAC[IN_ELIM_THM; IN_INTERS] THEN REWRITE_TAC[IN_UNION] THEN
        REWRITE_TAC[TAUT `(a \<or> b \<Longrightarrow> c) \<longleftrightarrow> (a \<Longrightarrow> c) \<and> (b \<Longrightarrow> c)`;
                    FORALL_AND_THM] THEN
        REWRITE_TAC[FORALL_IN_GSPEC] THEN
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
        REWRITE_TAC[TAUT `a \<and> ~(a \<and> b) \<longleftrightarrow> a \<and> ~b`] THEN
        REWRITE_TAC[AND_FORALL_THM] THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `h::real^N=>bool` THEN
        ASM_CASES_TAC `(h::real^N=>bool) \<in> H` THEN ASM_REWRITE_TAC[] THEN
        REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
         (SPEC `(fa:(real^N=>bool)->real^N) h \<bullet> z` REAL_SGN_CASES) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC[REAL_SGN_EQ] THEN
        SUBGOAL_THEN `\<exists>x::real^N. x \<in> C \<and> x \<in> S` MP_TAC THENL
         [ASM_MESON_TAC[MEMBER_NOT_EMPTY; \<subseteq>; NONEMPTY_HYPERPLANE_CELL];
          MATCH_MP_TAC(TAUT `~p \<Longrightarrow> p \<Longrightarrow> q`)] THEN
        MAP_EVERY EXPAND_TAC ["S"; "c"] THEN
        REWRITE_TAC[IN_INTERS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
        X_GEN_TAC `x::real^N` THEN REWRITE_TAC[AND_FORALL_THM] THEN
        DISCH_THEN(MP_TAC o SPEC `h::real^N=>bool`) THEN
        ASM_REWRITE_TAC[REAL_SGN_EQ] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h::real^N=>bool`) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(STRIP_ASSUME_TAC o GSYM)] THEN
      EXPAND_TAC "c" THEN
      W(MP_TAC o PART_MATCH (lhand o rand) CLOSURE_INTER_CONVEX o
        lhand o snd) THEN
      ANTS_TAC THENL
       [SIMP_TAC[CONVEX_INTERS; FORALL_IN_GSPEC; CONVEX_HALFSPACE_LT;
                 CONVEX_HYPERPLANE] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_INTERIOR_OPEN o
          lhand o lhand o rand o snd) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC OPEN_INTERS THEN
          ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
          REWRITE_TAC[FORALL_IN_IMAGE; OPEN_HALFSPACE_LT] THEN
          MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[FINITE_SUBSET];
          DISCH_THEN SUBST1_TAC] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_INTERIOR_OPEN_IN o
          rand o lhand o rand o snd) THEN
        ANTS_TAC THENL
         [MATCH_MP_TAC(MESON[OPEN_IN_SUBTOPOLOGY_REFL]
           `S \<subseteq> topspace tp \<and> t = S
            \<Longrightarrow> openin (subtopology tp t) S`) THEN
          REWRITE_TAC[SUBSET_UNIV; TOPSPACE_EUCLIDEAN] THEN
          REWRITE_TAC[AFFINE_HULL_EQ] THEN
          SIMP_TAC[AFFINE_INTERS; AFFINE_HYPERPLANE; FORALL_IN_GSPEC];
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[NONEMPTY_HYPERPLANE_CELL]];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[CLOSURE_INTERS_CONVEX_OPEN; FORALL_IN_GSPEC;
               CONVEX_HALFSPACE_LT; OPEN_HALFSPACE_LT] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[EMPTY_FACE_OF; INTER_EMPTY] THEN
      SUBGOAL_THEN
       `image closure {{x. fa h \<bullet> x < 0} | h \<in> J} =
        {{x. (fa:(real^N=>bool)->real^N) h \<bullet> x \<le> 0} | h \<in> J}`
      SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
        REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
        MATCH_MP_TAC(SET_RULE
         `(\<forall>x. x \<in> S \<Longrightarrow> f x = g x) \<Longrightarrow> f ` S = g ` S`) THEN
        GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC CLOSURE_HALFSPACE_LT THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
      `closure (\<Inter> {{x. fa h \<bullet> x = 0} | h \<in> H - J}) =
       \<Inter> {{x. (fa:(real^N=>bool)->real^N) h \<bullet> x = 0} | h \<in> H - J}`
      SUBST1_TAC THENL
       [REWRITE_TAC[CLOSURE_EQ] THEN
        SIMP_TAC[CLOSED_INTERS; FORALL_IN_GSPEC; CLOSED_HYPERPLANE];
        ALL_TAC] THEN
      ASM_CASES_TAC `J:(real^N=>bool)->bool = H` THENL
       [ASM_REWRITE_TAC[DIFF_EQ_EMPTY; INTER_UNIV; NOT_IN_EMPTY;
                        SET_RULE `{f x | x | False} = {}`; INTERS_0] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_REFL o
         MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        EXPAND_TAC "S" THEN AP_TERM_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `(\<forall>x. x \<in> S \<Longrightarrow> f x = x) \<Longrightarrow> S = {f x | x \<in> S}`) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `\<Inter> {{x. fa(h::real^N=>bool) \<bullet> x \<le> 0} | h \<in> J} \<inter>
        \<Inter> {{x. fa h \<bullet> x = 0} | h \<in> H - J} =
        \<Inter> {S \<inter> {x. fa h \<bullet> x = 0} | h \<in> H - J}`
      SUBST1_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[INTERS_IMAGE] THEN
        GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC `y::real^N` THEN
        REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
        ASM_CASES_TAC `(y::real^N) \<in> S` THEN ASM_REWRITE_TAC[] THENL
         [MATCH_MP_TAC(TAUT `a \<Longrightarrow> (a \<and> b \<longleftrightarrow> b)`) THEN
          UNDISCH_TAC `(y::real^N) \<in> S` THEN EXPAND_TAC "S" THEN
          REWRITE_TAC[IN_INTERS] THEN MATCH_MP_TAC MONO_FORALL THEN
          X_GEN_TAC `h::real^N=>bool` THEN
          DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `h::real^N=>bool`) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; SET_TAC[]];
          UNDISCH_TAC `~((y::real^N) \<in> S)` THEN MATCH_MP_TAC
           (TAUT `~q \<and> (p \<Longrightarrow> r) \<Longrightarrow> ~r \<Longrightarrow> (p \<longleftrightarrow> q)`) THEN
          CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          EXPAND_TAC "S" THEN REWRITE_TAC[IN_INTERS; AND_FORALL_THM] THEN
          MATCH_MP_TAC MONO_FORALL THEN
          X_GEN_TAC `h::real^N=>bool` THEN
          DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `h::real^N=>bool`) THEN
          ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
          DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
           [GSYM(CONJUNCT2 th)]) THEN
          ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
          ASM_CASES_TAC `(h::real^N=>bool) \<in> J` THEN
          ASM_SIMP_TAC[REAL_LE_REFL]];
        ALL_TAC] THEN
      MATCH_MP_TAC FACE_OF_INTERS THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `h::real^N=>bool` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
      ASM_SIMP_TAC[POLYHEDRON_IMP_CONVEX] THEN X_GEN_TAC `y::real^N` THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_INTERS] THEN
      DISCH_THEN(MP_TAC o SPEC `h::real^N=>bool`) THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `h::real^N=>bool`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [GSYM(CONJUNCT2 th)]) THEN
      REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `\<forall>h. h \<in> H \<Longrightarrow> hyperplane_cellcomplex A (- h)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
    EXISTS_TAC `{((fa:(real^N=>bool)->real^N) h,0)}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
      ASM_SIMP_TAC[HYPERPLANE_CELL_SING] THEN REPEAT DISJ2_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `h::real^N=>bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM(CONJUNCT2 th)]) THEN
      REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_UNIV] THEN
      REAL_ARITH_TAC;
      EXPAND_TAC "A" THEN
      REWRITE_TAC[IN_IMAGE; \<subseteq>; FORALL_UNWIND_THM2; IN_SING] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `\<forall>h::real^N=>bool. h \<in> H \<Longrightarrow> hyperplane_cellcomplex A h`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[HYPERPLANE_CELLCOMPLEX_COMPL;
                  COMPL_COMPL];
    ALL_TAC] THEN
  SUBGOAL_THEN `hyperplane_cellcomplex A (S::real^N=>bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_INTERS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A::real^N#real=>bool`;
                 `\<Inter> H::real^N=>bool`;
                 `- \<Inter> H`]
        EULER_CHARACTERISTIC_CELLCOMPLEX_UNION) THEN
  REWRITE_TAC[SET_RULE `disjnt S (- S)`] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[HYPERPLANE_CELLCOMPLEX_DIFF; HYPERPLANE_CELLCOMPLEX_UNIV];
    REWRITE_TAC[SET_RULE `S \<union> (- S) = UNIV`]] THEN
  REWRITE_TAC[DIFF_INTERS] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = (-- 1) ^ (DIM('N)) \<and>
    y = (-- 1) ^ (DIM('N))
    \<Longrightarrow> x = S + y \<Longrightarrow> S = 0`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `Euler_characteristic {} UNIV` THEN CONJ_TAC THENL
     [MATCH_MP_TAC EULER_CHARACTERSTIC_INVARIANT THEN
      ASM_REWRITE_TAC[FINITE_EMPTY] THEN CONJ_TAC THENL
       [MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
        EXISTS_TAC `{}:real^N#real=>bool` THEN REWRITE_TAC[EMPTY_SUBSET];
        ALL_TAC] THEN
      MATCH_MP_TAC HYPERPLANE_CELL_CELLCOMPLEX THEN
      REWRITE_TAC[HYPERPLANE_CELL_EMPTY];
      SIMP_TAC[EULER_CHARACTERISTIC_CELL; HYPERPLANE_CELL_EMPTY] THEN
      REWRITE_TAC[AFF_DIM_UNIV; NUM_OF_INT_OF_NUM]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) EULER_CHARACTERISTIC_INCLUSION_EXCLUSION o
    lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {t. t \<subseteq> {- t | t \<in> H} \<and> (t \<noteq> {})}
             (\<lambda>t.-1 ^ (card t + 1) * (-- 1) ^ (DIM('N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMP_CONJ; FORALL_SUBSET_IMAGE] THEN
    X_GEN_TAC `J:(real^N=>bool)->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN DISCH_TAC THEN AP_TERM_TAC THEN
    ABBREV_TAC `B = image (\<lambda>h::real^N=>bool. fa h::real^N,0) J` THEN
    SUBGOAL_THEN `(B::real^N#real=>bool) \<subseteq> A` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `\<Inter> (image (\<lambda>t. - t) H) =
      image (--) (interior S)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`S::real^N=>bool`; `H:(real^N=>bool)->bool`;
                     `fa:(real^N=>bool)->real^N`;
                     `\<lambda>h::real^N=>bool. 0`]
                RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
      ASM_SIMP_TAC[INTER_UNIV] THEN
      ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR] THEN
      DISCH_THEN(K ALL_TAC) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC[VECTOR_ARITH `-x::real^N = y \<longleftrightarrow> x =-y`; EXISTS_REFL] THEN
      X_GEN_TAC `x::real^N` THEN REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
      MATCH_MP_TAC(TAUT `(c \<Longrightarrow> b) \<and> (a \<longleftrightarrow> c) \<Longrightarrow> (a \<longleftrightarrow> b \<and> c)`) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "S" THEN REWRITE_TAC[IN_INTERS] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `h::real^N=>bool` THEN
        ASM_CASES_TAC `(h::real^N=>bool) \<in> H` THEN ASM_REWRITE_TAC[] THEN
        ASM SET_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC(MESON[]
         `(\<forall>h. P h \<Longrightarrow> (Q h \<longleftrightarrow> R h))
          \<Longrightarrow> ((\<forall>h. P h \<Longrightarrow> Q h) \<longleftrightarrow> (\<forall>h. P h \<Longrightarrow> R h))`) THEN
        X_GEN_TAC `h::real^N=>bool` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [SYM(CONJUNCT2(MATCH_MP th (ASSUME `(h::real^N=>bool) \<in> H`)))]) THEN
        REWRITE_TAC[IN_ELIM_THM; DOT_RNEG] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `hyperplane_cell B (\<Inter> (image (\<lambda>t. - t) J))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `~(\<Inter> (image (\<lambda>t. - t) J) = {})`
      MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[hyperplane_cell; GSYM MEMBER_NOT_EMPTY; IN_INTERS] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z::real^N` THEN
      REWRITE_TAC[IN_UNIV; IN_DIFF] THEN
      GEN_REWRITE_TAC RAND_CONV [EXTENSION] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `x::real^N` THEN MP_TAC th) THEN
      REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [\<in>] THEN
      REWRITE_TAC[hyperplane_equiv] THEN EXPAND_TAC "B" THEN
      REWRITE_TAC[FORALL_IN_IMAGE; hyperplane_side] THEN
      MATCH_MP_TAC(MESON[]
       `(\<forall>h. P h \<Longrightarrow> (Q h \<longleftrightarrow> R h))
        \<Longrightarrow> (\<forall>h. P h) \<Longrightarrow> ((\<forall>h. Q h) \<longleftrightarrow> (\<forall>h. R h))`) THEN
      X_GEN_TAC `h::real^N=>bool` THEN
      ASM_CASES_TAC `(h::real^N=>bool) \<in> J` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(h::real^N=>bool) \<in> H` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o C MATCH_MP (ASSUME
       `(h::real^N=>bool) \<in> H`)) THEN
      DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [SYM th] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
      REWRITE_TAC[IN_ELIM_THM; REAL_SUB_RZERO; REAL_NOT_LE] THEN
      MESON_TAC[REAL_SGN_EQ; real_gt];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `Euler_characteristic B (\<Inter> (image (\<lambda>t. - t) J))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EULER_CHARACTERSTIC_INVARIANT THEN
      ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
      EXISTS_TAC `B::real^N#real=>bool` THEN
      ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[EULER_CHARACTERISTIC_CELL] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(MESON[NUM_OF_INT_OF_NUM] `i = n \<Longrightarrow> nat i = n`) THEN
    REWRITE_TAC[AFF_DIM_EQ_FULL] THEN
    MATCH_MP_TAC(SET_RULE `\<forall>t. t \<subseteq> S \<and> t = UNIV \<Longrightarrow> S = UNIV`) THEN
    EXISTS_TAC `affine hull (\<Inter> (image (\<lambda>t. - t) H))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC AFFINE_HULL_OPEN THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[IMAGE_EQ_EMPTY; OPEN_NEGATIONS; OPEN_INTERIOR];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_RMUL] THEN
  MATCH_MP_TAC(REAL_RING `S = 1 \<Longrightarrow> S * t = t`) THEN
  MP_TAC(ISPECL [`\<lambda>t:(real^N=>bool)->bool. card t`;
                 `\<lambda>t:(real^N=>bool)->bool. (-1) ^ (card t + 1)`;
                 `{t.  t \<subseteq>
                     {- t | t \<in> H} \<and> (t \<noteq> {})}`;
                 `1..card(H:(real^N=>bool)->bool)`]
        SUM_GROUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t.  t \<subseteq> {- t | t \<in> H}}` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC FINITE_POWERSET THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_IMAGE];
      GEN_REWRITE_TAC id [\<subseteq>] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_NUMSEG] THEN
      REWRITE_TAC[SIMPLE_IMAGE; FORALL_SUBSET_IMAGE; IMP_CONJ] THEN
      X_GEN_TAC `J:(real^N=>bool)->bool` THEN DISCH_TAC THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN DISCH_TAC THEN
      SUBGOAL_THEN `finite(J:(real^N=>bool)->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_EQ_0; FINITE_IMAGE; ARITH_RULE `1 \<le> n \<longleftrightarrow> (n \<noteq> 0)`;
                   IMAGE_EQ_EMPTY] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `card(J:(real^N=>bool)->bool)` THEN
      ASM_SIMP_TAC[CARD_SUBSET; CARD_IMAGE_LE]];
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (1..card(H:(real^N=>bool)->bool))
        (\<lambda>n.-1 ^ (Suc n) * &((card H) choose n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n::num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
    SIMP_TAC[IN_ELIM_THM] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_CONST o lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t.  t \<subseteq> {- t | t \<in> H}}` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC FINITE_POWERSET THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_IMAGE];
      DISCH_THEN SUBST1_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `card {t. t \<subseteq> {- t | t \<in> H} \<and>
                          t HAS_SIZE n}` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN GEN_REWRITE_TAC id [EXTENSION] THEN
      X_GEN_TAC `t:(real^N=>bool)->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_CASES_TAC `t:(real^N=>bool)->bool = {}` THEN
      ASM_REWRITE_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_EMPTY] THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(p \<Longrightarrow> r) \<Longrightarrow> (p \<and> q \<longleftrightarrow> p \<and> r \<and> q)`) THEN
      SPEC_TAC(`t:(real^N=>bool)->bool`,`u:(real^N=>bool)->bool`) THEN
      REWRITE_TAC[SIMPLE_IMAGE; FORALL_SUBSET_IMAGE] THEN
      ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`card(H:(real^N=>bool)->bool)`;
                   `n::num`; `{- t | t \<in> H}`]
        NUMBER_OF_COMBINATIONS) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[HAS_SIZE]] THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    ASM_REWRITE_TAC[GSYM FINITE_HAS_SIZE] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`card(H:(real^N=>bool)->bool)`; `-- 1`; `1`]
        REAL_BINOMIAL_THEOREM) THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID; REAL_ADD_LINV] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; REAL_POW_ADD; REAL_POW_ONE; LE_0] THEN
  REWRITE_TAC[REAL_ARITH `(x * -- 1 ^ 1) * y = --(y * x)`] THEN
  REWRITE_TAC[real_pow; SUM_NEG; ADD_CLAUSES; REAL_MUL_RID] THEN
  REWRITE_TAC[binom] THEN MATCH_MP_TAC(REAL_ARITH
   `x = 0 \<Longrightarrow> x = 1 + y \<Longrightarrow>-y = 1`) THEN
  REWRITE_TAC[REAL_POW_ZERO] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `card(H:(real^N=>bool)->bool) = 0` THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[]);;


text\<open> ------------------------------------------------------------------------- \<close>
(* Euler-Poincare relation for special (n-1)-dimensional polytope.           *)
text\<open> ------------------------------------------------------------------------- \<close>

lemma Euler_poincare_lemma:
   "\<And>p::real^N=>bool.
        2 \<le> DIM('N) \<and> polytope p \<and> affine hull p = {x. x$1 = 1}
        \<Longrightarrow> sum (0..DIM('N)-1)
               (\<lambda>d. (-1) ^ d *
                    (card {f. f face_of p \<and> aff_dim f = d })) = 1"
oops 
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`axis 1 1::real^N`; `1`] AFF_DIM_HYPERPLANE) THEN
  SIMP_TAC[BASIS_NONZERO; DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
  ASM_CASES_TAC `p::real^N=>bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
    REWRITE_TAC[INT_ARITH `-- 1:int = x - 1 \<longleftrightarrow> x = 0`] THEN
    SIMP_TAC[INT_OF_NUM_EQ; LE_1; DIMINDEX_GE_1];
    DISCH_TAC] THEN
  ABBREV_TAC `s::real^N=>bool = conic hull p` THEN
  MP_TAC(ISPEC `s::real^N=>bool` EULER_POLYHEDRAL_CONE) THEN
  SUBGOAL_THEN
   `\<forall>f. f \<subseteq> {x. x$1 = 1}
        \<Longrightarrow> (conic hull f) \<inter> {x. x$1 = 1} = f`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    ASM_SIMP_TAC[HULL_SUBSET; SUBSET_INTER] THEN
    REWRITE_TAC[\<subseteq>; CONIC_HULL_EXPLICIT; IN_INTER; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`c::real`; `x::real^N`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE id [\<subseteq>]) THEN
    DISCH_THEN(MP_TAC o SPEC `x::real^N`) THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_RID; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `polyhedron(s::real^N=>bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `k::real^N=>bool` MP_TAC o
      GEN_REWRITE_RULE id [polytope]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(fun th -> SUBST1_TAC th THEN ASSUME_TAC th) THEN
    MP_TAC(ISPEC `k::real^N=>bool` CONVEX_CONE_HULL_SEPARATE_NONEMPTY) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[CONVEX_HULL_EQ_EMPTY]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC POLYHEDRON_CONVEX_CONE_HULL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP POLYHEDRON_IMP_CONVEX) THEN
  SUBGOAL_THEN `conic(s::real^N=>bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONIC_CONIC_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `(s \<noteq> UNIV)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `p::real^N=>bool`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[HULL_SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[INTER_UNIV] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    UNDISCH_TAC `polytope(p::real^N=>bool)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP POLYTOPE_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS; NOT_EXISTS_THM] THEN X_GEN_TAC `B::real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC
     `(\<chi> i. if i = 1 then 1 else B + 1):real^N`) THEN
    SIMP_TAC[LAMBDA_BETA; DIMINDEX_GE_1; LE_REFL; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN
    MP_TAC(ISPECL
    [`(\<chi> i. if i = 1 then 1 else B + 1):real^N`; `2`]
      COMPONENT_LE_NORM) THEN
    ASM_SIMP_TAC[ARITH; LAMBDA_BETA; DIMINDEX_GE_1; LE_REFL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s::real^N=>bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONIC_HULL_EQ_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPEC `s::real^N=>bool` CONIC_CONTAINS_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interior(s::real^N=>bool) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN MP_TAC(ISPEC `s::real^N=>bool`
     EMPTY_INTERIOR_SUBSET_HYPERPLANE) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a::real^N`; `b::real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `s \<subseteq> {x. x$1 = 1}` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `s \<subseteq> h' \<Longrightarrow> h \<subseteq> h' \<and> ~(h \<subset> h') \<Longrightarrow> s \<subseteq> h`)) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s::real^N=>bool` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[HULL_SUBSET];
        DISCH_TAC THEN
        MP_TAC(ISPECL [`a::real^N`; `b::real`] AFF_DIM_HYPERPLANE) THEN
        MP_TAC(ISPECL [`axis 1 1::real^N`; `1`] AFF_DIM_HYPERPLANE) THEN
        ASM_SIMP_TAC[BASIS_NONZERO; DOT_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
        MATCH_MP_TAC(INT_ARITH `a::int < b \<Longrightarrow> a = n \<Longrightarrow> (b \<noteq> n)`) THEN
        MATCH_MP_TAC AFF_DIM_PSUBSET THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (SET_RULE `s \<subset> t \<Longrightarrow> s' = s \<and> t' = t \<Longrightarrow> s' \<subset> t'`)) THEN
        REWRITE_TAC[AFFINE_HULL_EQ; AFFINE_HYPERPLANE] THEN
        MP_TAC(ISPECL [`axis 1 1::real^N`; `1`] AFFINE_HYPERPLANE) THEN
        SIMP_TAC[BASIS_NONZERO; DOT_BASIS; DIMINDEX_GE_1; LE_REFL]];
      REWRITE_TAC[\<subseteq>; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `0::real^N` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `\<forall>x::real^N. x \<in> s \<and> (x \<noteq> 0) \<Longrightarrow> 0 < x$1`
  ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[CONIC_HULL_EXPLICIT; IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN
    MAP_EVERY X_GEN_TAC [`c::real`; `x::real^N`] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x::real^N) \<in> affine hull p` MP_TAC THENL
     [ASM_MESON_TAC[HULL_SUBSET; \<subseteq>]; ASM_REWRITE_TAC[]] THEN
    SIMP_TAC[IN_ELIM_THM; REAL_LT_01];
    ALL_TAC] THEN
  SUBGOAL_THEN `\<forall>x::real^N. x \<in> s \<Longrightarrow> 0 \<le> x$1` ASSUME_TAC THENL
   [X_GEN_TAC `x::real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x::real^N = 0` THEN
    ASM_SIMP_TAC[VEC_COMPONENT; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_CLAUSES_LEFT o
    lhand o lhand o snd) THEN
  REWRITE_TAC[LE_0] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[AFF_DIM_EQ_0; real_pow; REAL_MUL_LID] THEN
  SUBGOAL_THEN `{f. f face_of s \<and> (\<exists>a::real^N. f = {a})} = {{0}}`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `f::real^N=>bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `a::real^N`)) THEN
      ASM_REWRITE_TAC[FACE_OF_SING] THEN
      ASM_MESON_TAC[EXTREME_POINT_OF_CONIC];
      DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      ASM_REWRITE_TAC[FACE_OF_SING; extreme_point_of; IN_SEGMENT] THEN
      MAP_EVERY X_GEN_TAC [`a::real^N`; `b::real^N`] THEN STRIP_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `u::real` THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[CART_EQ] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VEC_COMPONENT] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `0 < (a::real^N)$1 \<or> 0 < (b::real^N)$1` DISJ_CASES_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC(REAL_ARITH `0 < a \<and> 0 \<le> b \<Longrightarrow> ~(0 = a + b)`);
        MATCH_MP_TAC(REAL_ARITH `0 < b \<and> 0 \<le> a \<Longrightarrow> ~(0 = a + b)`)] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LT_MUL; REAL_SUB_LT]];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; NOT_IN_EMPTY; GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC(REAL_ARITH `s =-t \<Longrightarrow> (Suc 0) + s = 0 \<Longrightarrow> t = 1`) THEN
  SUBGOAL_THEN `DIM('N) = (DIM('N)-1)+1`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET; GSYM SUM_NEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d::num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_MUL_RNEG; REAL_MUL_LNEG] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
  EXISTS_TAC `\<lambda>f::real^N=>bool. f \<inter> {x. x$1 = 1}` THEN
  EXISTS_TAC `\<lambda>f::real^N=>bool. conic hull f` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{f::real^N=>bool | f face_of s}` THEN
    ASM_SIMP_TAC[FINITE_POLYHEDRON_FACES] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM; GSYM INT_OF_NUM_ADD]] THEN
  SUBGOAL_THEN
   `\<forall>f::real^N=>bool. f face_of p \<Longrightarrow> conic hull f \<inter> {x. x$1 = 1} = f`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `affine hull p::real^N=>bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; SUBSET_TRANS];
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `\<forall>f::real^N=>bool. f face_of s \<Longrightarrow> f \<inter> {x. x$1 = 1} face_of p`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `p = conic hull p \<inter> {x. x$1 = 1}` SUBST1_TAC
    THENL [ASM_MESON_TAC[FACE_OF_REFL; POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
    MATCH_MP_TAC FACE_OF_SLICE THEN
    ASM_REWRITE_TAC[CONVEX_STANDARD_HYPERPLANE];
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `\<forall>f. f face_of s  \<and> 0 < aff_dim f
        \<Longrightarrow> conic hull (f \<inter> {x. x$1 = 1}) = f`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[\<subseteq>; CONIC_HULL_EXPLICIT; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      ASM_MESON_TAC[FACE_OF_CONIC; conic];
      REWRITE_TAC[\<subseteq>; CONIC_HULL_EXPLICIT] THEN X_GEN_TAC `x::real^N` THEN
      DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
      ASM_CASES_TAC `x::real^N = 0` THENL
       [SUBGOAL_THEN `\<exists>y::real^N. y \<in> f \<and> (y \<noteq> 0)` STRIP_ASSUME_TAC THENL
         [MATCH_MP_TAC(SET_RULE
           `a \<in> s \<and> (s \<noteq> {a}) \<Longrightarrow> \<exists>y. y \<in> s \<and> (y \<noteq> a)`) THEN
          ASM_MESON_TAC[AFF_DIM_EQ_0; INT_LT_REFL];
          SUBGOAL_THEN `0 < (y::real^N)$1` ASSUME_TAC THENL
           [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; \<subseteq>]; ALL_TAC] THEN
          EXISTS_TAC `0` THEN ASM_REWRITE_TAC[REAL_POS; VECTOR_MUL_LZERO] THEN
          EXISTS_TAC `inverse(y$1) *\<^sub>R y::real^N` THEN
          ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_LINV;
                       REAL_LT_IMP_NZ] THEN
          ASM_MESON_TAC[FACE_OF_CONIC; conic; REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
        SUBGOAL_THEN `0 < (x::real^N)$1` ASSUME_TAC THENL
         [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; \<subseteq>]; ALL_TAC] THEN
        EXISTS_TAC `(x::real^N)$1` THEN EXISTS_TAC `inverse(x$1) *\<^sub>R x::real^N` THEN
        ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_LINV; REAL_LT_IMP_LE;
          REAL_LT_IMP_NZ; VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
        ASM_MESON_TAC[FACE_OF_CONIC; conic; REAL_LE_INV_EQ; REAL_LT_IMP_LE]]];
    ASM_SIMP_TAC[INT_ARITH `0::int < d + 1`]] THEN
  SUBGOAL_THEN
   `\<forall>f::real^N=>bool. f face_of p \<Longrightarrow> (conic hull f) face_of s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `f::real^N=>bool = {}` THEN
    ASM_REWRITE_TAC[CONIC_HULL_EMPTY; EMPTY_FACE_OF] THEN
    REWRITE_TAC[face_of] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC HULL_MONO THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      ASM_MESON_TAC[CONVEX_CONIC_HULL; FACE_OF_IMP_CONVEX];
      ALL_TAC] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[CONIC_HULL_EXPLICIT; IMP_CONJ] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`ca::real`; `a::real^N`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`cb::real`; `b::real^N`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`cx::real`; `x::real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `cx *\<^sub>R x::real^N = 0` THENL
     [ASM_REWRITE_TAC[IN_SEGMENT] THEN
      MATCH_MP_TAC(TAUT `(a \<Longrightarrow> ~b) \<Longrightarrow> a \<and> b \<Longrightarrow> c`) THEN
      DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `u::real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[CART_EQ] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VEC_COMPONENT] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT] THEN
      ONCE_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `0 < (ca *\<^sub>R a::real^N)$1 \<or> 0 < (cb *\<^sub>R b::real^N)$1`
      DISJ_CASES_TAC THENL
       [SUBGOAL_THEN `(ca *\<^sub>R a::real^N) \<in> s \<and> (cb *\<^sub>R b::real^N) \<in> s`
          (fun th -> ASM_MESON_TAC[th]) THEN
        ASM_MESON_TAC[conic; HULL_SUBSET; \<subseteq>];
        MATCH_MP_TAC(REAL_ARITH `0 < a \<and> 0 \<le> b \<Longrightarrow> ~(0 = a + b)`);
        MATCH_MP_TAC(REAL_ARITH `0 < b \<and> 0 \<le> a \<Longrightarrow> ~(0 = a + b)`)] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LT_MUL; REAL_SUB_LT] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_SUB_LT] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[conic; HULL_SUBSET; \<subseteq>];
      ALL_TAC] THEN
    UNDISCH_TAC `~(cx *\<^sub>R x::real^N = 0)` THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x::real^N = a` THENL
     [REWRITE_TAC[IN_SEGMENT] THEN DISCH_THEN
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u::real` MP_TAC)) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
       `x *\<^sub>R a::real^N = y *\<^sub>R a + z *\<^sub>R b \<longleftrightarrow> (x - y) *\<^sub>R a = z *\<^sub>R b`] THEN
      DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC LAND_CONV [CART_EQ] THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `(a::real^N) \<in> affine hull p \<and> b \<in> affine hull p`
      MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; \<subseteq>]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_ENTIRE; REAL_LT_IMP_NZ] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`ca::real`; `a::real^N`] THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
          MAP_EVERY EXISTS_TAC [`0`; `x::real^N`] THEN
          ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL]];
        CONJ_TAC THENL [EXISTS_TAC `ca::real`; EXISTS_TAC `cb::real`] THEN
        EXISTS_TAC `x::real^N` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `x::real^N = b` THENL
     [REWRITE_TAC[IN_SEGMENT] THEN DISCH_THEN
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u::real` MP_TAC)) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
       `x *\<^sub>R b::real^N = y *\<^sub>R a + z *\<^sub>R b \<longleftrightarrow> (x - z) *\<^sub>R b = y *\<^sub>R a`] THEN
      DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC LAND_CONV [CART_EQ] THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `(a::real^N) \<in> affine hull p \<and> b \<in> affine hull p`
      MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; \<subseteq>]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_ENTIRE;
                   REAL_LT_IMP_NE; REAL_SUB_0] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`0`; `x::real^N`] THEN
          ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL];
          MAP_EVERY EXISTS_TAC [`cb::real`; `b::real^N`] THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
        CONJ_TAC THENL [EXISTS_TAC `ca::real`; EXISTS_TAC `cb::real`] THEN
        EXISTS_TAC `x::real^N` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x::real^N) \<in> open_segment a b` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE id [IN_OPEN_SEGMENT]) THEN
      ASM_REWRITE_TAC[IN_OPEN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `u::real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC LAND_CONV [CART_EQ] THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[LE_REFL; DIMINDEX_GE_1; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `(x::real^N) \<in> affine hull p \<and>
                    a \<in> affine hull p \<and> b \<in> affine hull p`
      MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; HULL_SUBSET; \<subseteq>]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
      REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
      DISCH_THEN(MP_TAC o AP_TERM `(%) (inverse cx) :real^N=>real^N`) THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
      DISCH_THEN(K ALL_TAC) THEN EXISTS_TAC `inverse(cx) * u * cb` THEN
      REWRITE_TAC[REAL_ARITH `inverse(cx) * x::real = x / cx`] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_LT_LE] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_LZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `a + b = cx \<Longrightarrow> 0 \<le> a \<Longrightarrow> b \<le> 1 * cx`)) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ADD_LDISTRIB] THEN
        BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`(1 - u) * ca + u * cb = cx`; `(cx \<noteq> 0)`] THEN
        CONV_TAC REAL_FIELD];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE id [face_of]) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(MP_TAC o SPECL [`a::real^N`; `b::real^N`; `x::real^N`]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN
   `\<forall>f::real^N=>bool. f face_of p \<and> (f \<noteq> {})
                     \<Longrightarrow> aff_dim(conic hull f) = aff_dim f + 1`
  (LABEL_TAC "*") THENL
   [ALL_TAC;
    CONJ_TAC THEN X_GEN_TAC `f::real^N=>bool` THEN STRIP_TAC THENL
     [REMOVE_THEN "*" (MP_TAC o SPEC `f \<inter> {x. x$1 = 1}`) THEN
      ASM_SIMP_TAC[INT_ARITH `0::int < d + 1`; INT_EQ_ADD_RCANCEL] THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      SUBGOAL_THEN `\<exists>y::real^N. y \<in> f \<and> (y \<noteq> 0)` STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `a \<in> s \<and> (s \<noteq> {a}) \<Longrightarrow> \<exists>y. y \<in> s \<and> (y \<noteq> a)`) THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`s::real^N=>bool`; `f::real^N=>bool`]
            FACE_OF_CONIC) THEN
          ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN REPEAT DISCH_TAC;
          DISCH_TAC] THEN
        UNDISCH_TAC `aff_dim(f::real^N=>bool) = d + 1` THEN
        ASM_REWRITE_TAC[AFF_DIM_SING; AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        SUBGOAL_THEN `0 < (y::real^N)$1` ASSUME_TAC THENL
         [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; \<subseteq>]; ALL_TAC] THEN
        EXISTS_TAC `inverse(y$1) *\<^sub>R y::real^N` THEN
        ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_LINV;
                     REAL_LT_IMP_NZ] THEN
        MP_TAC(ISPECL [`s::real^N=>bool`; `f::real^N=>bool`]
          FACE_OF_CONIC) THEN
        ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN
        REWRITE_TAC[conic] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
      REMOVE_THEN "*" (MP_TAC o SPEC `f::real^N=>bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(f::real^N=>bool) = d` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC]] THEN
  X_GEN_TAC `f::real^N=>bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(INT_ARITH `f < a \<and> a \<le> f + 1 \<Longrightarrow> a::int = f + 1`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC AFF_DIM_PSUBSET THEN
    SIMP_TAC[\<subset>; HULL_MONO; HULL_SUBSET] THEN
    REWRITE_TAC[EXTENSION; NOT_FORALL_THM] THEN EXISTS_TAC `0::real^N` THEN
    MATCH_MP_TAC(TAUT `~p \<and> q \<Longrightarrow> ~(p \<longleftrightarrow> q)`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `\<forall>t. (x \<notin> t) \<and> s \<subseteq> t \<Longrightarrow> (x \<notin> s)`) THEN
      EXISTS_TAC `affine hull p::real^N=>bool` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC HULL_MONO THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
      MATCH_MP_TAC(SET_RULE
       `x \<in> s \<and> s \<subseteq> P hull s \<Longrightarrow> x \<in> P hull s`) THEN
      ASM_SIMP_TAC[CONIC_CONTAINS_0; HULL_SUBSET; CONIC_CONIC_HULL] THEN
      ASM_REWRITE_TAC[CONIC_HULL_EQ_EMPTY]];
    MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `aff_dim((0::real^N) insert (affine hull f))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[AFF_DIM_INSERT; AFF_DIM_AFFINE_HULL] THEN INT_ARITH_TAC] THEN
    ONCE_REWRITE_TAC[GSYM AFF_DIM_AFFINE_HULL] THEN
    MATCH_MP_TAC AFF_DIM_SUBSET THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[AFFINE_AFFINE_HULL; \<subseteq>; CONIC_HULL_EXPLICIT] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`c::real`; `x::real^N`] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `c *\<^sub>R x::real^N = 0 + c *\<^sub>R (x - 0)`] THEN
    MATCH_MP_TAC IN_AFFINE_ADD_MUL_DIFF THEN
    ASM_SIMP_TAC[AFFINE_AFFINE_HULL; HULL_INC; IN_INSERT]]);;

lemma Euler_poincare_special:
   "\<And>p::real^N=>bool.
        2 \<le> DIM('N) \<and> polytope p \<and> affine hull p = {x. x$1 = 0}
        \<Longrightarrow> sum (0..DIM('N)-1)
               (\<lambda>d. (-1) ^ d *
                    (card {f. f face_of p \<and> aff_dim f = d })) = 1"
oops 
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `image (\<lambda>x::real^N. axis 1 1 + x) p` EULER_POINCARE_LEMMA) THEN
  ASM_REWRITE_TAC[POLYTOPE_TRANSLATION_EQ; AFFINE_HULL_TRANSLATION] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[EXISTS_REFL; VECTOR_ARITH
     `a + x::real^N = y \<longleftrightarrow> x = y - a`] THEN
    SIMP_TAC[IN_ELIM_THM; VECTOR_ADD_COMPONENT; BASIS_COMPONENT;
             DIMINDEX_GE_1; LE_REFL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SET_RULE `{f. f face_of s \<and> P f} =
                          {f. f \<in> {f. f face_of s} \<and> P f}`] THEN
    REWRITE_TAC[FACES_OF_TRANSLATION] THEN
    REWRITE_TAC[SET_RULE `{y. y \<in> f ` s \<and> P y} =
                          {f x |x| x \<in> s \<and> P(f x)}`] THEN
    REWRITE_TAC[AFF_DIM_TRANSLATION_EQ; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d::num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SIMPLE_IMAGE_GEN] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `(\<forall>x y. Q x y \<Longrightarrow> x = y)
        \<Longrightarrow> (\<forall>x y. P x \<and> P y \<and> Q x y \<Longrightarrow> x = y)`) THEN
      REWRITE_TAC[INJECTIVE_IMAGE] THEN VECTOR_ARITH_TAC;
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{f::real^N=>bool | f face_of p}` THEN
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[]]]);;

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Now Euler-Poincare for a general full-dimensional polytope.               \<close>
text\<open> ------------------------------------------------------------------------- \<close>

lemma Euler_poincare_full:
   "\<And>p::real^N=>bool.
        polytope p \<and> aff_dim p = &(DIM('N))
        \<Longrightarrow> sum (0..DIM('N))
                (\<lambda>d. (-1) ^ d *
                     (card {f. f face_of p \<and> aff_dim f = d })) = 1"
oops 
  REPEAT STRIP_TAC THEN ABBREV_TAC
   `f::real^N=>real^(N,1)finite_sum =
          \<lambda>x. \<chi> i. if i = 1 then 0 else x$(i-1)` THEN
  ABBREV_TAC `s = image (f::real^N=>real^(N,1)finite_sum) p` THEN
  MP_TAC(ISPEC `s::real^(N,1)finite_sum=>bool` EULER_POINCARE_SPECIAL) THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; ADD_SUB] THEN
  REWRITE_TAC[DIMINDEX_GE_1; ARITH_RULE `2 \<le> n + 1 \<longleftrightarrow> 1 \<le> n`] THEN
  SUBGOAL_THEN `linear(f::real^N=>real^(N,1)finite_sum)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[linear] THEN
    SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "s" THEN
  ASM_SIMP_TAC[POLYTOPE_LINEAR_IMAGE; AFFINE_HULL_LINEAR_IMAGE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EQ_FULL]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `y::real^(N,1)finite_sum` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x::real^N` SUBST1_TAC) THEN
      EXPAND_TAC "f" THEN SIMP_TAC[LAMBDA_BETA; LE_REFL; DIMINDEX_GE_1];
      DISCH_TAC THEN
      EXISTS_TAC `(\<chi> i. (y::real^(N,1)finite_sum)$(Suc i)):real^N` THEN
      EXPAND_TAC "f" THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
      X_GEN_TAC `i::num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_FINITE_SUM; DIMINDEX_1;
       DIMINDEX_GE_1; ARITH_RULE `1 \<le> i \<and> (i \<noteq> 1) \<Longrightarrow> 1 \<le> i - 1`;
       ARITH_RULE `1 \<le> n \<and> i \<le> n + 1 \<Longrightarrow> i - 1 \<le> n`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC];
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `d::num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `\<forall>x y. (f::real^N=>real^(N,1)finite_sum) x = f y \<longleftrightarrow> x = y`
    ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN
      ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_FINITE_SUM; DIMINDEX_1;
        DIMINDEX_GE_1; ARITH_RULE `1 \<le> i \<and> (i \<noteq> 1) \<Longrightarrow> 1 \<le> i - 1`;
        ARITH_RULE `1 \<le> n \<and> i \<le> n + 1 \<Longrightarrow> i - 1 \<le> n`] THEN
      REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `i::num` THENL
       [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ADD_SUB] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    EXPAND_TAC "s" THEN
    MP_TAC(ISPECL [`f::real^N=>real^(N,1)finite_sum`; `p::real^N=>bool`]
        FACES_OF_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[SET_RULE `{f. f face_of s \<and> P f} =
                          {f. f \<in> {f. f face_of s} \<and> P f}`] THEN
    ASM_REWRITE_TAC[SET_RULE `{y. y \<in> f ` s \<and> P y} =
                              {f x |x| x \<in> s \<and> P(f x)}`] THEN
    ASM_SIMP_TAC[AFF_DIM_INJECTIVE_LINEAR_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SIMPLE_IMAGE_GEN] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
       `(\<forall>x y. Q x y \<Longrightarrow> x = y)
        \<Longrightarrow> (\<forall>x y. P x \<and> P y \<and> Q x y \<Longrightarrow> x = y)`) THEN
      ASM_REWRITE_TAC[INJECTIVE_IMAGE];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{f::real^N=>bool | f face_of p}` THEN
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[]]]);;

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> In particular the Euler relation in 3D.                                   \<close>
text\<open> ------------------------------------------------------------------------- \<close>

lemma Euler_relation:
   "\<And>p::real^3=>bool.
        polytope p \<and> aff_dim p = 3
        \<Longrightarrow> (card {v. v face_of p \<and> aff_dim v = 0} +
             card {f. f face_of p \<and> aff_dim f = 2}) -
            card {e. e face_of p \<and> aff_dim e = 1} = 2"
oops 
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `p::real^3=>bool` EULER_POINCARE_FULL) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `3`; SUM_CLAUSES_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LNEG] THEN
  SUBGOAL_THEN `{f::real^3=>bool | f face_of p \<and> aff_dim f = 3} = {p}`
   (fun th -> SIMP_TAC[th; NOT_IN_EMPTY; FINITE_EMPTY; CARD_CLAUSES])
  THENL
   [MATCH_MP_TAC(SET_RULE
     `P a \<and> (\<forall>x. P x \<Longrightarrow> x = a) \<Longrightarrow> {x. P x} = {a}`) THEN
    ASM_SIMP_TAC[FACE_OF_REFL; POLYTOPE_IMP_CONVEX] THEN
    X_GEN_TAC `f::real^3=>bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f::real^3=>bool`; `p::real^3=>bool`]
        FACE_OF_AFF_DIM_LT) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; INT_LT_REFL];
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_ARITH `((x +-y) + z) +-1::real = 1 \<longleftrightarrow>
                            x + z = y + 2`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD_SUB2]]);;
