chapter \<open>Euler's Polyhedron Formula\<close>

text \<open>One of the Famous 100 Theorems, ported from HOL Light\<close>
text\<open> Formalization of Jim Lawrence's proof of Euler's relation.                \<close>

theory Euler_Formula
  imports "HOL-Analysis.Analysis" "Inclusion_Exclusion" "HOL-ex.Sketch_and_Explore"
begin

section \<open>Preliminaries\<close>

(*FIX NAMING CONVENTIONS inter, etc.*)
thm convex_closure_inter
lemmas closure_Int_convex = convex_closure_inter_two

lemmas span_not_UNIV_orthogonal = span_not_univ_orthogonal

(*THIS IS A BETTER FORMULATION THAN THE ORIGINAL convex_closure_inter*)

thm convex_closure_rel_interior_inter (*REPLACE*)
lemma convex_closure_rel_interior_Int:
  assumes "\<forall>S\<in>\<F>. convex (S :: 'n::euclidean_space set)"
    and "\<Inter>(rel_interior ` \<F>) \<noteq> {}"
  shows "\<Inter>(closure ` \<F>) \<subseteq> closure (\<Inter>(rel_interior ` \<F>))"
proof -
  obtain x where x: "\<forall>S\<in>\<F>. x \<in> rel_interior S"
    using assms by auto
  {
    fix y
    assume "y \<in> \<Inter>{closure S |S. S \<in> \<F>}"
    then have y: "\<forall>S \<in> \<F>. y \<in> closure S"
      by auto
    {
      assume "y = x"
      then have "y \<in> closure (\<Inter>(rel_interior ` \<F>))"
        using closure_subset x by fastforce
    }
    moreover
    {
      assume "y \<noteq> x"
      { fix e :: real
        assume e: "e > 0"
        define e1 where "e1 = min 1 (e/norm (y - x))"
        then have e1: "e1 > 0" "e1 \<le> 1" "e1 * norm (y - x) \<le> e"
          using \<open>y \<noteq> x\<close> \<open>e > 0\<close> le_divide_eq[of e1 e "norm (y - x)"]
          by simp_all
        define z where "z = y - e1 *\<^sub>R (y - x)"
        {
          fix S
          assume "S \<in> \<F>"
          then have "z \<in> rel_interior S"
            using rel_interior_closure_convex_shrink[of S x y e1] assms x y e1 z_def
            by auto
        }
        then have *: "z \<in> \<Inter>(rel_interior ` \<F>)"
          by auto
        have "\<exists>z. z \<in> \<Inter>(rel_interior ` \<F>) \<and> z \<noteq> y \<and> dist z y \<le> e"
          using \<open>y \<noteq> x\<close> z_def * e1 e dist_norm[of z y]
          by (rule_tac x="z" in exI) auto
      }
      then have "y \<in> closure (\<Inter>(rel_interior ` \<F>))"
        by (meson closure_approachable_le)
    }
    ultimately have "y \<in> closure (\<Inter>(rel_interior ` \<F>))"
      by auto
  }
  then show ?thesis by auto
qed


lemma closure_Inter_convex:
  fixes \<F> :: "'n::euclidean_space set set"
  assumes  "\<And>S. S \<in> \<F> \<Longrightarrow> convex S" and "\<Inter>(rel_interior ` \<F>) \<noteq> {}"
  shows "closure(\<Inter>\<F>) = \<Inter>(closure ` \<F>)"
proof -
  have "\<Inter>(closure ` \<F>) \<le> closure (\<Inter>(rel_interior ` \<F>))"
    by (meson assms convex_closure_rel_interior_Int)
  moreover
  have "closure (\<Inter>(rel_interior ` \<F>)) \<subseteq> closure (\<Inter>\<F>)"
    using rel_interior_inter_aux closure_mono[of "\<Inter>(rel_interior ` \<F>)" "\<Inter>\<F>"]
    by auto
  ultimately show ?thesis
    using closure_Int[of \<F>] by blast
qed

lemma closure_Inter_convex_open:
    "(\<And>S::'n::euclidean_space set. S \<in> \<F> \<Longrightarrow> convex S \<and> open S)
        \<Longrightarrow> closure(\<Inter>\<F>) = (if \<Inter>\<F> = {} then {} else \<Inter>(closure ` \<F>))"
  by (simp add: closure_Inter_convex rel_interior_open)

thm convex_closure_interior

lemma empty_interior_subset_hyperplane_aux:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" "0 \<in> S" and empty_int: "interior S = {}"
  shows "\<exists>a b. a\<noteq>0 \<and> S \<subseteq> {x. a \<bullet> x = b}"
proof -
  have False if "\<And>a. a = 0 \<or> (\<forall>b. \<exists>T \<in> S. a \<bullet> T \<noteq> b)"
  proof -
    have rel_int: "rel_interior S \<noteq> {}"
      using assms rel_interior_eq_empty by auto
    moreover 
    have "dim S < dim (UNIV::'a set)"
      by (metis affine_hull_span_0 \<open>0 \<in> S\<close> rel_int dim_UNIV dim_eq_full dim_subset_UNIV empty_int hull_inc order_less_le rel_interior_interior)
    then obtain a where "a \<noteq> 0" and a: "span S \<subseteq> {x. a \<bullet> x = 0}"
      using lowdim_subset_hyperplane by auto
    have "span UNIV = span S"
      by (metis span_base span_not_UNIV_orthogonal that)
    then have "UNIV \<subseteq> affine hull S"
      by (simp add: \<open>0 \<in> S\<close> hull_inc affine_hull_span_0)
    ultimately show False
      using \<open>rel_interior S \<noteq> {}\<close> empty_int rel_interior_interior by blast
  qed
  then show ?thesis
    by blast
qed

lemma empty_interior_subset_hyperplane:
  fixes S :: "'a::euclidean_space set"
  assumes "convex S" and int: "interior S = {}"
  obtains a b where "a \<noteq> 0" "S \<subseteq> {x. a \<bullet> x = b}"
proof (cases "S = {}")
  case True
  then show ?thesis
    using that by blast
next
  case False
  then obtain u where "u \<in> S"
    by blast
  have "\<exists>a b. a \<noteq> 0 \<and> (\<lambda>x. x - u) ` S \<subseteq> {x. a \<bullet> x = b}"
  proof (rule empty_interior_subset_hyperplane_aux)
    show "convex ((\<lambda>x. x - u) ` S)"
      using \<open>convex S\<close> by force
    show "0 \<in> (\<lambda>x. x - u) ` S"
      by (simp add: \<open>u \<in> S\<close>)
    show "interior ((\<lambda>x. x - u) ` S) = {}"
      by (simp add: int interior_translation_subtract)
  qed
  then obtain a b where "a \<noteq> 0" and ab: "(\<lambda>x. x - u) ` S \<subseteq> {x. a \<bullet> x = b}"
    by metis
  then have "S \<subseteq> {x. a \<bullet> x = b + (a \<bullet> u)}"
    using ab by (auto simp: algebra_simps)
  then show ?thesis
    using \<open>a \<noteq> 0\<close> that by auto
qed



lemma aff_dim_psubset:
   "(affine hull S) \<subset> (affine hull T) \<Longrightarrow> aff_dim S < aff_dim T"
  by (metis aff_dim_affine_hull aff_dim_empty aff_dim_subset affine_affine_hull affine_dim_equal order_less_le)

lemma aff_dim_eq_full_gen:
   "S \<subseteq> T \<Longrightarrow> (aff_dim S = aff_dim T \<longleftrightarrow> affine hull S = affine hull T)"
  by (smt (verit, del_insts) aff_dim_affine_hull2 aff_dim_psubset hull_mono psubsetI)

lemma aff_dim_eq_full:
  fixes S :: "'n::euclidean_space set"
  shows "aff_dim S = (DIM('n)) \<longleftrightarrow> affine hull S = UNIV"
  by (metis aff_dim_UNIV aff_dim_affine_hull affine_hull_UNIV)


(*** FOR CONVEX.THY ***)
thm cone_convex_hull
section \<open>Conic sets and conic hull\<close>

definition conic :: "'a::real_vector set \<Rightarrow> bool"
  where "conic S \<equiv> \<forall>x c. x \<in> S \<longrightarrow> 0 \<le> c \<longrightarrow> (c *\<^sub>R x) \<in> S"

lemma conicD: "\<lbrakk>conic S; x \<in> S; 0 \<le> c\<rbrakk> \<Longrightarrow> (c *\<^sub>R x) \<in> S"
  by (meson conic_def)

lemma subspace_imp_conic: "subspace S \<Longrightarrow> conic S"
  by (simp add: conic_def subspace_def)

lemma conic_empty [simp]: "conic {}"
  using conic_def by blast

lemma conic_UNIV: "conic UNIV"
  by (simp add: conic_def)

lemma conic_Inter: "(\<And>S. S \<in> \<F> \<Longrightarrow> conic S) \<Longrightarrow> conic(\<Inter>\<F>)"
  by (simp add: conic_def)

lemma conic_linear_image:
   "\<lbrakk>conic S; linear f\<rbrakk> \<Longrightarrow> conic(f ` S)"
  by (smt (verit) conic_def image_iff linear.scaleR)

lemma conic_linear_image_eq:
   "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> conic (f ` S) \<longleftrightarrow> conic S"
  by (smt (verit) conic_def conic_linear_image inj_image_mem_iff linear_cmul)


lemma conic_mul: "\<lbrakk>conic S; x \<in> S; 0 \<le> c\<rbrakk> \<Longrightarrow> (c *\<^sub>R x) \<in> S"
  using conic_def by blast

lemma conic_conic_hull: "conic(conic hull S)"
  by (metis (no_types, lifting) conic_Inter hull_def mem_Collect_eq)

lemma conic_hull_eq: "(conic hull S = S) \<longleftrightarrow> conic S"
  by (metis conic_conic_hull hull_same)

lemma conic_hull_UNIV [simp]: "conic hull UNIV = UNIV"
  by simp

lemma conic_negations: "conic S \<Longrightarrow> conic (image uminus S)"
  by (auto simp: conic_def image_iff)

lemma conic_span [iff]: "conic(span S)"
  by (simp add: subspace_imp_conic)

lemma conic_hull_explicit:
   "conic hull S = {c *\<^sub>R x| c x. 0 \<le> c \<and> x \<in> S}"
  proof (rule hull_unique)
    show "S \<subseteq> {c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> S}"
      by (metis (no_types) cone_hull_expl hull_subset)
  show "conic {c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> S}"
    using mult_nonneg_nonneg by (force simp: conic_def)
qed (auto simp: conic_def)

lemma conic_hull_as_image:
   "conic hull S = (\<lambda>z. fst z *\<^sub>R snd z) ` ({0..} \<times> S)"
  by (force simp add: conic_hull_explicit)

lemma conic_hull_linear_image:
   "linear f \<Longrightarrow> conic hull f ` S = f ` (conic hull S)"
  by (force simp add: conic_hull_explicit image_iff set_eq_iff linear_scale) 

lemma conic_hull_image_scale:
  assumes "\<And>x. x \<in> S \<Longrightarrow> 0 < c x"
  shows   "conic hull (\<lambda>x. c x *\<^sub>R x) ` S = conic hull S"
proof
  show "conic hull (\<lambda>x. c x *\<^sub>R x) ` S \<subseteq> conic hull S"
  proof (rule hull_minimal)
    show "(\<lambda>x. c x *\<^sub>R x) ` S \<subseteq> conic hull S"
      using assms conic_hull_explicit by fastforce
  qed (simp add: conic_conic_hull)
  show "conic hull S \<subseteq> conic hull (\<lambda>x. c x *\<^sub>R x) ` S"
  proof (rule hull_minimal)
    show "S \<subseteq> conic hull (\<lambda>x. c x *\<^sub>R x) ` S"
    proof clarsimp
      fix x
      assume "x \<in> S"
      then have "x = inverse(c x) *\<^sub>R c x *\<^sub>R x"
        using assms by fastforce
      then show "x \<in> conic hull (\<lambda>x. c x *\<^sub>R x) ` S"
        by (smt (verit, best) \<open>x \<in> S\<close> assms conic_conic_hull conic_mul hull_inc image_eqI inverse_nonpositive_iff_nonpositive)
    qed
  qed (simp add: conic_conic_hull)
qed

lemma convex_conic_hull:
  assumes "convex S"
  shows "convex (conic hull S)"
proof (clarsimp simp add: conic_hull_explicit convex_alt)
  fix c x d y and u :: real
  assume \<section>: "(0::real) \<le> c" "x \<in> S" "(0::real) \<le> d" "y \<in> S" "0 \<le> u" "u \<le> 1"
  show "\<exists>c'' x''. ((1 - u) * c) *\<^sub>R x + (u * d) *\<^sub>R y = c'' *\<^sub>R x'' \<and> 0 \<le> c'' \<and> x'' \<in> S"
  proof (cases "(1 - u) * c = 0")
    case True
    with \<open>0 \<le> d\<close> \<open>y \<in> S\<close>\<open>0 \<le> u\<close>  
    show ?thesis by force
  next
    case False
    define \<xi> where "\<xi> \<equiv> (1 - u) * c + u * d"
    have *: "c * u \<le> c"
      by (simp add: "\<section>" mult_left_le)
    have "\<xi> > 0"
      using False \<section> by (smt (verit, best) \<xi>_def split_mult_pos_le)
    then have **: "c + d * u = \<xi> + c * u"
      by (simp add: \<xi>_def mult.commute right_diff_distrib')
    show ?thesis
    proof (intro exI conjI)
      show "0 \<le> \<xi>"
        using \<open>0 < \<xi>\<close> by auto
      show "((1 - u) * c) *\<^sub>R x + (u * d) *\<^sub>R y = \<xi> *\<^sub>R (((1 - u) * c / \<xi>) *\<^sub>R x + (u * d / \<xi>) *\<^sub>R y)"
        using \<open>\<xi> > 0\<close> by (simp add: algebra_simps diff_divide_distrib)
      show "((1 - u) * c / \<xi>) *\<^sub>R x + (u * d / \<xi>) *\<^sub>R y \<in> S"
        using \<open>0 < \<xi>\<close> 
        by (intro convexD [OF assms]) (auto simp: \<section> field_split_simps * **)
    qed
  qed
qed

lemma conic_halfspace_le: "conic {x. a \<bullet> x \<le> 0}"
  by (auto simp: conic_def mult_le_0_iff)

lemma conic_halfspace_ge: "conic {x. a \<bullet> x \<ge> 0}"
  by (auto simp: conic_def mult_le_0_iff)

lemma conic_hull_empty [simp]: "conic hull {} = {}"
  by (simp add: conic_hull_eq)

lemma conic_contains_0: "conic S \<Longrightarrow> (0 \<in> S \<longleftrightarrow> S \<noteq> {})"
  by (simp add: Convex.cone_def cone_contains_0 conic_def)

lemma conic_hull_eq_empty: "conic hull S = {} \<longleftrightarrow> (S = {})"
  using conic_hull_explicit by fastforce

lemma conic_sums: "\<lbrakk>conic S; conic T\<rbrakk> \<Longrightarrow> conic (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  by (simp add: conic_def) (metis scaleR_right_distrib)

lemma conic_Times: "\<lbrakk>conic S; conic T\<rbrakk> \<Longrightarrow> conic(S \<times> T)"
  by (auto simp: conic_def)

lemma conic_Times_eq:
   "conic(S \<times> T) \<longleftrightarrow> S = {} \<or> T = {} \<or> conic S \<and> conic T" (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (force simp: conic_def)
  show "?rhs \<Longrightarrow> ?lhs"
    by (force simp: conic_Times)
qed

lemma conic_hull_0 [simp]: "conic hull {0} = {0}"
  by (simp add: conic_hull_eq subspace_imp_conic)

lemma conic_hull_contains_0 [simp]: "0 \<in> conic hull S \<longleftrightarrow> (S \<noteq> {})"
  by (simp add: conic_conic_hull conic_contains_0 conic_hull_eq_empty)

lemma conic_hull_eq_sing:
  "conic hull S = {x} \<longleftrightarrow> S = {0} \<and> x = 0"
proof
  show "conic hull S = {x} \<Longrightarrow> S = {0} \<and> x = 0"
    by (metis conic_conic_hull conic_contains_0 conic_def conic_hull_eq hull_inc insert_not_empty singleton_iff)
qed simp

lemma conic_hull_Int_affine_hull:
  assumes "T \<subseteq> S" "0 \<notin> affine hull S"
  shows "(conic hull T) \<inter> (affine hull S) = T"
proof -
  have TaffS: "T \<subseteq> affine hull S"
    using \<open>T \<subseteq> S\<close> hull_subset by fastforce
  moreover
  have "conic hull T \<inter> affine hull S \<subseteq> T"
  proof (clarsimp simp: conic_hull_explicit)
    fix c x
    assume "c *\<^sub>R x \<in> affine hull S"
      and "0 \<le> c"
      and "x \<in> T"
    show "c *\<^sub>R x \<in> T"
    proof (cases "c=1")
      case True
      then show ?thesis
        by (simp add: \<open>x \<in> T\<close>)
    next
      case False
      then have "0 = inverse(1 - c) *\<^sub>R c *\<^sub>R x + (1 - inverse(1 - c)) *\<^sub>R x"
        apply (simp add: algebra_simps)
        by (smt (verit, ccfv_SIG) diff_add_cancel mult.commute real_vector_affinity_eq scaleR_collapse scaleR_scaleR)
      then have "0 \<in> affine hull S"
        by (smt (verit) \<open>c *\<^sub>R x \<in> affine hull S\<close> \<open>x \<in> T\<close> affine_affine_hull TaffS in_mono mem_affine)
      then show ?thesis
        using assms by auto        
    qed
  qed
  ultimately show ?thesis
    by (auto simp: hull_inc)
qed

lemma conic_hull_eq_span_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "0 \<in> rel_interior S"
  shows "conic hull S = span S \<and> conic hull S = affine hull S"
proof -
  obtain \<epsilon> where "\<epsilon>>0" and \<epsilon>: "cball 0 \<epsilon> \<inter> affine hull S \<subseteq> S"
    using assms mem_rel_interior_cball by blast
  have *: "affine hull S = span S"
    by (meson affine_hull_span_0 assms hull_inc mem_rel_interior_cball)
  moreover
  have "conic hull S \<subseteq> span S"
    by (simp add: hull_minimal span_superset)
  moreover
  have "affine hull S \<subseteq> conic hull S"
  proof clarsimp
    fix x
    assume "x \<in> affine hull S"
    show "x \<in> conic hull S"
    proof (cases "x=0")
      case True
      then show ?thesis
        using \<open>x \<in> affine hull S\<close> by auto
    next
      case False
      then have "(\<epsilon> / norm x) *\<^sub>R x \<in> cball 0 \<epsilon> \<inter> affine hull S"
        using \<open>0 < \<epsilon>\<close> \<open>x \<in> affine hull S\<close> * span_mul by fastforce
      then have "(\<epsilon> / norm x) *\<^sub>R x \<in> S"
        by (meson \<epsilon> subsetD)
      then show ?thesis
        apply (simp add: conic_hull_explicit)
        by (smt (verit, del_insts) \<open>0 < \<epsilon>\<close> divide_nonneg_nonneg eq_vector_fraction_iff norm_eq_zero norm_ge_zero)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma conic_hull_eq_span:
  fixes S :: "'a::euclidean_space set"
  assumes "0 \<in> rel_interior S"
  shows "conic hull S = span S"
  by (simp add: assms conic_hull_eq_span_affine_hull)

lemma conic_hull_eq_affine_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "0 \<in> rel_interior S"
  shows "conic hull S = affine hull S"
  using assms conic_hull_eq_span_affine_hull by blast

lemma conic_hull_eq_span_eq:
  fixes S :: "'a::euclidean_space set"
  shows "0 \<in> rel_interior(conic hull S) \<longleftrightarrow> conic hull S = span S" (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (metis conic_hull_eq_span conic_span hull_hull hull_minimal hull_subset span_eq)
  show "?rhs \<Longrightarrow> ?lhs"
  by (metis rel_interior_affine subspace_affine subspace_span)
qed

lemma open_in_subset_relative_interior:
  fixes S :: "'a::euclidean_space set"
  shows "openin (top_of_set (affine hull T)) S \<Longrightarrow> (S \<subseteq> rel_interior T) = (S \<subseteq> T)"
  by (meson order.trans rel_interior_maximal rel_interior_subset)


section\<open>Closure of conic hulls\<close>

proposition closedin_conic_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "compact T" "0 \<notin> T" "T \<subseteq> S"
  shows   "closedin (top_of_set (conic hull S)) (conic hull T)"
proof -
  have **: "compact ({0..} \<times> T \<inter> (\<lambda>z. fst z *\<^sub>R snd z) -` K)" (is "compact ?L")
    if "K \<subseteq> (\<lambda>z. (fst z) *\<^sub>R snd z) ` ({0..} \<times> S)" "compact K" for K
  proof -
    obtain r where "r > 0" and r: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> r"
      by (metis \<open>compact K\<close> bounded_normE compact_imp_bounded)
    show ?thesis
      unfolding compact_eq_bounded_closed
    proof
      have "bounded ({0..r / setdist{0}T} \<times> T)"
        by (simp add: assms(1) bounded_Times compact_imp_bounded)
      moreover have "?L \<subseteq> ({0..r / setdist{0}T} \<times> T)"
      proof clarsimp
        fix a b
        assume "a *\<^sub>R b \<in> K" and "b \<in> T" and "0 \<le> a"
        have "setdist {0} T \<noteq> 0"
          using \<open>b \<in> T\<close> assms compact_imp_closed setdist_eq_0_closed by auto
        then have T0: "setdist {0} T > 0"
          using less_eq_real_def by fastforce
        then have "a * setdist {0} T \<le> r"
          by (smt (verit, ccfv_SIG) \<open>0 \<le> a\<close> \<open>a *\<^sub>R b \<in> K\<close> \<open>b \<in> T\<close> dist_0_norm mult_mono' norm_scaleR r setdist_le_dist singletonI)
        with T0 \<open>r>0\<close> show "a \<le> r / setdist {0} T"
          by (simp add: divide_simps)
      qed
      ultimately show "bounded ?L"
        by (meson bounded_subset)
      show "closed ?L"
      proof (rule continuous_closed_preimage)
        show "continuous_on ({0..} \<times> T) (\<lambda>z. fst z *\<^sub>R snd z)"
          by (intro continuous_intros)
        show "closed ({0::real..} \<times> T)"
          by (simp add: assms(1) closed_Times compact_imp_closed)
        show "closed K"
          by (simp add: compact_imp_closed that(2))
      qed
    qed
  qed
  show ?thesis
    unfolding conic_hull_as_image
  proof (rule proper_map)
    show  "compact ({0..} \<times> T \<inter> (\<lambda>z. fst z *\<^sub>R snd z) -` K)" (is "compact ?L")
      if "K \<subseteq> (\<lambda>z. (fst z) *\<^sub>R snd z) ` ({0..} \<times> S)" "compact K" for K
    proof -
      obtain r where "r > 0" and r: "\<And>x. x \<in> K \<Longrightarrow> norm x \<le> r"
        by (metis \<open>compact K\<close> bounded_normE compact_imp_bounded)
      show ?thesis
        unfolding compact_eq_bounded_closed
      proof
        have "bounded ({0..r / setdist{0}T} \<times> T)"
          by (simp add: assms(1) bounded_Times compact_imp_bounded)
        moreover have "?L \<subseteq> ({0..r / setdist{0}T} \<times> T)"
        proof clarsimp
          fix a b
          assume "a *\<^sub>R b \<in> K" and "b \<in> T" and "0 \<le> a"
          have "setdist {0} T \<noteq> 0"
            using \<open>b \<in> T\<close> assms compact_imp_closed setdist_eq_0_closed by auto
          then have T0: "setdist {0} T > 0"
            using less_eq_real_def by fastforce
          then have "a * setdist {0} T \<le> r"
            by (smt (verit, ccfv_SIG) \<open>0 \<le> a\<close> \<open>a *\<^sub>R b \<in> K\<close> \<open>b \<in> T\<close> dist_0_norm mult_mono' norm_scaleR r setdist_le_dist singletonI)
          with T0 \<open>r>0\<close> show "a \<le> r / setdist {0} T"
            by (simp add: divide_simps)
        qed
        ultimately show "bounded ?L"
          by (meson bounded_subset)
        show "closed ?L"
        proof (rule continuous_closed_preimage)
          show "continuous_on ({0..} \<times> T) (\<lambda>z. fst z *\<^sub>R snd z)"
            by (intro continuous_intros)
          show "closed ({0::real..} \<times> T)"
            by (simp add: assms(1) closed_Times compact_imp_closed)
          show "closed K"
            by (simp add: compact_imp_closed that(2))
        qed
      qed
    qed
    show "(\<lambda>z. fst z *\<^sub>R snd z) ` ({0::real..} \<times> T) \<subseteq> (\<lambda>z. fst z *\<^sub>R snd z) ` ({0..} \<times> S)"
      using \<open>T \<subseteq> S\<close> by force
  qed auto
qed

lemma closed_conic_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "0 \<in> rel_interior S \<or> compact S \<and> 0 \<notin> S"
  shows   "closed(conic hull S)"
  using assms
proof
  assume "0 \<in> rel_interior S"
  then show "closed (conic hull S)"
    by (simp add: conic_hull_eq_span)
next
  assume "compact S \<and> 0 \<notin> S"
  then have "closedin (top_of_set UNIV) (conic hull S)"
    using closedin_conic_hull by force
  then show "closed (conic hull S)"
    by simp
qed 

lemma conic_closure:
  fixes S :: "'a::euclidean_space set"
  shows "conic S \<Longrightarrow> conic(closure S)"
  by (meson Convex.cone_def cone_closure conic_def)

lemma closure_conic_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "0 \<in> rel_interior S \<or> bounded S \<and> ~(0 \<in> closure S)"
  shows   "closure(conic hull S) = conic hull (closure S)"
  using assms
proof
  assume "0 \<in> rel_interior S"
  then show "closure (conic hull S) = conic hull closure S"
    by (metis closed_affine_hull closure_closed closure_same_affine_hull closure_subset conic_hull_eq_affine_hull subsetD subset_rel_interior)
next
  have "\<And>x. x \<in> conic hull closure S \<Longrightarrow> x \<in> closure (conic hull S)"
    by (metis (no_types, opaque_lifting) closure_mono conic_closure conic_conic_hull subset_eq subset_hull)
  moreover 
  assume "bounded S \<and> 0 \<notin> closure S"
  then have "\<And>x. x \<in> closure (conic hull S) \<Longrightarrow> x \<in> conic hull closure S"
    by (metis closed_conic_hull closure_Un_frontier closure_closed closure_mono compact_closure hull_Un_subset le_sup_iff subsetD)
  ultimately show "closure (conic hull S) = conic hull closure S"
    by blast
qed


lemma faces_of_linear_image:
   "\<lbrakk>linear f; inj f\<rbrakk>
        \<Longrightarrow> {T. T face_of (f ` S)} = (image f) ` {T. T face_of S}"
  by (smt (verit) Collect_cong face_of_def face_of_linear_image setcompr_eq_image subset_imageE)

lemma face_of_conic:
  assumes "conic S" "f face_of S"
  shows "conic f"
  unfolding conic_def
proof (intro strip)
  fix x and c::real
  assume "x \<in> f" and "0 \<le> c"
  have f: "\<And>a b x. \<lbrakk>a \<in> S; b \<in> S; x \<in> f; x \<in> open_segment a b\<rbrakk> \<Longrightarrow> a \<in> f \<and> b \<in> f"
    using \<open>f face_of S\<close> face_ofD by blast
  show "c *\<^sub>R x \<in> f"
  proof (cases "x=0 \<or> c=1")
    case True
    then show ?thesis
      using \<open>x \<in> f\<close> by auto
  next
    case False
    with \<open>0 \<le> c\<close> obtain d e where de: "0 \<le> d" "0 \<le> e" "d < 1" "1 < e" "d < e" "(d = c \<or> e = c)"
      apply (simp add: neq_iff)
      by (metis gt_ex less_eq_real_def order_less_le_trans zero_less_one)
    then obtain [simp]: "c *\<^sub>R x \<in> S" "e *\<^sub>R x \<in> S" \<open>x \<in> S\<close>
      using \<open>x \<in> f\<close> assms conic_mul face_of_imp_subset by blast
    have "x \<in> open_segment (d *\<^sub>R x) (e *\<^sub>R x)" if "c *\<^sub>R x \<notin> f"
      using de False that
      apply (simp add: in_segment)
      apply (rule_tac x="(1 - d) / (e - d)" in exI)
      apply (simp add: field_simps)
      by (smt (verit, del_insts) add_divide_distrib divide_self scaleR_collapse)
    then show ?thesis
      using \<open>conic S\<close> f [of "d *\<^sub>R x" "e *\<^sub>R x" x] de \<open>x \<in> f\<close>
      by (force simp add: conic_def in_segment)
  qed
qed

thm extreme_point_of_convex_hull_insert
lemma extreme_point_of_conic:
  assumes "conic S" and x: "x extreme_point_of S"
  shows "x = 0"
proof -
  have "{x} face_of S"
    by (simp add: face_of_singleton x)
  then have "conic{x}"
    using assms(1) face_of_conic by blast
  then show ?thesis
    by (force simp add: conic_def)
qed

section \<open>Convex cones and corresponding hulls\<close>

definition convex_cone :: "'a::real_vector set \<Rightarrow> bool"
  where "convex_cone \<equiv> \<lambda>S. S \<noteq> {} \<and> convex S \<and> conic S"

lemma convex_cone_iff:
   "convex_cone S \<longleftrightarrow>
        0 \<in> S \<and> (\<forall>x \<in> S. \<forall>y \<in> S. x + y \<in> S) \<and> (\<forall>x \<in> S. \<forall>c\<ge>0. c *\<^sub>R x \<in> S)"
    by (metis Convex.cone_def conic_contains_0 conic_def convex_cone convex_cone_def)

lemma convex_cone_add: "\<lbrakk>convex_cone S; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x+y \<in> S"
  by (simp add: convex_cone_iff)

lemma convex_cone_scaleR: "\<lbrakk>convex_cone S; 0 \<le> c; x \<in> S\<rbrakk> \<Longrightarrow> c *\<^sub>R x \<in> S"
  by (simp add: convex_cone_iff)

lemma convex_cone_nonempty: "convex_cone S \<Longrightarrow> S \<noteq> {}"
  by (simp add: convex_cone_def)

lemma convex_cone_linear_image:
   "convex_cone S \<and> linear f \<Longrightarrow> convex_cone(f ` S)"
  by (simp add: conic_linear_image convex_cone_def convex_linear_image)

lemma convex_cone_linear_image_eq:
   "\<lbrakk>linear f; inj f\<rbrakk> \<Longrightarrow> (convex_cone(f ` S) \<longleftrightarrow> convex_cone S)"
  by (simp add: conic_linear_image_eq convex_cone_def)

lemma convex_cone_halfspace_ge: "convex_cone {x. a \<bullet> x \<ge> 0}"
  by (simp add: convex_cone_iff inner_simps(2))

lemma convex_cone_halfspace_le: "convex_cone {x. a \<bullet> x \<le> 0}"
  by (simp add: convex_cone_iff inner_right_distrib mult_nonneg_nonpos)

lemma convex_cone_contains_0: "convex_cone S \<Longrightarrow> 0 \<in> S"
  using convex_cone_iff by blast

lemma convex_cone_Inter:
   "(\<And>S. S \<in> f \<Longrightarrow> convex_cone S) \<Longrightarrow> convex_cone(\<Inter> f)"
  by (simp add: convex_cone_iff)

lemma convex_cone_convex_cone_hull: "convex_cone(convex_cone hull S)"
  by (metis (no_types, lifting) convex_cone_Inter hull_def mem_Collect_eq)

lemma convex_convex_cone_hull: "convex(convex_cone hull S)"
  by (meson convex_cone_convex_cone_hull convex_cone_def)

lemma conic_convex_cone_hull: "conic(convex_cone hull S)"
  by (metis convex_cone_convex_cone_hull convex_cone_def)

lemma convex_cone_hull_nonempty: "convex_cone hull S \<noteq> {}"
  by (simp add: convex_cone_convex_cone_hull convex_cone_nonempty)

lemma convex_cone_hull_contains_0: "0 \<in> convex_cone hull S"
  by (simp add: convex_cone_contains_0 convex_cone_convex_cone_hull)

lemma convex_cone_hull_add:
   "\<lbrakk>x \<in> convex_cone hull S; y \<in> convex_cone hull S\<rbrakk> \<Longrightarrow> x + y \<in> convex_cone hull S"
  by (simp add: convex_cone_add convex_cone_convex_cone_hull)

lemma convex_cone_hull_mul:
   "\<lbrakk>x \<in> convex_cone hull S; 0 \<le> c\<rbrakk> \<Longrightarrow> (c *\<^sub>R x) \<in> convex_cone hull S"
  by (simp add: conic_convex_cone_hull conic_mul)

thm convex_sums
lemma convex_cone_sums:
   "\<lbrakk>convex_cone S; convex_cone T\<rbrakk> \<Longrightarrow> convex_cone (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  by (simp add: convex_cone_def conic_sums convex_sums)

lemma convex_cone_Times:
   "\<lbrakk>convex_cone S; convex_cone T\<rbrakk> \<Longrightarrow> convex_cone(S \<times> T)"
  by (simp add: conic_Times convex_Times convex_cone_def)

lemma convex_cone_Times_D1: "convex_cone (S \<times> T) \<Longrightarrow> convex_cone S"
  by (metis Times_empty conic_Times_eq convex_cone_def convex_convex_hull convex_hull_Times hull_same times_eq_iff)

lemma convex_cone_Times_eq:
   "convex_cone(S \<times> T) \<longleftrightarrow> convex_cone S \<and> convex_cone T" 
proof (cases "S={} \<or> T={}")
  case True
  then show ?thesis 
    by (auto dest: convex_cone_nonempty)
next
  case False
  then have "convex_cone (S \<times> T) \<Longrightarrow> convex_cone T"
    by (metis conic_Times_eq convex_cone_def convex_convex_hull convex_hull_Times hull_same times_eq_iff)
  then show ?thesis
    using convex_cone_Times convex_cone_Times_D1 by blast 
qed


lemma convex_cone_hull_Un:
  "convex_cone hull(S \<union> T) = (\<Union>x \<in> convex_cone hull S. \<Union>y \<in> convex_cone hull T. {x + y})"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof (rule hull_minimal)
    show "S \<union> T \<subseteq> (\<Union>x\<in>convex_cone hull S. \<Union>y\<in>convex_cone hull T. {x + y})"
      apply (clarsimp simp: subset_iff)
      by (metis add_0 convex_cone_hull_contains_0 group_cancel.rule0 hull_inc)
    show "convex_cone (\<Union>x\<in>convex_cone hull S. \<Union>y\<in>convex_cone hull T. {x + y})"
      by (simp add: convex_cone_convex_cone_hull convex_cone_sums)
  qed
next
  show "?rhs \<subseteq> ?lhs"
    by clarify (metis convex_cone_hull_add hull_mono le_sup_iff subsetD subsetI)
qed

lemma convex_cone_singleton [iff]: "convex_cone {0}"
  by (simp add: convex_cone_iff)

lemma convex_hull_subset_convex_cone_hull:
   "convex hull S \<subseteq> convex_cone hull S"
  by (simp add: convex_convex_cone_hull hull_minimal hull_subset)


lemma conic_hull_subset_convex_cone_hull:
   "conic hull S \<subseteq> convex_cone hull S"
  by (simp add: conic_convex_cone_hull hull_minimal hull_subset)


lemma convex_cone_hull_separate_nonempty:
  assumes "S \<noteq> {}"
  shows "convex_cone hull S = conic hull (convex hull S)"   (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (simp add: assms conic_conic_hull conic_hull_eq_empty convex_cone_def convex_conic_hull hull_inc hull_minimal subsetI)
  show "?rhs \<subseteq> ?lhs"
    by (simp add: conic_convex_cone_hull convex_hull_subset_convex_cone_hull subset_hull)
qed

lemma convex_cone_hull_empty [simp]: "convex_cone hull {} = {0}"
  by (metis convex_cone_hull_contains_0 convex_cone_singleton hull_redundant hull_same)

lemma convex_cone_hull_separate:
   "convex_cone hull S = insert 0 (conic hull (convex hull S))"
  by (cases "S={}") (simp_all add: convex_cone_hull_separate_nonempty insert_absorb)

lemma convex_cone_hull_convex_hull_nonempty:
   "S \<noteq> {} \<Longrightarrow> convex_cone hull S = (\<Union>x \<in> convex hull S. \<Union>c\<in>{0..}. {c *\<^sub>R x})"
  by (force simp: convex_cone_hull_separate_nonempty conic_hull_as_image)


lemma convex_cone_hull_convex_hull:
   "convex_cone hull S = insert 0 (\<Union>x \<in> convex hull S. \<Union>c\<in>{0..}. {c *\<^sub>R x})"
  by (force simp add: convex_cone_hull_separate conic_hull_as_image)

lemma convex_cone_hull_linear_image:
   "linear f \<Longrightarrow> convex_cone hull (f ` S) = image f (convex_cone hull S)"
  by (metis (no_types, lifting) conic_hull_linear_image convex_cone_hull_separate convex_hull_linear_image image_insert linear_0)

lemma subspace_imp_convex_cone: "subspace S \<Longrightarrow> convex_cone S"
  by (simp add: convex_cone_iff subspace_def)

lemma convex_cone_span: "convex_cone(span S)"
  by (simp add: subspace_imp_convex_cone)

lemma convex_cone_negations:
   "convex_cone S \<Longrightarrow> convex_cone (image uminus S)"
  by (simp add: convex_cone_linear_image module_hom_uminus)

lemma subspace_convex_cone_symmetric:
   "subspace S \<longleftrightarrow> convex_cone S \<and> (\<forall>x \<in> S. -x \<in> S)"
  by (smt (verit) convex_cone_iff scaleR_left.minus subspace_def subspace_neg)


section \<open> Finitely generated cone is polyhedral, and hence closed\<close>

proposition polyhedron_convex_cone_hull:
  fixes S :: "'a::euclidean_space set"
  assumes "finite S"
  shows "polyhedron(convex_cone hull S)"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (simp add: affine_imp_polyhedron)
next
  case False
  then have "polyhedron(convex hull (insert 0 S))"
    by (simp add: assms polyhedron_convex_hull)
  then obtain F a b where "finite F" 
         and F: "convex hull (insert 0 S) = \<Inter> F" 
         and ab: "\<And>h. h \<in> F \<Longrightarrow> a h \<noteq> 0 \<and> h = {x. a h \<bullet> x \<le> b h}"
    unfolding polyhedron_def by metis
  then have "F \<noteq> {}"
    by (metis bounded_convex_hull finite_imp_bounded Inf_empty assms finite_insert not_bounded_UNIV)
  show ?thesis
    unfolding polyhedron_def
  proof (intro exI conjI)
    show "convex_cone hull S = \<Inter> {h \<in> F. b h = 0}" (is "?lhs = ?rhs")
    proof
      show "?lhs \<subseteq> ?rhs"
      proof (rule hull_minimal)
        show "S \<subseteq> \<Inter> {h \<in> F. b h = 0}"
          by (smt (verit, best) F InterE InterI hull_subset insert_subset mem_Collect_eq subset_eq)
        have "\<And>S. \<lbrakk>S \<in> F; b S = 0\<rbrakk> \<Longrightarrow> convex_cone S"
          by (metis ab convex_cone_halfspace_le)
        then show "convex_cone (\<Inter> {h \<in> F. b h = 0})"
          by (force intro: convex_cone_Inter)
      qed
      have "x \<in> convex_cone hull S"
        if x: "\<And>h. \<lbrakk>h \<in> F; b h = 0\<rbrakk> \<Longrightarrow> x \<in> h" for x
      proof -
        have "\<exists>t. 0 < t \<and> (t *\<^sub>R x) \<in> h" if "h \<in> F" for h
        proof (cases "b h = 0")
          case True
          then show ?thesis
            by (metis x linordered_field_no_ub mult_1 scaleR_one that zero_less_mult_iff)
        next
          case False
          then have "b h > 0"
            by (smt (verit, del_insts) F InterE ab hull_subset inner_zero_right insert_subset mem_Collect_eq that)
          then have "0 \<in> interior {x. a h \<bullet> x \<le> b h}"
            by (simp add: ab that)
          then have "0 \<in> interior h"
            using ab that by auto
          then obtain \<epsilon> where "0 < \<epsilon>" and \<epsilon>: "ball 0 \<epsilon> \<subseteq> h"
            using mem_interior by blast
          show ?thesis
          proof (cases "x=0")
            case True
            then show ?thesis
              using \<epsilon> \<open>0 < \<epsilon>\<close> by auto
          next
            case False
            with \<epsilon> \<open>0 < \<epsilon>\<close> show ?thesis
              by (rule_tac x="\<epsilon> / (2 * norm x)" in exI) (auto simp add: divide_simps)
          qed
        qed
        then obtain t where t: "\<And>h. h \<in> F \<Longrightarrow> 0 < t h \<and> (t h *\<^sub>R x) \<in> h" 
          by metis
        then have "Inf (t ` F) *\<^sub>R x /\<^sub>R Inf (t ` F) = x"
          by (smt (verit) \<open>F \<noteq> {}\<close> \<open>finite F\<close> divideR_right finite_imageI finite_less_Inf_iff image_iff image_is_empty)
        moreover have "Inf (t ` F) *\<^sub>R x /\<^sub>R Inf (t ` F) \<in> convex_cone hull S"
        proof (rule conicD [OF conic_convex_cone_hull])
          have "Inf (t ` F) *\<^sub>R x \<in> \<Inter> F"
          proof clarify
            fix h
            assume  "h \<in> F"
            have eq: "Inf (t ` F) *\<^sub>R x = (1 - Inf(t ` F) / t h) *\<^sub>R 0 + (Inf(t ` F) / t h) *\<^sub>R t h *\<^sub>R x"
              using \<open>h \<in> F\<close> t by force
            show "Inf (t ` F) *\<^sub>R x \<in> h"
              unfolding eq
            proof (rule convexD_alt)
              have "h = {x. a h \<bullet> x \<le> b h}"
                by (simp add: \<open>h \<in> F\<close> ab)
              then show "convex h"
                by (metis convex_halfspace_le)
              show "0 \<in> h"
                by (metis F InterE \<open>h \<in> F\<close> hull_subset insertCI subsetD)
              show "t h *\<^sub>R x \<in> h"
                by (simp add: \<open>h \<in> F\<close> t)
              show "0 \<le> Inf (t ` F) / t h"
                by (metis \<open>F \<noteq> {}\<close> \<open>h \<in> F\<close> cINF_greatest divide_nonneg_pos less_eq_real_def t)
              show "Inf (t ` F) / t h \<le> 1"
                by (simp add: \<open>finite F\<close> \<open>h \<in> F\<close> cInf_le_finite t)
            qed
          qed
          moreover have "convex hull (insert 0 S) \<subseteq> convex_cone hull S"
            by (simp add: convex_cone_hull_contains_0 convex_convex_cone_hull hull_minimal hull_subset)
          ultimately show "Inf (t ` F) *\<^sub>R x \<in> convex_cone hull S"
            using F by blast
          show "0 \<le> inverse (Inf (t ` F))"
            using t by (simp add: \<open>F \<noteq> {}\<close> \<open>finite F\<close> finite_less_Inf_iff less_eq_real_def)
        qed
        ultimately show ?thesis
          by auto
      qed
      then show "?rhs \<subseteq> ?lhs"
        by auto
    qed
    show "\<forall>h\<in>{h \<in> F. b h = 0}. \<exists>a b. a \<noteq> 0 \<and> h = {x. a \<bullet> x \<le> b}"
      using ab by blast
  qed (auto simp: \<open>finite F\<close>)
qed


lemma closed_convex_cone_hull:
  fixes S :: "'a::euclidean_space set"
  shows "finite S \<Longrightarrow> closed(convex_cone hull S)"
  by (simp add: polyhedron_convex_cone_hull polyhedron_imp_closed)

lemma polyhedron_convex_cone_hull_polytope:
  fixes S :: "'a::euclidean_space set"
  shows "polytope S \<Longrightarrow> polyhedron(convex_cone hull S)"
  by (metis convex_cone_hull_separate hull_hull polyhedron_convex_cone_hull polytope_def)

lemma polyhedron_conic_hull_polytope:
  fixes S :: "'a::euclidean_space set"
  shows "polytope S \<Longrightarrow> polyhedron(conic hull S)"
  by (metis conic_hull_eq_empty convex_cone_hull_separate_nonempty hull_hull polyhedron_convex_cone_hull_polytope polyhedron_empty polytope_def)

lemma closed_conic_hull_strong:
  fixes S :: "'a::euclidean_space set"
  shows 
   "0 \<in> rel_interior S \<or> polytope S \<or> compact S \<and> ~(0 \<in> S)
    \<Longrightarrow> closed(conic hull S)"
  using closed_conic_hull polyhedron_conic_hull_polytope polyhedron_imp_closed by blast


(*** END OF EXTRAS ***)


text\<open> Interpret which "side" of a hyperplane a point is on.                     \<close>

definition hyperplane_side
  where "hyperplane_side \<equiv> \<lambda>(a,b). \<lambda>x. sgn (a \<bullet> x - b)"

text\<open> Equivalence relation imposed by a hyperplane arrangement.                 \<close>

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

section\<open> Cells of a hyperplane arrangement\<close>

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

section\<open> A cell complex is considered to be a union of such cells\<close>

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
  define U where "U \<equiv> \<Union> {T \<in> {\<Inter>(g ` \<C>) |g. \<forall>S\<in>\<C>. g S \<in> \<F> S}. T \<noteq> {}}"
  have "\<Inter>\<C> = \<Union>{\<Inter>(g ` \<C>) |g. \<forall>S\<in>\<C>. g S \<in> \<F> S}"
    using False \<F> unfolding Inter_over_Union [symmetric]
    by blast
  also have "\<dots> = U"
    unfolding U_def
    by blast
  finally have "\<Inter>\<C> = U" .
  have "hyperplane_cellcomplex A U"
    using False \<F> unfolding U_def
    apply (intro hyperplane_cellcomplex_Union hyperplane_cell_cellcomplex)
    by (auto simp: intro!: hyperplane_cell_Inter)
  then show ?thesis
     by (simp add: \<open>\<Inter>\<C> = U\<close>)
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


section\<open> Euler characteristic\<close>


definition Euler_characteristic :: "('a::euclidean_space \<times> real) set \<Rightarrow> 'a set \<Rightarrow> int"
  where "Euler_characteristic A S \<equiv>
        (\<Sum>C | hyperplane_cell A C \<and> C \<subseteq> S. (-1) ^ nat (aff_dim C))"

lemma Euler_characteristic_empty [simp]: "Euler_characteristic A {} = 0"
  by (simp add: sum.neutral Euler_characteristic_def)

lemma Euler_characteristic_cell_Union:
  assumes "\<And>C. C \<in> \<C> \<Longrightarrow> hyperplane_cell A C"
  shows "Euler_characteristic A (\<Union> \<C>) = (\<Sum>C\<in>\<C>. (- 1) ^ nat (aff_dim C))"
proof -
  have "\<And>x. \<lbrakk>hyperplane_cell A x; x \<subseteq> \<Union> \<C>\<rbrakk> \<Longrightarrow> x \<in> \<C>"
    by (metis assms disjnt_Union1 disjnt_subset1 disjoint_hyperplane_cells_eq)
  then have "{C. hyperplane_cell A C \<and> C \<subseteq> \<Union> \<C>} = \<C>"
    by (auto simp add: assms)
  then show ?thesis
    by (auto simp: Euler_characteristic_def)
qed

lemma Euler_characteristic_cell:
   "hyperplane_cell A C \<Longrightarrow> Euler_characteristic A C = (-1) ^ (nat(aff_dim C))"
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
        (\<Sum>d = 0..DIM('n). (-1) ^ d * int (card {C. hyperplane_cell A C \<and> C \<subseteq> S \<and> aff_dim C = int d}))"
        (is "_ = ?rhs")
proof -
  have "\<And>T. \<lbrakk>hyperplane_cell A T; T \<subseteq> S\<rbrakk> \<Longrightarrow> aff_dim T \<in> {0..DIM('n)}"
    by (metis atLeastAtMost_iff nle_le order.strict_iff_not aff_dim_negative_iff 
        nonempty_hyperplane_cell aff_dim_le_DIM)
  then have *: "aff_dim ` {C. hyperplane_cell A C \<and> C \<subseteq> S} \<subseteq> int ` {0..DIM('n)}"
    by (auto simp: image_int_atLeastAtMost)
  have "Euler_characteristic A  S = (\<Sum>y\<in>int ` {0..DIM('n)}.
       \<Sum>C\<in>{x. hyperplane_cell A x \<and> x \<subseteq> S \<and> aff_dim x = y}. (- 1) ^ nat y) "
    using sum.group [of "{C. hyperplane_cell A C \<and> C \<subseteq> S}" "int ` {0..DIM('n)}" aff_dim "\<lambda>C. (-1::int) ^ nat(aff_dim C)", symmetric]
    by (simp add: assms Euler_characteristic_def finite_restrict_hyperplane_cells *)
  also have "\<dots> = ?rhs"
    by (simp add: sum.reindex mult_of_nat_commute)
  finally show ?thesis .
qed


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
      define r where "r \<equiv> (\<Sum>D\<in>{C' \<inter> C |C'. hyperplane_cell {(a, b)} C' \<and> C' \<inter> C \<noteq> {}}. (-1::int) ^ nat (aff_dim D))"
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
      also have "\<dots> = (-1) ^ nat(aff_dim C)"
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
          also have "\<dots> = (-1) ^ nat(aff_dim C)"
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
          also have "\<dots> = (-1) ^ nat (aff_dim (C \<inter> {x. a \<bullet> x = b})) 
                         + (-1) ^ nat (aff_dim (C \<inter> {x. b < a \<bullet> x})) 
                         + (-1) ^ nat (aff_dim (C \<inter> {x. a \<bullet> x < b}))"
            using hyperplane_cells_distinct_lemma [of a b] Cab
            by (auto simp add: sum.insert_if Int_commute Int_left_commute)
          also have "\<dots> = (- 1) ^ nat (aff_dim C)"
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
  fixes S :: "'n::euclidean_space set"
  assumes "polyhedron S" "conic S" and intS: "interior S \<noteq> {}" and "S \<noteq> UNIV"
  shows "(\<Sum>d = 0..DIM('n). (- 1) ^ d * int (card {f. f face_of S \<and> aff_dim f = int d})) = 0"  (is "?lhs = 0")
proof -
  have [simp]: "affine hull S = UNIV"
    by (simp add: affine_hull_nonempty_interior intS)
  with \<open>polyhedron S\<close>
  obtain H where "finite H"
    and Seq: "S = \<Inter>H"
    and Hex: "\<And>h. h\<in>H \<Longrightarrow> \<exists>a b. a\<noteq>0 \<and> h = {x. a \<bullet> x \<le> b}"
    and Hsub: "\<And>\<G>. \<G> \<subset> H \<Longrightarrow> S \<subset> \<Inter>\<G>"
    by (fastforce simp add: polyhedron_Int_affine_minimal)
  have "0 \<in> S"
    using assms(2) conic_contains_0 intS interior_empty by blast
  have *: "\<exists>a. a\<noteq>0 \<and> h = {x. a \<bullet> x \<le> 0}" if "h \<in> H" for h
  proof -
    obtain a b where "a\<noteq>0" and ab: "h = {x. a \<bullet> x \<le> b}"
      using Hex [OF \<open>h \<in> H\<close>] by blast
    have "0 \<in> \<Inter>H"
      using Seq \<open>0 \<in> S\<close> by force
    then have "0 \<in> h"
      using that by blast
    consider "b=0" | "b < 0" | "b > 0"
      by linarith
    then
    show ?thesis
    proof cases
      case 1
      then show ?thesis
        using \<open>a \<noteq> 0\<close> ab by blast
    next
      case 2
      then show ?thesis
        using \<open>0 \<in> h\<close> ab by auto
    next
      case 3
      have "S \<subset> \<Inter>(H - {h})"
        using Hsub [of "H - {h}"] that by auto
      then obtain x where x: "x \<in> \<Inter>(H - {h})" and "x \<notin> S"
        by auto
      define \<epsilon> where "\<epsilon> \<equiv> min (1/2) (b / (a \<bullet> x))"
      have "b < a \<bullet> x"
        using \<open>x \<notin> S\<close> ab x by (fastforce simp add: \<open>S = \<Inter>H\<close>)
      with 3 have "0 < a \<bullet> x"
        by auto
      with 3 have "0 < \<epsilon>"
        by (simp add: \<epsilon>_def)
      have "\<epsilon> < 1"
        using \<epsilon>_def by linarith
      have "\<epsilon> * (a \<bullet> x) \<le> b"
        unfolding \<epsilon>_def using \<open>0 < a \<bullet> x\<close> pos_le_divide_eq by fastforce
      have "x = inverse \<epsilon> *\<^sub>R \<epsilon> *\<^sub>R x"
        using \<open>0 < \<epsilon>\<close> by force
      moreover 
      have "\<epsilon> *\<^sub>R x \<in> S"
      proof -
        have  "\<epsilon> *\<^sub>R x \<in> h"
          by (simp add: \<open>\<epsilon> * (a \<bullet> x) \<le> b\<close> ab)
        moreover have "\<epsilon> *\<^sub>R x \<in> \<Inter>(H - {h})"
        proof -
          have "\<epsilon> *\<^sub>R x \<in> k" if "x \<in> k" "k \<in> H" "k \<noteq> h" for k
          proof -
            obtain a' b' where "a'\<noteq>0" "k = {x. a' \<bullet> x \<le> b'}"
              using Hex \<open>k \<in> H\<close> by blast
            have "(0 \<le> a' \<bullet> x \<Longrightarrow> a' \<bullet> \<epsilon> *\<^sub>R x \<le> a' \<bullet> x)"
              by (metis \<open>\<epsilon> < 1\<close> inner_scaleR_right order_less_le pth_1 real_scaleR_def scaleR_right_mono)
            moreover have "(0 \<le> -(a' \<bullet> x) \<Longrightarrow> 0 \<le> -(a' \<bullet> \<epsilon> *\<^sub>R x)) "
              using \<open>0 < \<epsilon>\<close> mult_le_0_iff order_less_imp_le by auto
            ultimately
            have "a' \<bullet> x \<le> b' \<Longrightarrow> a' \<bullet> \<epsilon> *\<^sub>R x \<le> b'"
              by (smt (verit) InterD \<open>0 \<in> \<Inter>H\<close> \<open>k = {x. a' \<bullet> x \<le> b'}\<close> inner_zero_right mem_Collect_eq that(2))
            then show ?thesis
              using \<open>k = {x. a' \<bullet> x \<le> b'}\<close> \<open>x \<in> k\<close> by fastforce
          qed
          with x show ?thesis
            by blast
        qed
        ultimately show ?thesis
          using Seq by blast
      qed
      with \<open>conic S\<close> have "inverse \<epsilon> *\<^sub>R \<epsilon> *\<^sub>R x \<in> S"
        by (meson \<open>0 < \<epsilon>\<close> conic_def inverse_nonnegative_iff_nonnegative order_less_le)
      ultimately show ?thesis
        using \<open>x \<notin> S\<close> by presburger
    qed
  qed
  then obtain fa where fa: "\<And>h. h \<in> H \<Longrightarrow> fa h \<noteq> 0 \<and> h = {x. fa h \<bullet> x \<le> 0}"
    by metis
  define fa_le_0 where "fa_le_0 \<equiv> \<lambda>h. {x. fa h \<bullet> x \<le> 0}"
  have fa': "\<And>h. h \<in> H \<Longrightarrow> fa_le_0 h = h"
    using fa fa_le_0_def by blast
  define A where "A \<equiv> (\<lambda>h. (fa h,0::real)) ` H"
  have "finite A"
    using \<open>finite H\<close> by (simp add: A_def)
  then have "?lhs = Euler_characteristic A S"
  proof -
    have [simp]: "card {f. f face_of S \<and> aff_dim f = int d} = card {C. hyperplane_cell A C \<and> C \<subseteq> S \<and> aff_dim C = int d}"
      if "finite A" and "d \<le> card (Basis::'n set)"
      for d :: nat
    proof (rule bij_betw_same_card)
      have "hyperplane_cell A (rel_interior f) \<and> rel_interior f \<subseteq> S
          \<and> aff_dim (rel_interior f) = d \<and> closure (rel_interior f) = f" 
        if "f face_of S" "aff_dim f = d" for f
      proof -
        have 1: "closure(rel_interior f) = f" 
        proof -
          have "closure(rel_interior f) = closure f"
            by (meson convex_closure_rel_interior face_of_imp_convex that(1))
          also have "\<dots> = f"
            by (meson assms(1) closure_closed face_of_polyhedron_polyhedron polyhedron_imp_closed that(1))
          finally show ?thesis .
        qed
        then have 2: "aff_dim (rel_interior f) = d"
          by (metis closure_aff_dim that(2))
        have "f \<noteq> {}"
          using aff_dim_negative_iff [of f] by (simp add: that(2))
        obtain J0 where "J0 \<subseteq> H" and J0: "f = \<Inter> (fa_le_0 ` H) \<inter> (\<Inter>h \<in> J0. {x. fa h \<bullet> x = 0})"
        proof (cases "f = S")
          case True
          have "S = \<Inter> (fa_le_0 ` H)"
            using Seq fa by (auto simp: fa_le_0_def)
          then show ?thesis
            using True that by blast
        next
          case False
          have fexp: "f = \<Inter>{S \<inter> {x. fa h \<bullet> x = 0} | h. h \<in> H \<and> f \<subseteq> S \<inter> {x. fa h \<bullet> x = 0}}"
            proof (rule face_of_polyhedron_explicit)
              show "S = affine hull S \<inter> \<Inter> H"
                by (simp add: Seq hull_subset inf.absorb2)
            qed (auto simp: False \<open>f \<noteq> {}\<close> \<open>f face_of S\<close> \<open>finite H\<close> Hsub fa)
          show ?thesis
          proof
            have *: "\<And>x h. \<lbrakk>x \<in> f; h \<in> H\<rbrakk> \<Longrightarrow> fa h \<bullet> x \<le> 0"
              using Seq fa face_of_imp_subset \<open>f face_of S\<close> by fastforce
            show "f = \<Inter> (fa_le_0 ` H) \<inter> (\<Inter>h \<in> {h \<in> H.  f \<subseteq> S \<inter> {x. fa h \<bullet> x = 0}}. {x. fa h \<bullet> x = 0})"
              apply (auto simp: * fa_le_0_def)
              apply (subst fexp)
              apply clarsimp
              by (metis Inter_iff Seq fa mem_Collect_eq)
          qed blast
        qed 
        define H' where "H' = (\<lambda>h. {x. -(fa h) \<bullet> x \<le> 0}) ` H"
        have "\<exists>J. finite J \<and> J \<subseteq> H \<union> H' \<and> f = affine hull f \<inter> \<Inter>J"
        proof (intro exI conjI)
          let ?J = "H \<union> image (\<lambda>h. {x. -(fa h) \<bullet> x \<le> 0}) J0"
          show "finite (?J::'n set set)"
            using \<open>J0 \<subseteq> H\<close> \<open>finite H\<close> finite_subset by fastforce
          show "?J \<subseteq> H \<union> H'"
            using \<open>J0 \<subseteq> H\<close> by (auto simp: H'_def)
          have "f = \<Inter>?J"
          proof
            show "f \<subseteq> \<Inter>?J"
              unfolding J0 by (auto simp: fa')
            have "\<And>x j. \<lbrakk>j \<in> J0; \<forall>h\<in>H. x \<in> h; \<forall>j\<in>J0. 0 \<le> fa j \<bullet> x\<rbrakk> \<Longrightarrow> fa j \<bullet> x = 0"
              by (metis \<open>J0 \<subseteq> H\<close> fa in_mono inf.absorb2 inf.orderE mem_Collect_eq)
            then show "\<Inter>?J \<subseteq> f"
              unfolding J0 by (auto simp: fa')
          qed
          then show "f = affine hull f \<inter> \<Inter>?J"
            by (simp add: Int_absorb1 hull_subset)
        qed 
        then have **: "\<exists>n J. finite J \<and> card J = n \<and> J \<subseteq> H \<union> H' \<and> f = affine hull f \<inter> \<Inter>J"
          by blast
        obtain J nJ where J: "finite J" "card J = nJ" "J \<subseteq> H \<union> H'" and feq: "f = affine hull f \<inter> \<Inter>J"
          and minJ:  "\<And>m J'. \<lbrakk>finite J'; m < nJ; card J' = m; J' \<subseteq> H \<union> H'\<rbrakk> \<Longrightarrow> f \<noteq> affine hull f \<inter> \<Inter>J'"
          using exists_least_iff [THEN iffD1, OF **] by metis
        have FF: "f \<subset> (affine hull f \<inter> \<Inter>J')" if "J' \<subset> J" for J'
        proof -
          have "f \<noteq> affine hull f \<inter> \<Inter>J'"
            using minJ
            by (metis J finite_subset psubset_card_mono psubset_imp_subset psubset_subset_trans that)
          then show ?thesis
            by (metis Int_subset_iff Inter_Un_distrib feq hull_subset inf_sup_ord(2) psubsetI sup.absorb4 that)
        qed
        have "\<exists>a. {x. a \<bullet> x \<le> 0} = h \<and> (h \<in> H \<and> a = fa h \<or> (\<exists>h'. h' \<in> H \<and> a = -(fa h')))" 
          if "h \<in> J" for h
        proof -
          have "h \<in> H \<union> H'"
            using \<open>J \<subseteq> H \<union> H'\<close> that by blast
          then show ?thesis
          proof
            show ?thesis if "h \<in> H"
              using that fa by blast
          next
            assume "h \<in> H'"
            then obtain h' where "h' \<in> H" "h = {x. 0 \<le> fa h' \<bullet> x}"
              by (auto simp: H'_def)
            then show ?thesis
              by (force simp add: intro!: exI[where x="- (fa h')"])
          qed
        qed
        then obtain ga 
          where ga_h: "\<And>h. h \<in> J \<Longrightarrow> h = {x. ga h \<bullet> x \<le> 0}" 
            and ga_fa: "\<And>h. h \<in> J \<Longrightarrow> h \<in> H \<and> ga h = fa h \<or> (\<exists>h'. h' \<in> H \<and> ga h = -(fa h'))" 
          by metis
        have 3: "hyperplane_cell A (rel_interior f)"
        proof -
          have D: "rel_interior f = {x \<in> f. \<forall>h\<in>J. ga h \<bullet> x < 0}"
          proof (rule rel_interior_polyhedron_explicit [OF \<open>finite J\<close> feq])
            show "ga h \<noteq> 0 \<and> h = {x. ga h \<bullet> x \<le> 0}" if "h \<in> J" for h
              using that fa ga_fa ga_h by force
          qed (auto simp: FF)
          have H: "h \<in> H \<and> ga h = fa h" if "h \<in> J" for h
          proof -
            obtain z where z: "z \<in> rel_interior f"
              using "1" \<open>f \<noteq> {}\<close> by force
            then have "z \<in> f \<and> z \<in> S"
              using D \<open>f face_of S\<close> face_of_imp_subset by blast
            then show ?thesis
              using ga_fa [OF that]
              by (smt (verit, del_insts) D InterE Seq fa inner_minus_left mem_Collect_eq that z)
          qed
          then obtain K where "K \<subseteq> H" 
            and K: "f = \<Inter> (fa_le_0 ` H) \<inter> (\<Inter>h \<in> K. {x. fa h \<bullet> x = 0})"
            using J0 \<open>J0 \<subseteq> H\<close> by blast
          have E: "rel_interior f = {x. (\<forall>h \<in> H. fa h \<bullet> x \<le> 0) \<and> (\<forall>h \<in> K. fa h \<bullet> x = 0) \<and> (\<forall>h \<in> J. ga h \<bullet> x < 0)}"
            unfolding D by (simp add: K fa_le_0_def)
          have relif: "rel_interior f \<noteq> {}"
            using "1" \<open>f \<noteq> {}\<close> by force
          with E have "disjnt J K"
            using H disjnt_iff by fastforce
          define IFJK where "IFJK \<equiv> \<lambda>h. if h \<in> J then {x. fa h \<bullet> x < 0}
                         else if h \<in> K then {x. fa h \<bullet> x = 0}
                         else if rel_interior f \<subseteq> {x. fa h \<bullet> x = 0}
                         then {x. fa h \<bullet> x = 0}
                         else {x. fa h \<bullet> x < 0}"
          have relint_f: "rel_interior f = \<Inter>(IFJK ` H)" 
          proof
            have A: False 
              if x: "x \<in> rel_interior f" and y: "y \<in> rel_interior f" and less0: "fa h \<bullet> y < 0"
                and fa0:  "fa h \<bullet> x = 0" and "h \<in> H" "h \<notin> J" "h \<notin> K"  for x h y
            proof -
              obtain \<epsilon> where "x \<in> f" "\<epsilon>>0" 
                and \<epsilon>: "\<And>t. \<lbrakk>dist x t \<le> \<epsilon>; t \<in> affine hull f\<rbrakk> \<Longrightarrow> t \<in> f"
                using x by (force simp add: mem_rel_interior_cball)
              then have "y \<noteq> x"
                using fa0 less0 by force
              define x' where "x' \<equiv> x + (\<epsilon> / norm(y - x)) *\<^sub>R (x - y)"
              have "x \<in> affine hull f \<and> y \<in> affine hull f"
                by (metis \<open>x \<in> f\<close> hull_inc mem_rel_interior_cball y)
              moreover have "dist x x' \<le> \<epsilon>"
                using \<open>0 < \<epsilon>\<close> \<open>y \<noteq> x\<close> by (simp add: x'_def divide_simps dist_norm norm_minus_commute)
              ultimately have "x' \<in> f"
                by (simp add: \<epsilon> mem_affine_3_minus x'_def)
              have "x' \<in> S"
                using \<open>f face_of S\<close> \<open>x' \<in> f\<close> face_of_imp_subset by auto
              then have "x' \<in> h"
                using Seq that(5) by blast
              then have "x' \<in> {x. fa h \<bullet> x \<le> 0}"
                using fa that(5) by blast
              moreover have "\<epsilon> / norm (y - x) * -(fa h \<bullet> y) > 0"
                using  \<open>0 < \<epsilon>\<close> \<open>y \<noteq> x\<close> less0 by (simp add: field_split_simps)
              ultimately show ?thesis
                by (simp add: x'_def fa0 inner_diff_right inner_right_distrib)
            qed
            show "rel_interior f \<subseteq> \<Inter>(IFJK ` H)"
              unfolding IFJK_def by (smt (verit, ccfv_SIG) A E H INT_I in_mono mem_Collect_eq subsetI)
            show "\<Inter>(IFJK ` H) \<subseteq> rel_interior f"
              using \<open>K \<subseteq> H\<close> \<open>disjnt J K\<close>
              apply (clarsimp simp add: ball_Un E H disjnt_iff IFJK_def)
              apply (smt (verit, del_insts) IntI Int_Collect subsetD)
              done
          qed
          obtain z where zrelf: "z \<in> rel_interior f"
            using relif by blast
          moreover
          have H: "z \<in> IFJK h \<Longrightarrow> (x \<in> IFJK h) = (hyperplane_side (fa h, 0) z = hyperplane_side (fa h, 0) x)" for h x
            using zrelf by (auto simp: IFJK_def hyperplane_side_def sgn_if split: if_split_asm)
          then have "z \<in> \<Inter>(IFJK ` H) \<Longrightarrow> (x \<in> \<Inter>(IFJK ` H)) = hyperplane_equiv A z x" for x
            unfolding A_def Inter_iff hyperplane_equiv_def ball_simps using H by blast
          then have "x \<in> rel_interior f \<longleftrightarrow> hyperplane_equiv A z x" for x
            using relint_f zrelf by presburger
          ultimately show ?thesis
            by (metis equalityI hyperplane_cell mem_Collect_eq subset_iff)
        qed
        have 4: "rel_interior f \<subseteq> S"
          by (meson face_of_imp_subset order_trans rel_interior_subset that(1))
        show ?thesis
          using "1" "2" "3" "4" by blast
      qed
      moreover have "(closure c face_of S \<and> aff_dim (closure c) = d) \<and> rel_interior (closure c) = c"
        if c: "hyperplane_cell A c" and "c \<subseteq> S" "aff_dim c = d" for c
      proof (intro conjI)
        obtain J where "J \<subseteq> H" and J: "c = (\<Inter>h \<in> J. {x. (fa h) \<bullet> x < 0}) \<inter> (\<Inter>h \<in> (H - J). {x. (fa h) \<bullet> x = 0})"
        proof -
          obtain z where z: "c = {y. \<forall>x \<in> H.  sgn (fa x \<bullet> y) = sgn (fa x \<bullet> z)}"
            using c by (force simp: hyperplane_cell A_def hyperplane_equiv_def hyperplane_side_def)
          show thesis
          proof
            let ?J = "{h \<in> H. sgn(fa h \<bullet> z) = -1}"
            show "c = (\<Inter>h \<in>?J. {x. fa h \<bullet> x < 0}) \<inter> (\<Inter>h\<in>H - ?J. {x. fa h \<bullet> x = 0})"
              unfolding z
            proof (intro  conjI set_eqI iffI IntI; clarsimp)
              show "fa h \<bullet> x < 0"
                if "\<forall>h\<in>H. sgn (fa h \<bullet> x) = sgn (fa h \<bullet> z)" and "h \<in> H" and "sgn (fa h \<bullet> z) = - 1" for x h
                using that by (metis sgn_1_neg)
              show "sgn (fa h \<bullet> z) = - 1"
                if "\<forall>h\<in>H. sgn (fa h \<bullet> x) = sgn (fa h \<bullet> z)" and "h \<in> H" and "fa h \<bullet> x \<noteq> 0" for x h
              proof -
                have "\<lbrakk>0 < fa h \<bullet> x; 0 < fa h \<bullet> z\<rbrakk> \<Longrightarrow> False"
                  using that fa by (smt (verit, del_insts) Inter_iff Seq \<open>c \<subseteq> S\<close> mem_Collect_eq subset_iff z)
                then show ?thesis
                  by (metis that sgn_if sgn_zero_iff)
              qed
              then show "sgn (fa h \<bullet> x) = sgn (fa h \<bullet> z)"
                if "h \<in> H" and "\<forall>h. h \<in> H \<and> sgn (fa h \<bullet> z) = - 1 \<longrightarrow> fa h \<bullet> x < 0"
                  and "\<forall>h\<in>H - {h \<in> H. sgn (fa h \<bullet> z) = - 1}. fa h \<bullet> x = 0"
                for x h
                using that by (metis (mono_tags, lifting) Diff_iff mem_Collect_eq sgn_neg)            
            qed
          qed auto
        qed
        have "finite J"
          using \<open>J \<subseteq> H\<close> \<open>finite H\<close> finite_subset by blast
        show "closure c face_of S"
        proof -
          have cc: "closure c = closure (\<Inter>h\<in>J. {x. fa h \<bullet> x < 0}) \<inter> closure (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0})"
            unfolding J
          proof (rule closure_Int_convex)
            show "convex (\<Inter>h\<in>J. {x. fa h \<bullet> x < 0})"
              by (simp add: convex_INT convex_halfspace_lt)
            show "convex (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0})"
              by (simp add: convex_INT convex_hyperplane)
            have o1: "open (\<Inter>h\<in>J. {x. fa h \<bullet> x < 0})"
              by (metis open_INT[OF \<open>finite J\<close>] open_halfspace_lt)
            have o2: "openin (top_of_set (affine hull (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0}))) (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0})"
            proof -
              have "affine (\<Inter>h\<in>H - J. {n. fa h \<bullet> n = 0})"
                using affine_hyperplane by auto
              then show ?thesis
                by (metis (no_types) affine_hull_eq openin_subtopology_self)
            qed
            show "rel_interior (\<Inter>h\<in>J. {x. fa h \<bullet> x < 0}) \<inter> rel_interior (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0}) \<noteq> {}"
              by (metis nonempty_hyperplane_cell c rel_interior_open o1 rel_interior_openin o2 J)
          qed
          have clo_im_J: "closure ` ((\<lambda>h. {x. fa h \<bullet> x < 0}) ` J) = (\<lambda>h. {x. fa h \<bullet> x \<le> 0}) ` J"
            using \<open>J \<subseteq> H\<close> by (force simp add: image_comp fa)
          have cleq: "closure (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0}) = (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0})"
            by (intro closure_closed) (blast intro: closed_hyperplane)
          have **: "(\<Inter>h\<in>J. {x. fa h \<bullet> x \<le> 0}) \<inter> (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0}) face_of S"
            if "(\<Inter>h\<in>J. {x. fa h \<bullet> x < 0}) \<noteq> {}"
          proof (cases "J=H")
            case True
            have [simp]: "(\<Inter>x\<in>H. {xa. fa x \<bullet> xa \<le> 0}) = \<Inter>H"
              using fa by auto
            show ?thesis
              using \<open>polyhedron S\<close> by (simp add: Seq True polyhedron_imp_convex face_of_refl)
          next
            case False
            have **: "(\<Inter>h\<in>J. {n. fa h \<bullet> n \<le> 0}) \<inter> (\<Inter>h\<in>H - J. {x. fa h \<bullet> x = 0}) =
                     (\<Inter>h\<in>H - J. S \<inter> {x. fa h \<bullet> x = 0})"  (is "?L = ?R")
            proof
              show "?L \<subseteq> ?R"
                by clarsimp (smt (verit) DiffI InterI Seq fa mem_Collect_eq)
              show "?R \<subseteq> ?L"
               apply clarsimp
                using False Seq \<open>J \<subseteq> H\<close> fa by blast
            qed
            show ?thesis
              unfolding **
            proof (rule face_of_Inter)
              show "(\<lambda>h. S \<inter> {x. fa h \<bullet> x = 0}) ` (H - J) \<noteq> {}"
                using False \<open>J \<subseteq> H\<close> by blast
              show "T face_of S"
                if T: "T \<in> (\<lambda>h. S \<inter> {x. fa h \<bullet> x = 0}) ` (H - J)" for T
              proof -
                obtain h where h: "T = S \<inter> {x. fa h \<bullet> x = 0}" and "h \<in> H" "h \<notin> J"
                  using T by auto
                have "S \<inter> {x. fa h \<bullet> x = 0} face_of S"
                proof (rule face_of_Int_supporting_hyperplane_le)
                  show "convex S"
                    by (simp add: assms(1) polyhedron_imp_convex)
                  show "fa h \<bullet> x \<le> 0" if "x \<in> S" for x
                    using that Seq fa \<open>h \<in> H\<close> by auto
                qed
                then show ?thesis
                  using h by blast
              qed
            qed
          qed
          have *: "\<And>S. S \<in> (\<lambda>h. {x. fa h \<bullet> x < 0}) ` J \<Longrightarrow> convex S \<and> open S"
            using convex_halfspace_lt open_halfspace_lt by fastforce
          show ?thesis
            unfolding cc 
            apply (simp add: * closure_Inter_convex_open)
            by (metis "**" cleq clo_im_J image_image)
        qed
        show "aff_dim (closure c) = int d"
          by (simp add: that)
        show "rel_interior (closure c) = c"
          by (metis \<open>finite A\<close> c convex_rel_interior_closure hyperplane_cell_convex hyperplane_cell_relative_interior)
      qed
      ultimately
      show "bij_betw (rel_interior) {f. f face_of S \<and> aff_dim f = int d} {C. hyperplane_cell A C \<and> C \<subseteq> S \<and> aff_dim C = int d}"
        unfolding bij_betw_def inj_on_def
        apply (intro conjI)
         apply (smt (verit) mem_Collect_eq)
        using image_eqI by blast
    qed
    show ?thesis
      by (simp add: Euler_characteristic \<open>finite A\<close>)
  qed
  also have "\<dots> = 0"
  proof -
    have A: "hyperplane_cellcomplex A (- h)" if "h \<in> H" for h
    proof (rule hyperplane_cellcomplex_mono [OF hyperplane_cell_cellcomplex])
      have "- h = {x. fa h \<bullet> x = 0} \<or> - h = {x. fa h \<bullet> x < 0} \<or> - h = {x. 0 < fa h \<bullet> x}"
        by (smt (verit, ccfv_SIG) Collect_cong Collect_neg_eq fa that)
      then show "hyperplane_cell {(fa h,0)} (- h)"
        by (simp add: hyperplane_cell_singleton fa that)
      show "{(fa h,0)} \<subseteq> A"
        by (simp add: A_def that)
    qed
    then have "\<And>h. h \<in> H \<Longrightarrow> hyperplane_cellcomplex A h"
      using hyperplane_cellcomplex_Compl by fastforce
    then have "hyperplane_cellcomplex A S"
      by (simp add: Seq hyperplane_cellcomplex_Inter)
    then have D: "Euler_characteristic A (UNIV::'n set) =
             Euler_characteristic A (\<Inter>H) + Euler_characteristic A (- \<Inter>H)"
      using Euler_characteristic_cellcomplex_Un 
      by (metis Compl_partition Diff_cancel Diff_eq Seq \<open>finite A\<close> disjnt_def hyperplane_cellcomplex_Compl)
    have "Euler_characteristic A UNIV = Euler_characteristic {} (UNIV::'n set)"
      by (simp add: Euler_characterstic_invariant \<open>finite A\<close>)
    then have E: "Euler_characteristic A UNIV = (-1) ^ (DIM('n))"
      by (simp add: Euler_characteristic_cell)
    have DD: "Euler_characteristic A (\<Inter> (uminus ` J)) = (- 1) ^ DIM('n)"
      if "J \<noteq> {}" "J \<subseteq> H" for J
    proof -
      define B where "B \<equiv> (\<lambda>h. (fa h,0::real)) ` J"
      then have "B \<subseteq> A"
        by (simp add: A_def image_mono that)
      have "\<exists>x. y = -x" if "y \<in> \<Inter> (uminus ` H)" for y::'n  \<comment> \<open>Weirdly, the assumption is not used\<close>
        by (metis add.inverse_inverse)
      moreover have "-x \<in> \<Inter> (uminus ` H) \<longleftrightarrow> x \<in> interior S" for x
      proof -
        have 1: "interior S = {x \<in> S. \<forall>h\<in>H. fa h \<bullet> x < 0}"
          using rel_interior_polyhedron_explicit [OF \<open>finite H\<close> _ fa]
          by (metis (no_types, lifting) inf_top_left  Hsub Seq \<open>affine hull S = UNIV\<close> rel_interior_interior)
        have 2: "\<And>x y. \<lbrakk>y \<in> H; \<forall>h\<in>H. fa h \<bullet> x < 0; - x \<in> y\<rbrakk> \<Longrightarrow> False" 
          by (smt (verit, best) fa inner_minus_right mem_Collect_eq)
        show ?thesis
          apply (simp add: 1)
          by (smt (verit) 2 * fa Inter_iff Seq inner_minus_right mem_Collect_eq)
      qed
      ultimately have INT_Compl_H: "\<Inter> (uminus ` H) = uminus ` interior S"
        by blast
      obtain z where z: "z \<in> \<Inter> (uminus ` J)" 
        using \<open>J \<subseteq> H\<close> \<open>\<Inter> (uminus ` H) = uminus ` interior S\<close> intS by fastforce
      have "\<Inter> (uminus ` J) = Collect (hyperplane_equiv B z)" (is "?L = ?R")
      proof
        show "?L \<subseteq> ?R"
          using fa \<open>J \<subseteq> H\<close> z 
          by (fastforce simp add: hyperplane_equiv_def hyperplane_side_def B_def set_eq_iff )
        show "?R \<subseteq> ?L"
          using z \<open>J \<subseteq> H\<close> apply (clarsimp simp add: hyperplane_equiv_def hyperplane_side_def B_def)
          by (metis fa in_mono mem_Collect_eq sgn_le_0_iff)
      qed
      then have hyper_B: "hyperplane_cell B (\<Inter> (uminus ` J))"
        by (metis hyperplane_cell)
      have "Euler_characteristic A (\<Inter> (uminus ` J)) = Euler_characteristic B (\<Inter> (uminus ` J))"
      proof (rule Euler_characterstic_invariant [OF \<open>finite A\<close>])
        show "finite B"
          using \<open>B \<subseteq> A\<close> \<open>finite A\<close> finite_subset by blast
        show "hyperplane_cellcomplex A (\<Inter> (uminus ` J))"
          by (meson \<open>B \<subseteq> A\<close> hyper_B hyperplane_cell_cellcomplex hyperplane_cellcomplex_mono)
        show "hyperplane_cellcomplex B (\<Inter> (uminus ` J))"
          by (simp add: hyper_B hyperplane_cell_cellcomplex)
      qed
      also have "\<dots> = (- 1) ^ nat (aff_dim (\<Inter> (uminus ` J)))"
        using Euler_characteristic_cell hyper_B by blast
      also have "\<dots> = (- 1) ^ DIM('n)"
      proof -
        have "affine hull \<Inter> (uminus ` H) = UNIV"
          by (simp add: INT_Compl_H affine_hull_nonempty_interior intS interior_negations)
        then have "affine hull \<Inter> (uminus ` J) = UNIV"
          by (metis Inf_superset_mono hull_mono subset_UNIV subset_antisym subset_image_iff that(2))
        with aff_dim_eq_full show ?thesis
          by (metis nat_int)
      qed
      finally show ?thesis .
    qed
    have EE: "(\<Sum>\<T> | \<T> \<subseteq> uminus ` H \<and> \<T>\<noteq>{}. (-1) ^ (card \<T> + 1) * Euler_characteristic A (\<Inter>\<T>))
             = (\<Sum>\<T> | \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {}. (-1) ^ (card \<T> + 1) * (- 1) ^ DIM('n))"
      by (intro sum.cong [OF refl]) (fastforce simp add: subset_image_iff intro!: DD)
    also have "\<dots> = (-1) ^ DIM('n)"
    proof -
      have A: "(\<Sum>y = 1..card H. \<Sum>t\<in>{x \<in> {\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {}}. card x = y}. (- 1) ^ (card t + 1)) 
          = (\<Sum>\<T>\<in>{\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {}}. (- 1) ^ (card \<T> + 1))"
      proof (rule sum.group)
        show "card ` {\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {}} \<subseteq> {1..card H}"
        apply clarsimp
        by (meson \<open>finite H\<close> card_eq_0_iff finite_surj le_zero_eq not_less_eq_eq surj_card_le)
      qed (auto simp add: \<open>finite H\<close>)

      have "(\<Sum>n = Suc 0..card H. - (int (card {x. x \<subseteq> uminus ` H \<and> x \<noteq> {} \<and> card x = n}) * (- 1) ^ n))
          = (\<Sum>n = Suc 0..card H. (-1) ^ (Suc n) * (card H choose n))"
      proof (rule sum.cong [OF refl])
        fix n
        assume "n \<in> {Suc 0..card H}"
        then have "{\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {} \<and> card \<T> = n} = {\<T>. \<T> \<subseteq> uminus ` H \<and> card \<T> = n}"
          by auto
        then have "card{\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {} \<and> card \<T> = n} = card (uminus ` H) choose n"
          by (simp add: \<open>finite H\<close> n_subsets)
        also have "\<dots> = card H choose n"
          by (metis card_image double_complement inj_on_inverseI)
        finally
        show "- (int (card {\<T>. \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {} \<and> card \<T> = n}) * (- 1) ^ n) = (- 1) ^ Suc n * int (card H choose n)"
          by simp
      qed
      also have "\<dots> = - (\<Sum>k = Suc 0..card H. (-1) ^ k * (card H choose k))"
        by (simp add: sum_negf)
      also have "\<dots> = 1 - (\<Sum>k=0..card H. (-1) ^ k * (card H choose k))"
        apply (simp add: sum.head [of 0])
        using atLeastSucAtMost_greaterThanAtMost by presburger
      also have "\<dots> = 1 - 0 ^ card H"
        using binomial_ring [of "-1" "1::int" "card H"] by (simp add: mult.commute atLeast0AtMost)
      also have "\<dots> = 1"
        using Seq \<open>finite H\<close> \<open>S \<noteq> UNIV\<close> card_0_eq by auto
      finally have C: "(\<Sum>n = Suc 0..card H. - (int (card {x. x \<subseteq> uminus ` H \<and> x \<noteq> {} \<and> card x = n}) * (- 1) ^ n)) = (1::int)" .

      have "(\<Sum>\<T> | \<T> \<subseteq> uminus ` H \<and> \<T> \<noteq> {}. (- 1) ^ (card \<T> + 1)) = (1::int)"
        unfolding A [symmetric] by (simp add: C)
      then show ?thesis
        by (simp flip: sum_distrib_right power_Suc)
    qed
    finally have "(\<Sum>\<T> | \<T> \<subseteq> uminus ` H \<and> \<T>\<noteq>{}. (-1) ^ (card \<T> + 1) * Euler_characteristic A (\<Inter>\<T>))
             = (-1) ^ DIM('n)" .
    then have  "Euler_characteristic A (\<Union> (uminus ` H)) = (-1) ^ (DIM('n))"
      using Euler_characteristic_inclusion_exclusion [OF \<open>finite A\<close>]
      by (smt (verit) A Collect_cong \<open>finite H\<close> finite_imageI image_iff sum.cong)
    then show ?thesis
      using D E by (simp add: uminus_Inf Seq)
  qed
  finally show ?thesis .
qed



section\<open>Euler-Poincare relation for special $(n-1)$-dimensional polytope \<close>

lemma Euler_Poincare_lemma:
  fixes p :: "'n::euclidean_space set"
  assumes "DIM('n) \<ge> 2" "polytope p" "i \<in> Basis" and affp: "affine hull p = {x. x \<bullet> i = 1}"
  shows "(\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * int (card {f. f face_of p \<and> aff_dim f = int d})) = 1"
proof -
  have "aff_dim p = aff_dim {x. i \<bullet> x = 1}"
    by (metis (no_types, lifting) Collect_cong aff_dim_affine_hull affp inner_commute)
  also have "... = int (DIM('n) - 1)"
    using aff_dim_hyperplane [of i 1] \<open>i \<in> Basis\<close> by fastforce
  finally have AP: "aff_dim p = int (DIM('n) - 1)" .
  show ?thesis
  proof (cases "p = {}")
    case True
    with AP show ?thesis by simp
  next
    case False
    define S where "S \<equiv> conic hull p"
    have 1: "(conic hull f) \<inter> {x. x \<bullet> i = 1} = f" if "f \<subseteq> {x. x \<bullet> i = 1}" for f
      using that
      by (smt (verit, ccfv_threshold) affp conic_hull_Int_affine_hull hull_hull inner_zero_left mem_Collect_eq)
    obtain K where "finite K" and K: "p = convex hull K"
      by (meson assms(2) polytope_def)
    then have "convex_cone hull K = conic hull (convex hull K)"
      using False convex_cone_hull_separate_nonempty by auto
    then have "polyhedron S"
      using polyhedron_convex_cone_hull
      by (simp add: S_def \<open>polytope p\<close> polyhedron_conic_hull_polytope)
    then have "convex S"
      by (simp add: polyhedron_imp_convex)
    then have "conic S"
      by (simp add: S_def conic_conic_hull)
    then have "0 \<in> S"
      by (simp add: False S_def)
    have "S \<noteq> UNIV"
    proof
      assume "S = UNIV"
      then have "conic hull p \<inter> {x. x\<bullet>i = 1} = p"
        by (metis "1" affp hull_subset)
      then have "bounded {x. x \<bullet> i = 1}"
        using S_def \<open>S = UNIV\<close> assms(2) polytope_imp_bounded by auto
      then obtain B where "B>0" and B: "\<And>x. x \<in> {x. x \<bullet> i = 1} \<Longrightarrow> norm x \<le> B"
        using bounded_normE by blast
      define x where "x \<equiv> (\<Sum>b\<in>Basis. (if b=i then 1 else B+1) *\<^sub>R b)"
      obtain j where j: "j \<in> Basis" "j\<noteq>i"
        using \<open>DIM('n) \<ge> 2\<close>
        by (metis DIM_complex DIM_ge_Suc0 card_2_iff' card_le_Suc0_iff_eq euclidean_space_class.finite_Basis le_antisym)
      have "B+1 \<le> \<bar>x \<bullet> j\<bar>"
        using j by (simp add: x_def)
      also have "\<dots> \<le> norm x"
        using Basis_le_norm j by blast
      finally have "norm x > B"
        by simp
      moreover have "x \<bullet> i = 1"
        by (simp add: x_def \<open>i \<in> Basis\<close>)
      ultimately show False
        using B by force
    qed
    have "S \<noteq> {}"
      by (metis False S_def empty_subsetI equalityI hull_subset)
    have "\<And>c x. \<lbrakk>0 < c; x \<in> p; x \<noteq> 0\<rbrakk> \<Longrightarrow> 0 < (c *\<^sub>R x) \<bullet> i"
      by (metis (mono_tags, lifting) affp hull_subset inner_commute inner_simps(6) insert_absorb insert_subset mem_Collect_eq mult.right_neutral)
    then have doti_gt0: "0 < x \<bullet> i" if S: "x \<in> S" and "x \<noteq> 0" for x
      using that by (auto simp add: S_def conic_hull_explicit)

    then have doti_ge0: "0 \<le> x \<bullet> i" if "x \<in> S" for x (*USED?*)
      using that by force
    have "\<And>a. {a} face_of S \<Longrightarrow> a = 0"
      using \<open>conic S\<close> conic_contains_0 face_of_conic by blast
    moreover have "{0} face_of S"
    proof -
      have "\<And>a b u. \<lbrakk>a \<in> S; b \<in> S; a \<noteq> b; u < 1; 0 < u; (1 - u) *\<^sub>R a + u *\<^sub>R b = 0\<rbrakk> \<Longrightarrow> False"
        using conic_def euclidean_all_zero_iff inner_left_distrib scaleR_eq_0_iff
        by (smt (verit, del_insts) doti_gt0 \<open>conic S\<close> \<open>i \<in> Basis\<close>)
      then show ?thesis
        by (auto simp add: in_segment face_of_singleton extreme_point_of_def \<open>0 \<in> S\<close>)
    qed
    ultimately have face_0: "{f. f face_of S \<and> (\<exists>a. f = {a})} = {{0}}"
      by auto
    have "interior S \<noteq> {}"
    proof
      assume "interior S = {}"
      then obtain a b where "a \<noteq> 0" and ab: "S \<subseteq> {x. a \<bullet> x = b}"
        by (metis \<open>convex S\<close> empty_interior_subset_hyperplane)
      have "{x. x \<bullet> i = 1} \<subseteq> {x. a \<bullet> x = b}"
        by (metis S_def ab affine_hyperplane affp hull_inc subset_eq subset_hull)
      moreover have "\<not> {x. x \<bullet> i = 1} \<subset> {x. a \<bullet> x = b}"
        using aff_dim_hyperplane [of a b]
        by (metis AP \<open>a \<noteq> 0\<close> aff_dim_eq_full_gen affine_hyperplane affp hull_subset less_le_not_le subset_hull)
      ultimately have "S \<subseteq> {x. x \<bullet> i = 1}"
        using ab by auto
      with \<open>S \<noteq> {}\<close> show False
        using \<open>conic S\<close> conic_contains_0 by fastforce
    qed
    then have "(\<Sum>d = 0..DIM('n). (-1) ^ d * int (card {f. f face_of S \<and> aff_dim f = int d})) = 0"
      using Euler_polyhedral_cone \<open>S \<noteq> UNIV\<close> \<open>conic S\<close> \<open>polyhedron S\<close> by blast
    then have "1 + (\<Sum>d = 1..DIM('n). (-1) ^ d * (card {f. f face_of S \<and> aff_dim f = d})) = 0"
      by (simp add: sum.atLeast_Suc_atMost aff_dim_eq_0 face_0)
    moreover have "(\<Sum>d = 1..DIM('n). (-1) ^ d * (card {f. f face_of S \<and> aff_dim f = d}))
                 = - (\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * int (card {f. f face_of p \<and> aff_dim f = int d}))"
    proof -
      have "(\<Sum>d = 1..DIM('n). (-1) ^ d * (card {f. f face_of S \<and> aff_dim f = d}))
          = (\<Sum>d = Suc 0..Suc (DIM('n)-1). (-1) ^ d * (card {f. f face_of S \<and> aff_dim f = d}))"
        by auto
      also have "... = - (\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of S \<and> aff_dim f = 1 + int d})"
        unfolding sum.atLeast_Suc_atMost_Suc_shift by (simp add: sum_negf)
      also have "... = - (\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of p \<and> aff_dim f = int d})"
      proof -
        { fix d
          assume "d \<le> DIM('n) - Suc 0"

          have F: "\<And>f. f face_of p \<Longrightarrow> conic hull f \<inter> {x. x \<bullet> i = 1} = f"
            by (metis "1" affp face_of_imp_subset hull_subset le_inf_iff)

          have G: "\<And>f. f face_of S \<Longrightarrow>  f \<inter> {x. x \<bullet> i = 1} face_of p"
            by (metis "1" S_def affp convex_affine_hull face_of_slice hull_subset)

          have "finite {f. f face_of S \<and> aff_dim f = 1 + int d}"
            by (simp add: \<open>polyhedron S\<close> finite_polyhedron_faces)
          moreover
          have "finite {f. f face_of p \<and> aff_dim f = int d}"
            by (simp add: assms(2) finite_polytope_faces)
          moreover have f_Int_face_P: "f \<inter> {x. x \<bullet> i = 1} face_of p"
            if "f face_of S" for f
            by (metis "1" S_def affp convex_affine_hull face_of_slice hull_subset that)
          moreover 
          have conic_face_p: "(conic hull f) face_of S" if "f face_of p" for f
          proof (cases "f={}")
            case False
            have "{c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> f} \<subseteq> {c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> p}"
              using face_of_imp_subset that by blast
            moreover
            have "convex {c *\<^sub>R x |c x. 0 \<le> c \<and> x \<in> f}"
              by (metis (no_types) cone_hull_expl convex_cone_hull face_of_imp_convex that)
            moreover
            have "(\<exists>c x. ca *\<^sub>R a = c *\<^sub>R x \<and> 0 \<le> c \<and> x \<in> f) \<and> (\<exists>c x. cb *\<^sub>R b = c *\<^sub>R x \<and> 0 \<le> c \<and> x \<in> f)"
              if "\<forall>a\<in>p. \<forall>b\<in>p. (\<exists>x\<in>f. x \<in> open_segment a b) \<longrightarrow> a \<in> f \<and> b \<in> f"
                and "0 \<le> ca" "a \<in> p" "0 \<le> cb" "b \<in> p"
                and "0 \<le> cx" "x \<in> f" and oseg: "cx *\<^sub>R x \<in> open_segment (ca *\<^sub>R a) (cb *\<^sub>R b)"
              for ca a cb b cx x
            proof -
              have ai: "a \<bullet> i = 1" and bi: "b \<bullet> i = 1"
                using affp hull_inc that(3,5) by fastforce+
              have xi: "x \<bullet> i = 1"
                using affp that \<open>f face_of p\<close> face_of_imp_subset hull_subset by fastforce
              show ?thesis
              proof (cases "cx *\<^sub>R x = 0")
                case True
                then show ?thesis
                  using \<open>{0} face_of S\<close> face_ofD \<open>conic S\<close> that
                  by (smt (verit, best) S_def conic_def hull_subset insertCI singletonD subsetD)
              next
                case False
                then have "cx \<noteq> 0" "x \<noteq> 0"
                  by auto
                obtain u where "0 < u" "u < 1" and u: "cx *\<^sub>R x = (1 - u) *\<^sub>R (ca *\<^sub>R a) + u *\<^sub>R (cb *\<^sub>R b)"
                  using oseg in_segment(2) by metis
                show ?thesis
                proof (cases "x = a")
                  case True
                  then have ua: "(cx - (1 - u) * ca) *\<^sub>R a = (u * cb) *\<^sub>R b"
                    using u by (simp add: algebra_simps)
                  then have "(cx - (1 - u) * ca) * 1 = u * cb * 1"
                    by (metis ai bi inner_scaleR_left)
                  then have "a=b \<or> cb = 0"
                    using ua \<open>0 < u\<close> by force
                  then show ?thesis
                    by (metis True scaleR_zero_left that(2) that(4) that(7))
                next
                  case False
                  show ?thesis
                  proof (cases "x = b")
                    case True
                    then have ub: "(cx - (u * cb)) *\<^sub>R b = ((1 - u) * ca) *\<^sub>R a"
                      using u by (simp add: algebra_simps)
                    then have "(cx - (u * cb)) * 1 = ((1 - u) * ca) * 1"
                      by (metis ai bi inner_scaleR_left)
                    then have "a=b \<or> ca = 0"
                      using \<open>u < 1\<close> ub by auto
                    then show ?thesis
                      using False True that(4) that(7) by auto
                  next
                    case False
                    have "cx > 0"
                      using \<open>cx \<noteq> 0\<close> that(6) by linarith
                    have "ca > 0"
                      by (smt (verit, ccfv_SIG) False \<open>cx \<noteq> 0\<close> add_0 bi inner_commute inner_real_def inner_simps(6) real_inner_1_right scaleR_cancel_left scaleR_eq_0_iff that(2) u vector_space_assms(3) xi)
                    have aff: "x \<in> affine hull p \<and> a \<in> affine hull p \<and> b \<in> affine hull p"
                      using affp xi ai bi by blast
                    show ?thesis
                    proof (cases "cb=0") 
                      case True
                      have u': "cx *\<^sub>R x = ((1 - u) * ca) *\<^sub>R a"
                        using u by (simp add: True)
                      then have "cx = ((1 - u) * ca)"
                        by (metis ai inner_scaleR_left mult.right_neutral xi)
                      then show ?thesis
                        using True u' \<open>cx \<noteq> 0\<close> \<open>ca \<ge> 0\<close> \<open>x \<in> f\<close> by auto
                    next
                      case False
                      with \<open>cb \<ge> 0\<close> have "cb > 0"
                        by linarith
                      { have False if "a=b"
                        proof -
                          have *: "cx *\<^sub>R x = ((1 - u) * ca + u * cb) *\<^sub>R b"
                            using u that by (simp add: algebra_simps)
                          then have "cx = ((1 - u) * ca + u * cb)"
                            by (metis xi bi inner_scaleR_left mult.right_neutral)
                          with \<open>x \<noteq> b\<close> \<open>cx \<noteq> 0\<close> * show False
                            by force
                        qed
                      }
                      moreover 
                      have "cx *\<^sub>R x /\<^sub>R cx = (((1 - u) * ca) *\<^sub>R a + (cb * u) *\<^sub>R b) /\<^sub>R cx"
                        using u by simp
                      then have xeq: "x = ((1-u) * ca / cx) *\<^sub>R a + (cb * u / cx) *\<^sub>R b"
                        by (simp add: \<open>cx \<noteq> 0\<close> divide_inverse_commute scaleR_right_distrib)
                      then have proj: "1 = ((1-u) * ca / cx) + (cb * u / cx)"
                        using ai bi xi by (simp add: inner_left_distrib)
                      then have eq: "cx + ca * u = ca + cb * u"
                        using \<open>cx > 0\<close> by (simp add: field_simps)
                      have "\<exists>u>0. u < 1 \<and> x = (1 - u) *\<^sub>R a + u *\<^sub>R b"
                      proof (intro exI conjI)
                        show "0 < inverse cx * u * cb"
                          by (simp add: \<open>0 < cb\<close> \<open>0 < cx\<close> \<open>0 < u\<close>)
                        show "inverse cx * u * cb < 1"
                          using proj \<open>0 < ca\<close> \<open>0 < cx\<close> \<open>u < 1\<close> by (simp add: divide_simps)
                        show "x = (1 - inverse cx * u * cb) *\<^sub>R a + (inverse cx * u * cb) *\<^sub>R b"
                          using eq \<open>cx \<noteq> 0\<close> by (simp add: xeq field_simps)
                      qed
                      ultimately show ?thesis
                        using that by (metis in_segment(2))
                    qed
                  qed
                qed
              qed
            qed
            ultimately show ?thesis
              using that by (auto simp add: S_def conic_hull_explicit face_of_def)
          qed auto
          moreover
          have conic_hyperplane_eq: "conic hull (f \<inter> {x. x \<bullet> i = 1}) = f"
            if "f face_of S" "0 < aff_dim f" for f
          proof
            show "conic hull (f \<inter> {x. x \<bullet> i = 1}) \<subseteq> f"
              by (metis \<open>conic S\<close> face_of_conic inf_le1 subset_hull that(1))
            have "\<exists>c x'. x = c *\<^sub>R x' \<and> 0 \<le> c \<and> x' \<in> f \<and> x' \<bullet> i = 1" if "x \<in> f" for x
            proof (cases "x=0")
              case True
              obtain y where "y \<in> f" "y \<noteq> 0"
                by (metis \<open>0 < aff_dim f\<close> aff_dim_eq_0 aff_dim_subset insert_subset linorder_not_less subset_eq)
              then have "y \<bullet> i > 0"
                using \<open>f face_of S\<close> doti_gt0 face_of_imp_subset by blast
              then have "y /\<^sub>R (y \<bullet> i) \<in> f \<and> (y /\<^sub>R (y \<bullet> i)) \<bullet> i = 1"
                using \<open>conic S\<close> \<open>f face_of S\<close> \<open>y \<in> f\<close> conic_def face_of_conic by fastforce
              then show ?thesis
                using True by fastforce
            next
              case False
              then have "x \<bullet> i > 0"
                using \<open>f face_of S\<close> doti_gt0 face_of_imp_subset that by blast
              then have "x /\<^sub>R (x \<bullet> i) \<in> f \<and> (x /\<^sub>R (x \<bullet> i)) \<bullet> i = 1"
                using \<open>conic S\<close> \<open>f face_of S\<close> \<open>x \<in> f\<close> conic_def face_of_conic by fastforce
              then show ?thesis
                by (metis \<open>0 < x \<bullet> i\<close> divideR_right eucl_less_le_not_le)
            qed
            then show "f \<subseteq> conic hull (f \<inter> {x. x \<bullet> i = 1})"
              by (auto simp: conic_hull_explicit)
          qed

          have conic_face_S: "conic hull f face_of S" 
            if "f face_of S" for f
            by (metis \<open>conic S\<close> face_of_conic hull_same that)

          moreover 
          have aff_1d: "aff_dim (conic hull f) = aff_dim f + 1" (is "?lhs = ?rhs")
            if "f face_of p" and d: "aff_dim f = int d" for f
          proof (rule order_antisym)
            have "f \<noteq> {}"
              using d by force
            have "?lhs \<le> aff_dim(affine hull (insert 0 (affine hull f)))"
            proof (intro aff_dim_subset hull_minimal)
              show "f \<subseteq> affine hull insert 0 (affine hull f)"
                by (metis hull_insert hull_subset insert_subset)
              show "conic (affine hull insert 0 (affine hull f))"
                by (metis affine_hull_span_0 conic_span hull_inc insertI1)
            qed
            also have "\<dots> \<le> ?rhs"
              by (simp add: aff_dim_insert)
            finally show "?lhs \<le> ?rhs" .
            have "aff_dim f < aff_dim (conic hull f)"
            proof (intro aff_dim_psubset psubsetI)
              show "affine hull f \<subseteq> affine hull (conic hull f)"
                by (simp add: hull_mono hull_subset)
              have "0 \<notin> affine hull f"
                using affp face_of_imp_subset hull_mono that(1) by fastforce
              moreover have "0 \<in> affine hull (conic hull f)"
                by (simp add: \<open>f \<noteq> {}\<close> hull_inc)
              ultimately show "affine hull f \<noteq> affine hull (conic hull f)"
                by auto
            qed
            then show "?rhs \<le> ?lhs"
              by simp
          qed 

          have conic_eq_f: "conic hull f \<inter> {x. x \<bullet> i = 1} = f"
            if "f face_of p" for f
            by (metis "1" affp face_of_imp_subset hull_subset le_inf_iff that)

          have MF: "aff_dim (f \<inter> {x. x \<bullet> i = 1}) = int d"
            if "f face_of S" "aff_dim f = 1 + int d" for f
          proof -
            have "conic f"
              using \<open>conic S\<close> face_of_conic that(1) by blast
            then have "0 \<in> f"
              using conic_contains_0 that by force
            moreover have "\<not> f \<subseteq> {0}"
              using subset_singletonD that(2) by fastforce
            ultimately obtain y where y: "y \<in> f" "y \<noteq> 0"
              by blast
            then have "y \<bullet> i > 0"
              using doti_gt0 face_of_imp_subset that(1) by blast

            have "inverse(y \<bullet> i) *\<^sub>R y \<in> f"
              using \<open>0 < y \<bullet> i\<close> \<open>conic S\<close> conic_mul face_of_conic that(1) y(1) by fastforce
            moreover have "inverse(y \<bullet> i) *\<^sub>R y \<in> {x. x \<bullet> i = 1}"
              using \<open>y \<bullet> i > 0\<close> by (simp add: field_simps)
            ultimately have YYY: "inverse(y \<bullet> i) *\<^sub>R y \<in> (f \<inter> {x. x \<bullet> i = 1})"
              by blast

            have "aff_dim (conic hull (f \<inter> {x. x \<bullet> i = 1})) = aff_dim (f \<inter> {x. x \<bullet> i = 1}) + 1"
            proof (rule aff_1d)
              show "f \<inter> {x. x \<bullet> i = 1} face_of p"
                by (simp add: G that(1))
              have "aff_dim (f \<inter> {x. x \<bullet> i = 1}) < aff_dim f"
                apply (intro aff_dim_psubset psubsetI)
                 apply (simp add: hull_mono)
                using \<open>0 \<in> f\<close> \<open>convex S\<close> \<open>f \<inter> {x. x \<bullet> i = 1} face_of p\<close> affp assms(3) face_of_imp_eq_affine_Int face_of_imp_subset hull_mono that(1) by fastforce
              moreover have "\<not> aff_dim (f \<inter> {x. x \<bullet> i = 1}) < aff_dim f - 1"
                  using aff_1d[of f] f_Int_face_P [OF that(1)] conic_eq_f
                    sorry
              ultimately show "aff_dim (f \<inter> {x. x \<bullet> i = 1}) = int d"
                using that(2) by linarith
            qed
            then show ?thesis
              by (simp add: conic_hyperplane_eq that)
          qed

          have "card {f. f face_of S \<and> aff_dim f = 1 + int d} =
               card {f. f face_of p \<and> aff_dim f = int d}"
            apply (intro bij_betw_same_card [of "(\<lambda>f. f \<inter> {x. x \<bullet> i = 1})"])
            unfolding bij_betw_def
            apply (intro conjI)
             apply (smt (verit) conic_hyperplane_eq inj_on_def mem_Collect_eq of_nat_less_0_iff)     
            apply (auto simp: image_iff G MF) 
            by (metis F add.commute aff_1d conic_face_p)
        }
        then show ?thesis
          by force
      qed
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by auto
  qed
qed

oops 


(*
    CONJ_TAC THEN X_GEN_TAC `f::real^N=>bool` THEN STRIP_TAC THENL
     [REMOVE_THEN "*" (MP_TAC o SPEC `f \<inter> {x. x$1 = 1}`) THEN
      ASM_SIMP_TAC[INT_ARITH `0::int < d + 1`; INT_EQ_ADD_RCANCEL] THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      SUBGOAL_THEN `\<exists>y. y \<in> f \<and> (y \<noteq> 0)` STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `a \<in> S \<and> (S \<noteq> {a}) \<Longrightarrow> \<exists>y. y \<in> S \<and> (y \<noteq> a)`) THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`S::real^N=>bool`; `f::real^N=>bool`]
            FACE_OF_CONIC) THEN
          ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN REPEAT DISCH_TAC;
          DISCH_TAC] THEN
        UNDISCH_TAC `aff_dim f = d + 1` THEN
        ASM_REWRITE_TAC[AFF_DIM_SING; AFF_DIM_EMPTY] THEN INT_ARITH_TAC;

        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        SUBGOAL_THEN `0 < (y::real^N)$1` ASSUME_TAC THENL
         [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; \<subseteq>]; ALL_TAC] THEN

        EXISTS_TAC `inverse(y \<bullet> i) *\<^sub>R y` THEN
        ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; REAL_MUL_LINV;
                     REAL_LT_IMP_NZ] THEN
        MP_TAC(ISPECL [`S::real^N=>bool`; `f::real^N=>bool`]
          FACE_OF_CONIC) THEN
        ASM_SIMP_TAC[CONIC_CONTAINS_0] THEN
        REWRITE_TAC[conic] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];

      REMOVE_THEN "*" (MP_TAC o SPEC `f::real^N=>bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(f::real^N=>bool) = d` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC]] THEN
*)


lemma Euler_poincare_special:
  fixes p :: "'n::euclidean_space set"
  assumes "2 \<le> DIM('n)" "polytope p" "i \<in> Basis" and affp: "affine hull p = {x. x \<bullet> i = 0}"
  shows "(\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of p \<and> aff_dim f = d}) = 1"
proof -
  { fix d
    have eq: "image((+) i) ` {f. f face_of p} \<inter> image((+) i) ` {f. aff_dim f = int d}
             = image((+) i) ` {f. f face_of p} \<inter> {f. aff_dim f = int d}"
      by (auto simp: aff_dim_translation_eq)
    have "card {f. f face_of p \<and> aff_dim f = int d} = card (image((+) i) ` {f. f face_of p \<and> aff_dim f = int d})"
      by (simp add: inj_on_image card_image)
    also have "\<dots>  = card (image((+) i) ` {f. f face_of p} \<inter> {f. aff_dim f = int d})"
      by (simp add: Collect_conj_eq image_Int inj_on_image eq)
    also have "\<dots> = card {f. f face_of (+) i ` p \<and> aff_dim f = int d}"
      by (simp add: Collect_conj_eq faces_of_translation)
    finally have "card {f. f face_of p \<and> aff_dim f = int d} = card {f. f face_of (+) i ` p \<and> aff_dim f = int d}" .
  } 
  then
  have "(\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of p \<and> aff_dim f = d})
      = (\<Sum>d = 0..DIM('n) - 1. (-1) ^ d * card {f. f face_of (+) i ` p \<and> aff_dim f = int d})"
    by simp
  also have "\<dots> = 1"
  proof (rule Euler_Poincare_lemma)
    have "\<And>x. \<lbrakk>i \<in> Basis; x \<bullet> i = 1\<rbrakk> \<Longrightarrow> \<exists>y. y \<bullet> i = 0 \<and> x = y + i"
      by (metis add_cancel_left_left eq_diff_eq inner_diff_left inner_same_Basis)
    then show "affine hull (+) i ` p = {x. x \<bullet> i = 1}"
      using \<open>i \<in> Basis\<close> unfolding affine_hull_translation affp by (auto simp: algebra_simps)
  qed (use assms polytope_translation_eq in auto)
  finally show ?thesis .
qed


section\<open>Now Euler-Poincare for a general full-dimensional polytope\<close>

lemma Euler_Poincare_full:
  fixes p :: "'n::euclidean_space set"
  assumes "polytope p" "aff_dim p = DIM('n)"
  shows "(\<Sum>d = 0..DIM('n). (-1) ^ d * (card {f. f face_of p \<and> aff_dim f = d})) = 1"
proof -
  define augm:: "'n \<Rightarrow> 'n \<times> real" where "augm \<equiv> \<lambda>x. (x,0)"
  define S where "S \<equiv> augm ` p"
  obtain i::'n where i: "i \<in> Basis"
    by (meson SOME_Basis)
  have "bounded_linear augm"
    by (auto simp: augm_def bounded_linearI')
  then have "polytope S"
    unfolding S_def using polytope_linear_image \<open>polytope p\<close> bounded_linear.linear by blast
  have face_pS: "\<And>F. F face_of p \<longleftrightarrow> augm ` F face_of S"
    using S_def \<open>bounded_linear augm\<close> augm_def bounded_linear.linear face_of_linear_image inj_on_def by blast
  have aff_dim_eq[simp]: "aff_dim (augm ` F) = aff_dim F" for F
    using \<open>bounded_linear augm\<close> aff_dim_injective_linear_image bounded_linear.linear 
    unfolding augm_def inj_on_def by blast
  have *: "{F. F face_of S \<and> aff_dim F = int d} = (image augm) ` {F. F face_of p \<and> aff_dim F = int d}"
            (is "?lhs = ?rhs") for d
  proof
    have "\<And>G. \<lbrakk>G face_of S; aff_dim G = int d\<rbrakk>
         \<Longrightarrow> \<exists>F. F face_of p \<and> aff_dim F = int d \<and> G = augm ` F"
      by (metis face_pS S_def aff_dim_eq face_of_imp_subset subset_imageE)
    then show "?lhs \<subseteq> ?rhs"
      by (auto simp: image_iff)
  qed (auto simp: image_iff face_pS)
  have ceqc: "card {f. f face_of S \<and> aff_dim f = int d} = card {f. f face_of p \<and> aff_dim f = int d}" for d
    unfolding *
    by (rule card_image) (auto simp add: inj_on_def augm_def)
  have "(\<Sum>d = 0..DIM('n \<times> real) - 1. (- 1) ^ d * int (card {f. f face_of S \<and> aff_dim f = int d})) = 1"
  proof (rule Euler_poincare_special)
    show "2 \<le> DIM('n \<times> real)"
      by auto
    have snd0: "(a, b) \<in> affine hull S \<Longrightarrow> b = 0" for a b
      using S_def \<open>bounded_linear augm\<close> affine_hull_linear_image augm_def by blast
    moreover have "\<And>a. (a, 0) \<in> affine hull S"
      using S_def \<open>bounded_linear augm\<close> aff_dim_eq_full affine_hull_linear_image assms(2) augm_def by blast
    ultimately show "affine hull S = {x. x \<bullet> (0::'n, 1::real) = 0}"
      by auto
  qed (auto simp: \<open>polytope S\<close> Basis_prod_def)
  then show ?thesis
    by (simp add: ceqc)
qed


text\<open> In particular the Euler relation in 3D\<close>

lemma Euler_relation:
  fixes p :: "'n::euclidean_space set"
  assumes "polytope p" "aff_dim p = 3" "DIM('n) = 3"
  shows "(card {v. v face_of p \<and> aff_dim v = 0} + card {f. f face_of p \<and> aff_dim f = 2}) - card {e. e face_of p \<and> aff_dim e = 1} = 2"
proof -
  have 3: "{f. f face_of p \<and> aff_dim f = 3} = {p}"
    using assms
    apply (auto simp: face_of_refl polytope_imp_convex)
    using face_of_imp_subset apply blast
    apply (metis assms(1) assms(2) face_of_aff_dim_lt less_irrefl polytope_imp_convex)
    done
  have "(\<Sum>d = 0..3. (-1) ^ d * int (card {f. f face_of p \<and> aff_dim f = int d})) = 1"
    using Euler_Poincare_full [of p] assms by simp
  then show ?thesis
    by (simp add: sum.atLeast0_atMost_Suc_shift numeral_3_eq_3 3)
qed

end
