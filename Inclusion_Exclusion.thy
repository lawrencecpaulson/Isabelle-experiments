chapter \<open>Inclusion-exclusion principle\<close>

text \<open>One of the Famous 100 Theorems, ported from HOL Light\<close>
text\<open> Inclusion-exclusion principle, the usual and generalized forms.                \<close>

theory Inclusion_Exclusion
  imports Main "HOL-ex.Sketch_and_Explore"
begin

(*MOVE UP*)
lemma Inter_over_Union:
  "\<Inter> {\<Union> (\<F> x) |x. x \<in> S} = \<Union> {\<Inter> (G ` S) |G. \<forall>x\<in>S. G x \<in> \<F> x}" 
proof -
  have "\<And>x. \<forall>s\<in>S. \<exists>X \<in> \<F> s. x \<in> X \<Longrightarrow> \<exists>G. (\<forall>x\<in>S. G x \<in> \<F> x) \<and> (\<forall>s\<in>S. x \<in> G s)"
    by metis
  then show ?thesis
    by (auto simp flip: all_simps ex_simps)
qed

text\<open> ========================================================================= \<close>
text\<open> .           \<close>
text\<open> ========================================================================= \<close>

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Simple set theory lemmas.                                                 \<close>
text\<open> ------------------------------------------------------------------------- \<close>

lemma subset_insert_exists:
   "s \<subseteq> (insert x t) \<longleftrightarrow> s \<subseteq> t \<or> (\<exists>u. u \<subseteq> t \<and> s = insert x u)"
  by (metis insert_Diff insert_mono subset_insertI2 subset_insert_iff)

lemma finite_subsets_restrict:
   "finite s \<Longrightarrow> finite {t. t \<subseteq> s \<and> p t}"
  by auto

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Versions for additive real functions, where the additivity applies only   \<close>
(* to some specific subsets (e.g. cardinality of finite sets, measurable     *)
(* sets with bounded measure).                                               *)
text\<open> ------------------------------------------------------------------------- \<close>

lemma aux:
  "{t. t \<subseteq> (insert a s) \<and> P t} = {t. t \<subseteq> s \<and> P t} \<union> {insert a t |t. t \<subseteq> s \<and> P(insert a t)}"
  apply safe
    apply (metis in_mono subset_insert_exists)
   apply blast
  by blast

thm int_card_UNION

locale Incl_Excl =
  fixes P :: "'a set \<Rightarrow> bool" and f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes disj_add: "\<lbrakk>P S; P T; disjnt S T\<rbrakk> \<Longrightarrow> f(S \<union> T) = f S + f T"
    and empty: "P{}"
    and Int: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S \<inter> T)"
    and Un: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S \<union> T)"
    and Diff: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S - T)"

begin

lemma f_empty [simp]: "f{} = 0"
  using disj_add empty by fastforce

lemma DD: "\<lbrakk>P S; P T; S\<subseteq>T\<rbrakk> \<Longrightarrow> f T = f S + f(T-S)"
  by (metis Diff Diff_disjoint Diff_partition disj_add disjnt_def)

lemma E: "\<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> f(S \<union> T) + f(S \<inter> T) = f S + f T"
  by (smt (verit, ccfv_threshold) Groups.add_ac(2) Incl_Excl.Diff Incl_Excl.Int Incl_Excl_axioms Int_Diff_Un Int_Diff_disjoint Int_absorb Un_Diff Un_Int_eq(2) disj_add disjnt_def group_cancel.add2 sup_bot.right_neutral)

lemma restricted_indexed:
  assumes "finite A" and X: "\<And>a. a \<in> A \<Longrightarrow> P(X a)"
  shows "f(\<Union>(X ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
proof -
  have "\<lbrakk>finite A; card A = n; \<forall>a \<in> A. P (X a)\<rbrakk>
              \<Longrightarrow> f(\<Union>(X ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))" for n X and A :: "'c set"
  proof (induction n arbitrary: A X rule: less_induct)
    case (less n0 A0 X)
    show ?case
    proof (cases "n0=0")
      case True
      with less show ?thesis
       by fastforce
    next
      case False
      with less.prems obtain A n a where *: "n0 = Suc n" "A0 = insert a A" "a \<notin> A" "card A = n" "finite A"
        by (metis card_Suc_eq_finite not0_implies_Suc)
      with less have "P (X a)" by blast
      have APX: "\<forall>a \<in> A. P (X a)"
        by (simp add: "*" less.prems)
      have PUXA: "P (\<Union> (X ` A))"
        using \<open>finite A\<close> APX
        by (induction) (auto simp: empty Un)
      have "f (\<Union> (X ` A0)) = f (X a \<union> \<Union> (X ` A))"
        by (simp add: *)
      also have "... = f (X a) + f (\<Union> (X ` A)) - f (X a \<inter> \<Union> (X ` A))"
        using E add_diff_cancel PUXA \<open>P (X a)\<close> by metis
      also have "... = f (X a) - (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ card B * f (\<Inter> (X ` B))) +
                       (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ card B * f (X a \<inter> \<Inter> (X ` B)))"
      proof -
        have 1: "f (\<Union>i\<in>A. X a \<inter> X i) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter>b\<in>B. X a \<inter> X b))"
          using less.IH [of n A "\<lambda>i. X a \<inter> X i"] APX Int \<open>P (X a)\<close>  by (simp add: *)
        have 2: "X a \<inter> \<Union> (X ` A) = (\<Union>i\<in>A. X a \<inter> X i)"
          by auto
        have 3: "f (\<Union> (X ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
          using less.IH [of n A X] APX Int \<open>P (X a)\<close>  by (simp add: *)
        show ?thesis
          apply (simp add: )
          unfolding 3 2 1
          by (simp add: sum_negf)
      qed
      also have "... = (\<Sum>B | B \<subseteq> A0 \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
      proof -
        have F: "{insert a B |B. B \<subseteq> A} = insert a ` Pow A \<and> {B. B \<subseteq> A \<and> B \<noteq> {}} = Pow A - {{}}"
          by auto
        have G: "(\<Sum>B\<in>Pow A. (- 1) ^ card (insert a B) * f (X a \<inter> \<Inter> (X ` B))) = (\<Sum>B\<in>Pow A. - ((- 1) ^ card B * f (X a \<inter> \<Inter> (X ` B))))"
          apply (rule sum.cong [OF refl])
          apply (simp add: )
          apply (subst card_insert_if)
          apply (simp add: "*"(5) finite_subset)
          using "*"(3) by auto
        show ?thesis
          apply (simp add: *)
          apply (simp add: aux)
          apply (subst sum.union_disjoint)
             apply (simp add: "*"(5))
            apply (simp add: "*"(5))
          using * apply blast
          apply (simp add: sum_negf)
          apply (simp add: F)
          apply (subst sum.reindex)
          using "*"(3) inj_on_def apply fastforce
          apply (simp add: o_def)
          apply (subst sum_diff)
          apply (simp add: "*"(5))
          apply simp
          apply (simp add: )
          apply (simp add: G sum_negf)
          done
      qed
      finally show ?thesis .
    qed   
  qed
  then show ?thesis
    by (meson assms)
qed


lemma restricted:
  assumes "finite A" "\<And>a. a \<in> A \<Longrightarrow> P a"
  shows  "f(\<Union> A) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> B))"
  using restricted_indexed [of A "\<lambda>x. x"] assms by auto

end

end

