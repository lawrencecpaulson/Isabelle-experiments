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


text\<open> Simple set theory lemmas.                                                 \<close>


lemma subset_insert_exists:
   "s \<subseteq> (insert x t) \<longleftrightarrow> s \<subseteq> t \<or> (\<exists>u. u \<subseteq> t \<and> s = insert x u)"
  by (metis insert_Diff insert_mono subset_insertI2 subset_insert_iff)

lemma finite_subsets_restrict:
   "finite s \<Longrightarrow> finite {t. t \<subseteq> s \<and> p t}"
  by auto


text\<open> Versions for additive real functions, where the additivity applies only   \<close>
(* to some specific subsets (e.g. cardinality of finite sets, measurable     *)
(* sets with bounded measure).                                               *)


lemma subset_insert_lemma:
  "{T. T \<subseteq> (insert a s) \<and> P T} = {T. T \<subseteq> s \<and> P T} \<union> {insert a T |T. T \<subseteq> s \<and> P(insert a T)}" (is "?L=?R")
proof
  show "?L \<subseteq> ?R"
    by (smt (verit, best) UnCI mem_Collect_eq subsetI subset_insert_exists)
qed blast

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
          unfolding 3 2 1
          by (simp add: sum_negf)
      qed
      also have "... = (\<Sum>B | B \<subseteq> A0 \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> (X ` B)))"
      proof -
         have F: "{insert a B |B. B \<subseteq> A} = insert a ` Pow A \<and> {B. B \<subseteq> A \<and> B \<noteq> {}} = Pow A - {{}}"
          by auto
        have G: "(\<Sum>B\<in>Pow A. (- 1) ^ card (insert a B) * f (X a \<inter> \<Inter> (X ` B))) = (\<Sum>B\<in>Pow A. - ((- 1) ^ card B * f (X a \<inter> \<Inter> (X ` B))))"
        proof (rule sum.cong [OF refl])
          fix B
          assume B: "B \<in> Pow A"
          then have "finite B"
            using \<open>finite A\<close> finite_subset by auto
          show "(- 1) ^ card (insert a B) * f (X a \<inter> \<Inter> (X ` B)) = - ((- 1) ^ card B * f (X a \<inter> \<Inter> (X ` B)))"
            using B * by (auto simp add: card_insert_if \<open>finite B\<close>)
        qed
        have disj: "{B. B \<subseteq> A \<and> B \<noteq> {}} \<inter> {insert a B |B. B \<subseteq> A} = {}"
          using * by blast
        have inj: "inj_on (insert a) (Pow A)"
          using "*" inj_on_def by fastforce
        show ?thesis
          apply (simp add: * subset_insert_lemma sum.union_disjoint disj sum_negf)
          apply (simp add: F G sum_negf sum.reindex [OF inj] o_def sum_diff *)
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


lemma Incl_Excl_UN:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes "\<And>S T. disjnt S T \<Longrightarrow> f(S \<union> T) = f S + f T" "finite A"
  shows "f(\<Union>(G ` A)) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (-1) ^ (card B + 1) * f (\<Inter> (G ` B)))"
proof -
  interpret Incl_Excl "\<lambda>x. True" f
    by (simp add: Incl_Excl.intro assms(1))
  show ?thesis
    using restricted_indexed assms by blast
qed

lemma Incl_Excl_Union:
  fixes f :: "'a set \<Rightarrow> 'b::ring_1"
  assumes "\<And>S T. disjnt S T \<Longrightarrow> f(S \<union> T) = f S + f T" "finite A"
  shows "f(\<Union> A) = (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}. (- 1) ^ (card B + 1) * f (\<Inter> B))"
  using Incl_Excl_UN[of f A "\<lambda>X. X"] assms by simp


subsection\<open> Versions for unrestrictedly additive functions.                           \<close>

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Special case of cardinality, the most common case.                        \<close>
text\<open> ------------------------------------------------------------------------- \<close>

lemma inclusion_exclusion:
   "finite S \<and> (\<forall>k. k \<in> S \<Longrightarrow> finite k)
        \<Longrightarrow> &(card(\<Union> S)) =
                sum {T. T \<subseteq> S \<and> (T \<noteq> {})}
                    (\<lambda>t. (-1) ^ (card T + 1) * &(card(\<Inter> T)))"
oops 
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\<lambda>s::A=>bool. finite S`; `\<lambda>s::A=>bool. (card S)`;
    `S:(A=>bool)->bool`] INCLUSION_EXCLUSION_REAL_RESTRICTED) THEN
  ASM_SIMP_TAC[FINITE_INTER; FINITE_UNION; FINITE_DIFF; FINITE_EMPTY] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[CARD_UNION; disjnt; REAL_OF_NUM_ADD]);;

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> A more conventional form.                                                 \<close>
text\<open> ------------------------------------------------------------------------- \<close>

lemma inclusion_exclusion_usual:
   "\<And>S:(A=>bool)->bool.
        finite S \<and> (\<forall>k. k \<in> S \<Longrightarrow> finite k)
        \<Longrightarrow> &(card(\<Union> S)) =
                sum (1..card S) (\<lambda>n. (-1) ^ (Suc n) *
                                     sum {T. T \<subseteq> S \<and> T HAS_SIZE n}
                                         (\<lambda>t. &(card(\<Inter> T))))"
oops 
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INCLUSION_EXCLUSION] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) (ISPEC `card` SUM_IMAGE_GEN) o
     lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(MESON[] `S = T \<and> sum T f = sum T g \<Longrightarrow> sum S f = sum T g`) THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC id [EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG; IN_ELIM_THM] THEN
    REWRITE_TAC[ARITH_RULE `1 \<le> a \<longleftrightarrow> (a \<noteq> 0)`] THEN
    ASM_MESON_TAC[CHOOSE_SUBSET; CARD_SUBSET; FINITE_SUBSET; CARD_EQ_0;
                  HAS_SIZE];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n::num` THEN REWRITE_TAC[IN_NUMSEG] THEN
  STRIP_TAC THEN REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[IN_ELIM_THM; HAS_SIZE] THEN
  GEN_REWRITE_TAC id [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[CARD_EQ_0; ARITH_RULE `~(1 \<le> 0)`; FINITE_SUBSET]);;

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> A combinatorial lemma about subsets of a finite set.                      \<close>
text\<open> ------------------------------------------------------------------------- \<close>

lemma finite_subsets_restrict:
   "\<And>S::A=>bool p. finite S \<Longrightarrow> finite {T. T \<subseteq> S \<and> p T}"
oops 
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{T::A=>bool | T \<subseteq> S}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]);;

lemma card_adjust_lemma:
   "\<And>f::A=>B S x y.
        finite S \<and>
        (\<forall>x y. x \<in> S \<and> y \<in> S \<and> f x = f y \<Longrightarrow> x = y) \<and>
        x = y + card (f ` S)
        \<Longrightarrow> x = y + card S"
oops 
  MESON_TAC[CARD_IMAGE_INJ]);;

lemma card_subsets_step:
   "finite S \<and> (x \<notin> S) \<and> u \<subseteq> S
           \<Longrightarrow> card {T. T \<subseteq> (insert x S) \<and> u \<subseteq> T \<and> ODD(card T)} =
                 card {T. T \<subseteq> S \<and> u \<subseteq> T \<and> ODD(card T)} +
                 card {T. T \<subseteq> S \<and> u \<subseteq> T \<and> EVEN(card T)} \<and>
               card {T. T \<subseteq> (insert x S) \<and> u \<subseteq> T \<and> EVEN(card T)} =
                 card {T. T \<subseteq> S \<and> u \<subseteq> T \<and> EVEN(card T)} +
                 card {T. T \<subseteq> S \<and> u \<subseteq> T \<and> ODD(card T)}"
oops 
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE[`:A`,`:B`] CARD_ADJUST_LEMMA) THEN
  EXISTS_TAC `\<lambda>u. (x::A) insert u` THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
   ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT; FINITE_INSERT] THEN CONJ_TAC THENL
    [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
     REWRITE_TAC[TAUT `~(a \<and> b) \<longleftrightarrow> b \<Longrightarrow> ~a`; FORALL_IN_IMAGE] THEN
     ASM SET_TAC[];
     ALL_TAC] THEN
   GEN_REWRITE_TAC id [EXTENSION] THEN X_GEN_TAC `T::A=>bool` THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNION; SUBSET_INSERT_EXISTS] THEN
   REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
   REWRITE_TAC[RIGHT_OR_DISTRIB; LEFT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN
   AP_TERM_TAC THEN GEN_REWRITE_TAC id [FUN_EQ_THM] THEN
   X_GEN_TAC `v::A=>bool` THEN
   ASM_CASES_TAC `T = (x::A) insert v` THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `(v::A=>bool) \<subseteq> S` THEN ASM_REWRITE_TAC[] THEN
   BINOP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[CARD_CLAUSES; EVEN; NOT_ODD; FINITE_SUBSET; \<subseteq>] THEN
   ASM_MESON_TAC[CARD_CLAUSES; EVEN; NOT_ODD; FINITE_SUBSET; \<subseteq>]));;

lemma card_subsupersets_even_odd:
   "\<And>S u::A=>bool.
        finite u \<and> S \<subset> u
        \<Longrightarrow> card {T. S \<subseteq> T \<and> T \<subseteq> u \<and> EVEN(card T)} =
            card {T. S \<subseteq> T \<and> T \<subseteq> u \<and> ODD(card T)}"
oops 
  ONCE_REWRITE_TAC[TAUT `a \<and> b \<and> c \<longleftrightarrow> b \<and> a \<and> c`] THEN
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `card(u::A=>bool)` THEN
  REWRITE_TAC[PSUBSET_ALT] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x::A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (SET_RULE
   `x \<in> S \<Longrightarrow> S = x insert (S - {x})`)) THEN
  MP_TAC(SET_RULE `~((x::A) \<in> (u - {x}))`) THEN
  ABBREV_TAC `v::A=>bool = u - {x}` THEN STRIP_TAC THEN
  SUBGOAL_THEN `finite v \<and> (S::A=>bool) \<subseteq> v` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[FINITE_INSERT]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_SUBSETS_STEP] THEN ASM_CASES_TAC `S::A=>bool = v` THENL
   [REWRITE_TAC[CONJ_ASSOC; SUBSET_ANTISYM_EQ] THEN MATCH_ACCEPT_TAC ADD_SYM;
    ASM_SIMP_TAC[CARD_CLAUSES; LT; \<subset>]]);;

lemma sum_alternating_cancels:
   "\<And>S::A=>bool f.
        finite S \<and>
        card {x. x \<in> S \<and> EVEN(f x)} = card {x. x \<in> S \<and> ODD(f x)}
        \<Longrightarrow> sum S (\<lambda>x. (-1) ^ (f x)) = 0"
oops 
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {x. x \<in> S \<and> EVEN(f x)} (\<lambda>x. (-1) ^ (f x)) +
              sum {x::A | x \<in> S \<and> ODD(f x)} (\<lambda>x. (-1) ^ (f x))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_SIMP_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
    REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_NEG; REAL_POW_ONE; GSYM NOT_EVEN; SUM_CONST;
               FINITE_RESTRICT; REAL_ARITH `x * 1 + x *-1 = 0`]);;

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> Hence a general "Moebius inversion" inclusion-exclusion principle.        \<close>
text\<open> This "symmetric" form is from Ira Gessel: "Symmetric Inclusion-Exclusion" \<close>
text\<open> ------------------------------------------------------------------------- \<close>

lemma inclusion_exclusion_symmetric:
   "\<And>f g:(A=>bool)->real.
    (\<forall>S. finite S
         \<Longrightarrow> g S = sum {T. T \<subseteq> S} (\<lambda>t. (-1) ^ (card T) * f T))
    \<Longrightarrow> \<forall>S. finite S
            \<Longrightarrow> f S = sum {T. T \<subseteq> S} (\<lambda>t. (-1) ^ (card T) * g T)"
oops 
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {T::A=>bool | T \<subseteq> S}
                  (\<lambda>t. (-1) ^ (card T) *
                       sum {u. u \<in> {u. u \<subseteq> S} \<and> u \<subseteq> T}
                           (\<lambda>u. (-1) ^ (card u) * f u))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; SET_RULE
     `S \<subseteq> T \<Longrightarrow> (u \<subseteq> T \<and> u \<subseteq> S \<longleftrightarrow> u \<subseteq> S)`] THEN
    ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_RESTRICT o lhs o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_RMUL; IN_ELIM_THM] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum {u. u \<subseteq> S} (\<lambda>u::A=>bool. if u = S then f S else 0)` THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[SUM_DELTA; IN_ELIM_THM; SUBSET_REFL]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u::A=>bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SUBSET_ANTISYM_EQ; SET_RULE `{x. x = a} = {a}`] THEN
    REWRITE_TAC[SUM_SING; REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; REAL_POW_ONE; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN REPEAT DISJ1_TAC THEN
  MATCH_MP_TAC SUM_ALTERNATING_CANCELS THEN
  ASM_SIMP_TAC[FINITE_SUBSETS_RESTRICT; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a \<and> b) \<and> c \<longleftrightarrow> b \<and> a \<and> c`] THEN
  MATCH_MP_TAC CARD_SUBSUPERSETS_EVEN_ODD THEN ASM SET_TAC[]);;

text\<open> ------------------------------------------------------------------------- \<close>
text\<open> The more typical non-symmetric version.                                   \<close>
text\<open> ------------------------------------------------------------------------- \<close>

lemma inclusion_exclusion_mobius:
   "\<And>f g:(A=>bool)->real.
        (\<forall>S. finite S \<Longrightarrow> g S = sum {T. T \<subseteq> S} f)
        \<Longrightarrow> \<forall>S. finite S
                \<Longrightarrow> f S = sum {T. T \<subseteq> S}
                               (\<lambda>t. (-1) ^ (card S - card T) * g T)"
oops 
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\<lambda>t.-1 ^ card(T::A=>bool) * f T`; `g:(A=>bool)->real`]
                INCLUSION_EXCLUSION_SYMMETRIC) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[EVEN_ADD; REAL_POW_ONE; REAL_POW_NEG; REAL_MUL_LID; ETA_AX];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `S::A=>bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(*) ((-1) ^ (card(S::A=>bool)))`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD; GSYM MULT_2] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `u::A=>bool` THEN REWRITE_TAC[IN_ELIM_THM; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_POW_SUB; REAL_ARITH `~(-1 = 0)`; CARD_SUBSET] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN REAL_ARITH_TAC);;


end

