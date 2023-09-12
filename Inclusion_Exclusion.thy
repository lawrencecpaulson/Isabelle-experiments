chapter \<open>Inclusion-exclusion principle\<close>

text \<open>One of the Famous 100 Theorems, ported from HOL Light\<close>
text\<open> Inclusion-exclusion principle, the usual and generalized forms.                \<close>

theory Inclusion_Exclusion
  imports Main "HOL-ex.Sketch_and_Explore"
begin


(**the above all imported to HOL/Binomial.thy**)

text\<open> A combinatorial lemma about subsets of a finite set.                      \<close>


lemma finite_subsets_restrict:
   "finite s \<Longrightarrow> finite {t. t \<subseteq> s \<and> p t}"
  by auto

lemma card_adjust_lemma:
   "\<lbrakk>inj_on f S; x = y + card (f ` S)\<rbrakk> \<Longrightarrow> x = y + card S"
  by (simp add: card_image)

lemma card_subsets_step:
  assumes "finite S" "x \<notin> S" "U \<subseteq> S"
  shows "card {T. T \<subseteq> (insert x S) \<and> U \<subseteq> T \<and> odd(card T)} =
                 card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> odd(card T)} +
                 card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> even(card T)} \<and>
               card {T. T \<subseteq> (insert x S) \<and> U \<subseteq> T \<and> even(card T)} =
                 card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> even(card T)} +
                 card {T. T \<subseteq> S \<and> U \<subseteq> T \<and> odd(card T)}"
proof -
  have inj: "inj_on (insert x) {T. T \<subseteq> S \<and> P T}" for P
    using assms by (auto simp: inj_on_def)
  have [simp]: "finite {T. T \<subseteq> S \<and> P T}"  "finite (insert x ` {T. T \<subseteq> S \<and> P T})" for P
    using \<open>finite S\<close> by auto
  have [simp]: "disjnt {T. T \<subseteq> S \<and> P T} (insert x ` {T. T \<subseteq> S \<and> Q T})" for P Q
    using assms by (auto simp: disjnt_iff)
  have eq: "{T. T \<subseteq> S \<and> U \<subseteq> T \<and> P T} \<union> insert x ` {T. T \<subseteq> S \<and> U \<subseteq> T \<and> Q T}
          = {T. T \<subseteq> insert x S \<and> U \<subseteq> T \<and> P T}"  (is "?L = ?R")
    if "\<And>A. A \<subseteq> S \<Longrightarrow> Q (insert x A) \<longleftrightarrow> P A" "\<And>A. \<not> Q A \<longleftrightarrow> P A" for P Q
  proof
    show "?L \<subseteq> ?R"
      by (clarsimp simp: image_iff subset_iff) (meson subsetI that)
    show "?R \<subseteq> ?L"
      using \<open>U \<subseteq> S\<close>
      by (clarsimp simp: image_iff) (smt (verit) insert_iff mk_disjoint_insert subset_iff that)
  qed
  have [simp]: "\<And>A. A \<subseteq> S \<Longrightarrow> even (card (insert x A)) \<longleftrightarrow> odd (card A)"
    by (metis assms card_insert_disjoint even_Suc finite_subset subsetD)
  show ?thesis
    by (intro conjI card_adjust_lemma [OF inj]; simp add: eq flip: card_Un_disjnt)
qed

lemma card_subsupersets_even_odd:
   " finite U \<and> S \<subset> U
        \<Longrightarrow> card {T. S \<subseteq> T \<and> T \<subseteq> U \<and> even(card T)} =
            card {T. S \<subseteq> T \<and> T \<subseteq> U \<and> odd(card T)}"
oops 
  ONCE_REWRITE_TAC[TAUT `a \<and> b \<and> c \<longleftrightarrow> b \<and> a \<and> c`] THEN
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `card(U::A=>bool)` THEN
  REWRITE_TAC[PSUBSET_ALT] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x::A` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o MATCH_MP (SET_RULE
   `x \<in> S \<Longrightarrow> S = x insert (S - {x})`)) THEN
  MP_TAC(SET_RULE `~((x::A) \<in> (U - {x}))`) THEN
  ABBREV_TAC `v::A=>bool = U - {x}` THEN STRIP_TAC THEN
  SUBGOAL_THEN `finite v \<and> (S::A=>bool) \<subseteq> v` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[FINITE_INSERT]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_SUBSETS_STEP] THEN ASM_CASES_TAC `S::A=>bool = v` THENL
   [REWRITE_TAC[CONJ_ASSOC; SUBSET_ANTISYM_EQ] THEN MATCH_ACCEPT_TAC ADD_SYM;
    ASM_SIMP_TAC[CARD_CLAUSES; LT; \<subset>]]);;

lemma sum_alternating_cancels:
   "\<And>S::A=>bool f.
        finite S \<and>
        card {x. x \<in> S \<and> even(f x)} = card {x. x \<in> S \<and> odd(f x)}
        \<Longrightarrow> sum S (\<lambda>x. (-1) ^ (f x)) = 0"
oops 
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {x. x \<in> S \<and> even(f x)} (\<lambda>x. (-1) ^ (f x)) +
              sum {x::A | x \<in> S \<and> odd(f x)} (\<lambda>x. (-1) ^ (f x))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_SIMP_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN
    REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_NEG; REAL_POW_ONE; GSYM NOT_EVEN; SUM_CONST;
               FINITE_RESTRICT; REAL_ARITH `x * 1 + x *-1 = 0`]);;


text\<open> Hence a general "Moebius inversion" inclusion-exclusion principle.        \<close>
text\<open> This "symmetric" form is from Ira Gessel: "Symmetric Inclusion-Exclusion" \<close>


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
                       sum {U. U \<in> {U. U \<subseteq> S} \<and> U \<subseteq> T}
                           (\<lambda>u. (-1) ^ (card U) * f U))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; SET_RULE
     `S \<subseteq> T \<Longrightarrow> (U \<subseteq> T \<and> U \<subseteq> S \<longleftrightarrow> U \<subseteq> S)`] THEN
    ASM_MESON_TAC[FINITE_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUM_RESTRICT o lhs o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUM_RMUL; IN_ELIM_THM] THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum {U. U \<subseteq> S} (\<lambda>u::A=>bool. if U = S then f S else 0)` THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[SUM_DELTA; IN_ELIM_THM; SUBSET_REFL]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `U::A=>bool` THEN
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


text\<open> The more typical non-symmetric version.                                   \<close>


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
  X_GEN_TAC `U::A=>bool` THEN REWRITE_TAC[IN_ELIM_THM; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_POW_SUB; REAL_ARITH `~(-1 = 0)`; CARD_SUBSET] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN REAL_ARITH_TAC);;


end

