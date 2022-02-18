section \<open>Alternative defn of ALEPH that's defined on all sets, not just ordinals\<close>

theory ALEPH imports
  "HOL-ex.Sketch_and_Explore" "ZFC_in_HOL.ZFC_Typeclasses"
   
begin


lemma Nats_infinite: "\<not> finite \<nat>"
apply (auto simp: Nats_def)
  by (auto dest!: finite_imageD simp: inj_on_def infinite_UNIV_char_0 Nats_def)


definition ALEPH :: "V \<Rightarrow> V"   (\<open>\<aleph>_\<close> [90] 90) 
  where "ALEPH \<equiv> transrec (\<lambda>f x. \<omega> \<squnion> \<Squnion>((\<lambda>y. csucc(f y)) ` elts x))"

lemma Card_ALEPH [simp, intro]:
     "InfCard(ALEPH x)"
proof (induction x rule: eps_induct)
  case (step x)
  show ?case
  proof (cases "x=0")
    case True
    then show ?thesis
      by (simp add: ALEPH_def transrec [where a=0] InfCard_def step)
  next
    case False
    with step show ?thesis 
      by (simp add: ALEPH_def transrec [where a=x] InfCard_def Card_UN step)
  qed
qed

lemma ALEPH_0 [simp]: "ALEPH 0 = \<omega>"
  by (simp add: ALEPH_def transrec [where a=0])

lemma ALEPH_lt_succD [simp]: "(ALEPH x) < ALEPH (succ x)"
  apply (simp add: ALEPH_def transrec [where a="succ x"])
  apply (simp add: flip: ALEPH_def)
  by (metis Card_ALEPH InfCard_def Sup_V_insert less_csucc less_supI1 replacement small_elts sup.strict_coboundedI2)

lemma mem_ALEPH_succ: "ALEPH (\<alpha>) \<in> elts (ALEPH (succ \<alpha>))"
  by (meson ALEPH_lt_succD Card_ALEPH Card_is_Ord InfCard_def Ord_mem_iff_lt)

lemma ALEPH_succ [simp]: "ALEPH (succ x) = csucc (ALEPH x)"
proof (rule ccontr)
  assume "ALEPH (succ x) \<noteq> csucc (ALEPH x)"
  then consider "ALEPH (succ x) < csucc (ALEPH x)" | "ALEPH (succ x) > csucc (ALEPH x)"
    by (meson Card_ALEPH InfCard_def csucc_le dual_order.order_iff_strict mem_ALEPH_succ)
  then show False
  proof cases
    case 1
    then show ?thesis
      by (meson Card_ALEPH InfCard_def csucc_le leD mem_ALEPH_succ)
  next
    case 2
    then show ?thesis
      
      sorry
  qed

  using ALEPH_lt_succD
  apply (simp add: ALEPH_def transrec [where a="succ x"])
  apply (rule )
apply (simp add: flip: ALEPH_def)
apply (auto simp: )
  using InfCard_csucc InfCard_def apply blast

lemma ALEPH_Limit: "Limit \<gamma> \<Longrightarrow> ALEPH  \<gamma> = \<Squnion> (ALEPH ` elts \<gamma>)"
  by (simp add: ALEPH_def transrec [where a=\<gamma>])

lemma ALEPH_increasing:
  assumes ab: "\<alpha> < \<beta>" "Ord \<alpha>" "Ord \<beta>" shows "ALEPH(\<alpha>) < ALEPH(\<beta>)"
proof -
  { fix x
    have "\<lbrakk>Ord x; x \<in> elts \<beta>\<rbrakk> \<Longrightarrow> ALEPH(x) \<in> elts (ALEPH \<beta>)"
      using \<open>Ord \<beta>\<close>
    proof (induct \<beta> arbitrary: x rule: Ord_induct3)
      case 0 thus ?case by simp
    next
      case (succ \<beta>)
      then consider "x = \<beta>" |"x \<in> elts \<beta>"
        using OrdmemD by auto
      then show ?case
      proof cases
        case 1
        then show ?thesis
          by (simp add: Card_is_Ord Ord_mem_iff_lt succ.hyps(1))
      next
        case 2
        with succ show ?thesis
          by (metis ALEPH_succ Card_ALEPH le_csucc vsubsetD)
      qed
    next
      case (Limit \<gamma>)
      hence sc: "succ x \<in> elts \<gamma>"
        by (simp add: Limit_def Ord_mem_iff_lt)
      hence "ALEPH  x \<in> elts (\<Squnion> (ALEPH ` elts \<gamma>))" 
        using Limit
        by blast
      thus ?case using Limit
        by (simp add: ALEPH_Limit)
    qed
  } thus ?thesis using ab
    by (simp add: Card_is_Ord Ord_mem_iff_lt)
qed

lemma countable_iff_le_ALEPH0: "countable (elts A) \<longleftrightarrow> vcard A \<le> ALEPH 0"
proof
  show "vcard A \<le> ALEPH 0"
    if "countable (elts A)"
  proof (cases "finite (elts A)")
    case True
    then show ?thesis
      using vcard_finite_set by fastforce
  next
    case False
    then have "elts \<omega> \<approx> elts A"
      using countableE_infinite [OF that]     
      by (simp add: eqpoll_def \<omega>_def) (meson bij_betw_def bij_betw_inv bij_betw_trans inj_ord_of_nat)
    then show ?thesis
      using Card_\<omega> Card_def cardinal_cong vcard_def by auto
  qed
  show "countable (elts A)"
    if "vcard A \<le> ALEPH 0"
  proof -
    have "elts A \<lesssim> elts \<omega>"
      using cardinal_le_lepoll [OF that] by simp
    then show ?thesis
      by (simp add: countable_iff_lepoll \<omega>_def inj_ord_of_nat)
  qed
qed

lemma
  assumes "Ord \<alpha>"
  shows "Aleph \<alpha> = transrec (\<lambda>f x. \<omega> \<squnion> \<Squnion>((\<lambda>y. csucc(f y)) ` elts x)) \<alpha>"
  using assms
proof(induction \<alpha> rule: Ord_induct3)
  case 0
  then show ?case 
    by (simp add: transrec [where a=0])
next
  case (succ \<alpha>)
  then show ?case
    apply (simp add: )
    apply (auto simp: transrec [where a="succ \<alpha>"])
    apply (rule antisym)
     apply (auto simp: )
     apply (metis (no_types, lifting) Card_Aleph Un_iff elts_sup_iff le_csucc transrec vsubsetD)

    sorry
next
  case (Limit \<alpha>)
  then show ?case
    apply (simp add: transrec [where a="\<alpha>"])
    apply (simp add: Aleph_Limit)
    apply (rule antisym)
     apply (auto simp: )
    apply (metis (no_types, lifting) Card_Aleph Limit_is_Ord Ord_in_Ord le_csucc rev_vsubsetD)
    apply (metis Aleph_0 Limit_def)
    by (metis Aleph_succ Limit_def)
qed


end
