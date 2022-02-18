section \<open>Alternative defn of Aleph that's defined on all sets, not just ordinals\<close>

theory ALEPH imports
  "HOL-ex.Sketch_and_Explore" "ZFC_in_HOL.ZFC_Typeclasses"
   
begin

thm inj_on_of_nat
lemma Nats_infinite: "\<not> finite (\<nat> :: 'a::semiring_char_0 set)"
  by (metis Nats_def finite_imageD infinite_UNIV_char_0 inj_on_of_nat)

definition Aleph :: "V \<Rightarrow> V"    (\<open>\<aleph>_\<close> [90] 90)
  where "Aleph \<equiv> transrec (\<lambda>f x. \<omega> \<squnion> \<Squnion>((\<lambda>y. csucc(f y)) ` elts x))"

lemma Aleph: "Aleph \<alpha> = \<omega> \<squnion> (\<Squnion>y\<in>elts \<alpha>. csucc (Aleph y))"
  by (simp add: Aleph_def transrec[of _ \<alpha>])

lemma Card_Aleph [simp, intro]: "InfCard(Aleph x)"
proof (induction x rule: eps_induct)
  case (step x)
  then show ?case
    by (simp add: Aleph [of x] InfCard_def Card_UN step)
qed

lemma Aleph_0 [simp]: "Aleph 0 = \<omega>"
  by (simp add: Aleph [of 0])

lemma mem_Aleph_succ: "Aleph (\<alpha>) \<in> elts (Aleph (succ \<alpha>))"
  apply (simp add: Aleph [of "succ \<alpha>"])
  by (meson Card_Aleph Card_csucc Card_is_Ord InfCard_def Ord_mem_iff_lt less_csucc)

lemma Aleph_lt_succD [simp]: "(Aleph x) < Aleph (succ x)"
  by (simp add: InfCard_is_Limit Limit_is_Ord OrdmemD mem_Aleph_succ)

thm Aleph_succ
lemma Aleph_succ [simp]: "Aleph (succ x) = csucc (Aleph x)"
proof (rule antisym)
  show "Aleph (ZFC_in_HOL.succ x) \<le> csucc (Aleph x)"
    apply (simp add: Aleph [of "succ x"])
    by (metis Aleph Card_Aleph InfCard_def Sup_V_insert le_csucc le_sup_iff order_refl replacement small_elts)
  show "csucc (Aleph x) \<le> Aleph (ZFC_in_HOL.succ x)"
    by (force simp add: Aleph [of "succ x"])
qed

lemma csucc_Aleph_le_Aleph: "\<alpha> \<in> elts \<beta> \<Longrightarrow> csucc (Aleph \<alpha>) \<le> (Aleph \<beta>)"
  by (metis Aleph ZFC_in_HOL.SUP_le_iff replacement small_elts sup_ge2)

lemma Aleph_in_Aleph: "\<alpha> \<in> elts \<beta> \<Longrightarrow> Aleph \<alpha> \<in> elts (Aleph \<beta>)"
  using csucc_Aleph_le_Aleph mem_Aleph_succ by auto

lemma Aleph_Limit:
  assumes "Limit \<gamma>"
  shows "Aleph \<gamma> = \<Squnion> (Aleph ` elts \<gamma>)"
proof -
  have [simp]: "\<gamma> \<noteq> 0"
    using assms by auto 
  show ?thesis
  proof (rule antisym)
    show "Aleph \<gamma> \<le> \<Squnion> (Aleph ` elts \<gamma>)"
      apply (simp add: Aleph [of \<gamma>])
      by (metis (mono_tags, lifting) Aleph_0 Aleph_succ Limit_def ZFC_in_HOL.SUP_le_iff ZFC_in_HOL.Sup_upper assms imageI replacement small_elts)
    show "\<Squnion> (Aleph ` elts \<gamma>) \<le> Aleph \<gamma>"
      apply (simp add: cSup_le_iff)
      by (meson Card_Aleph InfCard_def csucc_Aleph_le_Aleph le_csucc order_trans)
  qed
qed

thm Aleph_increasing
lemma Aleph_increasing:
  assumes ab: "\<alpha> < \<beta>" "Ord \<alpha>" "Ord \<beta>" shows "Aleph(\<alpha>) < Aleph(\<beta>)"
  by (meson Aleph_in_Aleph Card_Aleph Card_iff_initial InfCard_def Ord_mem_iff_lt assms)

lemma countable_iff_le_Aleph0: "countable (elts A) \<longleftrightarrow> vcard A \<le> Aleph 0"
proof
  show "vcard A \<le> Aleph 0"
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
    if "vcard A \<le> Aleph 0"
  proof -
    have "elts A \<lesssim> elts \<omega>"
      using cardinal_le_lepoll [OF that] by simp
    then show ?thesis
      by (simp add: countable_iff_lepoll \<omega>_def inj_ord_of_nat)
  qed
qed

end
