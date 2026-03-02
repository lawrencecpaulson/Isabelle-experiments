theory Sylow
  imports Group_Theory "HOL-Computational_Algebra.Primes"

"HOL-ex.Sketch_and_Explore"

begin

text \<open>See also \<^cite>\<open>"Kammueller-Paulson:1999"\<close>.\<close>

text \<open>The Combinatorial Argument Underlying the First Sylow Theorem\<close>

text\<open>needed in this form to prove Sylow's theorem\<close>
corollary (in algebraic_semidom) div_combine: 
  "\<lbrakk>prime_elem p; \<not> p ^ Suc r dvd n; p ^ (a + r) dvd n * k\<rbrakk> \<Longrightarrow> p ^ a dvd k"
  by (metis add_Suc_right mult.commute prime_elem_power_dvd_cases)

lemma exponent_p_a_m_k_equation: 
  fixes p :: nat
  assumes "0 < m" "0 < k" "p \<noteq> 0" "k < p^a" 
    shows "multiplicity p (p^a * m - k) = multiplicity p (p^a - k)"
proof (rule multiplicity_cong [OF iffI])
  fix r
  assume *: "p ^ r dvd p ^ a * m - k" 
  show "p ^ r dvd p ^ a - k"
  proof -
    have "k \<le> p ^ a * m" using assms
      by (meson nat_dvd_not_less dvd_triv_left leI mult_pos_pos order.strict_trans)
    then have "r \<le> a"
      by (meson "*" \<open>0 < k\<close> \<open>k < p^a\<close> dvd_diffD1 dvd_triv_left leI less_imp_le_nat nat_dvd_not_less power_le_dvd)
    then have "p^r dvd p^a * m" by (simp add: le_imp_power_dvd)
    thus ?thesis
      by (meson \<open>k \<le> p ^ a * m\<close> \<open>r \<le> a\<close> * dvd_diffD1 dvd_diff_nat le_imp_power_dvd)
  qed
next
  fix r
  assume *: "p ^ r dvd p ^ a - k" 
  with assms have "r \<le> a"
    by (meson dvd_diffD1 dvd_imp_le le_imp_power_dvd linorder_not_le order_le_less power_le_dvd)
  show "p ^ r dvd p ^ a * m - k"
  proof -
    have "p^r dvd p^a*m"
      by (simp add: \<open>r \<le> a\<close> le_imp_power_dvd)
    then show ?thesis
      by (meson assms * dvd_diffD1 dvd_diff_nat le_imp_power_dvd less_imp_le_nat \<open>r \<le> a\<close>)
  qed
qed

lemma p_not_div_choose_lemma: 
  fixes p :: nat
  assumes eeq: "\<And>i. Suc i < K \<Longrightarrow> multiplicity p (Suc i) = multiplicity p (Suc (j + i))"
      and "k < K" and p: "prime p"
    shows "multiplicity p (j + k choose k) = 0"
  using \<open>k < K\<close>
proof (induction k)
  case 0 then show ?case by simp
next
  case (Suc k)
  then have *: "(Suc (j+k) choose Suc k) > 0" by simp
  then have "multiplicity p ((Suc (j+k) choose Suc k) * Suc k) = multiplicity p (Suc k)"
    by (subst Suc_times_binomial_eq [symmetric], subst prime_elem_multiplicity_mult_distrib)
       (insert p Suc.prems, simp_all add: eeq [symmetric] Suc.IH)
  with p * show ?case
    by (subst (asm) prime_elem_multiplicity_mult_distrib) simp_all
qed

text\<open>The lemma above, with two changes of variables\<close>
lemma p_not_div_choose:
  assumes "k < K" and "k \<le> n" 
      and eeq: "\<And>j. \<lbrakk>0<j; j<K\<rbrakk> \<Longrightarrow> multiplicity p (n - k + (K - j)) = multiplicity p (K - j)"
      and "prime p"
    shows "multiplicity p (n choose k) = 0"
proof (rule p_not_div_choose_lemma [of K p "n-k" k, simplified assms nat_minus_add_max max_absorb1])
  show "\<And>i. Suc i < K \<Longrightarrow> multiplicity p (Suc i) = multiplicity p (Suc (n - k + i))"
    by (metis add_Suc_right diff_diff_cancel eeq nat_less_le zero_less_Suc zero_less_diff)
qed auto

proposition const_p_fac:
  assumes "m>0" and prime: "prime p"
  shows "multiplicity p (p^a * m choose p^a) = multiplicity p m"
proof-
  from assms have p: "0 < p ^ a" "0 < p^a * m" "p^a \<le> p^a * m"
    by (auto simp: prime_gt_0_nat) 
  have *: "multiplicity p ((p^a * m - 1) choose (p^a - 1)) = 0"
    apply (rule p_not_div_choose [where K = "p^a"])
    using p exponent_p_a_m_k_equation by (auto simp: diff_le_mono prime)
  have "multiplicity p ((p ^ a * m choose p ^ a) * p ^ a) = a + multiplicity p m"
  proof -
    have "(p ^ a * m choose p ^ a) * p ^ a = p ^ a * m * (p ^ a * m - 1 choose (p ^ a - 1))" 
      (is "_ = ?rhs") using prime 
      by (subst times_binomial_minus1_eq [symmetric]) (auto simp: prime_gt_0_nat)
    also from p have "p ^ a - Suc 0 \<le> p ^ a * m - Suc 0" by linarith
    with prime * p have "multiplicity p ?rhs = multiplicity p (p ^ a * m)"
      by (subst prime_elem_multiplicity_mult_distrib) auto
    also have "\<dots> = a + multiplicity p m" 
      using prime p by (subst prime_elem_multiplicity_mult_distrib) simp_all
    finally show ?thesis .
  qed
  then show ?thesis
    using prime p by (subst (asm) prime_elem_multiplicity_mult_distrib) simp_all
qed

lemma le_extend_mult: "\<lbrakk>0 < c; a \<le> b\<rbrakk> \<Longrightarrow> a \<le> b * c" for c :: nat
  using gr0_conv_Suc by fastforce

locale sylow = Group G "(\<cdot>)" \<one>
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  fixes p::nat
  assumes finite_G: "finite G"
    and prime_p: "prime p"
    and order_G: "card G = (p^a) * m"


  oops +
  fixes p and a and m and calM and RelM
  assumes prime_p: "prime p"
    and order_G: "order G = (p^a) * m"
    and finite_G[iff]: "finite (carrier G)"
  defines "calM \<equiv> {s. s \<subseteq> carrier G \<and> card s = p^a}"
    and "RelM \<equiv> {(N1, N2). N1 \<in> calM \<and> N2 \<in> calM \<and> (\<exists>g \<in> carrier G. N1 = N2 #> g)}"
begin

lemma RelM_subset: "RelM \<subseteq> calM \<times> calM"
  by (auto simp only: RelM_def)

lemma RelM_refl_on: "refl_on calM RelM"
  by (auto simp: refl_on_def RelM_def calM_def) (blast intro!: coset_mult_one [symmetric])

lemma RelM_sym: "sym RelM"
  unfolding sym_def RelM_def calM_def
  using coset_mult_assoc coset_mult_one r_inv_ex
  by (smt (verit, best) case_prod_conv mem_Collect_eq)

lemma RelM_trans: "trans RelM"
  by (auto simp add: trans_def RelM_def calM_def coset_mult_assoc)

lemma RelM_equiv: "equiv calM RelM"
  using RelM_subset RelM_refl_on RelM_sym RelM_trans by (intro equivI)

lemma M_subset_calM_prep: "M' \<in> calM // RelM  \<Longrightarrow> M' \<subseteq> calM"
  unfolding RelM_def by (blast elim!: quotientE)

end

subsection \<open>Main Part of the Proof\<close>

locale sylow_central = sylow +
  fixes H and M1 and M
  assumes M_in_quot: "M \<in> calM // RelM"
    and not_dvd_M: "\<not> (p ^ Suc (multiplicity p m) dvd card M)"
    and M1_in_M: "M1 \<in> M"
  defines "H \<equiv> {g. g \<in> carrier G \<and> M1 #> g = M1}"
begin

lemma M_subset_calM: "M \<subseteq> calM"
  by (simp add: M_in_quot M_subset_calM_prep)

lemma card_M1: "card M1 = p^a"
  using M1_in_M M_subset_calM calM_def by blast

lemma exists_x_in_M1: "\<exists>x. x \<in> M1"
  using prime_p [THEN prime_gt_Suc_0_nat] card_M1 one_in_subset by fastforce

lemma M1_subset_G [simp]: "M1 \<subseteq> carrier G"
  using M1_in_M M_subset_calM calM_def mem_Collect_eq subsetCE by blast

lemma M1_inj_H: "\<exists>f \<in> H\<rightarrow>M1. inj_on f H"
proof -
  from exists_x_in_M1 obtain m1 where m1M: "m1 \<in> M1"..
  show ?thesis
  proof
    have "m1 \<in> carrier G"
      by (simp add: m1M M1_subset_G [THEN subsetD])
    then show "inj_on (\<lambda>z\<in>H. m1 \<otimes> z) H"
      by (simp add: H_def inj_on_def)
    show "restrict ((\<otimes>) m1) H \<in> H \<rightarrow> M1"
      using H_def m1M rcosI by auto
  qed
qed

end


subsection \<open>Discharging the Assumptions of \<open>sylow_central\<close>\<close>

context sylow
begin

lemma EmptyNotInEquivSet: "{} \<notin> calM // RelM"
  using RelM_equiv in_quotient_imp_non_empty by blast

lemma existsM1inM: "M \<in> calM // RelM \<Longrightarrow> \<exists>M1. M1 \<in> M"
  using RelM_equiv equiv_Eps_in by blast

lemma zero_less_o_G: "0 < order G"
  by (simp add: order_def card_gt_0_iff carrier_not_empty)

lemma zero_less_m: "m > 0"
  using zero_less_o_G by (simp add: order_G)

lemma card_calM: "card calM = (p^a) * m choose p^a"
  by (simp add: calM_def n_subsets order_G [symmetric] order_def)

lemma zero_less_card_calM: "card calM > 0"
  by (simp add: card_calM zero_less_binomial le_extend_mult zero_less_m)

lemma max_p_div_calM: "\<not> (p ^ Suc (multiplicity p m) dvd card calM)"
proof
  assume "p ^ Suc (multiplicity p m) dvd card calM"
  with zero_less_card_calM prime_p
  have "Suc (multiplicity p m) \<le> multiplicity p (card calM)"
    by (intro multiplicity_geI) auto
  then show False
    by (simp add: card_calM const_p_fac prime_p zero_less_m)
qed

lemma finite_calM: "finite calM"
  unfolding calM_def by (rule finite_subset [where B = "Pow (carrier G)"]) auto

lemma lemma_A1: "\<exists>M \<in> calM // RelM. \<not> (p ^ Suc (multiplicity p m) dvd card M)"
  using RelM_equiv equiv_imp_dvd_card finite_calM max_p_div_calM by blast

end


subsubsection \<open>Introduction and Destruct Rules for \<open>H\<close>\<close>

context sylow_central
begin

lemma H_I: "\<lbrakk>g \<in> carrier G; M1 #> g = M1\<rbrakk> \<Longrightarrow> g \<in> H"
  by (simp add: H_def)

lemma H_into_carrier_G: "x \<in> H \<Longrightarrow> x \<in> carrier G"
  by (simp add: H_def)

lemma in_H_imp_eq: "g \<in> H \<Longrightarrow> M1 #> g = M1"
  by (simp add: H_def)

lemma H_m_closed: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> H"
  by (simp add: H_def coset_mult_assoc [symmetric])

lemma H_not_empty: "H \<noteq> {}"
  by (force simp add: H_def intro: exI [of _ \<one>])

lemma H_is_subgroup: "subgroup H G"
proof (rule subgroupI)
  show "H \<subseteq> carrier G"
    using H_into_carrier_G by blast
  show "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
    by (metis H_I H_into_carrier_G M1_subset_G coset_mult_assoc coset_mult_one in_H_imp_eq inv_closed r_inv)
  show "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
    by (blast intro: H_m_closed)
qed (use H_not_empty in auto)

lemma rcosetGM1g_subset_G: "\<lbrakk>g \<in> carrier G; x \<in> M1 #> g\<rbrakk> \<Longrightarrow> x \<in> carrier G"
  by (blast intro: M1_subset_G [THEN r_coset_subset_G, THEN subsetD])

lemma finite_M1: "finite M1"
  by (rule finite_subset [OF M1_subset_G finite_G])

lemma finite_rcosetGM1g: "g \<in> carrier G \<Longrightarrow> finite (M1 #> g)"
  using rcosetGM1g_subset_G finite_G M1_subset_G cosets_finite rcosetsI by blast

lemma M1_cardeq_rcosetGM1g: "g \<in> carrier G \<Longrightarrow> card (M1 #> g) = card M1"
  by (metis M1_subset_G card_rcosets_equal rcosetsI)

lemma M1_RelM_rcosetGM1g: 
  assumes "g \<in> carrier G"
  shows "(M1, M1 #> g) \<in> RelM"
proof -
  have "M1 #> g \<subseteq> carrier G"
    by (simp add: assms r_coset_subset_G)
  moreover have "card (M1 #> g) = p ^ a"
    using assms by (simp add: card_M1 M1_cardeq_rcosetGM1g)
  moreover have "\<exists>h\<in>carrier G. M1 = M1 #> g #> h"
    by (metis assms M1_subset_G coset_mult_assoc coset_mult_one r_inv_ex)
  ultimately show ?thesis
    by (simp add: RelM_def calM_def card_M1)
qed

end


subsection \<open>Equal Cardinalities of \<open>M\<close> and the Set of Cosets\<close>

text \<open>Injections between \<^term>\<open>M\<close> and \<^term>\<open>rcosets\<^bsub>G\<^esub> H\<close> show that
 their cardinalities are equal.\<close>

lemma ElemClassEquiv: "\<lbrakk>equiv A r; C \<in> A // r\<rbrakk> \<Longrightarrow> \<forall>x \<in> C. \<forall>y \<in> C. (x, y) \<in> r"
  unfolding equiv_def quotient_def sym_def trans_def by blast

context sylow_central
begin

lemma M_elem_map: "M2 \<in> M \<Longrightarrow> \<exists>g. g \<in> carrier G \<and> M1 #> g = M2"
  using M1_in_M M_in_quot [THEN RelM_equiv [THEN ElemClassEquiv]]
  by (simp add: RelM_def) (blast dest!: bspec)

lemmas M_elem_map_carrier = M_elem_map [THEN someI_ex, THEN conjunct1]

lemmas M_elem_map_eq = M_elem_map [THEN someI_ex, THEN conjunct2]

lemma M_funcset_rcosets_H:
  "(\<lambda>x\<in>M. H #> (SOME g. g \<in> carrier G \<and> M1 #> g = x)) \<in> M \<rightarrow> rcosets H"
  by (metis (lifting) H_is_subgroup M_elem_map_carrier rcosetsI restrictI subgroup.subset)

lemma inj_M_GmodH: "\<exists>f \<in> M \<rightarrow> rcosets H. inj_on f M"
proof
  let ?inv = "\<lambda>x. SOME g. g \<in> carrier G \<and> M1 #> g = x"
  show "inj_on (\<lambda>x\<in>M. H #> ?inv x) M"
  proof (rule inj_onI, simp)
    fix x y
    assume eq: "H #> ?inv x = H #> ?inv y" and xy: "x \<in> M" "y \<in> M"
    have "x = M1 #> ?inv x"
      by (simp add: M_elem_map_eq \<open>x \<in> M\<close>)
    also have "\<dots> = M1 #> ?inv y"
    proof (rule coset_mult_inv1 [OF in_H_imp_eq [OF coset_join1]])
      show "H #> ?inv x \<otimes> inv (?inv y) = H"
        by (simp add: H_into_carrier_G M_elem_map_carrier xy coset_mult_inv2 eq subsetI)
    qed (simp_all add: H_is_subgroup M_elem_map_carrier xy)
    also have "\<dots> = y"
      using M_elem_map_eq \<open>y \<in> M\<close> by simp
    finally show "x=y" .
  qed
  show "(\<lambda>x\<in>M. H #> ?inv x) \<in> M \<rightarrow> rcosets H"
    by (rule M_funcset_rcosets_H)
qed

end


subsubsection \<open>The Opposite Injection\<close>

context sylow_central
begin

lemma H_elem_map: "H1 \<in> rcosets H \<Longrightarrow> \<exists>g. g \<in> carrier G \<and> H #> g = H1"
  by (auto simp: RCOSETS_def)

lemmas H_elem_map_carrier = H_elem_map [THEN someI_ex, THEN conjunct1]

lemmas H_elem_map_eq = H_elem_map [THEN someI_ex, THEN conjunct2]

lemma rcosets_H_funcset_M:
  "(\<lambda>C \<in> rcosets H. M1 #> (SOME g. g \<in> carrier G \<and> H #> g = C)) \<in> rcosets H \<rightarrow> M"
  using in_quotient_imp_closed [OF RelM_equiv M_in_quot _  M1_RelM_rcosetGM1g]
  by (simp add: M1_in_M H_elem_map_carrier RCOSETS_def)

lemma inj_GmodH_M: "\<exists>g \<in> rcosets H\<rightarrow>M. inj_on g (rcosets H)"
proof
  let ?inv = "\<lambda>x. SOME g. g \<in> carrier G \<and> H #> g = x"
  show "inj_on (\<lambda>C\<in>rcosets H. M1 #> ?inv C) (rcosets H)"
  proof (rule inj_onI, simp)
    fix x y
    assume eq: "M1 #> ?inv x = M1 #> ?inv y" and xy: "x \<in> rcosets H" "y \<in> rcosets H"
    have "x = H #> ?inv x"
      by (simp add: H_elem_map_eq \<open>x \<in> rcosets H\<close>)
    also have "\<dots> = H #> ?inv y"
    proof (rule coset_mult_inv1 [OF coset_join2])
      show "?inv x \<otimes> inv (?inv y) \<in> carrier G"
        by (simp add: H_elem_map_carrier \<open>x \<in> rcosets H\<close> \<open>y \<in> rcosets H\<close>)
      then show "(?inv x) \<otimes> inv (?inv y) \<in> H"
        by (simp add: H_I H_elem_map_carrier xy coset_mult_inv2 eq)
      show "H \<subseteq> carrier G"
        by (simp add: H_is_subgroup subgroup.subset)
    qed (simp_all add: H_is_subgroup H_elem_map_carrier xy)
    also have "\<dots> = y"
      by (simp add: H_elem_map_eq \<open>y \<in> rcosets H\<close>)
    finally show "x=y" .
  qed
  show "(\<lambda>C\<in>rcosets H. M1 #> ?inv C) \<in> rcosets H \<rightarrow> M"
    using rcosets_H_funcset_M by blast
qed

lemma calM_subset_PowG: "calM \<subseteq> Pow (carrier G)"
  by (auto simp: calM_def)


lemma finite_M: "finite M"
  by (metis M_subset_calM finite_calM rev_finite_subset)

lemma cardMeqIndexH: "card M = card (rcosets H)"
  using inj_M_GmodH inj_GmodH_M
  by (metis H_is_subgroup card_bij finite_G finite_M finite_UnionD rcosets_part_G)

lemma index_lem: "card M * card H = order G"
  by (simp add: cardMeqIndexH lagrange H_is_subgroup)

lemma card_H_eq: "card H = p^a"
proof (rule antisym)
  show "p^a \<le> card H"
  proof (rule dvd_imp_le)
    have "p ^ (a + multiplicity p m) dvd card M * card H"
      by (simp add: index_lem multiplicity_dvd order_G power_add)
    then show "p ^ a dvd card H"
      using div_combine not_dvd_M prime_p by blast
    show "0 < card H"
      by (blast intro: subgroup.finite_imp_card_positive H_is_subgroup)
  qed
next
  show "card H \<le> p^a"
    using M1_inj_H card_M1 card_inj finite_M1 by fastforce
qed

end

lemma (in sylow) sylow_thm: "\<exists>H. subgroup H G \<and> card H = p^a"
proof -
  obtain M where M: "M \<in> calM // RelM" "\<not> (p ^ Suc (multiplicity p m) dvd card M)"
    using lemma_A1 by blast
  then obtain M1 where "M1 \<in> M"
    by (metis existsM1inM) 
  define H where "H \<equiv> {g. g \<in> carrier G \<and> M1 #> g = M1}"
  with M \<open>M1 \<in> M\<close>
  interpret sylow_central G p a m calM RelM H M1 M
    by unfold_locales (auto simp add: H_def calM_def RelM_def)
  show ?thesis
    using H_is_subgroup card_H_eq by blast
qed

text \<open>Needed because the locale's automatic definition refers to
  \<^term>\<open>semigroup G\<close> and \<^term>\<open>group_axioms G\<close> rather than
  simply to \<^term>\<open>group G\<close>.\<close>
lemma sylow_eq: "sylow G p a m \<longleftrightarrow> group G \<and> sylow_axioms G p a m"
  by (simp add: sylow_def group_def)


subsection \<open>Sylow's Theorem\<close>

theorem sylow_thm:
  "\<lbrakk>prime p; group G; order G = (p^a) * m; finite (carrier G)\<rbrakk>
    \<Longrightarrow> \<exists>H. subgroup H G \<and> card H = p^a"
  by (rule sylow.sylow_thm [of G p a m]) (simp add: sylow_eq sylow_axioms_def)

end
