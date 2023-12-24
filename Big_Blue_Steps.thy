section \<open>Big Blue Steps: theorems\<close>

theory Big_Blue_Steps imports Diagonal

begin

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

text \<open>How @{term b} and @{term m} are obtained from @{term l}\<close>
definition b_of where "b_of \<equiv> \<lambda>l::nat. nat\<lceil>l powr (1/4)\<rceil>"
definition m_of where "m_of \<equiv> \<lambda>l::nat. nat\<lceil>l powr (2/3)\<rceil>"

context Diagonal
begin

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
        by (auto simp: disjoint_family_on_def all_edges_betw_un_def)
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
        show "0 \<le> (5/4) powr (1/b) - 1"
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
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> finite (Step_class \<mu> l k bblue_step) \<and> card (Step_class \<mu> l k bblue_step) \<le> l powr (3/4)"
proof -
  have "finite (Step_class \<mu> l k bblue_step) \<and> card (Step_class \<mu> l k bblue_step) \<le> l powr (3/4)"
    if 41: "\<And>X. many_bluish \<mu> l k X \<Longrightarrow> X\<subseteq>V \<Longrightarrow> \<exists>S T. good_blue_book \<mu> X (S,T) \<and> card S \<ge> l powr (1/4)"
      and "Colours l k" for l k
  proof -
    define BBLUES where "BBLUES \<equiv> \<lambda>r. {m. m < r \<and> stepper_kind \<mu> l k m = bblue_step}"
    have cardB_ge: "card B \<ge> b_of l * card(BBLUES n)"
      if "stepper \<mu> l k n = (X,Y,A,B)" for n X Y A B
      using that
    proof (induction n arbitrary: X Y A B)
      case 0 then show ?case by (auto simp: BBLUES_def)
    next
      case (Suc n)
      obtain X' Y' A' B' where step_n: "stepper \<mu> l k n = (X',Y',A',B')"
        by (metis surj_pair)
      then have "valid_state (X',Y',A',B')"
        by (metis valid_state_stepper)
      have "B' \<subseteq> B"
        using Suc by (auto simp: next_state_def Let_def degree_reg_def step_n split: prod.split_asm if_split_asm)
      show ?case
      proof (cases "stepper_kind \<mu> l k n = bblue_step")
        case True
        have [simp]: "card (insert n (BBLUES n)) = Suc (card (BBLUES n))"
          by (simp add: BBLUES_def)
        have card_B': "card B' \<ge> b_of l * card (BBLUES n)"
          using step_n BBLUES_def Suc.IH by blast
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
        have eq: "BBLUES(Suc n) = insert n (BBLUES n)"
          using less_Suc_eq True unfolding BBLUES_def by blast
        then have "b_of l * card (BBLUES (Suc n)) = b_of l + b_of l * card (BBLUES n)"
          by auto
        also have "\<dots> \<le> card B' + card S"
          using ble card_B' by linarith
        also have "... \<le> card (B' \<union> S)"
          using ble \<open>disjnt B' S\<close> fin by (simp add: card_Un_disjnt)
        finally have **: "b_of l * card (BBLUES (Suc n)) \<le> card B"
          using dual_order.trans le_cardB by blast 
        then show ?thesis
          by (simp add: BBLUES_def)
      next
        case False
        then have "BBLUES(Suc n) = BBLUES n"
          using less_Suc_eq by (auto simp: BBLUES_def) 
        with \<open>B' \<subseteq> B\<close> show ?thesis
          by (metis Suc V_state card_mono dual_order.trans finB step_n)
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
      have "l = l powr (1/4) * l powr (3/4)"
        by (simp flip: powr_add)
      also have "\<dots> \<le> b_of l * l powr (3/4)"
        by (simp add: b_of_def mult_mono real_nat_ceiling_ge)
      also have "\<dots> \<le> b_of l * card{m. m<n \<and> stepper_kind \<mu> l k m = bblue_step}"
        using card_gt less_eq_real_def by fastforce
      also have "... \<le> card B"
        using cardB_ge step of_nat_mono unfolding BBLUES_def by blast
      also have "... < l"
        using stepper_B[OF step] \<open>\<mu>>0\<close> \<open>Colours l k\<close>
        by (metis Colours_def linorder_neqE_nat of_nat_less_iff size_clique_def size_clique_smaller)
      finally have False
        by simp
    } 
    moreover have "finite (Step_class \<mu> l k bblue_step)"
    proof (intro finite_Step_class)
      show "finite {m. m < n \<and> stepper_kind \<mu> l k m = bblue_step}" for n
        by fastforce
      have *: "card{m. m<n \<and> stepper_kind \<mu> l k m = bblue_step} \<le> l div b_of l"
        if "stepper \<mu> l k n = (X,Y,A,B)" for n X Y A B
      proof -
        have "b_of l \<noteq> 0"
          using Colours_ln0 [OF \<open>Colours l k\<close>] by (simp add: b_of_def)
        then show ?thesis
          using cardB_ge [OF that] card_B_limit [OF that \<open>Colours l k\<close>] 
          by (simp add: BBLUES_def mult.commute less_eq_div_iff_mult_less_eq)
      qed
      then show "card {m. m < n \<and> stepper_kind \<mu> l k m = bblue_step} < Suc (l div b_of l)" for n
        by (meson le_imp_less_Suc prod_cases4)
    qed
    ultimately show ?thesis by force
  qed
  with eventually_mono [OF Blue_4_1] \<open>\<mu>>0\<close> show ?thesis
    by presburger 
qed

corollary red_step_limit:
  assumes "\<mu>>0" "Colours l k"
  shows "finite (Step_class \<mu> l k red_step)" "card (Step_class \<mu> l k red_step) < k"
proof -
  define REDS where "REDS \<equiv> \<lambda>r. {m. m < r \<and> stepper_kind \<mu> l k m = red_step}"
  have *: "card(REDS n) \<le> card A"
    if "stepper \<mu> l k n = (X,Y,A,B)" for n X Y A B
    using that
  proof (induction n arbitrary: X Y A B)
    case 0
    then show ?case
      by (auto simp: REDS_def)
  next
    case (Suc n)
    obtain X' Y' A' B' where step_n: "stepper \<mu> l k n = (X',Y',A',B')"
      by (metis surj_pair)
    then have "valid_state (X',Y',A',B')"
      by (metis valid_state_stepper)
    then have "finite A'"
      using finA valid_state_def by auto
    have "A' \<subseteq> A"
      using Suc.prems by (auto simp: next_state_def Let_def degree_reg_def step_n split: prod.split_asm if_split_asm)
    show ?case
    proof (cases "stepper_kind \<mu> l k n = red_step")
      case True
      then have "REDS (Suc n) = insert n (REDS n)"
        by (auto simp: REDS_def)
      moreover have "card (insert n (REDS n)) = Suc (card (REDS n))"
        by (simp add: REDS_def)
      ultimately have [simp]: "card (REDS (Suc n)) = Suc (card (REDS n))"
        by presburger
      have card_A': "card (REDS n) \<le> card A'"
        using step_n REDS_def Suc.IH by blast
      have Aeq: "A = insert (choose_central_vx \<mu> (X',Y',A',B')) A'"
        using Suc.prems True
        by (auto simp: stepper_kind_def next_state_kind_def next_state_def Let_def step_n split: if_split_asm)
      have "choose_central_vx \<mu> (X',Y',A',B') \<in> X'"
        using True
        apply (clarsimp simp: stepper_kind_def next_state_kind_def step_n split: if_split_asm)
        by (metis V_state choose_central_vx_X step_n)
      moreover
      have "disjnt X' A'"
        using \<open>valid_state (X',Y',A',B')\<close> by (simp add: valid_state_def disjoint_state_def)
      ultimately have "choose_central_vx \<mu> (X',Y',A',B') \<notin> A'"
        by (simp add: disjnt_iff)
      then have "card (REDS (Suc n)) \<le> card A"
        by (simp add: Aeq \<open>finite A'\<close> card_A')
      then show ?thesis
        by (simp add: REDS_def)
    next
      case False
      then have "REDS(Suc n) = REDS n"
        using less_Suc_eq unfolding REDS_def by blast
      with \<open>A' \<subseteq> A\<close> show ?thesis
        by (smt (verit, best) Suc V_state card_seteq order.trans finA nat_le_linear step_n)
    qed
  qed
  have less_k: "card (REDS n) < k" for n
  proof -
    obtain X Y A B where step: "stepper \<mu> l k n = (X,Y,A,B)"
      using prod_cases4 by blast
    with * show ?thesis
      using \<open>Colours l k\<close> card_A_limit by fastforce
  qed
  moreover have "\<And>n. finite (REDS n)" "incseq REDS"
    by (auto simp: REDS_def incseq_def)
  ultimately have "\<forall>\<^sup>\<infinity>n. \<Union> (range REDS) = REDS n"
    using Union_incseq_finite by blast
  then have "finite (\<Union> (range REDS))"
    using REDS_def eventually_sequentially by force
  moreover have "(Step_class \<mu> l k red_step) \<subseteq> \<Union> (range REDS)"
    by (auto simp: Step_class_def REDS_def)
  ultimately show "finite (Step_class \<mu> l k red_step)"
    using infinite_super by blast
  with less_k show "card (Step_class \<mu> l k red_step) < k"
    by (metis (full_types) REDS_def Step_class_iterates)
qed

corollary bblue_dboost_step_limit:
  assumes "\<mu>>0"
  shows "\<forall>\<^sup>\<infinity>l. \<forall>k. Colours l k \<longrightarrow> 
            finite (Step_class \<mu> l k dboost_step) 
          \<and> card (Step_class \<mu> l k bblue_step) + card (Step_class \<mu> l k dboost_step) < l"
proof -
  have "finite (Step_class \<mu> l k dboost_step) 
      \<and> card (Step_class \<mu> l k bblue_step) + card (Step_class \<mu> l k dboost_step) < l"
    if 41: "\<And>X. many_bluish \<mu> l k X \<Longrightarrow> X\<subseteq>V \<Longrightarrow> \<exists>S T. good_blue_book \<mu> X (S,T) \<and> card S \<ge> l powr (1/4)"
      and "Colours l k" for l k
  proof 
    define BDB where "BDB \<equiv> \<lambda>r. {m. m < r \<and> stepper_kind \<mu> l k m \<in> {bblue_step,dboost_step}}"
    have *: "card(BDB n) \<le> card B"
      if "stepper \<mu> l k n = (X,Y,A,B)" for n X Y A B
      using that
    proof (induction n arbitrary: X Y A B)
      case 0
      then show ?case
        by (auto simp: BDB_def)
    next
      case (Suc n)
      obtain X' Y' A' B' where step_n: "stepper \<mu> l k n = (X',Y',A',B')"
        by (metis surj_pair)
      then obtain "valid_state (X',Y',A',B')" and "V_state (X',Y',A',B')"
        and disjst: "disjoint_state(X',Y',A',B')"
        by (metis valid_state_def valid_state_stepper)
      have "B' \<subseteq> B"
        using Suc.prems by (auto simp: next_state_def Let_def degree_reg_def step_n split: prod.split_asm if_split_asm)
      show ?case
      proof (cases "stepper_kind \<mu> l k n \<in> {bblue_step,dboost_step}")
        case True
        then have "BDB (Suc n) = insert n (BDB n)"
          by (auto simp: BDB_def)
        moreover have "card (insert n (BDB n)) = Suc (card (BDB n))"
          by (simp add: BDB_def)
        ultimately have card_Suc[simp]: "card (BDB (Suc n)) = Suc (card (BDB n))"
          by presburger
        have card_B': "card (BDB n) \<le> card B'"
          using step_n BDB_def Suc.IH by blast
        consider "stepper_kind \<mu> l k n = bblue_step" | "stepper_kind \<mu> l k n = dboost_step"
          using True by force
        then have Bigger: "B' \<subset> B"
        proof cases
          case 1
          then have "\<not> termination_condition (real l) k X' Y'"
            by (auto simp: stepper_kind_def step_n)
          with 1 obtain S where "A' = A" "Y' = Y" and manyb: "many_bluish \<mu> l k X'" 
            and cbb: "choose_blue_book \<mu> (X',Y,A,B') = (S,X)" and le_cardB: "B = B' \<union> S"
            using Suc.prems 
            by (auto simp: stepper_kind_def next_state_kind_def next_state_def step_n split: prod.split_asm if_split_asm)
          then have VS: "V_state (X',Y,A,B')" and ds: "disjoint_state (X',Y,A,B')"
            using \<open>valid_state (X',Y',A',B')\<close> by (auto simp: valid_state_def)
          then have "X' \<subseteq> V"
            by (simp add: V_state_def)
          then have "l powr (1/4) \<le> real (card S)"
            using \<open>Colours l k\<close> 41 [OF manyb]
            by (smt (verit, best) VS best_blue_book_is_best cbb choose_blue_book_works of_nat_mono)
          then have "S \<noteq> {}"
            using Colours_ln0 \<open>Colours l k\<close> by fastforce
          moreover have "disjnt B' S"
            using choose_blue_book_subset [OF \<open>V_state (X',Y',A',B')\<close>] disjst cbb
            unfolding disjoint_state_def
            by (smt (verit) in_mono \<open>A' = A\<close> \<open>Y' = Y\<close> disjnt_iff old.prod.case)
          ultimately show ?thesis
            by (metis \<open>B' \<subseteq> B\<close> disjnt_Un1 disjnt_self_iff_empty le_cardB psubsetI)
        next
          case 2
          then have "choose_central_vx \<mu> (X',Y',A',B') \<in> X'"
            apply (clarsimp simp: stepper_kind_def next_state_kind_def step_n split: if_split_asm)
            by (metis V_state choose_central_vx_X step_n)
          moreover have "disjnt B' X'"
            using disjst disjnt_sym by (force simp add: disjoint_state_def)
          ultimately have "choose_central_vx \<mu> (X',Y',A',B') \<notin> B'"
            by (meson disjnt_iff)
          then show ?thesis
            using 2 Suc.prems 
            by (auto simp: stepper_kind_def next_state_kind_def next_state_def step_n Let_def split: if_split_asm)
        qed
        moreover have "finite B"
          by (metis Suc.prems V_state finB)
        ultimately show ?thesis
          by (metis card.infinite card_B' card_Suc card_seteq dual_order.trans nat.case nless_le not_less_eq_eq)
      next
        case False
        then have "BDB (Suc n) = BDB n"
          using less_Suc_eq unfolding BDB_def by blast
        with \<open>B' \<subseteq> B\<close> show ?thesis
          by (smt (verit, best) Suc V_state card_seteq order.trans finB nat_le_linear step_n)
      qed
    qed
    have less_l: "card (BDB n) < l" for n
    proof -
      obtain X Y A B where "stepper \<mu> l k n = (X,Y,A,B)"
        using prod_cases4 by blast
      with * show ?thesis
        using \<open>Colours l k\<close> card_B_limit by fastforce
    qed
    moreover have fin: "\<And>n. finite (BDB n)" "incseq BDB"
      by (auto simp: BDB_def incseq_def)
    ultimately have **: "\<forall>\<^sup>\<infinity>n. \<Union> (range BDB) = BDB n"
      using Union_incseq_finite by blast
    then have "finite (\<Union> (range BDB))"
      using BDB_def eventually_sequentially by force
    moreover have Uneq: "(Step_class \<mu> l k bblue_step \<union> Step_class \<mu> l k dboost_step) = \<Union> (range BDB)"
      by (auto simp: Step_class_def BDB_def)
    ultimately have "finite (Step_class \<mu> l k bblue_step \<union> Step_class \<mu> l k dboost_step)"
      by presburger
    then show "finite (Step_class \<mu> l k dboost_step)"
      by blast
    obtain n where "\<Union> (range BDB) = BDB n"
      using ** by fastforce
    then show "card (Step_class \<mu> l k bblue_step) + card (Step_class \<mu> l k dboost_step) < l"
      using less_l fin Uneq
      by (metis card_Un_disjnt disjnt_Step_class finite_Un stepkind.distinct(8)) 
  qed
  with eventually_mono [OF Blue_4_1] \<open>\<mu>>0\<close> show ?thesis
    by presburger 
qed


section \<open>Density-boost steps\<close>

text \<open>"See observation 5.5 below"\<close>
lemma sum_Weight_ge0: "(\<Sum>x\<in>X. \<Sum>y\<in>X. Weight X Y x y) \<ge> 0"
  sorry

end

end

