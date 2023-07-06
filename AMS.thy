section \<open>Abstract Metric Spaces\<close>

theory AMS
  imports
    "HOL-Analysis.Analysis" "HOL-Library.Equipollence"
    "HOL-ex.Sketch_and_Explore"
begin



(******* delete sym_diff from Analysis/Equivalence_Measurable_On_Borel ******)


lemma power_of_nat_log_le: "b > 1 \<Longrightarrow> b ^ nat (floor(log b x)) \<le> x"
  oops

    lemma inj_onCI: "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x = f y \<Longrightarrow> x \<noteq> y \<Longrightarrow> False) \<Longrightarrow> inj_on f A"
      by (force simp: inj_on_def)

    
    thm first_countable_def Metric_space.openin_mtopology
    lemma (in Metric_space) first_countable_mtopology: "first_countable mtopology"
    proof (clarsimp simp add: first_countable_def)
      fix x
      assume "x \<in> M"
      define \<B> where "\<B> \<equiv> mball x ` {r \<in> \<rat>. 0 < r}"
      show "\<exists>\<B>. countable \<B> \<and> (\<forall>V\<in>\<B>. openin mtopology V) \<and> (\<forall>U. openin mtopology U \<and> x \<in> U \<longrightarrow> (\<exists>V\<in>\<B>. x \<in> V \<and> V \<subseteq> U))"
      proof (intro exI conjI ballI)
        show "countable \<B>"
          by (simp add: \<B>_def countable_rat)
        show "\<forall>U. openin mtopology U \<and> x \<in> U \<longrightarrow> (\<exists>V\<in>\<B>. x \<in> V \<and> V \<subseteq> U)"
        proof clarify
          fix U
          assume "openin mtopology U" and "x \<in> U"
          then obtain r where "r>0" and r: "mball x r \<subseteq> U"
            by (meson openin_mtopology)
          then obtain q where "q \<in> Rats" "0 < q" "q < r"
            using Rats_dense_in_real by blast
          then show "\<exists>V\<in>\<B>. x \<in> V \<and> V \<subseteq> U"
            unfolding \<B>_def using \<open>x \<in> M\<close> r by fastforce
        qed
      qed (auto simp: \<B>_def)
    qed
    
    lemma metrizable_imp_first_countable:
       "metrizable_space X \<Longrightarrow> first_countable X"
      by (force simp add: metrizable_space_def Metric_space.first_countable_mtopology)
    

subsection\<open> Theorems from Kuratowski\<close>

text\<open>Kuratowski, Remark on an Invariance Theorem, \emph{Fundamenta Mathematicae} \textbf{37} (1950), pp. 251-252. 
 The idea is that in suitable spaces, to show "number of components of the complement" (without 
 distinguishing orders of infinity) is a homeomorphic invariant, it 
 suffices to show it for closed subsets. Kuratowski states the main result 
 for a "locally connected continuum", and seems clearly to be implicitly   
 assuming that means metrizable. We call out the general topological       
 hypotheses more explicitly, which do not however include connectedness.   \<close>


lemma separation_by_closed_intermediates_count:
  assumes X: "hereditarily normal_space X"
    and "finite \<U>"
    and pwU: "pairwise (separatedin X) \<U>"
    and nonempty: "{} \<notin> \<U>"
    and UU: "\<Union>\<U> = topspace X - S"
  obtains C where "closedin X C" "C \<subseteq> S"
                  "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                     \<Longrightarrow> \<exists>\<V>. finite \<V> \<and> card \<V> = card \<U> \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - D"
proof -
  obtain F where F: "\<And>S. S \<in> \<U> \<Longrightarrow> openin X (F S) \<and> S \<subseteq> F S"
    and pwF: "pairwise (\<lambda>S T. disjnt (F S) (F T)) \<U>"
    using assms by (smt (verit, best) Diff_subset Sup_le_iff hereditarily_normal_separation_pairwise)
  show thesis
  proof
    show "closedin X (topspace X - \<Union>(F ` \<U>))"
      using F by blast
    show "topspace X - \<Union>(F ` \<U>) \<subseteq> S"
      using UU F by auto
    show "\<exists>\<V>. finite \<V> \<and> card \<V> = card \<U> \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - C"
      if "closedin X C" "C \<subseteq> S" and C: "topspace X - \<Union>(F ` \<U>) \<subseteq> C" for C
    proof (intro exI conjI strip)
      show "finite ((\<lambda>S. F S - C) ` \<U>)"
        by (simp add: assms(2))
      have "inj_on (\<lambda>S. F S - C) \<U>"
        using pwF F
        unfolding inj_on_def pairwise_def disjnt_iff
        by (metis Diff_iff UU UnionI nonempty subset_empty subset_eq \<open>C \<subseteq> S\<close>)
      then show "card ((\<lambda>S. F S - C) ` \<U>) = card \<U>"
        using card_image by blast
      show "pairwise (separatedin X) ((\<lambda>S. F S - C) ` \<U>)"
        using \<open>closedin X C\<close> F pwF by (force simp: pairwise_def openin_diff separatedin_open_sets disjnt_iff)
      show "{} \<notin> (\<lambda>S. F S - C) ` \<U>"
        using nonempty UU \<open>C \<subseteq> S\<close> F
        by clarify (metis DiffD2 Diff_eq_empty_iff F UnionI subset_empty subset_eq)
      show "(\<Union>S\<in>\<U>. F S - C) = topspace X - C"
        using UU F C openin_subset by fastforce
    qed
  qed
qed

lemma separation_by_closed_intermediates_gen:
  assumes X: "hereditarily normal_space X"
    and discon: "\<not> connectedin X (topspace X - S)"
  obtains C where "closedin X C" "C \<subseteq> S"
                  "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk> \<Longrightarrow> \<not> connectedin X (topspace X - D)"
proof -
  obtain C1 C2 where Ueq: "C1 \<union> C2 = topspace X - S" and "C1 \<noteq> {}" "C2 \<noteq> {}" 
    and sep: "separatedin X C1 C2" and "C1 \<noteq> C2"
    by (metis Diff_subset connectedin_eq_not_separated discon separatedin_refl)
  then obtain C where "closedin X C" "C \<subseteq> S"
    and C: "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                     \<Longrightarrow> \<exists>\<V>. finite \<V> \<and> card \<V> = Suc (Suc 0) \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - D"
    using separation_by_closed_intermediates_count [of X "{C1,C2}" S] X
    apply (simp add: pairwise_insert separatedin_sym)
    by metis
  have "\<not> connectedin X (topspace X - D)"
    if D: "closedin X D" "C \<subseteq> D" "D \<subseteq> S" for D 
  proof -
    obtain V1 V2 where *: "pairwise (separatedin X) {V1,V2}" "{} \<notin> {V1,V2}" 
                          "\<Union>{V1,V2} = topspace X - D" "V1\<noteq>V2"
      by (smt (verit, ccfv_SIG) C [OF D] pairwise_insert card_Suc_eq_finite card_0_eq insert_iff)
    then have "disjnt V1 V2"
      by (metis pairwise_insert separatedin_imp_disjoint singleton_iff)
      with * show ?thesis
        by (auto simp add: connectedin_eq_not_separated pairwise_insert)
    qed
  then show thesis
    using \<open>C \<subseteq> S\<close> \<open>closedin X C\<close> that by auto
qed


lemma separation_by_closed_intermediates_eq_count:
  assumes lcX: "locally_connected_space X" and hnX: "hereditarily normal_space X"
  shows "(\<exists>\<U>. finite \<U> \<and> card \<U> = n \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S
                   \<longrightarrow> (\<exists>\<U>. finite \<U> \<and> card \<U> = n \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D)))"
         (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis hnX separation_by_closed_intermediates_count)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "n=0")
    case True
    with R show ?thesis
      by (metis Diff_mono card_0_eq ccSup_empty empty_iff subsetI subset_antisym)
  next
    case False
    obtain C where "closedin X C" "C \<subseteq> S"
             and C: "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                      \<Longrightarrow> \<exists>\<U>. finite \<U> \<and> card \<U> = n \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D"
      using R by force
    then have "C \<subseteq> topspace X"
      by (simp add: closedin_subset)
    define \<U> where "\<U> \<equiv> {D \<in> connected_components_of (subtopology X (topspace X - C)). D-S \<noteq> {}}"
    have ope\<U>: "openin X U" if "U \<in> \<U>" for U
      using that  \<open>closedin X C\<close> lcX locally_connected_space_open_connected_components 
      by (fastforce simp add: closedin_def \<U>_def)
    have "{} \<notin> \<U>"
      by (auto simp: \<U>_def)
    have "pairwise disjnt \<U>"
      using connected_components_of_disjoint by (fastforce simp add: pairwise_def \<U>_def)
    show ?lhs
    proof (rule ccontr)
      assume con: "\<nexists>\<U>. finite \<U> \<and> card \<U> = n \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S"
      have card\<U>: "finite \<U> \<and> card \<U> < n"
      proof (rule ccontr)
        assume "\<not> (finite \<U> \<and> card \<U> < n)"
        then obtain \<V> where "\<V> \<subseteq> \<U>" "finite \<V>" "card \<V> = n"
          by (metis infinite_arbitrarily_large linorder_not_less obtain_subset_with_card_n)
        then obtain T where "T \<in> \<V>"
          using False by force
        define \<W> where "\<W> \<equiv> insert (topspace X - S - \<Union>(\<V> - {T})) ((\<lambda>D. D - S) ` (\<V> - {T}))"
        have "\<Union>\<W> = topspace X - S"
          using \<open>\<And>U. U \<in> \<U> \<Longrightarrow> openin X U\<close> \<open>\<V> \<subseteq> \<U>\<close> topspace_def by (fastforce simp: \<W>_def)
        moreover have "{} \<notin> \<W>"
        proof -
          obtain a where "a \<in> T" "a \<notin> S"
            using \<U>_def \<open>T \<in> \<V>\<close> \<open>\<V> \<subseteq> \<U>\<close> by blast
          then have "a \<in> topspace X"
            using \<open>T \<in> \<V>\<close> ope\<U> \<open>\<V> \<subseteq> \<U>\<close> openin_subset by blast
          moreover have "a \<notin> \<Union> (\<V> - {T})"
            using diff_Union_pairwise_disjoint [of \<V> "{T}"] \<open>disjoint \<U>\<close> pairwise_subset \<open>T \<in> \<V>\<close> \<open>\<V> \<subseteq> \<U>\<close> \<open>a \<in> T\<close> 
            by auto
          ultimately have "topspace X - S - \<Union> (\<V> - {T}) \<noteq> {}"
            using \<open>a \<notin> S\<close> by blast
          moreover have "\<And>V. V \<in> \<V> - {T} \<Longrightarrow> V - S \<noteq> {}"
            using \<U>_def \<open>\<V> \<subseteq> \<U>\<close> by blast
          ultimately show ?thesis
            by (metis (no_types, lifting) \<W>_def image_iff insert_iff)
        qed
        moreover have "disjoint \<V>"
          using \<open>\<V> \<subseteq> \<U>\<close> \<open>disjoint \<U>\<close> pairwise_subset by blast
        then have inj: "inj_on (\<lambda>D. D - S) (\<V> - {T})"
          unfolding inj_on_def using \<open>\<V> \<subseteq> \<U>\<close> disjointD \<U>_def inf_commute by blast
        have "finite \<W>" "card \<W> = n"
          using \<open>{} \<notin> \<W>\<close> \<open>n \<noteq> 0\<close> \<open>T \<in> \<V>\<close>
          by (auto simp add: \<W>_def \<open>finite \<V>\<close> card_insert_if card_image inj \<open>card \<V> = n\<close>)
        moreover have "pairwise (separatedin X) \<W>"
        proof -
          have "disjoint \<W>"
            using \<open>disjoint \<V>\<close> by (auto simp: \<W>_def pairwise_def disjnt_iff)
          have "pairwise (separatedin (subtopology X (topspace X - S))) \<W>"
          proof (intro pairwiseI)
            fix A B
            assume \<section>: "A \<in> \<W>" "B \<in> \<W>" "A \<noteq> B"
            then have "disjnt A B"
              by (meson \<open>disjoint \<W>\<close> pairwiseD)
            have "closedin (subtopology X (topspace X - C)) (\<Union>(\<V> - {T}))"
              using \<U>_def \<open>\<V> \<subseteq> \<U>\<close> closedin_connected_components_of \<open>finite \<V>\<close>
              by (force simp add: intro!: closedin_Union)
            with \<open>C \<subseteq> S\<close> have "openin (subtopology X (topspace X - S)) (topspace X - S - \<Union>(\<V> - {T}))"
              by (fastforce simp add: openin_closedin_eq closedin_subtopology Int_absorb1)
            moreover have "\<And>V. V \<in> \<V> \<and> V\<noteq>T \<Longrightarrow> openin (subtopology X (topspace X - S)) (V - S)"
              using \<open>\<V> \<subseteq> \<U>\<close> ope\<U>
              by (metis IntD2 Int_Diff inf.orderE openin_subset openin_subtopology) 
            ultimately have "openin (subtopology X (topspace X - S)) A" "openin (subtopology X (topspace X - S)) B"
              using \<section> \<W>_def by blast+
            with \<open>disjnt A B\<close> show "separatedin (subtopology X (topspace X - S)) A B"
              using separatedin_open_sets by blast
          qed
          then show ?thesis
            by (simp add: pairwise_def separatedin_subtopology)
        qed
        ultimately show False
          using con by blast
      qed
      obtain \<V> where "finite \<V>" "card \<V> = n" "{} \<notin> \<V>"
                and pw\<V>: "pairwise (separatedin X) \<V>" and UV: "\<Union>\<V> = topspace X - (topspace X - \<Union>\<U>)"
      proof -
        have "closedin X (topspace X - \<Union>\<U>)"
          using ope\<U> by blast
        moreover 
        have "C \<subseteq> topspace X - \<Union>\<U>"
          using \<open>C \<subseteq> topspace X\<close> connected_components_of_subset by (fastforce simp: \<U>_def)
        moreover have "topspace X - \<Union>\<U> \<subseteq> S"
          using Union_connected_components_of [of "subtopology X (topspace X - C)"] \<open>C \<subseteq> S\<close>
          by (auto simp: \<U>_def)
        ultimately show thesis
          by (metis C that)
      qed
      have "\<V> \<lesssim> \<U>"
      proof (rule lepoll_relational_full)
        have "\<Union>\<V> = \<Union>\<U>"
          by (simp add: Sup_le_iff UV double_diff ope\<U> openin_subset)
        then show "\<exists>U. U \<in> \<U> \<and> \<not> disjnt U V" if "V \<in> \<V>" for V
          using that
          by (metis \<open>{} \<notin> \<V>\<close> disjnt_Union1 disjnt_self_iff_empty)
        show "C1 = C2"
          if "T \<in> \<U>" and "C1 \<in> \<V>" and "C2 \<in> \<V>" and "\<not> disjnt T C1" and "\<not> disjnt T C2" for T C1 C2
        proof (cases "C1=C2")
          case False
          then have "connectedin X T"
            using \<U>_def connectedin_connected_components_of connectedin_subtopology \<open>T \<in> \<U>\<close> by blast
          have "T \<subseteq> C1 \<union> \<Union>(\<V> - {C1})"
            using \<open>\<Union> \<V> = \<Union> \<U>\<close> \<open>T \<in> \<U>\<close> by auto
          with \<open>connectedin X T\<close>
          have "\<not> separatedin X C1 (\<Union>(\<V> - {C1}))"
            unfolding connectedin_eq_not_separated_subset
            by (smt (verit) that False disjnt_def UnionI disjnt_iff insertE insert_Diff)
          with that show ?thesis
            by (metis (no_types, lifting) \<open>finite \<V>\<close> finite_Diff pairwiseD pairwise_alt pw\<V> separatedin_Union(1) separatedin_def)
        qed auto
      qed
      then show False
        using \<open>card \<V> = n\<close> card\<U>
        by (simp add: \<open>finite \<V>\<close> lepoll_iff_card_le)
    qed
  qed
qed

lemma separation_by_closed_intermediates_eq_gen:
  assumes "locally_connected_space X" "hereditarily normal_space X"
  shows "\<not> connectedin X (topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S \<longrightarrow> \<not> connectedin X (topspace X - D)))"
    (is "?lhs = ?rhs")
proof -
  have *: "(\<exists>C1 C2. separatedin X C1 C2 \<and> C1\<noteq>C2 \<and> C1\<noteq>{} \<and> C2\<noteq>{} \<and> C1 \<union> C2 = topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S
                   \<longrightarrow> (\<exists>C1 C2. separatedin X C1 C2 \<and> C1\<noteq>C2 \<and> C1\<noteq>{} \<and> C2\<noteq>{} \<and> C1 \<union> C2 = topspace X - D)))"
    using separation_by_closed_intermediates_eq_count [OF assms, of "Suc(Suc 0)" S]
    apply (simp add: card_Suc_eq pairwise_insert separatedin_sym flip: ex_simps cong: conj_cong)
    apply (simp add: eq_sym_conv conj_ac)
    done
  with separatedin_refl
  show ?thesis
    apply (simp add: connectedin_eq_not_separated)
    by (smt (verit, best) separatedin_refl)
qed



lemma lepoll_connnected_components_connectedin:
  assumes "\<And>C. C \<in> \<U> \<Longrightarrow> connectedin X C"  "\<Union>\<U> = topspace X"
  shows "connected_components_of X \<lesssim> \<U>"
proof -
  have "connected_components_of X \<lesssim> \<U> - {{}}"
  proof (rule lepoll_relational_full)
    show "\<exists>U. U \<in> \<U> - {{}} \<and> U \<subseteq> V"
      if "V \<in> connected_components_of X" for V 
      using that unfolding connected_components_of_def image_iff
      by (metis Union_iff assms connected_component_of_maximal empty_iff insert_Diff_single insert_iff)
    show "V = V'"
      if "U \<in> \<U> - {{}}" "V \<in> connected_components_of X" "V' \<in> connected_components_of X" "U \<subseteq> V" "U \<subseteq> V'"
      for U V V'
      by (metis DiffD2 disjointD insertCI le_inf_iff pairwise_disjoint_connected_components_of subset_empty that)
  qed
  also have "\<dots> \<lesssim> \<U>"
    by (simp add: subset_imp_lepoll)
  finally show ?thesis .
qed

lemma lepoll_connected_components_alt:
  "{..<n::nat} \<lesssim> connected_components_of X \<longleftrightarrow>
    n = 0 \<or> (\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (cases "n=0")
next
  case False
  show ?thesis 
  proof
    assume L: ?lhs 
    with False show ?rhs
    proof (induction n rule: less_induct)
      case (less n)
      show ?case
      proof (cases "n\<le>1")
        case True
        with less.prems connected_components_of_empty_space show ?thesis
          by (force simp add: le_Suc_eq eqpoll_iff_finite_card card_Suc_eq simp flip: ex_simps)
      next
        case False
        then have "n-1 \<noteq> 0"
          by linarith
        have n1_lesspoll: "{..<n-1} \<prec> {..<n}"
          using False lesspoll_iff_finite_card by fastforce
        also have "\<dots> \<lesssim> connected_components_of X"
          using less by blast
        finally have "{..<n-1} \<lesssim> connected_components_of X"
          using lesspoll_imp_lepoll by blast 
        then obtain \<U> where Ueq: "\<U> \<approx> {..<n-1}" and "{} \<notin> \<U>" 
          and pwU: "pairwise (separatedin X) \<U>" and UU: "\<Union>\<U> = topspace X"
          by (meson \<open>n - 1 \<noteq> 0\<close> diff_less gr0I less zero_less_one)
        show ?thesis
        proof (cases "\<forall>C \<in> \<U>. connectedin X C")
          case True
          then show ?thesis
            using lepoll_connnected_components_connectedin [of \<U> X] less.prems
            by (metis UU Ueq lepoll_antisym lepoll_trans lepoll_trans2 lesspoll_def n1_lesspoll)
          next
            case False
            with UU obtain C A B where ABC: "C \<in> \<U>" "A \<union> B = C" "A \<noteq> {}" "B \<noteq> {}" and sep: "separatedin X A B"
              by (fastforce simp add: connectedin_eq_not_separated)
            define \<V> where "\<V> \<equiv> insert A (insert B (\<U> - {C}))"
            have "\<V> \<approx> {..<n}"
            proof -
              have "A \<noteq> B"
                using \<open>B \<noteq> {}\<close> sep by auto
              moreover obtain "A \<notin> \<U>" "B \<notin> \<U>"
                using pwU unfolding pairwise_def
                by (metis ABC sep separatedin_Un(1) separatedin_refl separatedin_sym)
              moreover have "card \<U> = n-1" "finite \<U>"
                using Ueq eqpoll_iff_finite_card by blast+
              ultimately
              have "card (insert A (insert B (\<U> - {C}))) = n"
                using \<open>C \<in> \<U>\<close> by (auto simp add: card_insert_if)
              then show ?thesis
                using \<V>_def \<open>finite \<U>\<close> eqpoll_iff_finite_card by blast
            qed
            moreover have "{} \<notin> \<V>"
              using ABC \<V>_def \<open>{} \<notin> \<U>\<close> by blast
            moreover have "\<Union>\<V> = topspace X"
              using ABC UU \<V>_def by auto
            moreover have "pairwise (separatedin X) \<V>"
              using pwU sep ABC unfolding  \<V>_def
              apply (simp add: separatedin_sym pairwise_def)
              by (metis member_remove remove_def separatedin_Un(1))
            ultimately show ?thesis
              by blast
          qed
      qed
    qed
  next
    assume ?rhs
    then obtain \<U> where "\<U> \<approx> {..<n}" "{} \<notin> \<U>" and pwU: "pairwise (separatedin X) \<U>" and UU: "\<Union>\<U> = topspace X"
      using False by force
    have "card (connected_components_of X) \<ge> n" if "finite (connected_components_of X)"
    proof -
      have "\<U> \<lesssim> connected_components_of X"
      proof (rule lepoll_relational_full)
        show "\<exists>T. T \<in> connected_components_of X \<and> \<not> disjnt T C" if "C \<in> \<U>" for C 
          by (metis that UU Union_connected_components_of Union_iff \<open>{} \<notin> \<U>\<close> disjnt_iff equals0I)
        show "(C1::'a set) = C2"
          if "T \<in> connected_components_of X" and "C1 \<in> \<U>" "C2 \<in> \<U>" "\<not> disjnt T C1" "\<not> disjnt T C2" for T C1 C2
        proof (rule ccontr)
          assume "C1 \<noteq> C2"
          then have "connectedin X T"
            by (simp add: connectedin_connected_components_of that(1))
          moreover have "\<not> separatedin X C1 (\<Union>(\<U> - {C1}))"
            using \<open>connectedin X T\<close> pwU unfolding pairwise_def
            by (smt (verit) Sup_upper UU Union_connected_components_of \<open>C1 \<noteq> C2\<close> complete_lattice_class.Sup_insert connectedin_subset_separated_union disjnt_subset2 disjnt_sym insert_Diff separatedin_imp_disjoint that)
          ultimately show False
            using \<open>\<U> \<approx> {..<n}\<close>
            apply (simp add: connectedin_eq_not_separated_subset eqpoll_iff_finite_card)
            by (metis Sup_upper UU finite_Diff pairwise_alt pwU separatedin_Union(1) that(2))
        qed
      qed
      then show ?thesis
        by (metis \<open>\<U> \<approx> {..<n}\<close> eqpoll_iff_finite_card lepoll_iff_card_le that)
    qed
    then show ?lhs
      by (metis card_lessThan finite_lepoll_infinite finite_lessThan lepoll_iff_card_le)
  qed
qed auto


lemma lemmaX:
  assumes "\<And>S T. R S T \<Longrightarrow> R T S"
  shows "(\<forall>S T n. R S T \<longrightarrow> (f S \<approx> {..<n::nat} \<longleftrightarrow> f T \<approx> {..<n::nat})) \<longleftrightarrow>
         (\<forall>n S T. R S T \<longrightarrow> {..<n::nat} \<lesssim> f S \<longrightarrow> {..<n::nat} \<lesssim> f T)"
  apply (rule )
   apply (meson eqpoll_iff_finite_card eqpoll_sym finite_lepoll_infinite finite_lessThan lepoll_trans2)
  by (smt (verit, best) assms card_lessThan eqpoll_iff_card eqpoll_imp_lepoll finite_lepoll_infinite finite_lessThan lepoll_antisym lepoll_iff_finite_card lessI linorder_not_le nle_le)



lemma lemur: (*NEEDED?*)
   "pairwise (separatedin (subtopology X (topspace X - S))) \<U> \<and> {} \<notin> \<U> \<and>
     \<Union>\<U> = topspace(subtopology X (topspace X - S)) \<longleftrightarrow>
     pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S"
  by (auto simp: pairwise_def separatedin_subtopology)


lemma Kuratowski_component_number_invariance:
  assumes "compact_space X" "Hausdorff_space X" "locally_connected_space X" "hereditarily normal_space X"
  shows "((\<forall>S T n.
              closedin X S \<and> closedin X T \<and>
              (subtopology X S) homeomorphic_space (subtopology X T)
              \<longrightarrow> (connected_components_of
                    (subtopology X (topspace X - S)) \<approx> {..<n::nat} \<longleftrightarrow>
                   connected_components_of
                    (subtopology X (topspace X - T)) \<approx> {..<n::nat})) \<longleftrightarrow>
           (\<forall>S T n.
              (subtopology X S) homeomorphic_space (subtopology X T)
              \<longrightarrow> (connected_components_of
                    (subtopology X (topspace X - S)) \<approx> {..<n::nat} \<longleftrightarrow>
                   connected_components_of
                    (subtopology X (topspace X - T)) \<approx> {..<n::nat})))"
         (is "?lhs = ?rhs")
proof
  assume L: ?lhs 
  then
  show ?rhs
    apply (subst (asm)lemmaX)
    using homeomorphic_space_sym apply blast
    apply (subst lemmaX)
    using homeomorphic_space_sym apply blast
    apply (erule all_forward)
    apply (simp add: lepoll_connected_components_alt)
    apply (case_tac "n=0")
     apply (simp add: )
    apply (simp add: Int_absorb1)



    by (metis hnX separation_by_closed_intermediates_count)
qed blast

oops

  MAP_EVERY X_GEN_TAC [`S::A=>bool`; `t::A=>bool`] THEN
  ONCE_REWRITE_TAC[SUBTOPOLOGY_RESTRICT] THEN
  ONCE_REWRITE_TAC[SET_RULE `S - t = S - S \<inter> t`] THEN
  MP_TAC(SET_RULE
   `topspace X \<inter> (S::A=>bool) \<subseteq> topspace X \<and>
    topspace X \<inter> (t::A=>bool) \<subseteq> topspace X`) THEN
  SPEC_TAC(`topspace X \<inter> (t::A=>bool)`,`t::A=>bool`) THEN
  SPEC_TAC(`topspace X \<inter> (S::A=>bool)`,`S::A=>bool`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand)
    SEPARATION_BY_CLOSED_INTERMEDIATES_EQ_COUNT \<circ> lhand \<circ> snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC \<circ> PART_MATCH (lhand \<circ> rand)
    SEPARATION_BY_CLOSED_INTERMEDIATES_EQ_COUNT \<circ> rand \<circ> snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [homeomorphic_space]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; HOMEOMORPHIC_MAPS_MAP] THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`f::A=>A`; `g::A=>A`] THEN STRIP_TAC THEN
  X_GEN_TAC `C::A=>bool` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(LABEL_TAC "*") THEN EXISTS_TAC `image (f::A=>A) C` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology X (S::A=>bool)` THEN
    ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY; CLOSED_IN_COMPACT_SPACE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY]) THEN
    ASM SET_TAC[];
    X_GEN_TAC `d':A=>bool` THEN STRIP_TAC] THEN
  ABBREV_TAC `D = image (g::A=>A) d'` THEN
  SUBGOAL_THEN `closedin X (D::A=>bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "D" THEN MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology X (t::A=>bool)` THEN
    ASM_SIMP_TAC[COMPACT_IN_SUBTOPOLOGY; CLOSED_IN_COMPACT_SPACE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C::A=>bool) \<subseteq> D \<and> D \<subseteq> S` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                                CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC \<circ> SPEC `D::A=>bool`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[homeomorphic_space] THEN
  MAP_EVERY EXISTS_TAC [`f::A=>A`; `g::A=>A`] THEN
  SUBGOAL_THEN
   `subtopology X D::A topology = subtopology (subtopology X S) D \<and>
    subtopology X d':A topology = subtopology (subtopology X t) d'`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    CONJ_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC HOMEOMORPHIC_MAPS_SUBTOPOLOGIES] THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_MAPS_MAP] THEN
  ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HOMEOMORPHIC_EQ_EVERYTHING_MAP;
                              CONTINUOUS_MAP_IN_SUBTOPOLOGY]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TOPSPACE_SUBTOPOLOGY]) THEN
  ASM SET_TAC[]);;




subsection\<open>A perfect set in common cases must have cardinality >= c\<close>

lemma (in Metric_space) card_ge_perfect_set:
  assumes "mcomplete"
    and "mtopology derived_set_of S = S" "S \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> S"
proof -
  have "S \<subseteq> M"
    using assms(2) derived_set_of_infinite_mball by blast
  have "(UNIV::real set) \<lesssim> (UNIV::nat set set)"
    using eqpoll_imp_lepoll eqpoll_sym nat_sets_eqpoll_reals by blast
  also have "\<dots> \<lesssim> S"
  proof -
    have "\<exists>y z \<delta>. y \<in> S \<and> z \<in> S \<and> 0 < \<delta> \<and> \<delta> < \<epsilon>/2 \<and>
                  mcball y \<delta> \<subseteq> mcball x \<epsilon> \<and> mcball z \<delta> \<subseteq> mcball x \<epsilon> \<and> disjnt (mcball y \<delta>) (mcball z \<delta>)"
      if "x \<in> S" "0 < \<epsilon>" for x \<epsilon>
    proof -
      define S' where "S' \<equiv> S \<inter> mball x (\<epsilon>/4)"
      have "infinite S'"
        using derived_set_of_infinite_mball [of S] assms that S'_def
        by (smt (verit, ccfv_SIG) mem_Collect_eq zero_less_divide_iff)
      then have "\<And>x y z. \<not> (S' \<subseteq> {x,y,z})"
        using finite_subset by auto
      then obtain l r where lr: "l \<in> S'" "r \<in> S'" "l\<noteq>r" "l\<noteq>x" "r\<noteq>x"
        by (metis insert_iff subsetI)
      show ?thesis
      proof (intro exI conjI)
        show "l \<in> S" "r \<in> S" "d l r / 3 > 0"
          using lr by (auto simp: S'_def)
        show "d l r / 3 < \<epsilon>/2" "mcball l (d l r / 3) \<subseteq> mcball x \<epsilon>" "mcball r (d l r / 3) \<subseteq> mcball x \<epsilon>"
          using lr by (clarsimp simp: S'_def, smt (verit) commute triangle'')+
        show "disjnt (mcball l (d l r / 3)) (mcball r (d l r / 3))"
          using lr by (simp add: S'_def disjnt_iff) (smt (verit, best) mdist_pos_less triangle')
      qed
    qed
    then obtain l r \<delta> 
        where lrS: "\<And>x \<epsilon>. \<lbrakk>x \<in> S; 0 < \<epsilon>\<rbrakk> \<Longrightarrow> l x \<epsilon> \<in> S \<and> r x \<epsilon> \<in> S"
          and \<delta>: "\<And>x \<epsilon>. \<lbrakk>x \<in> S; 0 < \<epsilon>\<rbrakk> \<Longrightarrow> 0 < \<delta> x \<epsilon> \<and> \<delta> x \<epsilon> < \<epsilon>/2"
          and "\<And>x \<epsilon>. \<lbrakk>x \<in> S; 0 < \<epsilon>\<rbrakk> \<Longrightarrow>  mcball (l x \<epsilon>) (\<delta> x \<epsilon>) \<subseteq> mcball x \<epsilon> \<and> mcball (r x \<epsilon>) (\<delta> x \<epsilon>) \<subseteq> mcball x \<epsilon> \<and> 
                  disjnt (mcball (l x \<epsilon>) (\<delta> x \<epsilon>)) (mcball (r x \<epsilon>) (\<delta> x \<epsilon>))"
      by metis
    then have lr_mcball: "\<And>x \<epsilon>. \<lbrakk>x \<in> S; 0 < \<epsilon>\<rbrakk> \<Longrightarrow> mcball (l x \<epsilon>) (\<delta> x \<epsilon>) \<subseteq> mcball x \<epsilon> \<and> mcball (r x \<epsilon>) (\<delta> x \<epsilon>) \<subseteq> mcball x \<epsilon> "
          and lr_disjnt: "\<And>x \<epsilon>. \<lbrakk>x \<in> S; 0 < \<epsilon>\<rbrakk> \<Longrightarrow> disjnt (mcball (l x \<epsilon>) (\<delta> x \<epsilon>)) (mcball (r x \<epsilon>) (\<delta> x \<epsilon>))"
      by metis+
    obtain a where "a \<in> S"
      using \<open>S \<noteq> {}\<close> by blast
    define xe where "xe \<equiv> 
           \<lambda>B. rec_nat (a,1) (\<lambda>n (x,\<gamma>). ((if n\<in>B then r else l) x \<gamma>, \<delta> x \<gamma>))"
    have [simp]: "xe b 0 = (a,1)" for b
      by (simp add: xe_def)
    have "xe B (Suc n) = (let (x,\<gamma>) = xe B n in ((if n\<in>B then r else l) x \<gamma>, \<delta> x \<gamma>))" for B n
      by (simp add: xe_def)
    define x where "x \<equiv> \<lambda>B n. fst (xe B n)"
    define \<gamma> where "\<gamma> \<equiv> \<lambda>B n. snd (xe B n)"
    have [simp]: "x B 0 = a" "\<gamma> B 0 = 1" for B
      by (simp_all add: x_def \<gamma>_def xe_def)
    have x_Suc[simp]: "x B (Suc n) = ((if n\<in>B then r else l) (x B n) (\<gamma> B n))" 
     and \<gamma>_Suc[simp]: "\<gamma> B (Suc n) = \<delta> (x B n) (\<gamma> B n)" for B n
      by (simp_all add: x_def \<gamma>_def xe_def split: prod.split)
    interpret Submetric M d S
    proof qed (use \<open>S \<subseteq> M\<close> in metis)
    have "closedin mtopology S"
      by (metis assms(2) closure_of closure_of_eq inf.absorb_iff2 subset subset_Un_eq subset_refl topspace_mtopology)
    with \<open>mcomplete\<close>
    have "sub.mcomplete"
      by (metis closedin_mcomplete_imp_mcomplete)
    have *: "x B n \<in> S \<and> \<gamma> B n > 0" for B n
      by (induction n) (auto simp: \<open>a \<in> S\<close> lrS \<delta>)
    with subset have E: "x B n \<in> M" for B n
      by blast
    have \<gamma>_le: "\<gamma> B n \<le> (1/2)^n" for B n
    proof(induction n)
      case 0 then show ?case by auto
    next
      case (Suc n)
      then show ?case
        by simp (smt (verit) "*" \<delta> field_sum_of_halves)
    qed
    { fix B
      have "\<And>n. sub.mcball (x B (Suc n)) (\<gamma> B (Suc n)) \<subseteq> sub.mcball (x B n) (\<gamma> B n)"
        by (smt (verit, best) "*" Int_iff \<gamma>_Suc x_Suc in_mono lr_mcball mcball_submetric_eq subsetI)
      then have mon: "monotone (\<le>) (\<lambda>x y. y \<subseteq> x) (\<lambda>n. sub.mcball (x B n) (\<gamma> B n))"
        by (simp add: decseq_SucI)
      have "\<exists>n a. sub.mcball (x B n) (\<gamma> B n) \<subseteq> sub.mcball a \<epsilon>" if "\<epsilon>>0" for \<epsilon>
      proof -
        obtain n where "(1/2)^n < \<epsilon>"
          using \<open>0 < \<epsilon>\<close> real_arch_pow_inv by force
        with \<gamma>_le have \<epsilon>: "\<gamma> B n \<le> \<epsilon>"
          by (smt (verit))
        show ?thesis
        proof (intro exI)
          show "sub.mcball (x B n) (\<gamma> B n) \<subseteq> sub.mcball (x B n) \<epsilon>"
            by (simp add: \<epsilon> sub.mcball_subset_concentric)
        qed
      qed
      then have "\<exists>l. l \<in> S \<and> (\<Inter>n. sub.mcball (x B n) (\<gamma> B n)) = {l}"
        using \<open>sub.mcomplete\<close> mon 
        unfolding sub.mcomplete_nest_sing
        apply (drule_tac x="\<lambda>n. sub.mcball (x B n) (\<gamma> B n)" in spec)
        by (meson * order.asym sub.closedin_mcball sub.mcball_eq_empty)
    }
    then obtain z where z: "\<And>B. z B \<in> S \<and> (\<Inter>n. sub.mcball (x B n) (\<gamma> B n)) = {z B}"
      by metis
    show ?thesis
      unfolding lepoll_def
    proof (intro exI conjI)
      show "inj z"
      proof (rule inj_onCI)
        fix B C
        assume eq: "z B = z C" and "B \<noteq> C"
        then have ne: "sym_diff B C \<noteq> {}"
          by blast
        define n where "n \<equiv> LEAST k. k \<in> (sym_diff B C)"
        with ne have n: "n \<in> sym_diff B C"
          by (metis Inf_nat_def1 LeastI)
        then have non: "n \<in> B \<longleftrightarrow> n \<notin> C"
          by blast
        have BC_eq: "k \<in> B \<longleftrightarrow> k \<in> C" if "k<n" for k
          using that unfolding n_def by (meson DiffI UnCI not_less_Least)

        define J where "J \<equiv> \<lambda>B. {a. \<forall>n. a \<in> sub.mcball (x B n) (\<gamma> B n)}"
        have Jayne: "J B = {z B}" for B
          using z [of B] by (simp add: J_def set_eq_iff)
        then have "z C \<in> J B \<inter> J C"
          using eq by force
        then have H: "z C \<in> sub.mcball (x B (Suc n)) (\<gamma> B (Suc n)) \<and> z C \<in> sub.mcball (x C (Suc n)) (\<gamma> C (Suc n))"
          apply (simp add: J_def non "*" lrS)
          apply (metis (full_types) \<gamma>_Suc non x_Suc)+
          done

        have "(\<forall>m. m < p \<longrightarrow> (m \<in> B \<longleftrightarrow> m \<in> C)) \<Longrightarrow> x B p = x C p \<and> \<gamma> B p = \<gamma> C p" for p
          by (induction p) auto
        then have **: "x B n = x C n" "\<gamma> B n = \<gamma> C n"
          using BC_eq by blast+
        then show False
          using lr_disjnt * H non
          by (smt (verit) IntD2 \<gamma>_Suc disjnt_iff mcball_submetric_eq x_Suc)
      qed
      show "range z \<subseteq> S"
        using z by blast
    qed
  qed
  finally show ?thesis .
qed


lemma card_ge_perfect_set:
  assumes X: "completely_metrizable_space X \<or> locally_compact_space X \<and> Hausdorff_space X"
    and "X derived_set_of S = S" "S \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> S"
  using assms
  apply-
  apply (erule disjE)
  apply (metis Metric_space.card_ge_perfect_set completely_metrizable_space_def)

oops


    SUBGOAL_THEN
     `\<forall>X::A topology.
          locally_compact_space X \<and> Hausdorff_space X \<and>
          X derived_set_of topspace X = topspace X \<and> \<not> (topspace X = {})
          \<Longrightarrow> UNIV \<lesssim> topspace X`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC;
      MAP_EVERY X_GEN_TAC [`X::A topology`; `S::A=>bool`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC \<circ> SPEC `subtopology X (S::A=>bool)`) THEN
      SUBGOAL_THEN `(S::A=>bool) \<subseteq> topspace X` ASSUME_TAC THENL
       [ASM_MESON_TAC[DERIVED_SET_OF_SUBSET_TOPSPACE]; ALL_TAC] THEN
      ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_SUBTOPOLOGY;
                   DERIVED_SET_OF_SUBTOPOLOGY; SET_RULE `S \<inter> S = S`;
                   SET_RULE `S \<subseteq> u \<Longrightarrow> u \<inter> S = S`] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC LOCALLY_COMPACT_SPACE_CLOSED_SUBSET THEN
      ASM_REWRITE_TAC[CLOSED_IN_CONTAINS_DERIVED_SET; SUBSET_REFL]] THEN
    TRANS_TAC CARD_LE_TRANS `(:nat=>bool)` THEN
    SIMP_TAC[CARD_EQ_REAL; CARD_EQ_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC \<circ> GEN_REWRITE_RULE id [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `z::A`) THEN
    FIRST_ASSUM(MP_TAC \<circ> SPEC `z::A` \<circ> REWRITE_RULE[locally_compact_space]) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u::A=>bool`; `k::A=>bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `\<not> (u::A=>bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[];
      REPEAT(FIRST_X_ASSUM(K ALL_TAC \<circ> check (free_in `z::A`) \<circ> concl))] THEN
    SUBGOAL_THEN
     `\<forall>c. closedin X c \<and> c \<subseteq> k \<and> \<not> (X interior_of c = {})
          \<Longrightarrow> \<exists>d e. closedin X d \<and> d \<subseteq> k \<and>
                    \<not> (X interior_of d = {}) \<and>
                    closedin X e \<and> e \<subseteq> k \<and>
                    \<not> (X interior_of e = {}) \<and>
                    disjnt d e \<and> d \<subseteq> c \<and> e \<subseteq> (c::A=>bool)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_TAC `\<not> (X interior_of c::A=>bool = {})` THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `z::A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z::A) \<in> topspace X` ASSUME_TAC THENL
       [ASM_MESON_TAC[\<subseteq>; INTERIOR_OF_SUBSET_TOPSPACE]; ALL_TAC] THEN
      MP_TAC(ISPECL [`X::A topology`; `topspace X::A=>bool`]
            DERIVED_SET_OF_INFINITE_OPEN_IN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC \<circ> AP_TERM `\<lambda>s. (z::A) \<in> S`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC \<circ> SPEC `X interior_of c::A=>bool`) THEN
      ASM_SIMP_TAC[OPEN_IN_INTERIOR_OF; INTERIOR_OF_SUBSET_TOPSPACE;
                   SET_RULE `S \<subseteq> u \<Longrightarrow> u \<inter> S = S`] THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP (MESON[infinite; FINITE_SING; FINITE_SUBSET]
        `infinite S \<Longrightarrow> \<forall>a. \<not> (S \<subseteq> {a})`)) THEN
      DISCH_THEN(MP_TAC \<circ> MATCH_MP (SET_RULE
       `(\<forall>a. \<not> (S \<subseteq> {a})) \<Longrightarrow> \<exists>a b. a \<in> S \<and> b \<in> S \<and> (a \<noteq> b)`)) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`x::A`; `y::A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x::A) \<in> topspace X \<and> y \<in> topspace X`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[\<subseteq>; INTERIOR_OF_SUBSET_TOPSPACE]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC \<circ> SPECL [`x::A`; `y::A`] \<circ>
        REWRITE_RULE[Hausdorff_space]) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`v::A=>bool`; `w::A=>bool`] THEN STRIP_TAC THEN
      MP_TAC(ISPEC `X::A topology`
        LOCALLY_COMPACT_HAUSDORFF_IMP_REGULAR_SPACE) THEN
      ASM_REWRITE_TAC[GSYM NEIGHBOURHOOD_BASE_OF_CLOSED_IN] THEN
      REWRITE_TAC[NEIGHBOURHOOD_BASE_OF] THEN DISCH_THEN(fun th ->
        MP_TAC(SPECL [`X interior_of c \<inter> w::A=>bool`; `y::A`] th) THEN
        MP_TAC(SPECL [`X interior_of c \<inter> v::A=>bool`; `x::A`] th)) THEN
      ASM_SIMP_TAC[IN_INTER; OPEN_IN_INTER; OPEN_IN_INTERIOR_OF] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET_INTER] THEN
      MAP_EVERY X_GEN_TAC [`m::A=>bool`; `d::A=>bool`] THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [`n::A=>bool`; `e::A=>bool`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`d::A=>bool`; `e::A=>bool`] THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[TAUT
       `p \<and> q \<and> r \<and> S \<and> t \<longleftrightarrow> (q \<and> S) \<and> p \<and> r \<and> t`] THEN
      CONJ_TAC THENL
       [CONJ_TAC THENL [EXISTS_TAC `x::A`; EXISTS_TAC `y::A`] THEN
        REWRITE_TAC[interior_of; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        MP_TAC(ISPECL [`X::A topology`; `c::A=>bool`] INTERIOR_OF_SUBSET) THEN
        ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`l:(A=>bool)->A=>bool`; `r:(A=>bool)->A=>bool`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `\<forall>b. \<exists>d::nat=>A->bool.
          d 0 = k \<and>
          (\<forall>n. d(Suc n) = (if b n then r else l) (d n))`
    MP_TAC THENL
     [GEN_TAC THEN
      W(ACCEPT_TAC \<circ> prove_recursive_functions_exist num_RECURSION \<circ>
          snd \<circ> dest_exists \<circ> snd);
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM]] THEN
    X_GEN_TAC `d:(nat=>bool)->num=>A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `\<forall>b n. closedin X (d b n) \<and> d b n \<subseteq> k \<and>
            \<not> (X interior_of ((d:(nat=>bool)->num=>A->bool) b n) = {})`
    MP_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THENL
       [ASM_SIMP_TAC[SUBSET_REFL; COMPACT_IN_IMP_CLOSED_IN] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC \<circ> MATCH_MP (SET_RULE
         `(u \<noteq> {}) \<Longrightarrow> u \<subseteq> i \<Longrightarrow> (i \<noteq> {})`)) THEN
        ASM_SIMP_TAC[INTERIOR_OF_MAXIMAL_EQ];
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]];
      REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     `\<forall>b. \<not> (\<Inter>{(d:(nat=>bool)->num=>A->bool) b n | n \<in> UNIV} = {})`
    MP_TAC THENL
     [X_GEN_TAC `b::nat=>bool` THEN MATCH_MP_TAC COMPACT_SPACE_IMP_NEST THEN
      EXISTS_TAC `subtopology X (k::A=>bool)` THEN
      ASM_SIMP_TAC[CLOSED_IN_SUBSET_TOPSPACE; COMPACT_SPACE_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[INTERIOR_OF_EMPTY]; ALL_TAC] THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
      REPEAT(CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
      ASM_SIMP_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `x:(nat=>bool)->A` THEN
    REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN DISCH_TAC THEN
    REWRITE_TAC[le_c; IN_UNIV] THEN EXISTS_TAC `x:(nat=>bool)->A` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CLOSED_IN_SUBSET; \<subseteq>]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`b::nat=>bool`; `c::nat=>bool`] THEN
    GEN_REWRITE_TAC id [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; NOT_FORALL_THM] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; TAUT `\<not> (p \<longleftrightarrow> q) \<longleftrightarrow> p \<longleftrightarrow> \<not> q`] THEN
    X_GEN_TAC `n::nat` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `disjnt ((d:(nat=>bool)->num=>A->bool) b (Suc n)) (d c (Suc n))`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_SIMP_TAC[COND_SWAP] THEN
    SUBGOAL_THEN `(d:(nat=>bool)->num=>A->bool) b n = d c n` SUBST1_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[DISJOINT_SYM]] THEN
    UNDISCH_TAC `\<forall>m::nat. m < n \<Longrightarrow> (b m \<longleftrightarrow> c m)` THEN
    SPEC_TAC(`n::nat`,`p::nat`) THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[LT_SUC_LE; LE_REFL; LT_IMP_LE]]);;


