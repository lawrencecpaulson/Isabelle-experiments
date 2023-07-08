section \<open>Abstract Metric Spaces\<close>

theory AMS
  imports
    "HOL-Analysis.Analysis" "HOL-Library.Equipollence"
    "HOL-ex.Sketch_and_Explore"
begin


lemma power_of_nat_log_le:
  assumes "b > 1" "x\<ge>1"
  shows "b ^ nat \<lfloor>log b x\<rfloor> \<le> x"
proof -
  have "\<lfloor>log b x\<rfloor> \<ge> 0"
    using assms by auto
  then show ?thesis
    by (smt (verit) assms le_log_iff of_int_floor_le powr_int)
qed

(******* delete sym_diff from Analysis/Equivalence_Measurable_On_Borel ******)

thm lepoll_empty_iff_empty
lemma eqpoll_empty_iff_empty [simp]: "A \<approx> {} \<longleftrightarrow> A={}"
  by (metis card_0_eq eqpoll_finite_iff eqpoll_iff_card finite.emptyI)

lemma not_lesspoll_empty: "\<not> A \<prec> {}"
  by (simp add: lesspoll_def)

lemma eqpoll_singleton_iff: "A \<approx> {x} \<longleftrightarrow> (\<exists>u. A = {u})"
  by (metis card.infinite card_1_singleton_iff eqpoll_finite_iff eqpoll_iff_card not_less_eq_eq)

lemma eqpoll_doubleton_iff: "A \<approx> {x,y} \<longleftrightarrow> (\<exists>u v. A = {u,v} \<and> (u=v \<longleftrightarrow> x=y))"
proof (cases "x=y")
  case True
  then show ?thesis
    by (simp add: eqpoll_singleton_iff)
next
  case False
  then show ?thesis
    by (smt (verit, ccfv_threshold) card_1_singleton_iff card_Suc_eq_finite eqpoll_finite_iff
        eqpoll_iff_card finite.insertI singleton_iff)
qed



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
                     \<Longrightarrow> \<exists>\<V>. \<V> \<approx> \<U> \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - D"
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
    show "\<exists>\<V>. \<V> \<approx> \<U> \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - C"
      if "closedin X C" "C \<subseteq> S" and C: "topspace X - \<Union>(F ` \<U>) \<subseteq> C" for C
    proof (intro exI conjI strip)
      have "inj_on (\<lambda>S. F S - C) \<U>"
        using pwF F
        unfolding inj_on_def pairwise_def disjnt_iff
        by (metis Diff_iff UU UnionI nonempty subset_empty subset_eq \<open>C \<subseteq> S\<close>)
      then show "(\<lambda>S. F S - C) ` \<U> \<approx> \<U>"
        by simp
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
                     \<Longrightarrow> \<exists>\<V>. \<V> \<approx> {C1,C2} \<and> pairwise (separatedin X) \<V> \<and> {} \<notin> \<V> \<and> \<Union>\<V> = topspace X - D"
    using separation_by_closed_intermediates_count [of X "{C1,C2}" S] X
    apply (simp add: pairwise_insert separatedin_sym)
    by metis
  have "\<not> connectedin X (topspace X - D)"
    if D: "closedin X D" "C \<subseteq> D" "D \<subseteq> S" for D 
  proof -
    obtain V1 V2 where *: "pairwise (separatedin X) {V1,V2}" "{} \<notin> {V1,V2}" 
                          "\<Union>{V1,V2} = topspace X - D" "V1\<noteq>V2"
      by (metis C [OF D] \<open>C1 \<noteq> C2\<close> eqpoll_doubleton_iff)
    then have "disjnt V1 V2"
      by (metis pairwise_insert separatedin_imp_disjoint singleton_iff)
      with * show ?thesis
        by (auto simp add: connectedin_eq_not_separated pairwise_insert)
    qed
  then show thesis
    using \<open>C \<subseteq> S\<close> \<open>closedin X C\<close> that by auto
qed

lemma separation_by_closed_intermediates_eq_count:
  fixes n::nat
  assumes lcX: "locally_connected_space X" and hnX: "hereditarily normal_space X"
  shows "(\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S
                   \<longrightarrow> (\<exists>\<U>.  \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D)))"
         (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (smt (verit, best) hnX separation_by_closed_intermediates_count eqpoll_iff_finite_card eqpoll_trans)
next
  assume R: ?rhs
  show ?lhs
  proof (cases "n=0")
    case True
    with R show ?thesis
      by fastforce
  next
    case False
    obtain C where "closedin X C" "C \<subseteq> S"
             and C: "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
                      \<Longrightarrow> \<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D"
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
      assume con: "\<nexists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S"
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
          moreover have "a \<notin> \<Union>(\<V> - {T})"
            using diff_Union_pairwise_disjoint [of \<V> "{T}"] \<open>disjoint \<U>\<close> pairwise_subset \<open>T \<in> \<V>\<close> \<open>\<V> \<subseteq> \<U>\<close> \<open>a \<in> T\<close> 
            by auto
          ultimately have "topspace X - S - \<Union>(\<V> - {T}) \<noteq> {}"
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
          by (metis con eqpoll_iff_finite_card)
      qed
      obtain \<V> where "\<V> \<approx> {..<n} " "{} \<notin> \<V>"
                and pw\<V>: "pairwise (separatedin X) \<V>" and UV: "\<Union>\<V> = topspace X - (topspace X - \<Union>\<U>)"
      proof -
        have "closedin X (topspace X - \<Union>\<U>)"
          using ope\<U> by blast
        moreover have "C \<subseteq> topspace X - \<Union>\<U>"
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
            using \<open>\<Union>\<V> = \<Union>\<U>\<close> \<open>T \<in> \<U>\<close> by auto
          with \<open>connectedin X T\<close>
          have "\<not> separatedin X C1 (\<Union>(\<V> - {C1}))"
            unfolding connectedin_eq_not_separated_subset
            by (smt (verit) that False disjnt_def UnionI disjnt_iff insertE insert_Diff)
          with that show ?thesis
            by (metis (no_types, lifting) \<open>\<V> \<approx> {..<n}\<close> eqpoll_iff_finite_card finite_Diff pairwiseD pairwise_alt pw\<V> separatedin_Union(1) separatedin_def)
        qed auto
      qed
      then show False
        by (metis \<open>\<V> \<approx> {..<n}\<close> card\<U> eqpoll_iff_finite_card leD lepoll_iff_card_le)
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
  have *: "(\<exists>\<U>::'a set set. \<U> \<approx> {..<Suc (Suc 0)} \<and> P \<U>) \<longleftrightarrow> (\<exists>A B. A\<noteq>B \<and> P{A,B})" for P
    by (metis One_nat_def eqpoll_doubleton_iff lessThan_Suc lessThan_empty_iff zero_neq_one)
  have *: "(\<exists>C1 C2. separatedin X C1 C2 \<and> C1\<noteq>C2 \<and> C1\<noteq>{} \<and> C2\<noteq>{} \<and> C1 \<union> C2 = topspace X - S) \<longleftrightarrow>
         (\<exists>C. closedin X C \<and> C \<subseteq> S \<and>
              (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> S
                   \<longrightarrow> (\<exists>C1 C2. separatedin X C1 C2 \<and> C1\<noteq>C2 \<and> C1\<noteq>{} \<and> C2\<noteq>{} \<and> C1 \<union> C2 = topspace X - D)))"
    using separation_by_closed_intermediates_eq_count [OF assms, of "Suc(Suc 0)" S]
    apply (simp add: * pairwise_insert separatedin_sym cong: conj_cong)
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


subsection\<open>A perfect set in common cases must have at least the cardinality of the continuum\<close>

lemma (in Metric_space) lepoll_perfect_set:
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
        have H: "z C \<in> sub.mcball (x B (Suc n)) (\<gamma> B (Suc n)) \<and> z C \<in> sub.mcball (x C (Suc n)) (\<gamma> C (Suc n))"
          using z [of B] z [of C] apply (simp add: lrS set_eq_iff non *)
          by (smt (verit, best) \<gamma>_Suc eq non x_Suc)
        have "k \<in> B \<longleftrightarrow> k \<in> C" if "k<n" for k
          using that unfolding n_def by (meson DiffI UnCI not_less_Least)
        moreover have "(\<forall>m. m < p \<longrightarrow> (m \<in> B \<longleftrightarrow> m \<in> C)) \<Longrightarrow> x B p = x C p \<and> \<gamma> B p = \<gamma> C p" for p
          by (induction p) auto
        ultimately have "x B n = x C n" "\<gamma> B n = \<gamma> C n"
           by blast+
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

lemma lepoll_perfect_set_aux:
  assumes lcX: "locally_compact_space X" and hsX: "Hausdorff_space X"
    and eq: "X derived_set_of topspace X = topspace X" and "topspace X \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> topspace X"
proof -
  have "(UNIV::real set) \<lesssim> (UNIV::nat set set)"
    using eqpoll_imp_lepoll eqpoll_sym nat_sets_eqpoll_reals by blast
  also have "\<dots> \<lesssim> topspace X"
  proof -
    obtain z where z: "z \<in> topspace X"
      using assms by blast
    then obtain U K where "openin X U" "compactin X K" "U \<noteq> {}" "U \<subseteq> K"
      by (metis emptyE lcX locally_compact_space_def)
    then have "closedin X K"
      by (simp add: compactin_imp_closedin hsX)
    have intK_ne: "X interior_of K \<noteq> {}"
        using \<open>U \<noteq> {}\<close> \<open>U \<subseteq> K\<close> \<open>openin X U\<close> interior_of_eq_empty by blast
    have "\<exists>D E. closedin X D \<and> D \<subseteq> K \<and> X interior_of D \<noteq> {} \<and>
                closedin X E \<and> E \<subseteq> K \<and> X interior_of E \<noteq> {} \<and>
                disjnt D E \<and> D \<subseteq> C \<and> E \<subseteq> C"
      if "closedin X C" "C \<subseteq> K" and C: "X interior_of C \<noteq> {}" for C
    proof -
      obtain z where z: "z \<in> X interior_of C" "z \<in> topspace X"
        using C interior_of_subset_topspace by fastforce 
      obtain x y where "x \<in> X interior_of C" "y \<in> X interior_of C" "x\<noteq>y"
        by (metis z eq in_derived_set_of openin_interior_of)
      then have "x \<in> topspace X" "y \<in> topspace X"
        using interior_of_subset_topspace by force+
      with hsX obtain V W where "openin X V" "openin X W" "x \<in> V" "y \<in> W" "disjnt V W"
        by (metis Hausdorff_space_def \<open>x \<noteq> y\<close>)
      have *: "\<And>W x. openin X W \<and> x \<in> W
            \<Longrightarrow> \<exists>U V. openin X U \<and> closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
        using lcX hsX locally_compact_Hausdorff_imp_regular_space neighbourhood_base_of_closedin neighbourhood_base_of
        by metis
      obtain M D where MD: "openin X M" "closedin X D" "y \<in> M" "M \<subseteq> D" "D \<subseteq> X interior_of C \<inter> W"
        using * [of "X interior_of C \<inter> W" y]
        using \<open>openin X W\<close> \<open>y \<in> W\<close> \<open>y \<in> X interior_of C\<close> by fastforce
      obtain N E where NE: "openin X N" "closedin X E" "x \<in> N" "N \<subseteq> E" "E \<subseteq> X interior_of C \<inter> V"
        using * [of "X interior_of C \<inter> V" x]
        using \<open>openin X V\<close> \<open>x \<in> V\<close> \<open>x \<in> X interior_of C\<close> by fastforce
      show ?thesis
      proof (intro exI conjI)
        show "X interior_of D \<noteq> {}" "X interior_of E \<noteq> {}"
          using MD NE by (fastforce simp: interior_of_def)+
        show "disjnt D E"
          by (meson MD(5) NE(5) \<open>disjnt V W\<close> disjnt_subset1 disjnt_sym le_inf_iff)
      qed (use MD NE \<open>C \<subseteq> K\<close> interior_of_subset in force)+
    qed
    then obtain L R where
     LR: "\<And>C. \<lbrakk>closedin X C; C \<subseteq> K; X interior_of C \<noteq> {}\<rbrakk>
      \<Longrightarrow> closedin X (L C) \<and> (L C) \<subseteq> K \<and> X interior_of (L C) \<noteq> {} \<and>
                closedin X (R C) \<and> (R C) \<subseteq> K \<and> X interior_of (R C) \<noteq> {}"
     and disjLR: "\<And>C. \<lbrakk>closedin X C; C \<subseteq> K; X interior_of C \<noteq> {}\<rbrakk>
      \<Longrightarrow> disjnt (L C) (R C) \<and> (L C) \<subseteq> C \<and> (R C) \<subseteq> C"
      by metis
    define d where "d \<equiv> \<lambda>B. rec_nat K (\<lambda>n. if n \<in> B then R else L)"
    have d0[simp]: "d B 0 = K" for B
      by (simp add: d_def)
    have [simp]: "d B (Suc n) = (if n \<in> B then R else L) (d B n)" for B n
      by (simp add: d_def)
    have d_correct: "closedin X (d B n) \<and> d B n \<subseteq> K \<and> X interior_of (d B n) \<noteq> {}" for B n
    proof (induction n)
      case 0
      then show ?case by (auto simp: \<open>closedin X K\<close> intK_ne)
    next
      case (Suc n) with LR show ?case by auto
    qed
    have "(\<Inter>n. d B n) \<noteq> {}" for B
    proof (rule compact_space_imp_nest)
      show "compact_space (subtopology X K)"
        by (simp add: \<open>compactin X K\<close> compact_space_subtopology)
      show "closedin (subtopology X K) (d B n)" for n :: nat
        by (simp add: closedin_subset_topspace d_correct)
      show "d B n \<noteq> {}" for n :: nat
        by (metis d_correct interior_of_empty)
      show "antimono (d B)"
      proof (rule antimonoI [OF transitive_stepwise_le])
        fix n
        show "d B (Suc n) \<subseteq> d B n"
        by (simp add: d_correct disjLR)
      qed auto
    qed
    then obtain x where x: "\<And>B. x B \<in> (\<Inter>n. d B n)"
      unfolding set_eq_iff by (metis empty_iff)
    show ?thesis
      unfolding lepoll_def
    proof (intro exI conjI)
      show "inj x"
      proof (rule inj_onCI)
        fix B C
        assume eq: "x B = x C" and "B\<noteq>C"
        then have ne: "sym_diff B C \<noteq> {}"
          by blast
        define n where "n \<equiv> LEAST k. k \<in> (sym_diff B C)"
        with ne have n: "n \<in> sym_diff B C"
          by (metis Inf_nat_def1 LeastI)
        then have non: "n \<in> B \<longleftrightarrow> n \<notin> C"
          by blast
        have "k \<in> B \<longleftrightarrow> k \<in> C" if "k<n" for k
          using that unfolding n_def by (meson DiffI UnCI not_less_Least)
        moreover have "(\<forall>m. m < p \<longrightarrow> (m \<in> B \<longleftrightarrow> m \<in> C)) \<Longrightarrow> d B p = d C p" for p
          by (induction p) auto
        ultimately have "d B n = d C n"
          by blast
        then have "disjnt (d B (Suc n)) (d C (Suc n))"
          by (simp add: d_correct disjLR disjnt_sym non)
        then show False
          by (metis InterE disjnt_iff eq rangeI x)
      qed
      show "range x \<subseteq> topspace X"
        using x d0 \<open>compactin X K\<close> compactin_subset_topspace d_correct by fastforce
    qed
  qed
  finally show ?thesis .
qed

lemma lepoll_perfect_set:
  assumes X: "completely_metrizable_space X \<or> locally_compact_space X \<and> Hausdorff_space X"
    and S: "X derived_set_of S = S" "S \<noteq> {}"
  shows "(UNIV::real set) \<lesssim> S"
  using X
proof
  assume "completely_metrizable_space X"
  with assms show "(UNIV::real set) \<lesssim> S"
    by (metis Metric_space.lepoll_perfect_set completely_metrizable_space_def)
next
  assume "locally_compact_space X \<and> Hausdorff_space X"
  then show "(UNIV::real set) \<lesssim> S"
    using lepoll_perfect_set_aux [of "subtopology X S"]
    by (metis Hausdorff_space_subtopology S closedin_derived_set_of closedin_subset derived_set_of_subtopology 
        locally_compact_space_closed_subset subtopology_topspace topspace_subtopology topspace_subtopology_subset)
qed




lemma Kuratowski_aux1:
  assumes "\<And>S T. R S T \<Longrightarrow> R T S"
  shows "(\<forall>S T n. R S T \<longrightarrow> (f S \<approx> {..<n::nat} \<longleftrightarrow> f T \<approx> {..<n::nat})) \<longleftrightarrow>
         (\<forall>n S T. R S T \<longrightarrow> {..<n::nat} \<lesssim> f S \<longrightarrow> {..<n::nat} \<lesssim> f T)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (meson eqpoll_iff_finite_card eqpoll_sym finite_lepoll_infinite finite_lessThan lepoll_trans2)
next
  assume ?rhs then show ?lhs
    by (smt (verit, best) lepoll_iff_finite_card  assms eqpoll_iff_finite_card finite_lepoll_infinite 
        finite_lessThan le_Suc_eq lepoll_antisym lepoll_iff_card_le not_less_eq_eq)
qed

lemma Kuratowski_aux2:
   "pairwise (separatedin (subtopology X (topspace X - S))) \<U> \<and> {} \<notin> \<U> \<and>
     \<Union>\<U> = topspace(subtopology X (topspace X - S)) \<longleftrightarrow>
     pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - S"
  by (auto simp: pairwise_def separatedin_subtopology)

proposition Kuratowski_component_number_invariance_aux:
  assumes "compact_space X" and HsX: "Hausdorff_space X" 
    and lcX: "locally_connected_space X" and hnX: "hereditarily normal_space X"
    and hom: "(subtopology X S) homeomorphic_space (subtopology X T)"
    and leXS: "{..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - S))"
  assumes \<section>: "\<And>S T.
              \<lbrakk>closedin X S; closedin X T; (subtopology X S) homeomorphic_space (subtopology X T);
              {..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - S))\<rbrakk>
              \<Longrightarrow> {..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - T))"
  shows "{..<n::nat} \<lesssim> connected_components_of (subtopology X (topspace X - T))"
proof (cases "n=0")
  case False
  obtain f g where homf: "homeomorphic_map (subtopology X S) (subtopology X T) f" 
      and homg: "homeomorphic_map (subtopology X T) (subtopology X S) g"
    and gf: "\<And>x. x \<in> topspace (subtopology X S) \<Longrightarrow> g(f x) = x" 
    and fg: "\<And>y. y \<in> topspace (subtopology X T) \<Longrightarrow> f(g y) = y"
    and f: "f \<in> topspace (subtopology X S) \<rightarrow> topspace (subtopology X T)" 
    and g: "g \<in> topspace (subtopology X T) \<rightarrow> topspace (subtopology X S)"
    using homeomorphic_space_unfold hom by metis
  obtain C where "closedin X C" "C \<subseteq> S"
     and C: "\<And>D. \<lbrakk>closedin X D; C \<subseteq> D; D \<subseteq> S\<rbrakk>
           \<Longrightarrow> \<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D"
    using separation_by_closed_intermediates_eq_count [of X n S] assms
    by (smt (verit, ccfv_threshold) False Kuratowski_aux2 lepoll_connected_components_alt)
  have "\<exists>C. closedin X C \<and> C \<subseteq> T \<and>
          (\<forall>D. closedin X D \<and> C \<subseteq> D \<and> D \<subseteq> T
               \<longrightarrow> (\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and>
                        {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - D))"
  proof (intro exI, intro conjI strip)
    have "compactin X (f ` C)"
      by (meson \<open>C \<subseteq> S\<close> \<open>closedin X C\<close> assms(1) closedin_compact_space compactin_subtopology homeomorphic_map_compactness_eq homf)
    then show "closedin X (f ` C)"
      using \<open>Hausdorff_space X\<close> compactin_imp_closedin by blast
    show "f ` C \<subseteq> T"
      by (meson \<open>C \<subseteq> S\<close> \<open>closedin X C\<close> closedin_imp_subset closedin_subset_topspace homeomorphic_map_closedness_eq homf)
    fix D'
    assume D': "closedin X D' \<and> f ` C \<subseteq> D' \<and> D' \<subseteq> T"
    define D where "D \<equiv> g ` D'"
    have "compactin X D"
      unfolding D_def
      by (meson D' \<open>compact_space X\<close> closedin_compact_space compactin_subtopology homeomorphic_map_compactness_eq homg)
    then have "closedin X D"
      by (simp add: assms(2) compactin_imp_closedin)
    moreover have "C \<subseteq> D"
      using D' D_def \<open>C \<subseteq> S\<close> \<open>closedin X C\<close> closedin_subset gf image_iff by fastforce
    moreover have "D \<subseteq> S"
      by (metis D' D_def assms(1) closedin_compact_space compactin_subtopology homeomorphic_map_compactness_eq homg)
    ultimately obtain \<U> where "\<U> \<approx> {..<n}" "pairwise (separatedin X) \<U>" "{} \<notin> \<U>" "\<Union>\<U> = topspace X - D"
      using C by meson
    moreover have "(subtopology X D) homeomorphic_space (subtopology X D')"
      unfolding homeomorphic_space_def
    proof (intro exI)
      have "subtopology X D = subtopology (subtopology X S) D"
        by (simp add: \<open>D \<subseteq> S\<close> inf.absorb2 subtopology_subtopology)
      moreover have "subtopology X D' = subtopology (subtopology X T) D'"
        by (simp add: D' inf.absorb2 subtopology_subtopology)
      moreover have "homeomorphic_maps (subtopology X T) (subtopology X S) g f"
        by (simp add: fg gf homeomorphic_maps_map homf homg)
      ultimately
      have "homeomorphic_maps (subtopology X D') (subtopology X D) g f"
        by (metis D' D_def \<open>closedin X D\<close> closedin_subset homeomorphic_maps_subtopologies topspace_subtopology Int_absorb1)
      then show "homeomorphic_maps (subtopology X D) (subtopology X D') f g"
        using homeomorphic_maps_sym by blast
    qed
    ultimately show "\<exists>\<U>. \<U> \<approx> {..<n} \<and> pairwise (separatedin X) \<U> \<and> {} \<notin> \<U> \<and> \<Union> \<U> = topspace X - D'"
      by (smt (verit, ccfv_SIG) \<section> D' False \<open>closedin X D\<close> Kuratowski_aux2 lepoll_connected_components_alt)
  qed
  then have "\<exists>\<U>. \<U> \<approx> {..<n} \<and>
         pairwise (separatedin (subtopology X (topspace X - T))) \<U> \<and> {} \<notin> \<U> \<and> \<Union>\<U> = topspace X - T"
    using separation_by_closed_intermediates_eq_count [of X n T] Kuratowski_aux2 lcX hnX by auto
  with False show ?thesis
    using lepoll_connected_components_alt by fastforce
qed auto


theorem Kuratowski_component_number_invariance:
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
  then show ?rhs
    apply (subst (asm) Kuratowski_aux1, use homeomorphic_space_sym in blast)
    apply (subst Kuratowski_aux1, use homeomorphic_space_sym in blast)
    apply (blast intro: Kuratowski_component_number_invariance_aux assms)
    done
qed blast
