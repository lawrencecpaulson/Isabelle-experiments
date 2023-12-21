theory Ramsey_Extras imports
  General_Extras
  "HOL-Library.Equipollence" "HOL-Library.Ramsey" 
  "HOL-Probability.Probability"
  "Undirected_Graph_Theory.Undirected_Graph_Basics"  "Special_Function_Bounds.Exp_Bounds" 

begin

thm emeasure_uniform_count_measure
lemma emeasure_uniform_count_measure_if:
  "finite A \<Longrightarrow> emeasure (uniform_count_measure A) X = (if X \<subseteq> A then card X / card A else 0)"
  by (simp add: emeasure_notin_sets emeasure_uniform_count_measure sets_uniform_count_measure)

thm measure_uniform_count_measure
lemma measure_uniform_count_measure_if:
  "finite A \<Longrightarrow> measure (uniform_count_measure A) X = (if X \<subseteq> A then card X / card A else 0)"
  by (simp add: measure_uniform_count_measure measure_notin_sets sets_uniform_count_measure)

lemma emeasure_point_measure_finite_if:
  "finite A \<Longrightarrow> emeasure (point_measure A f) X = (if X \<subseteq> A then \<Sum>a\<in>X. f a else 0)"
  by (simp add: emeasure_point_measure_finite emeasure_notin_sets sets_point_measure)

(*
lemma measure_point_measure_finite_if:
  shows
  "finite A \<Longrightarrow> measure (point_measure A f) X = (if X \<subseteq> A then \<Sum>a\<in>X. f a else 0)"
  apply (simp add: measure_notin_sets sets_point_measure)

  apply (rule )
  defer
  apply (simp add: measure_notin_sets sets_point_measure)
apply (auto simp: )
  by (simp add: emeasure_point_measure_finite emeasure_notin_sets sets_point_measure)
*)

(*NOT USED ATM*)
definition "upair_define \<equiv> \<lambda>f e. THE u. \<exists>x y. e = {x,y} \<and> u = f x y"

lemma upair_define_apply:
  assumes "\<And>x y. f x y = f y x"
  shows "upair_define f {x,y} = f x y"
  using assms
  by (force simp add: upair_define_def doubleton_eq_iff)

lemma upair_define_apply_dom:
  assumes "\<And>x y. \<lbrakk>x\<in>A; y\<in>A\<rbrakk> \<Longrightarrow> f x y = f y x" "x\<in>A" "y\<in>A"
  shows "upair_define f {x,y} = f x y"
  using assms
  by (force simp add: upair_define_def doubleton_eq_iff)


(*for Equipollence*)
text \<open>Dedekind's definition of infinite set\<close>
lemma infinite_iff_psubset: "infinite A \<longleftrightarrow> (\<exists>B. B \<subset> A \<and> A\<approx>B)"
proof
  assume "infinite A"
  then obtain f :: "nat \<Rightarrow> 'a" where "inj f" and f: "range f \<subseteq> A"
    by (meson infinite_countable_subset)
  define C where "C \<equiv> A - range f"
  have C: "A = range f \<union> C" "range f \<inter> C = {}"
    using f by (auto simp: C_def)
  have *: "range (f \<circ> Suc) \<subset> range f"
    using inj_eq [OF \<open>inj f\<close>] by (fastforce simp: set_eq_iff)
  have "range f \<union> C \<approx> range (f \<circ> Suc) \<union> C"
  proof (intro Un_eqpoll_cong)
    show "range f \<approx> range (f \<circ> Suc)"
      by (meson \<open>inj f\<close> eqpoll_refl inj_Suc inj_compose inj_on_image_eqpoll_2)
    show "disjnt (range f) C"
      by (simp add: C disjnt_def)
    then show "disjnt (range (f \<circ> Suc)) C"
      using "*" disjnt_subset1 by blast
  qed auto
  moreover have "range (f \<circ> Suc) \<union> C \<subset> A"
    using "*" f C_def by blast
  ultimately show "\<exists>B\<subset>A. A \<approx> B"
    by (metis C(1))
next
  assume "\<exists>B\<subset>A. A \<approx> B" then show "infinite A"
    by (metis card_subset_eq eqpoll_finite_iff eqpoll_iff_card psubsetE)
qed

lemma infinite_iff_psubset_le: "infinite A \<longleftrightarrow> (\<exists>B. B \<subset> A \<and> A \<lesssim> B)"
  by (meson eqpoll_imp_lepoll infinite_iff_psubset lepoll_antisym psubsetE subset_imp_lepoll)

(*Ramsey*)
lemma finite_imp_finite_nsets: "finite A \<Longrightarrow> finite ([A]\<^bsup>k\<^esup>)"
  by (simp add: nsets_def)

lemma nsets2_E:
  assumes "e \<in> [A]\<^bsup>2\<^esup>"
  obtains x y where "e = {x,y}" "x \<in> A" "y \<in> A" "x\<noteq>y"
  using assms by (auto simp: nsets_def card_2_iff)

lemma subset_nsets_2:
  assumes "card A \<ge> 2" shows "A \<subseteq> \<Union>([A]\<^bsup>2\<^esup>)"
proof -
  obtain x y where "x \<in> A" "y \<in> A" "x\<noteq>y"
    using assms
    by (metis One_nat_def Suc_1 card.infinite card_le_Suc0_iff_eq nat_le_linear not_less_eq_eq)
  then show ?thesis
    by (auto simp: nsets_2_eq all_edges_def)
qed

lemma Pow_equals_UN_nsets:
  assumes "finite A" shows "Pow A = \<Union> (nsets A ` {..card A})"
  proof
    show "Pow A \<subseteq> \<Union> (nsets A ` {..card A})"
      using assms finite_subset by (force simp: nsets_def card_mono)
qed (auto simp: nsets_def)

lemma nsets_eq_iff:
  assumes "m \<le> card A" "n \<le> card A"
  shows "[A]\<^bsup>m\<^esup> = [A]\<^bsup>n\<^esup> \<longleftrightarrow> m=n \<or> A={}"
proof
  assume "[A]\<^bsup>m\<^esup> = [A]\<^bsup>n\<^esup>"
  then
  show "m = n \<or> A = {}"
    unfolding nsets_def using  obtain_subset_with_card_n [OF \<open>m \<le> card A\<close>] by blast
qed (use assms in auto)

lemma nsets_disjoint_iff:
  assumes "m \<le> card A" "n \<le> card A" "A \<noteq> {}"
  shows "nsets A m \<inter> nsets A n \<noteq> {} \<longleftrightarrow> m=n"
proof
  assume "[A]\<^bsup>m\<^esup> \<inter> [A]\<^bsup>n\<^esup> \<noteq> {}"
  then show "m = n"
    unfolding nsets_def by fastforce
qed (use assms in \<open>auto simp: nsets_eq_empty_iff\<close>)

lemma partn_lstE:
  assumes "partn_lst \<beta> \<alpha> \<gamma>" "f \<in> nsets \<beta> \<gamma>  \<rightarrow>  {..<l}" "length \<alpha> = l"
  obtains i H where "i < length \<alpha>" "H \<in> nsets \<beta> (\<alpha>!i)" "f ` (nsets H \<gamma>) \<subseteq> {i}"
  using partn_lst_def assms by blast

lemma partn_lst_less:
  assumes M: "partn_lst \<beta> \<alpha> n" and eq: "length \<alpha>' = length \<alpha>" 
    and le: "\<And>i. i < length \<alpha> \<Longrightarrow> \<alpha>'!i \<le> \<alpha>!i "
  shows "partn_lst \<beta> \<alpha>' n"
proof (clarsimp simp: partn_lst_def)
  fix f
  assume "f \<in> [\<beta>]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>'}"
  then obtain i H where i: "i < length \<alpha>"
                   and "H \<subseteq> \<beta>"  and H: "card H = (\<alpha>!i)" and "finite H"
                   and fi: "f ` nsets H n \<subseteq> {i}"
    using assms by (auto simp: partn_lst_def nsets_def)
  then have bij: "bij_betw (to_nat_on H) H {0..<\<alpha>!i}"
    by (metis atLeast0LessThan to_nat_on_finite)
  then have inj: "inj_on (inv_into H (to_nat_on H)) {0..<\<alpha>' ! i}"
    by (metis bij_betw_def dual_order.refl i inj_on_inv_into ivl_subset le)
  define H' where "H' = inv_into H (to_nat_on H) ` {0..<\<alpha>'!i}"
  show "\<exists>i<length \<alpha>'. \<exists>H\<in>[\<beta>]\<^bsup>(\<alpha>' ! i)\<^esup>. f ` [H]\<^bsup>n\<^esup> \<subseteq> {i}"
  proof (intro exI bexI conjI)
    show "i < length \<alpha>'"
      by (simp add: assms(2) i)
    have "H' \<subseteq> H"
      using bij \<open>i < length \<alpha>\<close> bij_betw_imp_surj_on le
      by (force simp: H'_def image_subset_iff intro: inv_into_into)
    then have "finite H'"
      by (simp add: \<open>finite H\<close> finite_subset)
    with \<open>H' \<subseteq> H\<close> have cardH': "card H' = (\<alpha>'!i)"
      unfolding H'_def by (simp add: inj card_image)
    show "f ` [H']\<^bsup>n\<^esup> \<subseteq> {i}"
      by (meson \<open>H' \<subseteq> H\<close> dual_order.trans fi image_mono nsets_mono)
    show "H' \<in> [\<beta>]\<^bsup>(\<alpha>'! i)\<^esup>"
      using \<open>H \<subseteq> \<beta>\<close> \<open>H' \<subseteq> H\<close> \<open>finite H'\<close> cardH' nsets_def by fastforce
  qed
qed

(*Ramsey?*)
lemma nsets_lepoll_cong:
  assumes "A \<lesssim> B"
  shows "[A]\<^bsup>k\<^esup> \<lesssim> [B]\<^bsup>k\<^esup>"
proof -
  obtain f where f: "inj_on f A" "f ` A \<subseteq> B"
    by (meson assms lepoll_def)
  define F where "F \<equiv> \<lambda>N. f ` N"
  have "inj_on F ([A]\<^bsup>k\<^esup>)"
    using F_def f inj_on_nsets by blast
  moreover
  have "F ` ([A]\<^bsup>k\<^esup>) \<subseteq> [B]\<^bsup>k\<^esup>"
    by (metis F_def bij_betw_def bij_betw_nsets f nsets_mono)
  ultimately show ?thesis
    by (meson lepoll_def)
qed

lemma nsets_eqpoll_cong:
  assumes "A\<approx>B"
  shows "[A]\<^bsup>k\<^esup> \<approx> [B]\<^bsup>k\<^esup>"
  by (meson assms eqpoll_imp_lepoll eqpoll_sym lepoll_antisym nsets_lepoll_cong)

lemma infinite_imp_infinite_nsets:
  assumes inf: "infinite A" and "k>0"
  shows "infinite ([A]\<^bsup>k\<^esup>)"
proof -
  obtain B where "B \<subset> A" "A\<approx>B"
    by (meson inf infinite_iff_psubset)
  then obtain a where a: "a \<in> A" "a \<notin> B"
    by blast
  then obtain N where "N \<subseteq> B" "finite N" "card N = k-1" "a \<notin> N"
    by (metis \<open>A \<approx> B\<close> inf eqpoll_finite_iff infinite_arbitrarily_large subset_eq)
  with a \<open>k>0\<close> \<open>B \<subset> A\<close> have "insert a N \<in> [A]\<^bsup>k\<^esup>"
    by (simp add: nsets_def)
  with a have "nsets B k \<noteq> nsets A k"
    by (metis (no_types, lifting) in_mono insertI1 mem_Collect_eq nsets_def)
  moreover have "nsets B k \<subseteq> nsets A k"
    using \<open>B \<subset> A\<close> nsets_mono by auto
  ultimately show ?thesis
    unfolding infinite_iff_psubset_le
    by (meson \<open>A \<approx> B\<close> eqpoll_imp_lepoll nsets_eqpoll_cong psubsetI)
qed

lemma finite_nsets_iff:
  assumes "k>0"
  shows "finite ([A]\<^bsup>k\<^esup>) \<longleftrightarrow> finite A"
  using assms finite_imp_finite_nsets infinite_imp_infinite_nsets by blast

lemma card_nsets [simp]: "card (nsets A k) = card A choose k"
proof (cases "finite A")
  case True
  then show ?thesis
    by (metis bij_betw_nsets bij_betw_same_card binomial_eq_nsets ex_bij_betw_nat_finite)
next
  case False
  then show ?thesis
    by (cases "k=0"; simp add: finite_nsets_iff)
qed


section \<open>Lemmas relating to Ramsey's theorem\<close>

lemma clique_Un: "\<lbrakk>clique K F; clique L F; \<forall>v\<in>K. \<forall>w\<in>L. v \<noteq> w \<longrightarrow> {v, w} \<in> F\<rbrakk> \<Longrightarrow> clique (K \<union> L) F"
  by (metis UnE clique_def doubleton_eq_iff)

lemma nsets2_eq_all_edges: "[A]\<^bsup>2\<^esup> = all_edges A"
  using card_2_iff' unfolding nsets_def all_edges_def
  by fastforce

(* not sure that the type class is the best approach when using Chelsea's locale*)
class infinite =
  assumes infinite_UNIV: "infinite (UNIV::'a set)"

instance nat :: infinite
  by (intro_classes) simp
instance prod :: (infinite, type) infinite
  by intro_classes (simp add: finite_prod infinite_UNIV)
instance list :: (type) infinite
  by intro_classes (simp add: infinite_UNIV_listI)


lemma null_clique[simp]: "clique {} E" and null_indep[simp]: "indep {} E"
  by (auto simp: clique_def indep_def)

lemma indep_eq_clique_compl: "indep R E = clique R (all_edges R - E)"
  by (auto simp: indep_def clique_def all_edges_def)

lemma all_edges_subset_iff_clique: "all_edges K \<subseteq> E \<longleftrightarrow> clique K E"
  by (fastforce simp add: card_2_iff clique_def all_edges_def)

lemma smaller_clique: "\<lbrakk>clique R E; R' \<subseteq> R\<rbrakk> \<Longrightarrow> clique R' E"
  by (auto simp: clique_def)

lemma smaller_indep: "\<lbrakk>indep R E; R' \<subseteq> R\<rbrakk> \<Longrightarrow> indep R' E"
  by (auto simp: indep_def)

definition "clique_indep \<equiv> \<lambda>m n K E. card K = m \<and> clique K E \<or> card K = n \<and> indep K E"

lemma clique_all_edges_iff: "clique K (E \<inter> all_edges K) \<longleftrightarrow> clique K E"
  by (simp add: clique_def all_edges_def)

lemma indep_all_edges_iff: "indep K (E \<inter> all_edges K) \<longleftrightarrow> indep K E"
  by (simp add: indep_def all_edges_def)

lemma clique_indep_all_edges_iff: "clique_indep s t K (E \<inter> all_edges K) = clique_indep s t K E"
  by (simp add: clique_all_edges_iff clique_indep_def indep_all_edges_iff)

text \<open>When talking about Ramsey numbers, sometimes cliques are best, sometimes colour maps\<close>

text \<open>identifying Ramsey numbers (possibly not the minimum) for a given type and pair of integers\<close>
definition is_clique_RN where
  "is_clique_RN \<equiv> \<lambda>U::'a itself. \<lambda>m n r. 
       (\<forall>V::'a set. \<forall>E. finite V \<longrightarrow> card V \<ge> r \<longrightarrow> (\<exists>K\<subseteq>V. clique_indep m n K E))"

text \<open>could be generalised to allow e.g. any hereditarily finite set\<close>
abbreviation is_Ramsey_number :: "[nat,nat,nat] \<Rightarrow> bool" where 
  "is_Ramsey_number m n r \<equiv> partn_lst {..<r} [m,n] 2"


definition "monochromatic \<equiv> \<lambda>\<beta> \<alpha> \<gamma> f i. \<exists>H \<in> nsets \<beta> \<alpha>. f ` (nsets H \<gamma>) \<subseteq> {i}"

lemma partn_lst_iff:
  "partn_lst \<beta> \<alpha> \<gamma> \<equiv> \<forall>f \<in> nsets \<beta> \<gamma>  \<rightarrow>  {..<length \<alpha>}. \<exists>i < length \<alpha>. monochromatic \<beta> (\<alpha>!i) \<gamma> f i"
  by (simp add: partn_lst_def monochromatic_def)

lemma is_clique_RN_imp_partn_lst:  
  fixes U :: "'a itself"
  assumes r: "is_clique_RN U m n r" and inf: "infinite (UNIV::'a set)"
  shows "partn_lst {..<r} [m,n] 2"
  unfolding partn_lst_iff 
proof (intro strip)
  fix f
  assume f: "f \<in> [{..<r}]\<^bsup>2\<^esup> \<rightarrow> {..<length [m,n]}"
  obtain V::"'a set" where "finite V" and V: "card V = r"
    by (metis inf infinite_arbitrarily_large)
  then obtain \<phi> where \<phi>: "bij_betw \<phi> V {..<r}"
    using to_nat_on_finite by blast
  have \<phi>_iff: "\<phi> v = \<phi> w \<longleftrightarrow> v=w" if "v\<in>V" "w\<in>V" for v w
    by (metis \<phi> bij_betw_inv_into_left that)
  define E where "E \<equiv> {e. \<exists>x\<in>V. \<exists>y\<in>V. e = {x,y} \<and> x \<noteq> y \<and> f {\<phi> x, \<phi> y} = 0}"
  obtain K where "K\<subseteq>V" and K: "clique_indep m n K E"
    by (metis r V \<open>finite V\<close> is_clique_RN_def nle_le)
  then consider (0) "card K = m" "clique K E" | (1) "card K = n" "indep K E"
    by (meson clique_indep_def)
  then have "\<exists>i<2. monochromatic {..<r} ([m, n] ! i) 2 f i"
  proof cases
    case 0
    have "f e = 0"
      if e: "e \<subseteq> \<phi> ` K" "finite e" "card e = 2" for e :: "nat set"
    proof -
      obtain x y where "x\<in>V" "y\<in>V" "e = {\<phi> x, \<phi> y} \<and> x \<noteq> y"
        using e \<open>K\<subseteq>V\<close> \<phi> by (fastforce simp: card_2_iff)
      then show ?thesis
        using e 0 
        apply (simp add: \<phi>_iff clique_def E_def doubleton_eq_iff image_iff)
        by (metis \<phi>_iff insert_commute)
    qed
    moreover have "\<phi> ` K \<in> [{..<r}]\<^bsup>m\<^esup>"
      unfolding nsets_def
    proof (intro conjI CollectI)
      show "\<phi> ` K \<subseteq> {..<r}"
        by (metis \<open>K \<subseteq> V\<close> \<phi> bij_betw_def image_mono)
      show "finite (\<phi> ` K)"
        using \<open>\<phi> ` K \<subseteq> {..<r}\<close> finite_nat_iff_bounded by auto
      show "card (\<phi> ` K) = m"
        by (metis "0"(1) \<open>K \<subseteq> V\<close> \<phi> bij_betw_same_card bij_betw_subset)
    qed
    ultimately show ?thesis
      apply (simp add: image_subset_iff monochromatic_def)
      by (metis (mono_tags, lifting) mem_Collect_eq nsets_def nth_Cons_0 pos2)
  next
    case 1
   have "f e = Suc 0"
      if e: "e \<subseteq> \<phi> ` K" "finite e" "card e = 2" for e :: "nat set"
    proof -
      obtain x y where "x\<in>V" "y\<in>V" "e = {\<phi> x, \<phi> y} \<and> x \<noteq> y"
        using e \<open>K\<subseteq>V\<close> \<phi> by (fastforce simp: card_2_iff)
      then show ?thesis
        using e 1 f bij_betw_imp_surj_on [OF \<phi>] 
        apply (simp add: indep_def E_def card_2_iff Pi_iff less_2_cases doubleton_eq_iff image_iff)
        by (metis \<open>K \<subseteq> V\<close> doubleton_in_nsets_2 imageI in_mono less_2_cases_iff less_irrefl numeral_2_eq_2)
    qed
    then have "f ` [\<phi> ` K]\<^bsup>2\<^esup> \<subseteq> {Suc 0}"
      by (simp add: image_subset_iff nsets_def)
    moreover have "\<phi> ` K \<in> [{..<r}]\<^bsup>n\<^esup>"
      unfolding nsets_def
    proof (intro conjI CollectI)
      show "\<phi> ` K \<subseteq> {..<r}"
        by (metis \<open>K \<subseteq> V\<close> \<phi> bij_betw_def image_mono)
      show "finite (\<phi> ` K)"
        using \<open>\<phi> ` K \<subseteq> {..<r}\<close> finite_nat_iff_bounded by auto
      show "card (\<phi> ` K) = n"
        by (metis "1"(1) \<open>K \<subseteq> V\<close> \<phi> bij_betw_same_card bij_betw_subset)
    qed 
    ultimately show ?thesis
      by (metis less_2_cases_iff monochromatic_def nth_Cons_0 nth_Cons_Suc)
  qed
  then show "\<exists>i<length [m,n]. monochromatic {..<r} ([m, n] ! i) 2 f i"
    by (simp add: numeral_2_eq_2)
qed

lemma partn_lst_imp_is_clique_RN: 
  fixes U :: "'a itself"
  assumes "partn_lst {..<r} [m,n] 2"
  shows "is_clique_RN U m n r"
  unfolding is_clique_RN_def
proof (intro strip)
  fix V::"'a set" and E ::"'a set set"
  assume V: "finite V" "r \<le> card V"
  obtain \<phi> where \<phi>: "bij_betw \<phi> {..<card V} V"
    using \<open>finite V\<close> bij_betw_from_nat_into_finite by blast
  define f :: "nat set \<Rightarrow> nat" where "f \<equiv> \<lambda>e. if \<phi>`e \<in> E then 0 else 1"
  have f: "f \<in> nsets {..<r} 2 \<rightarrow> {..<2}"
    by (simp add: f_def)
  obtain i H where "i<2" and H: "H \<subseteq> {..<r}" "finite H" "card H = [m,n] ! i" 
    and mono: "f ` (nsets H 2) \<subseteq> {i}"
    using partn_lstE [OF assms f]
    by (metis (mono_tags, lifting) length_Cons list.size(3) mem_Collect_eq nsets_def numeral_2_eq_2)
  have [simp]: "\<And>v w. \<lbrakk>v \<in> H; w \<in> H\<rbrakk> \<Longrightarrow> \<phi> v = \<phi> w \<longleftrightarrow> v=w"
    using bij_betw_imp_inj_on [OF \<phi>] H
    by (meson V(2) inj_on_def inj_on_subset lessThan_subset_iff)
  define K where "K \<equiv> \<phi> ` H"
  have [simp]: "\<And>v w. \<lbrakk>v \<in> K; w \<in> K\<rbrakk> \<Longrightarrow> inv_into {..<card V} \<phi> v = inv_into {..<card V} \<phi> w \<longleftrightarrow> v=w"
    using bij_betw_inv_into_right [OF \<phi>] H V \<phi>
    by (metis (no_types, opaque_lifting) K_def subsetD bij_betw_imp_surj_on image_mono lessThan_subset_iff)
  have "K \<subseteq> V"
    using H \<phi> V bij_betw_imp_surj_on by (fastforce simp: K_def nsets_def)
  have [simp]: "card (\<phi> ` H) = card H"
    using H by (metis V(2) \<phi> bij_betw_same_card bij_betw_subset lessThan_subset_iff)
  consider (0) "i=0" | (1) "i=1"
    using \<open>i<2\<close> by linarith
  then have "clique_indep m n K E"
  proof cases
    case 0 
    have "{v, w} \<in> E" if "v \<in> K" and "w \<in> K" and "v \<noteq> w"  for v w
    proof -
      have *: "{inv_into {..<card V} \<phi> v, inv_into {..<card V} \<phi> w} \<in> [H]\<^bsup>2\<^esup>"
        using that bij_betw_inv_into_left [OF \<phi>] H(1) V(2)
        by (auto simp: nsets_def card_insert_if K_def)
      show ?thesis
        using 0 \<open>K \<subseteq> V\<close> mono bij_betw_inv_into_right[OF \<phi>] that
        apply (simp add: f_def image_subset_iff)
        by (metis "*" image_empty image_insert subsetD)
    qed
    then show ?thesis 
      unfolding clique_indep_def clique_def
      by (simp add: "0" H(3) K_def)
  next
    case 1
    have "{v, w} \<notin> E" if "v \<in> K" and "w \<in> K" and "v \<noteq> w"  for v w
    proof -
      have *: "{inv_into {..<card V} \<phi> v, inv_into {..<card V} \<phi> w} \<in> [H]\<^bsup>2\<^esup>"
        using that bij_betw_inv_into_left [OF \<phi>] H(1) V(2)
        by (auto simp: nsets_def card_insert_if K_def)
      show ?thesis
        using 1 \<open>K \<subseteq> V\<close> mono bij_betw_inv_into_right[OF \<phi>] that
        apply (simp add: f_def image_subset_iff)
        by (metis "*" image_empty image_insert subsetD)
    qed
    then show ?thesis 
      unfolding clique_indep_def indep_def
      by (simp add: "1" H(3) K_def)
  qed
  with \<open>K \<subseteq> V\<close> show "\<exists>K. K \<subseteq> V \<and> clique_indep m n K E" by blast
qed

text \<open>All complete graphs of a given cardinality are the same\<close>
lemma is_clique_RN_any_type:
  assumes "is_clique_RN (U::'a itself) m n r" "infinite (UNIV::'a set)" 
  shows "is_clique_RN (V::'b::infinite itself) m n r"
  by (metis  partn_lst_imp_is_clique_RN is_clique_RN_imp_partn_lst assms)

lemma is_Ramsey_number_le:
  assumes "is_Ramsey_number m n r" and le: "m' \<le> m" "n' \<le> n"
  shows "is_Ramsey_number m' n' r"
  using partn_lst_less [where \<alpha> = "[m,n]" and \<alpha>' = "[m',n']"] assms
  by (force simp add: less_Suc_eq)

definition RN where
  "RN \<equiv> \<lambda>m n. LEAST r. is_Ramsey_number m n r"

lemma is_Ramsey_number_RN: "partn_lst {..< (RN m n)} [m,n] 2"
  by (metis LeastI_ex RN_def ramsey2_full)


lemma RN_le: "\<lbrakk>is_Ramsey_number m n r\<rbrakk> \<Longrightarrow> RN m n \<le> r"
  by (simp add: Least_le RN_def)

lemma RN_mono:
  assumes "m' \<le> m" "n' \<le> n"
  shows "RN m' n' \<le> RN m n"
  by (meson RN_le assms is_Ramsey_number_RN is_Ramsey_number_le)

lemma indep_iff_clique [simp]: "K \<subseteq> V \<Longrightarrow> indep K (all_edges V - E) \<longleftrightarrow> clique K E"
  by (auto simp: clique_def indep_def all_edges_def)

lemma clique_iff_indep [simp]: "K \<subseteq> V \<Longrightarrow> clique K (all_edges V - E) \<longleftrightarrow> indep K E"
  by (auto simp: clique_def indep_def all_edges_def)

lemma is_Ramsey_number_commute:
  assumes "is_Ramsey_number m n r"
  shows "is_Ramsey_number n m r"
  unfolding partn_lst_iff
proof (intro strip)
  fix f 
  assume f: "f \<in> [{..<r}]\<^bsup>2\<^esup> \<rightarrow> {..<length [n, m]}"
  define f' where "f' \<equiv> \<lambda>A. 1 - f A"
  then have "f' \<in> [{..<r}]\<^bsup>2\<^esup> \<rightarrow> {..<2}"
    by (auto simp: f'_def)
  then obtain i H where "i<2" and H: "H \<in> [{..<r}]\<^bsup>([m,n] ! i)\<^esup>" "f' ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
    using assms by (auto simp: partn_lst_def numeral_2_eq_2)
  then have "H \<subseteq> {..<r}"
    by (auto simp: nsets_def)
  then have fless2: "\<forall>x\<in>[H]\<^bsup>2\<^esup>. f x < Suc (Suc 0)"
    using funcset_mem [OF f] nsets_mono by force
  show "\<exists>i<length [n, m]. monochromatic {..<r} ([n,m] ! i) 2 f i"
    unfolding monochromatic_def
  proof (intro exI bexI conjI)
    show "f ` [H]\<^bsup>2\<^esup> \<subseteq> {1-i}"
      using H fless2 by (fastforce simp: f'_def)
    show "H \<in> [{..<r}]\<^bsup>([n, m] ! (1-i))\<^esup>"
      using \<open>i<2\<close> H by (fastforce simp add: less_2_cases_iff f'_def image_subset_iff)
  qed auto
qed

lemma RN_commute_aux: "RN n m \<le> RN m n"
  using RN_le is_Ramsey_number_RN is_Ramsey_number_commute by blast

lemma RN_commute: "RN m n = RN n m"
  by (simp add: RN_commute_aux le_antisym)


lemma RN_0 [simp]: "RN 0 m = 0"
  unfolding RN_def
proof (intro Least_equality)
  show "is_Ramsey_number 0 m 0"
    by (auto simp: partn_lst_def nsets_def)
qed auto

lemma RN_1 [simp]: 
  assumes "m>0" shows "RN (Suc 0) m = Suc 0"
  unfolding RN_def
proof (intro Least_equality)
  have [simp]: "[{..<Suc 0}]\<^bsup>2\<^esup> = {}" "[{}]\<^bsup>2\<^esup> = {}"
    by (auto simp: nsets_def card_2_iff)
  show "is_Ramsey_number (Suc 0) m (Suc 0)"
    by (auto simp: partn_lst_def)
  fix i
  assume i: "is_Ramsey_number (Suc 0) m i"
  show "i \<ge> Suc 0"
  proof (cases "i=0")
    case True
    with i assms show ?thesis
      by (auto simp: partn_lst_def nsets_empty_iff less_Suc_eq)
  qed auto
qed

lemma RN_0' [simp]: "RN m 0 = 0" and RN_1' [simp]: "m>0 \<Longrightarrow> RN m (Suc 0) = Suc 0"
  using RN_1 RN_commute by auto

lemma is_clique_RN_2: "is_clique_RN TYPE(nat) 2 m m"
  unfolding is_clique_RN_def
proof (intro strip)
  fix V :: "'a set" and E
  assume "finite V"
    and "m \<le> card V"
  show "\<exists>K. K \<subseteq> V \<and> clique_indep 2 m K E"
  proof (cases "\<exists>K. K \<subseteq> V \<and> card K = 2 \<and> clique K E")
    case False
    then have "indep V E"
      apply (clarsimp simp: clique_def indep_def card_2_iff)
      by (smt (verit, best) doubleton_eq_iff insert_absorb insert_iff subset_iff)
    then show ?thesis
      unfolding clique_indep_def
      by (meson \<open>m \<le> card V\<close> card_Ex_subset smaller_indep)
  qed (metis clique_indep_def)
qed

lemma RN_2 [simp]: 
  assumes "m>1"
  shows "RN 2 m = m"
  unfolding RN_def
proof (intro Least_equality)
  show "is_Ramsey_number 2 m m"
    using is_clique_RN_imp_partn_lst is_clique_RN_2 by blast
  fix i
  assume "is_Ramsey_number 2 m i"
  then have i: "is_clique_RN TYPE(nat) 2 m i"
    using partn_lst_imp_is_clique_RN by blast
  obtain V :: "nat set" where V: "card V = i" "finite V"
    by force
  show "i \<ge> m"
  proof (cases "i<m")
    case True
    then have "\<not> (\<exists>K\<subseteq>V. card K = 2 \<and> clique K {})"
      by (auto simp: clique_def card_2_iff')
    with i V assms show ?thesis
      unfolding is_clique_RN_def clique_indep_def by (metis card_mono dual_order.refl)
  qed auto
qed

lemma RN_2' [simp]: 
  assumes "m>1"
  shows "RN m 2 = m"
  using RN_2 RN_commute assms by force

lemma RN_3plus: 
  assumes "k \<ge> 3" "m>1"
  shows "RN k m \<ge> m"
proof -
  have "RN 2 m = m"
    using assms by auto
  with RN_mono[of 2 k m m] assms show ?thesis
    by force
qed

lemma RN_3plus': 
  assumes "k \<ge> 3" "m>1"
  shows "RN m k \<ge> m"
  using RN_3plus RN_commute assms by presburger

context sgraph
begin

lemma clique_iff: "F \<subseteq> all_edges K \<Longrightarrow> clique K F \<longleftrightarrow> F = all_edges K"
  by (auto simp: clique_def all_edges_def card_2_iff)

lemma indep_iff: "F \<subseteq> all_edges K \<Longrightarrow> indep K F \<longleftrightarrow> F = {}"
  by (auto simp: indep_def all_edges_def card_2_iff)

lemma all_edges_empty_iff: "all_edges K = {} \<longleftrightarrow> (\<exists>v. K \<subseteq> {v})"
  using clique_iff [OF empty_subsetI] by (metis clique_def empty_iff singleton_iff subset_iff)


text \<open>The original Ramsey number lower bound, by Erdős\<close>
(* requires re-factoring to take advantage of card_Pow_diff and with a symmetric treatment of 
independent sets, and also utilising Andrew's simpler estimation *)
proposition Ramsey_number_lower:  
  fixes n s::nat
  assumes "s \<ge> 3" and n: "real n \<le> 2 powr (s/2)"
  shows "\<not> is_clique_RN (TYPE (nat)) s s n"
proof
  define W where "W \<equiv> {..<n}"
  assume "is_clique_RN (TYPE (nat)) s s n"
  then have monoc: "\<And>F. \<exists>K\<subseteq>W. clique_indep s s K F"
    by (simp add: is_clique_RN_def W_def)
  then have "s \<le> n"
    by (metis W_def card_lessThan card_mono clique_indep_def finite_lessThan)
  have "s > 1" using assms by arith
  have "n>0"
    using \<open>1 < s\<close> \<open>s \<le> n\<close> by linarith
  define monoset where "monoset \<equiv> \<lambda>K::nat set. {F. F \<subseteq> all_edges K \<and> clique_indep s s K F}"

  have "(n choose s) \<le> n^s / fact s"  \<comment> \<open>probability calculation\<close>
    using binomial_fact_pow[of n s]
    by (smt (verit) fact_gt_zero of_nat_fact of_nat_mono of_nat_mult pos_divide_less_eq)  
  then have "(n choose s) * (2 / 2^(s choose 2)) \<le> 2 * n^s / (fact s * 2 ^ (s * (s-1) div 2))"
    by (simp add: choose_two divide_simps)
  also have "\<dots> \<le> 2 powr (1 + s/2) / fact s" 
  proof -
    have [simp]: "real (s * (s - Suc 0) div 2) = real s * (real s - 1) / 2"
      by (subst real_of_nat_div) auto
    have "n powr s \<le> (2 powr (s/2)) powr s"
      using n by (simp add: powr_mono2)
    then have "n powr s \<le> 2 powr (s * s / 2)"
      using \<open>n>0\<close> assms by (simp add: power2_eq_square powr_powr)
    then have "2 * n powr s \<le> 2 powr ((2 + s * s) / 2)"
      by (simp add: add_divide_distrib powr_add)
    then show ?thesis
      using n \<open>n>0\<close> by (simp add: field_simps flip: powr_realpow powr_add)
  qed
  also have "\<dots> < 1"
  proof -
    have "2 powr (1 + (k+3)/2) < fact (k+3)" for k
    proof (induction k)
      case 0
      have "2 powr (5/2) = sqrt (2^5)"
        by (metis divide_inverse mult.left_neutral numeral_powr_numeral_real powr_ge_pzero powr_half_sqrt powr_powr)
      also have "\<dots> < sqrt 36"
        by (intro real_sqrt_less_mono) auto
      finally show ?case
        by (simp add: eval_nat_numeral)
    next
      case (Suc k)
      have "2 powr (1 + real (Suc k + 3) / 2) = 2 powr (1/2) * 2 powr (1 + (k+3)/2)"
        apply (simp add: powr_add powr_half_sqrt_powr real_sqrt_mult)
        apply (simp flip: real_sqrt_mult)
        done
      also have "\<dots> \<le> sqrt 2 * fact (k+3)"
        using Suc.IH by (simp add: powr_half_sqrt)
      also have "\<dots> < real(k + 4) * fact (k + 3)"
        using sqrt2_less_2 by simp
      also have "\<dots> = fact (Suc (k + 3))"
        unfolding fact_Suc by simp
      finally show ?case by simp
    qed
    then have "2 powr (1 + s/2) < fact s"
      by (metis add.commute \<open>s\<ge>3\<close> le_Suc_ex)
    then show ?thesis
      by (simp add: divide_simps)
  qed
  finally have less_1: "real (n choose s) * (2 / 2 ^ (s choose 2)) < 1" .

  define \<Omega> where "\<Omega> \<equiv> Pow (all_edges W)"  \<comment>\<open>colour the edges randomly\<close>
  have "finite W" and cardW: "card W = n"
    by (auto simp: W_def)
  moreover
  have "card (all_edges W) = n choose 2"
    by (simp add: W_def card_all_edges)
  ultimately have card\<Omega>: "card \<Omega> = 2 ^ (n choose 2)"
    by (simp add: \<Omega>_def card_Pow finite_all_edges)
  then have fin_\<Omega>: "finite \<Omega>"
    by (simp add: \<Omega>_def \<open>finite W\<close> finite_all_edges)
  define M where "M \<equiv> uniform_count_measure \<Omega>"
  have space_eq: "space M = \<Omega>"
    by (simp add: M_def space_uniform_count_measure)
  have sets_eq: "sets M = Pow \<Omega>"
    by (simp add: M_def sets_uniform_count_measure)
  interpret P: prob_space M
    using M_def fin_\<Omega> card\<Omega> prob_space_uniform_count_measure by force

  \<comment>\<open>the event to avoid: monochromatic cliques, given @{term "K \<subseteq> W"};
      we are considering edges over the entire graph @{term W}, to agree with @{text monoc}\<close>
  define A where "A \<equiv> \<lambda>K. {F \<in> \<Omega>. F \<inter> all_edges K \<in> monoset K}"
  have A_ev: "A K \<in> P.events" for K
    by (auto simp: sets_eq A_def \<Omega>_def)
  have A_sub_\<Omega>: "A K \<subseteq> \<Omega>" for K
    by (auto simp: sets_eq A_def \<Omega>_def)
  have UA_sub_\<Omega>: "(\<Union>K \<in> nsets W s. A K) \<subseteq> \<Omega>"
    by (auto simp: \<Omega>_def A_def nsets_def all_edges_def)
  have s_choose_le: "s choose 2 \<le> n choose 2"
    using \<open>s \<le> n\<close> by (simp add: binomial_mono)
  have cardA: "card (A K) = 2 * 2 ^ ((n choose 2) - (s choose 2))" 
    if "K \<in> nsets W s" for K     \<comment>\<open>the cardinality involves the edges outside the clique\<close>
  proof -
    have K: "K \<subseteq> W" "finite K" "card K = s"
      using that by (auto simp: nsets_def)
    with \<open>finite W\<close> have [simp]: "finite ([K]\<^bsup>2\<^esup>)" "finite ([W]\<^bsup>2\<^esup>)"
      by (auto simp: finite_imp_finite_nsets)
    have "card ([K]\<^bsup>2\<^esup>) = s choose 2"
      by (simp add: K)
    have *: "all_edges K \<noteq> {}"
      using that \<open>s \<ge> 3\<close> subset_singletonD by (fastforce simp: nsets_def all_edges_empty_iff)

    define f :: "nat set set * nat set set \<Rightarrow> nat set set * nat set set" 
      where "f \<equiv> \<lambda>(EW,EA). ((EW \<inter> all_edges K) \<union> (EA - all_edges K), EA \<inter> all_edges K)"
    have "bij_betw f (Pow (nsets K 2) \<times> A K) 
                       (Pow (nsets W 2) \<times> {all_edges K, {}})"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on f (Pow ([K]\<^bsup>2\<^esup>) \<times> A K)"
        by (auto simp: inj_on_def f_def A_def nsets2_eq_all_edges)
      have *: "\<exists>EA\<subseteq>all_edges W. EA \<inter> all_edges K \<in> monoset K
                        \<and> EW = EW \<inter> all_edges K \<union> (EA - all_edges K) \<and> F = EA \<inter> all_edges K"
        if F: "F = all_edges K \<or> F = {}" and EW: "EW \<subseteq> all_edges W" for EW F
        using F
      proof
        assume \<section>: "F = all_edges K"
        show ?thesis
        proof (intro exI conjI)
          show "EW \<union> all_edges K \<subseteq> all_edges W"
            by (simp add: \<open>K \<subseteq> W\<close> all_edges_mono EW)
          show "(EW \<union> all_edges K) \<inter> all_edges K \<in> monoset K"
            by (simp add: K clique_iff clique_indep_def monoset_def)
        qed (use \<section> in auto)
      next
        assume \<section>: "F = {}"
        show ?thesis
        proof (intro exI conjI)
          show "(EW - all_edges K) \<inter> all_edges K \<in> monoset K"
            by (simp add: Int_commute K clique_indep_def indep_iff monoset_def)
        qed (use \<section> that in auto)
      qed
      have "f ` (Pow ([K]\<^bsup>2\<^esup>) \<times> A K) \<subseteq> Pow ([W]\<^bsup>2\<^esup>) \<times> {all_edges K, {}}"
        using K all_edges_mono
        by (auto simp: f_def A_def \<Omega>_def nsets2_eq_all_edges monoset_def clique_indep_def clique_iff indep_iff)
      moreover have "Pow ([W]\<^bsup>2\<^esup>) \<times> {all_edges K, {}} \<subseteq> f ` (Pow ([K]\<^bsup>2\<^esup>) \<times> A K)"
        apply (clarsimp simp: f_def A_def \<Omega>_def image_iff nsets2_eq_all_edges)
        apply (rule_tac x="a \<inter> all_edges K" in bexI; force simp add: *)
        done
      ultimately show "f ` (Pow ([K]\<^bsup>2\<^esup>) \<times> A K) = Pow ([W]\<^bsup>2\<^esup>) \<times> {all_edges K, {}}" 
        by blast
    qed
    then
    have "card (Pow (nsets K 2) \<times> A K)  = card (Pow (nsets W 2) \<times> {all_edges K, {}})"
      using bij_betw_same_card by blast
    then have "2 ^ (s choose 2) * card (A K) = 2 * 2 ^ (n choose 2)"
      using K  * by (simp add: card_Pow card_cartesian_product cardW)
    then have "2 ^ (s choose 2) * card (A K) = 2 * 2 ^ ((s choose 2) + (n choose 2 - (s choose 2)))"
      by (simp add: s_choose_le)
    then show ?thesis
      by (simp add: power_add)
  qed
  have MA: "measure M (A K) = (2 / 2 ^ (s choose 2))" if "K \<in> nsets W s" for K
    using that
    apply (simp add: M_def measure_uniform_count_measure_if A_sub_\<Omega> card\<Omega> fin_\<Omega> cardA)
    by (simp add: power_diff s_choose_le)
  then have prob_AK: "P.prob (A K) = 2 / 2 ^ (s choose 2)" if "K \<in> nsets W s" for K
    using that by (simp add: P.emeasure_eq_measure)
  have "P.prob (\<Union> K \<in> nsets W s. A K) \<le> (\<Sum>K \<in> nsets W s. P.prob (A K))"
    by (simp add: A_ev P.finite_measure_subadditive_finite \<open>finite W\<close> nsets_def image_subset_iff)
  also have "\<dots> = real (n choose s) * (2 / 2 ^ (s choose 2))"
    by (simp add: prob_AK W_def)
  also have "\<dots> < 1" 
    using less_1 by presburger
  finally have "P.prob (\<Union> K \<in> nsets W s. A K) < 1" .
  with A_ev UA_sub_\<Omega> obtain F where "F \<in> \<Omega> - (\<Union> K \<in> nsets W s. A K)"
    by (smt (verit, best) P.prob_space Diff_iff space_eq subset_antisym subset_iff)
  then have "\<forall>K \<in> nsets W s. \<not> clique_indep s s K F"
    by (simp add: A_def monoset_def \<Omega>_def clique_indep_all_edges_iff)
  then show False
    using monoc \<open>finite W\<close> finite_subset nsets_def by (fastforce simp add: clique_indep_def)
qed

lemma powr_half_ge:
  fixes x::real
  assumes "x\<ge>4"
  shows "x \<le> 2 powr (x/2)"
proof -
  have 1: "x \<le> 2 powr (x/2)" if "x=4"
    using that by simp
  have 2: "((\<lambda>x. 2 powr (x/2) - x) has_real_derivative ln 2 * (2 powr (y/2 - 1)) - 1) (at y)" for y
    by (rule derivative_eq_intros refl | simp add: powr_diff)+
  have 3: "ln 2 * (2 powr (y/2 - 1)) - 1 \<ge> 0" if "4 \<le> y" for y::real
  proof -
    have "1 \<le> ln 2 * 2 powr ((4 - 2) / (2::real))"
      using ln2_ge_two_thirds by simp
    also have "\<dots> \<le> ln 2 * (2 powr (y/2 - 1))"
      using that by (intro mult_left_mono powr_mono) auto
    finally show ?thesis by simp
  qed
  show ?thesis
    by (rule gen_upper_bound_increasing [OF assms 2 3]) auto
qed

theorem RN_lower:
  assumes "k \<ge> 3"
  shows "RN k k > 2 powr (k/2)"                              
  using assms Ramsey_number_lower is_Ramsey_number_RN
  by (smt (verit) partn_lst_imp_is_clique_RN)

text \<open>and trivially, off the diagonal too\<close>
corollary RN_lower_nodiag:
  assumes "k \<ge> 3" "l \<ge> k"
  shows "RN k l > 2 powr (k/2)"
  by (meson RN_lower RN_mono assms less_le_trans le_refl of_nat_mono)                       

theorem RN_lower_self:
  assumes "k \<ge> 4"
  shows "RN k k > k"
proof -
  have "k \<le> 2 powr (k/2)"
    using powr_half_ge numeral_le_real_of_nat_iff assms by blast
  also have "\<dots> < RN k k"
    using assms by (intro RN_lower) auto
  finally show ?thesis
    by fastforce
qed

lemma Ramsey_number_zero: "\<not> is_Ramsey_number (Suc m) (Suc n) 0"
  by (metis RN_1 RN_le is_Ramsey_number_le not_one_le_zero Suc_le_eq One_nat_def zero_less_Suc)

lemma Ramsey_number_times_lower: "\<not> is_clique_RN (TYPE(nat*nat)) (Suc m) (Suc n) (m*n)"
proof
  define edges where "edges \<equiv> {{(x,y),(x',y)}| x x' y. x<m \<and> x'<m \<and> y<n}"
  assume "is_clique_RN (TYPE(nat*nat)) (Suc m) (Suc n) (m*n)"
  then obtain K where K: "K \<subseteq> {..<m} \<times> {..<n}" and "clique_indep (Suc m) (Suc n) K edges"
    unfolding is_clique_RN_def
    by (metis card_cartesian_product card_lessThan finite_cartesian_product finite_lessThan le_refl)
  then consider "card K = Suc m \<and> clique K edges" | "card K = Suc n \<and> indep K edges"
    by (meson clique_indep_def)
  then show False
  proof cases
    case 1
    then have "inj_on fst K" "fst ` K \<subseteq> {..<m}"
      using K by (auto simp: inj_on_def clique_def edges_def doubleton_eq_iff)
    then have "card K \<le> m"
      by (metis card_image card_lessThan card_mono finite_lessThan)
    then show False
      by (simp add: "1")
  next
    case 2
    then have snd_eq: "snd u \<noteq> snd v" if "u \<in> K" "v \<in> K" "u \<noteq> v" for u v
      using that K unfolding edges_def indep_def
      by (smt (verit, best) lessThan_iff mem_Collect_eq mem_Sigma_iff prod.exhaust_sel subsetD)
    then have "inj_on snd K"
      by (meson inj_onI)
    moreover have "snd ` K \<subseteq> {..<n}"
      using comp_sgraph.wellformed K by auto
    ultimately show False
      by (metis "2" Suc_n_not_le_n card_inj_on_le card_lessThan finite_lessThan)
  qed
qed

theorem RN_times_lower:
  shows "RN (Suc m) (Suc n) > m*n"                              
  by (metis partn_lst_imp_is_clique_RN Ramsey_number_times_lower is_Ramsey_number_RN 
            partn_lst_greater_resource linorder_le_less_linear)

corollary RN_times_lower':
  shows "\<lbrakk>m>0; n>0\<rbrakk> \<Longrightarrow> RN m n > (m-1)*(n-1)"
  using RN_times_lower gr0_conv_Suc by force                              

lemma RN_gt1:
  assumes "2 \<le> k" "3 \<le> l" shows "k < RN k l"
    using RN_times_lower' [of k l] RN_3plus[of l] assms  
  by (smt (verit, best) Suc_1 Suc_pred less_le_trans Suc_le_eq n_less_n_mult_m nat_less_le numeral_3_eq_3 One_nat_def zero_less_diff)

lemma RN_gt2:
  assumes "2 \<le> k" "3 \<le> l" shows "k < RN l k"
  by (simp add: RN_commute assms RN_gt1)

text \<open>Andrew's calculation for the Ramsey lower bound. Symmetric, so works for both colours\<close>
lemma Ramsey_lower_calc:
  fixes s::nat and t::nat and p::real
  assumes "s \<ge> 3" "t \<ge> 3" "n > 4"
    and n: "real n \<le> exp ((real s - 1) * (real t - 1) / (2*(s+t)))"
  defines "p \<equiv> real s / (real s + real t)"
  shows "(n choose s) * p ^ (s choose 2) < 1/2"
proof -
  have p01: "0<p" "p<1"
    using assms by (auto simp: p_def)
  have "exp ((real s - 1) * (real t - 1) / (2*(s+t)))  \<le> exp (t / (s+t)) powr ((s-1)/2)"
    using \<open>s \<ge> 3\<close> by (simp add: mult_ac divide_simps of_nat_diff)
  with assms p01 have "n \<le> exp (t / (s+t)) powr ((s-1)/2)"
    by linarith
  then have "n * p powr ((s-1)/2) \<le> (exp (t / (s+t)) * p) powr ((s-1)/2)"
    using \<open>0<p\<close> by (simp add: powr_mult)
  also have "\<dots> < 1"
  proof -
    have "exp (real t / real (s+t)) * p < 1"
    proof -
      have "p = 1 - t / (s+t)"
        using assms by (simp add: p_def divide_simps)
      also have "\<dots> < exp (- real t / real (s+t))"
        using assms by (simp add: exp_minus_greater)
      finally show ?thesis
        by (simp add: exp_minus divide_simps mult.commute)
    qed
    then show ?thesis
      using powr01_less_one assms(1) p01(1) by auto
  qed
  finally have "n * p powr ((s-1)/2) < 1" .
  then have "(n * p powr ((s-1)/2)) ^ s < 1"
    using \<open>s \<ge> 3\<close> by (simp add: power_less_one_iff)
  then have B: "n^s * p ^ (s choose 2) < 1"
    using \<open>0<p\<close> \<open>4 < n\<close> \<open>s \<ge> 3\<close>
    by (simp add: choose_two_real powr_powr powr_mult of_nat_diff mult.commute flip: powr_realpow)
  have "(n choose s) * p ^ (s choose 2) \<le> n^s / fact s * p ^ (s choose 2)"
  proof (intro mult_right_mono)
    show "real (n choose s) \<le> real (n ^ s) / fact s"
      using binomial_fact_pow[of n s] of_nat_mono
      by (fastforce simp add: divide_simps mult.commute)
  qed (use p01 in auto)
  also have "\<dots> < 1 / fact s"
    using B by (simp add: divide_simps)
  also have "\<dots> \<le> 1/2"
    by (smt (verit, best) One_nat_def Suc_1 Suc_leD assms fact_2 fact_mono frac_less2 numeral_3_eq_3)
  finally show ?thesis .
qed


text \<open>Andrew Thomason's proof\<close> (* And the final bound can be sharpened per Andrew's suggestion*)
proposition Ramsey_number_lower_off_diag:  
  fixes n s::nat  
  assumes "s \<ge> 3" "t \<ge> 3" and n: "real n \<le> exp ((real s - 1) * (real t - 1) / (2*(s+t)))"
  shows "\<not> is_Ramsey_number s t n"
proof
  assume con: "is_Ramsey_number s t n"
  then have "(s - 1) * (t - 1) < n"
    using RN_times_lower' [of s t] assms by (metis RN_le numeral_3_eq_3 order_less_le_trans zero_less_Suc)
  moreover have "2*2 \<le> (s - 1) * (t - 1)"
    using assms by (intro mult_mono) auto
  ultimately have "n > 4"
    by simp
  define W where "W \<equiv> {..<n}"      
  have "finite W" and cardW: "card W = n"
    by (auto simp: W_def)
  define p where "p \<equiv> s / (s+t)"
  have p01: "0<p" "p<1"
    using assms by (auto simp: p_def)

  \<comment> \<open>Easier to represent the state as maps from edges to colours, not sets of coloured edges\<close>
   \<comment>\<open>colour the edges randomly\<close>
  define \<Omega> :: "(nat set \<Rightarrow> nat) set" where "\<Omega> \<equiv> (all_edges W) \<rightarrow>\<^sub>E {..<2}"
  have card\<Omega>: "card \<Omega> = 2 ^ (n choose 2)"
    by (simp add: \<Omega>_def \<open>finite W\<close> W_def card_all_edges card_funcsetE finite_all_edges)
  define coloured where "coloured \<equiv> \<lambda>F. \<lambda>f::nat set \<Rightarrow> nat. \<lambda>c. {e \<in> F. f e = c}"
  have finite_coloured[simp]: "finite (coloured F f c)" if "finite F" for f c F
    using coloured_def that by auto
  define pr where "pr \<equiv> \<lambda>F f. p ^ card (coloured F f 0) * (1-p) ^ card (coloured F f 1)"
  have pr01: "0 < pr U f" "pr U f \<le> 1" for U f \<comment> \<open>the inequality could be strict\<close>
    using \<open>0<p\<close> \<open>p<1\<close> by (auto simp: mult_le_one power_le_one pr_def card\<Omega>)
  define M where "M \<equiv> point_measure \<Omega> (pr (all_edges W))"
  have space_eq: "space M = \<Omega>"
    by (simp add: M_def space_point_measure)
  have sets_eq: "sets M = Pow \<Omega>"
    by (simp add: M_def sets_point_measure)
  have fin_\<Omega>[simp]: "finite \<Omega>"
    by (simp add: \<Omega>_def finite_PiE \<open>finite W\<close> finite_all_edges)
  have coloured_insert: 
    "coloured (insert e F) f c = (if f e = c then insert e (coloured F f c) else coloured F f c)"  for f e c F
    by (auto simp: coloured_def)
  have eq2: "{..<2} = {0, Suc 0}"
    by (simp add: insert_commute lessThan_Suc numeral_2_eq_2)
  have sum_pr_1 [simp]: "sum (pr U) (U \<rightarrow>\<^sub>E {..<2}) = 1" if "finite U" for U
    using that
  proof (induction U)
    case empty
    then show ?case
      by (simp add: pr_def coloured_def)
  next
    case (insert e F)
    then have [simp]: "e \<notin> coloured F f c" "coloured F (f(e := c)) c' = coloured F f c'" for f c c'
      by (auto simp: coloured_def)
    have inj: "inj_on (\<lambda>(y, g). g(e := y)) ({..<2} \<times> (F \<rightarrow>\<^sub>E {..<2}))"
      using \<open>e \<notin> F\<close> by (fastforce simp add: inj_on_def fun_eq_iff)
    show ?case
      using insert
      apply (simp add: pr_def coloured_insert PiE_insert_eq sum.reindex [OF inj] Information.sum_cartesian_product')
      apply (simp add: eq2 mult_ac flip: sum_distrib_left)
      done
  qed

  interpret P: prob_space M
  proof
    have "sum (pr (all_edges W)) \<Omega> = 1"
      using \<Omega>_def sum_pr_1 \<open>finite W\<close> finite_all_edges by blast
    with pr01 show "emeasure M (space M) = 1" 
      unfolding M_def
      by (metis fin_\<Omega> prob_space.emeasure_space_1 prob_space_point_measure zero_le
       ennreal_1 linorder_not_less nle_le sum_ennreal)
  qed
  \<comment>\<open>the event to avoid: monochromatic cliques, given @{term "K \<subseteq> W"};
      we are considering edges over the entire graph @{term W}\<close>
  define mono where "mono \<equiv> \<lambda>c K. {f \<in> \<Omega>. all_edges K \<subseteq> coloured (all_edges W) f c}"
  have mono_ev: "mono c K \<in> P.events" if "c<2" for K c
    by (auto simp: sets_eq mono_def \<Omega>_def)
  have mono_sub_\<Omega>: "mono c K \<subseteq> \<Omega>" if "c<2" for K c
    using mono_ev sets_eq that by auto

  have emeasure_eq: "emeasure M C = (if C \<subseteq> \<Omega> then (\<Sum>a\<in>C. ennreal (pr (all_edges W) a)) else 0)" for C
    by (simp add: M_def emeasure_notin_sets emeasure_point_measure_finite sets_point_measure)
  define pc where "pc \<equiv> \<lambda>c::nat. if c=0 then p else 1-p"
  have pc0: "0 \<le> pc c" for c
    using p01 pc_def by auto
  have coloured_upd: "coloured F (\<lambda>t\<in>F. if t \<in> G then c else f t) c' 
        = (if c=c' then G \<union> coloured (F-G) f c' else coloured (F-G) f c')" if "G \<subseteq> F" for F G f c c'
    using that by (auto simp: coloured_def)

  have prob_mono: "P.prob (mono c K) = pc c ^ (r choose 2)"  
    if "K \<in> nsets W r" "c<2" for r K c
  proof -
    have \<section>: "K \<subseteq> W" "finite K" "card K = r"
      using that by (auto simp: nsets_def)
    have *: "{f \<in> \<Omega>. all_edges K \<subseteq> coloured (all_edges W) f c} = 
          (\<Union>g \<in> (all_edges W - all_edges K) \<rightarrow>\<^sub>E {..<2}. {\<lambda>t \<in> all_edges W. if t \<in> all_edges K then c else g t})"
      (is "?L = ?R")
    proof
      show "?L \<subseteq> ?R"
      proof clarsimp
        fix f
        assume f: "f \<in> \<Omega>" and c: "all_edges K \<subseteq> coloured (all_edges W) f c"
        then show "\<exists>g\<in>all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2}. f = (\<lambda>t\<in>all_edges W. if t \<in> all_edges K then c else g t)"
          apply (rule_tac x="restrict f (all_edges W - all_edges K)" in bexI)
          apply (force simp add: \<Omega>_def coloured_def subset_iff)+
          done
      qed
      show "?R \<subseteq> ?L"
        using that all_edges_mono[OF \<open>K \<subseteq> W\<close>] by (auto simp: coloured_def \<Omega>_def nsets_def PiE_iff)
    qed

    have [simp]: "card (all_edges K \<union> coloured (all_edges W - all_edges K) f c)
                = (r choose 2) + card (coloured (all_edges W - all_edges K) f c)" for f c
      using \<section> \<open>finite W\<close>
      by (subst card_Un_disjoint) (auto simp: finite_all_edges coloured_def card_all_edges)

    have pr_upd: "pr (all_edges W) (\<lambda>t \<in> all_edges W. if t \<in> all_edges K then c else f t) 
        = pc c ^ (r choose 2) * pr (all_edges W - all_edges K) f" 
      if "f \<in> all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2}" for f
      using that all_edges_mono[OF \<open>K \<subseteq> W\<close>] p01 \<open>c<2\<close> \<section>
      by (simp add: pr_def coloured_upd pc_def power_add)
    have "emeasure M (mono c K) = (\<Sum>f \<in> mono c K. ennreal (pr (all_edges W) f))"
      using that by (simp add: emeasure_eq mono_sub_\<Omega>)
    also have "... = (\<Sum>f\<in>(\<Union>g\<in>all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2}.
                            {\<lambda>t\<in>all_edges W. if t \<in> all_edges K then c else g t}). 
                      ennreal (pr (all_edges W) f))" 
      by (simp add: mono_def *)
    also have "... = (\<Sum>g\<in>all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2}. 
                        \<Sum>f\<in>{\<lambda>t\<in>all_edges W. if t \<in> all_edges K then c else g t}. 
                           ennreal (pr (all_edges W) f))"
    proof (rule sum.UNION_disjoint_family)
      show "finite (all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2::nat})"
        by (simp add: \<open>finite W\<close> finite_PiE finite_all_edges)
      show "disjoint_family_on (\<lambda>g. {\<lambda>t\<in>all_edges W. if t \<in> all_edges K then c else g t}) (all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2})"
        apply (simp add: disjoint_family_on_def fun_eq_iff)
        by (metis DiffE PiE_E)
    qed auto
    also have "\<dots> = (\<Sum>x\<in>all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2}. ennreal (pc c ^ (r choose 2) * pr (all_edges W - all_edges K) x))"
      by (simp add: pr_upd)
    also have "... = ennreal (\<Sum>f\<in>all_edges W - all_edges K \<rightarrow>\<^sub>E {..<2}. 
                                pc c ^ (r choose 2) * pr (all_edges W - all_edges K) f)"
      using pr01 pc0 sum.cong sum_ennreal by (smt (verit) mult_nonneg_nonneg zero_le_power)
    also have "... = ennreal (pc c ^ (r choose 2))"
      by (simp add: \<open>finite W\<close> finite_all_edges flip: sum_distrib_left)
    finally have "emeasure M (mono c K) = ennreal (pc c ^ (r choose 2))" .
    then show ?thesis 
      using p01 that by (simp add: measure_eq_emeasure_eq_ennreal pc_def)
  qed

  define Reds where "Reds \<equiv> (\<Union>K \<in> nsets W s. mono 0 K)"
  define Blues where "Blues \<equiv> (\<Union>K \<in> nsets W t. mono 1 K)"
  have Uev: "\<Union> (mono c ` [W]\<^bsup>r\<^esup>) \<in> P.events" for c r
    by (simp add: local.mono_def sets_eq subset_iff)
  then have "Reds \<in> P.events" "Blues \<in> P.events"
    by (auto simp: Reds_def Blues_def)
  have prob_0: "P.prob Reds < 1/2" 
  proof -
    have "P.prob Reds \<le> (\<Sum>K \<in> nsets W s. P.prob (mono 0 K))"
      by (simp add: Reds_def \<open>finite W\<close> finite_imp_finite_nsets measure_UNION_le mono_ev)
    also have "\<dots> \<le> (n choose s) * (p ^ (s choose 2))"
      by (simp add: prob_mono pc_def cardW)
    also have "\<dots> < 1/2"
      using Ramsey_lower_calc \<open>4 < n\<close> assms(1) assms(2) n p_def by auto
    finally show ?thesis .
  qed
  moreover
  have prob_1: "P.prob Blues < 1/2" 
  proof -
    have "1-p = real t / (real t + real s)"
      using \<open>s \<ge> 3\<close> by (simp add: p_def divide_simps)
    with assms have *: "(n choose t) * (1-p) ^ (t choose 2) < 1/2"
      by (metis Ramsey_lower_calc add.commute mult.commute \<open>4 < n\<close>) 
    have "P.prob Blues \<le> (\<Sum>K \<in> nsets W t. P.prob (mono 1 K))"
      by (simp add: Blues_def \<open>finite W\<close> finite_imp_finite_nsets measure_UNION_le mono_ev)
    also have "\<dots> \<le> (n choose t) * ((1-p) ^ (t choose 2))"
      by (simp add: prob_mono pc_def cardW)
    also have "\<dots> < 1/2"
      using "*" by blast
    finally show ?thesis .
  qed
  ultimately have "P.prob (Reds \<union> Blues) < 1/2 + 1/2"
    using P.finite_measure_subadditive \<open>Blues \<in> P.events\<close> \<open>Reds \<in> P.events\<close> by fastforce
  then obtain F where F: "F \<in> \<Omega> - (Reds \<union> Blues)"
    by (metis Blues_def Diff_iff P.prob_space Pow_iff Reds_def Un_subset_iff Uev equalityI field_sum_of_halves less_irrefl sets_eq space_eq subsetI)
  have False if "i < 2" "H \<in> [W]\<^bsup>([s, t] ! i)\<^esup>" "F ` [H]\<^bsup>2\<^esup> \<subseteq> {i}" for i H
  proof -
    have "\<not> all_edges H \<subseteq> {e \<in> all_edges W. F e = 0}" "\<not> all_edges H \<subseteq> {e \<in> all_edges W. F e = 1}"
      using F that
      by (auto simp: less_2_cases_iff nsets2_eq_all_edges \<Omega>_def Reds_def Blues_def mono_def coloured_def image_subset_iff)
    moreover have "H \<subseteq> W"
      using that by (auto simp: nsets_def)
    ultimately show False
      using that all_edges_mono [OF \<open>H \<subseteq> W\<close>] by (auto simp: less_2_cases_iff nsets2_eq_all_edges)
  qed
  moreover have "F \<in> [{..<n}]\<^bsup>2\<^esup> \<rightarrow> {..<2}"
    using F by (auto simp: W_def \<Omega>_def nsets2_eq_all_edges)
  ultimately show False
    using con by (force simp add: W_def partn_lst_def numeral_2_eq_2)
qed

theorem RN_lower_off_diag:
  assumes "s \<ge> 3" "t \<ge> 3"
  shows "RN s t > exp ((real s - 1) * (real t - 1) / (2*(s+t)))"            
  using Ramsey_number_lower_off_diag [OF assms]
  using is_Ramsey_number_RN by force

end

end
