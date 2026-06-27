theory Isoperimetric_Lemmas
  imports "HOL-Analysis.Analysis" 
begin

(*MIGRATE THE FIRST TWO TO THE LIBRARY*)
text \<open>A nonempty bounded open connected subset of the reals is an open interval.\<close>

lemma open_bounded_connected_real_is_interval:
  fixes c :: "real set"
  assumes "open c" "connected c" "c \<noteq> {}" "bounded c"
  shows "c = {Inf c<..<Sup c}"
proof -
  have isiv: "is_interval c" using assms(2) by (simp add: is_interval_connected_1)
  have bb: "bdd_below c" and ba: "bdd_above c" using assms(4) bounded_imp_bdd_below bounded_imp_bdd_above by auto
  have InfnotIn: "Inf c \<notin> c"
  proof
    assume "Inf c \<in> c"
    then obtain b where "b < Inf c" "{b<..Inf c} \<subseteq> c" using open_left[OF assms(1) \<open>Inf c \<in> c\<close>, of "Inf c - 1"] by auto
    then have "(Inf c + b)/2 \<in> c" by auto
    moreover have "(Inf c + b)/2 < Inf c" using \<open>b < Inf c\<close> by simp
    ultimately show False using bb cInf_lower leD by blast
  qed
  have SupnotIn: "Sup c \<notin> c"
  proof
    assume "Sup c \<in> c"
    then obtain b where "Sup c < b" "{Sup c..<b} \<subseteq> c" using open_right[OF assms(1) \<open>Sup c \<in> c\<close>, of "Sup c + 1"] by auto
    then have "(Sup c + b)/2 \<in> c" by auto
    moreover have "Sup c < (Sup c + b)/2" using \<open>Sup c < b\<close> by simp
    ultimately show False using ba cSup_upper leD by blast
  qed
  show ?thesis
  proof (intro set_eqI iffI)
    fix x assume "x \<in> c"
    then have "Inf c \<le> x" "x \<le> Sup c" using bb ba cInf_lower cSup_upper by auto
    moreover have "x \<noteq> Inf c" using \<open>x \<in> c\<close> InfnotIn by auto
    moreover have "x \<noteq> Sup c" using \<open>x \<in> c\<close> SupnotIn by auto
    ultimately show "x \<in> {Inf c<..<Sup c}" by auto
  next
    fix x assume x: "x \<in> {Inf c<..<Sup c}"
    obtain u where u: "u \<in> c" "u < x" using x assms(3) bb
      by (metis cInf_lessD greaterThanLessThan_iff)
    obtain v where v: "v \<in> c" "x < v" using x assms(3) ba
      by (metis less_cSupD greaterThanLessThan_iff)
    show "x \<in> c" using isiv u v by (meson is_interval_1 less_imp_le)
  qed
qed

text \<open>A connected subset of a segment that contains both endpoints is the whole segment.)\<close>

lemma connected_subset_segment:
  fixes a b :: "'a::euclidean_space"
  assumes "connected S" "S \<subseteq> closed_segment a b" "a \<in> S" "b \<in> S"
  shows "S = closed_segment a b"
proof (cases "a = b")
  case True
  then show ?thesis using assms by auto
next
  case False
  define f where "f = (\<lambda>x::'a. (b - a) \<bullet> x)"
  define K where "K = (b - a) \<bullet> (b - a)"
  have contf: "continuous_on S f" by (auto simp: f_def continuous_intros)
  have nz: "K > 0" using False by (simp add: K_def inner_gt_zero_iff)
  have fseg: "\<And>u. f ((1-u) *\<^sub>R a + u *\<^sub>R b) = (b - a) \<bullet> a + u * K"
    by (simp add: f_def K_def inner_diff_right algebra_simps inner_diff_left inner_commute)
  have fa: "f a = (b - a) \<bullet> a" by (simp add: f_def)
  have fb: "f b = (b - a) \<bullet> a + K" using fseg[of 1] by simp
  show ?thesis
  proof (rule subset_antisym[OF assms(2)])
    show "closed_segment a b \<subseteq> S"
    proof
      fix x assume "x \<in> closed_segment a b"
      then obtain u where u: "x = (1 - u) *\<^sub>R a + u *\<^sub>R b" "0 \<le> u" "u \<le> 1"
        by (auto simp: in_segment)
      have fx: "f x = (b - a) \<bullet> a + u * K" using u(1) fseg by simp
      have mem: "f x \<in> closed_segment (f a) (f b)"
        unfolding closed_segment_eq_real_ivl using nz u(2,3) fa fb fx
        by (auto simp: mult_left_le_one_le)
      have "closed_segment (f a) (f b) \<subseteq> f ` S"
        by (simp add: assms closed_segment_eq_real_ivl connected_contains_Icc
            connected_continuous_image contf)
      then have "f x \<in> f ` S" using mem by blast
      then obtain s where s: "s \<in> S" "f s = f x" by auto
      have "s \<in> closed_segment a b" using s(1) assms(2) by blast
      then obtain v where v: "s = (1 - v) *\<^sub>R a + v *\<^sub>R b" "0 \<le> v" "v \<le> 1"
        by (auto simp: in_segment)
      have "(b - a) \<bullet> a + v * K = (b - a) \<bullet> a + u * K"
        using s(2) v(1) fseg fx by simp
      then have "v = u" using nz by simp
      then show "x \<in> S" using s(1) v(1) u(1) by simp
    qed
  qed
qed

text \<open>A connected subset of two arcs joined only at their common endpoints, containing both
  endpoints, must contain one of the two arcs in full. (HOL Light: CONNECTED\_SUBSET\_ARC\_PAIR.)\<close>

lemma connected_subset_arc_pair:
  fixes g h :: "real \<Rightarrow> 'a::euclidean_space"
  assumes "arc g" "arc h"
    "pathstart g = pathstart h" "pathfinish g = pathfinish h"
    "path_image g \<inter> path_image h = {pathstart g, pathfinish g}"
    "connected S" "S \<subseteq> path_image g \<union> path_image h"
    "pathstart g \<in> S" "pathfinish g \<in> S"
  shows "path_image g \<subseteq> S \<or> path_image h \<subseteq> S"
proof (rule ccontr)
  assume "\<not> (path_image g \<subseteq> S \<or> path_image h \<subseteq> S)"
  then have ng: "\<not> path_image g \<subseteq> S" and nh: "\<not> path_image h \<subseteq> S" by auto
  from ng obtain pg where pg: "pg \<in> path_image g" "pg \<notin> S" by blast
  then obtain p where p: "p \<in> {0..1}" "g p = pg" by (auto simp: path_image_def)
  from nh obtain ph where ph: "ph \<in> path_image h" "ph \<notin> S" by blast
  then obtain q where q: "q \<in> {0..1}" "h q = ph" by (auto simp: path_image_def)
  have gp: "g p \<notin> S" using p(2) pg(2) by simp
  have hq: "h q \<notin> S" using q(2) ph(2) by simp
  have pathg: "path g" and pathh: "path h" using assms(1,2) arc_imp_path by auto
  have img_g0p: "path_image (subpath 0 p g) = g ` {0..p}" using p(1) by (simp add: path_image_subpath)
  have img_gp1: "path_image (subpath p 1 g) = g ` {p..1}" using p(1) by (simp add: path_image_subpath)
  have img_h0q: "path_image (subpath 0 q h) = h ` {0..q}" using q(1) by (simp add: path_image_subpath)
  have img_hq1: "path_image (subpath q 1 h) = h ` {q..1}" using q(1) by (simp add: path_image_subpath)
  have comb_g: "g ` {0..p} \<union> g ` {p..1} = path_image g"
    using p(1) by (simp add: path_image_def image_Un [symmetric]) (metis ivl_disj_un_two_touch(4))
  have comb_h: "h ` {0..q} \<union> h ` {q..1} = path_image h"
    using q(1) by (simp add: path_image_def image_Un [symmetric]) (metis ivl_disj_un_two_touch(4))
  define E1 where "E1 = S - (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h))"
  define E2 where "E2 = S - (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h))"
  have cl_gp1: "closed (path_image (subpath p 1 g))"
    using pathg p(1) by (simp add: closed_path_image path_subpath)
  have cl_hq1: "closed (path_image (subpath q 1 h))"
    using pathh q(1) by (simp add: closed_path_image path_subpath)
  have cl_g0p: "closed (path_image (subpath 0 p g))"
    using pathg p(1) by (simp add: closed_path_image path_subpath)
  have cl_h0q: "closed (path_image (subpath 0 q h))"
    using pathh q(1) by (simp add: closed_path_image path_subpath)
  have "E1 = S \<inter> (- (path_image (subpath p 1 g) \<union> path_image (subpath q 1 h)))"
    unfolding E1_def by blast
  then have openE1: "openin (top_of_set S) E1"
    using cl_gp1 cl_hq1 by blast
  have "E2 = S \<inter> (- (path_image (subpath 0 p g) \<union> path_image (subpath 0 q h)))"
    unfolding E2_def by blast
  then have openE2: "openin (top_of_set S) E2"
    using cl_g0p cl_h0q by blast
  have injg: "inj_on g {0..1}" using assms(1) by (simp add: arc_def)
  have injh: "inj_on h {0..1}" using assms(2) by (simp add: arc_def)
  have "p > 0"  "p < 1" "q > 0" "q < 1"
    using assms p q pg ph by (auto simp: pathstart_def pathfinish_def less_eq_real_def)
  have ne_E1: "pathstart g \<in> E1"
  proof -
    have "g 0 \<notin> g ` {p..1}"
      by (smt (verit, del_insts) \<open>0 < p\<close> atLeastAtMost_iff image_iff inj_on_def injg)
    moreover have "g 0 \<notin> h ` {q..1}"
      using \<open>0 < q\<close> atLeastAtMost_iff image_iff inj_on_def injh \<open>pathstart g = pathstart h\<close>
      by (smt (verit) pathstart_def)
    ultimately show ?thesis
      unfolding E1_def using assms(8) img_gp1 img_hq1 by (simp add: pathstart_def)
  qed
  have ne_E2: "pathfinish g \<in> E2"
  proof -
    have "g 1 \<notin> g ` {0..p}"
      by (smt (verit, del_insts) \<open>p < 1\<close> atLeastAtMost_iff image_iff inj_on_def injg)
    moreover have "g 1 \<notin> h ` {0..q}"
      using \<open>q < 1\<close> atLeastAtMost_iff image_iff inj_on_def injh \<open>pathfinish g = pathfinish h\<close>
      by (smt (verit) pathfinish_def)
    ultimately show ?thesis
      unfolding E2_def using img_g0p img_h0q \<open>pathfinish g \<in> S\<close> by (simp add: pathfinish_def)
  qed
  have ps_g: "pathstart g = g 0" by (simp add: pathstart_def)
  have pf_g: "pathfinish g = g 1" by (simp add: pathfinish_def)
  have cross_gh: "g s = g 0 \<or> g s = g 1" 
    if s: "s \<in> {0..1}" and t: "t \<in> {0..1}" and eq: "g s = h t" for s t
  proof -
    have "g s \<in> path_image g" using s by (auto simp: path_image_def)
    moreover have "g s \<in> path_image h" using t eq by (auto simp: path_image_def)
    ultimately show "g s = g 0 \<or> g s = g 1" using ps_g pf_g assms(5) by auto
  qed
  have sub_p1: "{p..1} \<subseteq> {0..1}" using p(1) by auto
  have sub_0p: "{0..p} \<subseteq> {0..1}" using p(1) by auto
  have sub_q1: "{q..1} \<subseteq> {0..1}" using q(1) by auto
  have sub_0q: "{0..q} \<subseteq> {0..1}" using q(1) by auto
  have gh11: "g 1 = h 1" using assms(4) by (simp add: pathfinish_def)
  have gh00: "g 0 = h 0" using assms(3) by (simp add: pathstart_def)
  have cover_False: "False" 
    if xS: "x \<in> S" and inR1: "x \<in> g ` {p..1} \<union> h ` {q..1}" and inR2: "x \<in> g ` {0..p} \<union> h ` {0..q}" for x
  proof -
    from inR1 consider (g1) "x \<in> g ` {p..1}" | (h1) "x \<in> h ` {q..1}" by auto
    then show False
    proof cases
      case g1
      then obtain s where s: "s \<in> {p..1}" "x = g s" by auto
      from inR2 consider (a) "x \<in> g ` {0..p}" | (b) "x \<in> h ` {0..q}" by auto
      then show False
      proof cases
        case a
        then obtain t where t: "t \<in> {0..p}" "x = g t" by auto
        then show False using gp xS s(2)
          using arcD assms(1) s(1) by fastforce
      next
        case b
        then obtain t where t: "t \<in> {0..q}" "x = h t" by auto
        have eq: "g s = h t" using s(2) t(2) by simp
        have "g s = g 0 \<or> g s = g 1" using cross_gh s(1) sub_p1 t(1) sub_0q eq by blast
        with that show False
          by (metis Diff_iff E1_def E2_def img_g0p img_gp1 img_h0q img_hq1 ne_E1 ne_E2 pf_g ps_g s(2))
      qed
    next
      case h1
      then obtain s where s: "s \<in> {q..1}" "x = h s" by auto
      from inR2 consider (a) "x \<in> g ` {0..p}" | (b) "x \<in> h ` {0..q}" by auto
      then show False
      proof cases
        case a
        then obtain t where t: "t \<in> {0..p}" "x = g t" by auto
        have eq: "g t = h s" using s(2) t(2) by simp
        have "g t = g 0 \<or> g t = g 1" using cross_gh t(1) sub_0p s(1) sub_q1 eq by blast
        with that show False
          by (metis Diff_iff E1_def E2_def img_g0p img_gp1 img_h0q img_hq1 ne_E1 ne_E2 pf_g ps_g t(2))
      next
        case b
        then obtain t where t: "t \<in> {0..q}" "x = h t" by auto
        then show False using hq xS s(2)
          by (smt (verit, del_insts) s atLeastAtMost_iff inj_on_def injh) 
      qed
    qed
  qed
  have cover: "S \<subseteq> E1 \<union> E2"
    using E1_def E2_def cover_False img_g0p img_gp1 img_h0q img_hq1 by auto
  have "(g ` {p..1} \<union> h ` {q..1}) \<union> (g ` {0..p} \<union> h ` {0..q}) = path_image g \<union> path_image h"
    using comb_g comb_h by blast
  with assms(7) have disjoint: "E1 \<inter> E2 = {}"
    unfolding E1_def E2_def img_gp1 img_hq1 img_g0p img_h0q by blast
  have "openin (top_of_set S) E1 \<and> openin (top_of_set S) E2 \<and> S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {}"
    using openE1 openE2 cover disjoint ne_E1 ne_E2 by auto
  with assms(6) connected_openin show False by blast
qed

text \<open>If two frontier points of a bounded convex $2$-dimensional set are joined by a frontier arc whose
  interior (the arc minus the two points) stays connected and whose convex hull is the whole set,
  then the straight segment between the two points also lies on the frontier. The connectedness of
  the arc-minus-endpoints is what rules out the spurious ``chord through the interior'' case.\<close>

lemma seg_frontier_aux:
  fixes S :: "complex set"
  assumes cvx: "convex S" and cpt: "compact S" and intne: "interior S \<noteq> {}"
    and ga_fr: "ga \<in> frontier S" and gb_fr: "gb \<in> frontier S" and ne: "ga \<noteq> gb"
    and D1fr: "path_image D1 \<subseteq> frontier S"
    and D1con: "connected (path_image D1 - {ga, gb})"
    and gaD1: "ga \<in> path_image D1" and gbD1: "gb \<in> path_image D1"
    and hullD1: "convex hull (path_image D1) = S"
  shows "closed_segment ga gb \<subseteq> frontier S"
proof -
  have clSh: "closed S" using cpt by (rule compact_imp_closed)
  have relfr: "rel_frontier S = frontier S" using intne by (rule rel_frontier_nonempty_interior)
  have ga_cl: "ga \<in> closure S" and gb_cl: "gb \<in> closure S"
    using ga_fr gb_fr by (auto simp: frontier_def)
  have dich: "open_segment ga gb \<subseteq> frontier S \<or> open_segment ga gb \<subseteq> interior S"
    using convex_open_segment_cases_alt[OF cvx ga_cl gb_cl] .
  define A where "A = \<i> * (gb - ga)"
  have A_nz: "A \<noteq> 0" using ne by (simp add: A_def)
  define e where "e = inner A ga"
  have eb: "inner A gb = e"
    unfolding A_def e_def inner_complex_def by (simp add: algebra_simps)
  have opfr: "open_segment ga gb \<subseteq> frontier S"
  proof (rule ccontr)
    assume "\<not> open_segment ga gb \<subseteq> frontier S"
    then have segint: "open_segment ga gb \<subseteq> interior S" using dich by blast
    have mid_int: "midpoint ga gb \<in> interior S"
      using segint ne by (simp add: midpoint_in_open_segment subsetD)
    have mid_e: "inner A (midpoint ga gb) = e"
      using e_def eb by (simp add: midpoint_def inner_add_right inner_diff_right field_simps)
    have not_le: "\<not> (path_image D1 \<subseteq> {x. inner A x \<le> e})"
    proof
      assume "path_image D1 \<subseteq> {x. inner A x \<le> e}"
      then have "interior S \<subseteq> interior {x. inner A x \<le> e}"
        by (metis convex_halfspace_le hullD1 hull_minimal interior_mono)
      also have "interior {x. inner A x \<le> e} = {x. inner A x < e}"
        using A_nz by (simp add: interior_halfspace_le)
      finally have "inner A (midpoint ga gb) < e" using mid_int by blast
      then show False using mid_e by simp
    qed
    have not_ge: "\<not> (path_image D1 \<subseteq> {x. e \<le> inner A x})"
    proof
      assume "path_image D1 \<subseteq> {x. e \<le> inner A x}"
      then have "interior S \<subseteq> interior {x. e \<le> inner A x}"
        by (metis convex_halfspace_ge hullD1 hull_minimal interior_mono)
      also have "interior {x. e \<le> inner A x} = {x. e < inner A x}"
        using A_nz by (simp add: interior_halfspace_ge)
      finally have "e < inner A (midpoint ga gb)" using mid_int by blast
      then show False using mid_e by simp
    qed
    from not_le obtain x1 where x1: "x1 \<in> path_image D1" "inner A x1 > e" by force
    from not_ge obtain x2 where x2: "x2 \<in> path_image D1" "inner A x2 < e" by force
    have x1ne: "x1 \<notin> {ga, gb}" using x1(2) e_def eb by auto
    have x2ne: "x2 \<notin> {ga, gb}" using x2(2) e_def eb by auto
    have x1D: "x1 \<in> path_image D1 - {ga,gb}" using x1(1) x1ne by simp
    have x2D: "x2 \<in> path_image D1 - {ga,gb}" using x2(1) x2ne by simp
    obtain w where w: "w \<in> path_image D1 - {ga,gb}" "inner A w = e"
      using connected_ivt_hyperplane[OF D1con x2D x1D, where a=A and b=e] x1(2) x2(2) by force
    have w_fr: "w \<in> rel_frontier S" using w(1) D1fr relfr by auto
    have ga_rf: "ga \<in> rel_frontier S" using ga_fr relfr by simp
    have gb_rf: "gb \<in> rel_frontier S" using gb_fr relfr by simp
    have wne: "w \<noteq> ga" "w \<noteq> gb" using w(1) by auto
    have triple: "S \<subseteq> {x. inner A x \<le> e} \<or> S \<subseteq> {x. e \<le> inner A x}"
      using cvx ne convex_triple_rel_frontier e_def eb ga_rf gb_rf w(2) w_fr wne(1,2)
      by presburger
    have D1S: "path_image D1 \<subseteq> S" by (metis hullD1 hull_subset)
    from triple show False
      using D1S local.not_le not_ge by blast
  qed
  have "{ga, gb} \<subseteq> frontier S" using ga_fr gb_fr by simp
  then show ?thesis using opfr by (simp add: closed_segment_eq_open)
qed

subsection \<open>Convex curve lemmas\<close>

text \<open>Switching between views of a convex simple closed curve.\<close>

lemma convex_hull_eq_closure_inside:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "simple_path g" "pathfinish g = pathstart g"
    and conv: "convex (inside (path_image g))"
  shows "convex hull (path_image g) = closure (inside (path_image g))"
proof (rule equalityI)
  have bounded_inside: "bounded (inside (path_image g))"
    using Jordan_inside_outside g by blast
  have frontier_inside: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast
  show "convex hull (path_image g) \<subseteq> closure (inside (path_image g))"
    by (metis Diff_subset conv convex_closure convex_hull_subset frontier_def
        frontier_inside hull_same)
  moreover
  have "compact (closure (inside (path_image g)))"
    using compact_closure local.bounded_inside by blast
  ultimately show "closure (inside (path_image g)) \<subseteq> convex hull (path_image g)"
    by (metis (no_types) Krein_Milman_frontier conv closure_closure convex_closure 
        convex_interior_closure frontier_def frontier_inside)
qed


lemma frontier_convex_hull_eq_path_image:
  fixes g :: "real \<Rightarrow> complex"
  assumes g: "simple_path g" "pathfinish g = pathstart g"
    and conv: "convex (inside (path_image g))"
  shows "frontier (convex hull (path_image g)) = path_image g"
proof -
  have eq: "convex hull (path_image g) = closure (inside (path_image g))"
    by (rule convex_hull_eq_closure_inside[OF assms])
  have open_inside: "open (inside (path_image g))"
    and frontier_inside: "frontier (inside (path_image g)) = path_image g"
    using Jordan_inside_outside g by blast+
  have "frontier (convex hull (path_image g)) = 
        closure (inside (path_image g)) - inside (path_image g)"
    by (simp add: conv convex_interior_closure eq frontier_def interior_open open_inside)
  also have "\<dots> = frontier (inside (path_image g))"
    using interior_open[OF open_inside] by (simp add: frontier_def)
  also have "\<dots> = path_image g"
    by (rule frontier_inside)
  finally show ?thesis .
qed

lemma frontier_convex_hull_subset_path_image:
  fixes g :: "real \<Rightarrow> complex"
  assumes "simple_path g" "pathfinish g = pathstart g"
    "path_image g \<subseteq> frontier (convex hull (path_image g))"
  shows "frontier (convex hull path_image g) \<subseteq> path_image g"
proof -
  have bounded_hull: "bounded (convex hull (path_image g))"
    by (simp add: assms(1) bounded_convex_hull bounded_simple_path_image)
      \<comment> \<open>The interior of the convex hull is connected, bounded, and disjoint from @{term "path_image g"}\<close>
  have int_sub: "interior (convex hull (path_image g)) \<inter> path_image g = {}"
    using assms(3) frontier_def by auto
  have "connected (interior (convex hull (path_image g)))"
    by (simp add: convex_connected)
  moreover have "bounded (interior (convex hull (path_image g)))"
    using bounded_hull bounded_interior by blast
  moreover have "interior (convex hull (path_image g)) \<subseteq> - path_image g"
    using int_sub by blast
  moreover have "inside (path_image g) \<subseteq> convex hull path_image g"
    by (metis Un_subset_iff compl_le_swap2 convex_convex_hull hull_subset
        outside_subset_convex union_with_inside)
  ultimately have int_inside: "interior (convex hull (path_image g)) \<subseteq> inside (path_image g)"
    using Jordan_inside_outside[OF \<open>simple_path g\<close>] assms
    by (smt (verit) connected_Int_frontier diff_shunt inf.commute int_sub interior_Int
        interior_eq le_iff_inf)
  have "- (convex hull (path_image g)) \<subseteq> outside (path_image g)"
    by (simp add: hull_subset outside_subset_convex)
  hence inside_sub: "inside (path_image g) \<subseteq> convex hull (path_image g)"
    by (metis Un_subset_iff compl_le_swap2 union_with_inside)
      \<comment> \<open>Since @{term "inside (path_image g)"} is open and contained in the convex hull, it lies in the interior of the hull\<close>
  have "inside (path_image g) \<subseteq> interior (convex hull (path_image g))"
    by (simp add: Jordan_inside_outside assms inside_sub interior_maximal)
  with assms show ?thesis
    using frontier_convex_hull_eq_path_image int_inside by auto
qed

end
