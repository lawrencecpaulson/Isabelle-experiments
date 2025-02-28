theory Farey
  imports Complex_Main "HOL-Number_Theory.Totient" "HOL-Library.Sublist"
    "HOL-ex.Sketch_and_Explore"
begin

(*MOVE*)
lemma quotient_of_rat_of_int [simp]: "quotient_of (rat_of_int i) = (i, 1)"
  using Rat.of_int_def quotient_of_int by force

lemma ex_interval_simps [simp]:
      "(\<exists>x \<in> {..<u}. P x) \<longleftrightarrow> (\<exists>x<u. P x)"
      "(\<exists>x \<in> {..u}. P x) \<longleftrightarrow> (\<exists>x\<le>u. P x)"
      "(\<exists>x \<in> {l<..}. P x) \<longleftrightarrow> (\<exists>x>l. P x)"
      "(\<exists>x \<in> {l..}. P x) \<longleftrightarrow> (\<exists>x\<ge>l. P x)"
      "(\<exists>x \<in> {l<..<u}. P x) \<longleftrightarrow> (\<exists>x. l<x \<and> x<u \<and> P x)"
      "(\<exists>x \<in> {l..<u}. P x) \<longleftrightarrow> (\<exists>x. l\<le>x \<and> x<u \<and> P x)"
      "(\<exists>x \<in> {l<..u}. P x) \<longleftrightarrow> (\<exists>x. l<x \<and> x\<le>u \<and> P x)"
      "(\<exists>x \<in> {l..u}. P x) \<longleftrightarrow> (\<exists>x. l\<le>x \<and> x\<le>u \<and> P x)"
  by auto

lemma all_interval_simps [simp]:
      "(\<forall>x \<in> {..<u}. P x) \<longleftrightarrow> (\<forall>x<u. P x)"
      "(\<forall>x \<in> {..u}. P x) \<longleftrightarrow> (\<forall>x\<le>u. P x)"
      "(\<forall>x \<in> {l<..}. P x) \<longleftrightarrow> (\<forall>x>l. P x)"
      "(\<forall>x \<in> {l..}. P x) \<longleftrightarrow> (\<forall>x\<ge>l. P x)"
      "(\<forall>x \<in> {l<..<u}. P x) \<longleftrightarrow> (\<forall>x. l<x \<longrightarrow> x<u \<longrightarrow> P x)"
      "(\<forall>x \<in> {l..<u}. P x) \<longleftrightarrow> (\<forall>x. l\<le>x \<longrightarrow> x<u \<longrightarrow> P x)"
      "(\<forall>x \<in> {l<..u}. P x) \<longleftrightarrow> (\<forall>x. l<x \<longrightarrow> x\<le>u \<longrightarrow> P x)"
      "(\<forall>x \<in> {l..u}. P x) \<longleftrightarrow> (\<forall>x. l\<le>x \<longrightarrow> x\<le>u \<longrightarrow> P x)"
  by auto



thm int_div_less_self
lemma int_div_le_self: 
  \<open>x div k \<le> x\<close> if \<open>0 < x\<close>  for x k :: int
  by (metis div_by_1 int_div_less_self less_le_not_le nle_le nonneg1_imp_zdiv_pos_iff order.trans that)

section \<open>Farey Fractions\<close>

type_synonym farey = rat

definition num_farey :: "farey \<Rightarrow> int" where "num_farey \<equiv> \<lambda>x. fst (quotient_of x)" 
definition denom_farey :: "farey \<Rightarrow> int" where "denom_farey \<equiv> \<lambda>x. snd (quotient_of x)" 

definition farey :: "[int,int] \<Rightarrow> farey" where "farey \<equiv> \<lambda>a b. max 0 (min 1 (Fract a b))"

lemma farey01 [simp]: "0 \<le> farey a b" "farey a b \<le> 1"
  by (auto simp: min_def max_def farey_def)

lemma num_farey_nonneg: "x \<in> {0..1} \<Longrightarrow> num_farey x \<ge> 0"
  by (cases x) (simp add: num_farey_def quotient_of_Fract zero_le_Fract_iff)

lemma num_farey_le_denom: "x \<in> {0..1} \<Longrightarrow> num_farey x \<le> denom_farey x"
  by (cases x) (simp add: Fract_le_one_iff denom_farey_def num_farey_def quotient_of_Fract)

lemma denom_farey_pos: "denom_farey x > 0"
  by (simp add: denom_farey_def quotient_of_denom_pos')

lemma coprime_num_denom_farey [intro]: "coprime (num_farey x) (denom_farey x)"
  by (simp add: denom_farey_def num_farey_def quotient_of_coprime)

lemma rat_of_farey_conv_num_denom:
  "x = rat_of_int (num_farey x) / rat_of_int (denom_farey x)"
  by (simp add: denom_farey_def num_farey_def quotient_of_div)

lemma num_denom_farey_eqI:
  assumes "x = of_int a / of_int b" "b > 0" "coprime a b"
  shows   "num_farey x = a" "denom_farey x = b"
  using Fract_of_int_quotient assms quotient_of_Fract
  by (auto simp: num_farey_def denom_farey_def)

lemma farey_cases [cases type, case_names farey]:
  assumes "x \<in> {0..1}"
  obtains a b where "0\<le>a" "a\<le>b" "coprime a b" "x = Fract a b"
  by (metis Fract_of_int_quotient Rat_cases assms num_denom_farey_eqI num_farey_le_denom num_farey_nonneg)

lemma rat_of_farey: "\<lbrakk>x = of_int a / of_int b; x \<in> {0..1}\<rbrakk> \<Longrightarrow> x = farey a b"
  by (simp add: Fract_of_int_quotient farey_def max_def)

lemma farey_num_denom_eq [simp]: "x \<in> {0..1} \<Longrightarrow> farey (num_farey x) (denom_farey x) = x"
  using rat_of_farey rat_of_farey_conv_num_denom by fastforce

lemma farey_eqI:
  assumes "num_farey x = num_farey y" "denom_farey x = denom_farey y"
  shows   "x=y"
  by (metis Rat.of_int_def assms rat_of_farey_conv_num_denom)

lemma
  assumes "coprime a b" "0\<le>a" "a<b"
  shows num_farey_eq [simp]: "num_farey (farey a b) = a"
  and denom_farey_eq [simp]: "denom_farey (farey a b) = b"
  using Fract_less_one_iff quotient_of_Fract zero_le_Fract_iff
  using assms num_denom_farey_eqI rat_of_farey by force+

lemma
  assumes "0 \<le> a" "a \<le> b" "0<b"
  shows num_farey: "num_farey (farey a b) = a div (gcd a b)" 
    and denom_farey: "denom_farey (farey a b) = b div (gcd a b)"
proof -
  have "0 \<le> Fract a b" "Fract a b \<le> 1"
    using assms by (auto simp: Fract_le_one_iff zero_le_Fract_iff)
  with assms show "num_farey (farey a b) = a div (gcd a b)" "denom_farey (farey a b) = b div (gcd a b)"
    by (auto simp: num_farey_def denom_farey_def farey_def quotient_of_Fract Rat.normalize_def Let_def)
qed

lemma
  assumes "coprime a b" "0<b"
  shows num_farey_Fract [simp]: "num_farey (Fract a b) = a"
  and denom_farey_Fract [simp]: "denom_farey (Fract a b) = b"
  using Fract_of_int_quotient assms num_denom_farey_eqI by force+

lemma num_farey_0 [simp]: "num_farey 0 = 0"
  and denom_farey_0 [simp]: "denom_farey 0 = 1"
  and num_farey_1 [simp]: "num_farey 1 = 1"
  and denom_farey_1 [simp]: "denom_farey 1 = 1"
  by (auto simp: num_farey_def denom_farey_def)

lemma num_farey_neq_denom: "denom_farey x \<noteq> 1 \<Longrightarrow> num_farey x \<noteq> denom_farey x"
  by (metis denom_farey_0 div_0 div_self num_farey_1 rat_of_farey_conv_num_denom)

lemma num_farey_0_iff [simp]: "num_farey x = 0 \<longleftrightarrow> x = 0"
  unfolding num_farey_def
  by (metis div_0 eq_fst_iff of_int_0 quotient_of_div rat_zero_code)

lemma denom_farey_le1_cases:
  assumes "denom_farey x \<le> 1" "x \<in> {0..1}"
  shows "x = 0 \<or> x = 1"
proof -
  consider "num_farey x = 0" | "num_farey x = 1" "denom_farey x = 1"
    using assms num_farey_le_denom [of x] num_farey_nonneg [of x] by linarith
  then show ?thesis
    by (metis denom_farey_1 farey_eqI num_farey_0_iff num_farey_1)
qed

definition mediant :: "farey \<Rightarrow> farey \<Rightarrow> farey" where 
  "mediant \<equiv> \<lambda>x y. Fract (fst (quotient_of x) + fst (quotient_of y)) 
                         (snd (quotient_of x) + snd (quotient_of y))"

lemma mediant_eq_Fract:
  "mediant x y = Fract (num_farey x + num_farey y) (denom_farey x + denom_farey y)"
  by (simp add: denom_farey_def num_farey_def mediant_def)

lemma mediant_eq_farey:
  assumes "x \<in> {0..1}" "y \<in> {0..1}"
  shows "mediant x y = farey (num_farey x + num_farey y) (denom_farey x + denom_farey y)"
proof -
  have "0 \<le> num_farey x + num_farey y"
    using assms num_farey_nonneg by auto
  moreover have "num_farey x + num_farey y \<le> denom_farey x + denom_farey y"
    by (meson add_mono assms num_farey_le_denom)
  ultimately show ?thesis
    by (simp add: add_pos_pos denom_farey_pos Fract_of_int_quotient rat_of_farey mediant_eq_Fract)
qed

definition farey_consecutive :: "farey \<Rightarrow> farey \<Rightarrow> bool" where
  "farey_consecutive x y \<longleftrightarrow>
     denom_farey x * num_farey y - num_farey x * denom_farey y = 1"

fun farey_list_consecutive :: "farey list \<Rightarrow> bool" where
  "farey_list_consecutive [] = True"
| "farey_list_consecutive [x] = True"
| "farey_list_consecutive (x # y # xs) = (farey_consecutive x y \<and> farey_list_consecutive (y # xs))"


lemma farey_consecutive_imp_less:
  assumes "farey_consecutive x y"
  shows   "x < y"
  using assms
  by (auto simp: farey_consecutive_def rat_less_code denom_farey_def num_farey_def)

lemma denom_mediant: "denom_farey (mediant x y) \<le> denom_farey x + denom_farey y"
  using quotient_of_denom_pos' [of x] quotient_of_denom_pos' [of y]
  by (simp add: mediant_eq_Fract denom_farey_def num_farey_def quotient_of_Fract normalize_def Let_def int_div_le_self)

fun farey_step :: "nat \<Rightarrow> farey list \<Rightarrow> farey list" where
  "farey_step bd [] = []"
| "farey_step bd [x] = [x]"
| "farey_step bd (x # y # xs) =
     (if denom_farey x + denom_farey y \<le> bd
      then x # mediant x y # farey_step bd (y # xs)
      else x # farey_step bd (y # xs))"

lemma farey_step_denom_le:
  assumes "x \<in> set (farey_step bd xs)" "x \<notin> set xs"
  shows "denom_farey x \<le> bd"
  using assms
proof (induction xs rule: farey_step.induct)
  case (3 bd x y xs)
  then show ?case
    using denom_mediant by (auto intro: order.trans split: if_splits)
qed auto

lemma consecutive_imp_both_coprime:
  fixes a:: "'a::{algebraic_semidom,comm_ring_1}"
  assumes "b*c - a*d = 1" 
  shows   "coprime a b" "coprime c d"
  using mult.commute by (metis assms coprimeI dvd_diff dvd_mult2)+

lemma consecutive_imp_coprime:
  fixes a:: "'a::{algebraic_semidom,comm_ring_1}"
  assumes "b*c - a*d = 1" 
  shows   "coprime (a+c) (b+d)"
proof (rule coprimeI)
  fix k 
  assume k: "k dvd (a+c)" "k dvd (b+d)"
  moreover have "(b+d)*c = (a+c)*d + 1"
    using assms by (simp add: algebra_simps)
  ultimately show "is_unit k"
    by (metis add_diff_cancel_left' dvd_diff dvd_mult2)
qed

(* Theorem 5.4 *)
lemma farey_consecutive_mediant: 
  assumes "farey_consecutive x y"
  shows "farey_consecutive x (mediant x y)" "farey_consecutive (mediant x y) y"
  using assms quotient_of_denom_pos' [of x] quotient_of_denom_pos' [of y]
  unfolding farey_consecutive_def
  by (auto simp: mediant_eq_Fract denom_farey_def num_farey_def quotient_of_Fract consecutive_imp_coprime algebra_simps)

definition "fareys n \<equiv> sorted_list_of_set {x \<in> {0..1}. denom_farey x \<le> int n}"

lemma farey_set: "{x \<in> {0..1}. denom_farey x \<le> n} = (\<Union>b \<in> {1..n}. \<Union>a \<in> {0..b}. {farey a b})"
proof -
  have "\<exists>b \<in> {1..n}. \<exists>a \<in> {0..b}. x = farey a b"
    if "denom_farey x \<le> n" "x \<in> {0..1}" for x :: farey
    using that denom_farey_pos int_one_le_iff_zero_less num_farey_le_denom num_farey_nonneg by force
  moreover have "\<And>b a::int. 0 \<le> b \<Longrightarrow> b div gcd a b \<le> b"
    by (metis div_0 int_div_le_self nless_le)
  ultimately show ?thesis
    by (auto simp: denom_farey) (meson order_trans)
qed

lemma farey_set': "{x \<in> {0..1}. denom_farey x \<le> n} = (\<Union>b \<in> {1..n}. \<Union>a \<in> {0..b}. if coprime a b then {farey a b} else {})"
proof -
  have "\<exists>aa ba. farey a b = farey aa ba \<and> 0 \<le> aa \<and> aa \<le> ba \<and> 1 \<le> ba \<and> ba \<le> n \<and> coprime aa ba"
    if "1 \<le> b" and "b \<le> n" and "0 \<le> a" and "a \<le> b" for a b
  proof -
    let ?a = "a div gcd a b"
    let ?b = "b div gcd a b"
    have "coprime ?a ?b"
      by (metis div_gcd_coprime not_one_le_zero \<open>b\<ge>1\<close>)
    moreover have "farey a b = farey ?a ?b"
      using Fract_coprime farey_def by presburger
    moreover have "?a \<le> ?b \<and> ?b \<le> n"
      by (smt (verit, best) gcd_pos_int int_div_le_self that zdiv_mono1)
    ultimately show ?thesis
      using that by (metis denom_farey denom_farey_pos div_int_pos_iff gcd_ge_0_int int_one_le_iff_zero_less)
  qed
  then show ?thesis
    unfolding farey_set
    by (fastforce split: if_splits)
qed

lemma finite_farey_set: "finite {x \<in> {0..1}. denom_farey x \<le> int n}"
  unfolding farey_set by blast


lemma fareys_0 [simp]: "fareys 0 = []"
  unfolding fareys_def farey_set
  by simp

lemma fareys_1 [simp]: "fareys 1 = [0, 1]"
proof -
  have "{x \<in> {0..1}. denom_farey x \<le> 1} = {0,1}"
    using denom_farey_le1_cases by auto
  then show ?thesis
    by (simp add: fareys_def)
qed

lemma fareys_2 [simp]: "fareys 2 = [0, farey 1 2, 1]"
proof -
  have \<section>: "denom_farey x \<le> 2 \<longleftrightarrow> denom_farey x = 1 \<or> denom_farey x = 2" for x
    using denom_farey_pos [of x] by auto
  have "{x \<in> {0..1}. denom_farey x \<le> 2} = {farey 0 1, farey 1 2, farey 1 1}"
  proof -
    have "x = farey 1 1"
      if "x \<noteq> farey 0 1" "x \<in> {0..1}" "denom_farey x = 1" for x
      using that denom_farey_le1_cases order.eq_iff rat_of_farey by auto
    moreover have False
      if "x \<noteq> farey 0 1" "x \<noteq> farey 1 2" "denom_farey x = 2" "x \<in> {0..1}" for x
      using that num_farey_neq_denom 
      by (metis farey_def farey_num_denom_eq int_one_le_iff_zero_less nle_le num_farey_le_denom num_farey_nonneg one_add_one
          order_le_less rat_number_collapse(1) zle_add1_eq_le)
    moreover have "denom_farey (farey 1 1) = 1"
       by (simp add: Fract_of_int_quotient farey_def)
    ultimately show ?thesis
      by (auto simp: farey_set \<section>)
  qed
  also have "... = {0, 1/2, 1::rat}"
    by (simp add: farey_def Fract_of_int_quotient)
  finally show ?thesis
    by (simp add: fareys_def farey_def Fract_of_int_quotient)
qed

lemma farey_set_increasing: "set (fareys n) \<subseteq> set (fareys (Suc n))"
  using farey_set by (force simp: fareys_def)

definition fareys_new :: "nat \<Rightarrow> rat set" where
  "fareys_new n \<equiv> {farey a n| a. coprime a n \<and> a \<in> {0..int n}}"

lemma set_fareys_Suc: "set (fareys (Suc n)) = set (fareys n) \<union> fareys_new (Suc n)"
proof -
  have "\<exists>b\<ge>1. b \<le> int n \<and> (\<exists>a\<ge>0. a \<le> b \<and> coprime a b \<and> farey c d = farey a b)"
    if "farey c d \<notin> fareys_new (Suc n)"
      and "coprime c d" "1 \<le> d" "d \<le> 1 + int n" "0 \<le> c" "c \<le> d"
    for c d
  proof (cases "d = 1 + int n")
    case True
    with that show ?thesis
      by (auto simp: fareys_new_def)
  qed (use that in auto)
  moreover have "\<exists>d\<ge>1. d \<le> 1 + int n \<and> (\<exists>c\<ge>0. c \<le> d \<and> coprime c d \<and> x = farey c d)"
    if "x \<in> fareys_new (Suc n)" for x
    using that int_one_le_iff_zero_less by (force simp add: fareys_new_def)
  ultimately show ?thesis
    unfolding fareys_def farey_set'
    by fastforce
qed


lemma farey_list_consecutive_step:
  assumes "farey_list_consecutive xs"
  shows "farey_list_consecutive (farey_step n xs)"
  using assms
proof (induction xs rule: farey_step.induct)
  case (3 bd x y xs)
  then show ?case
    by (cases xs) (force simp: farey_consecutive_mediant)+
qed auto


lemma fareys_consecutive: "farey_list_consecutive (fareys n)"
proof (induction n rule: fareys.induct)
  case 2
  then show ?case
    by (auto simp: farey_consecutive_def)
next
  case (3 n)
  then show ?case
    by (simp add: farey_list_consecutive_step)
qed auto


lemma monotone_fareys: "monotone (\<le>) subseq fareys"
proof
  fix m n :: nat
  assume "m \<le> n"
  have [intro]: "subseq xs (farey_step bd xs)" for xs bd
    by (induction bd xs rule: farey_step.induct) (auto intro: subseq_Cons')
  have "subseq (fareys (Suc m)) (fareys (Suc m + n))" for m n
    by (induction n) (auto intro: subseq_order.trans)
  moreover have "subseq (fareys 0) (fareys (Suc 0))"
    by simp
  ultimately show "subseq (fareys m) (fareys n)"
    using \<open>m \<le> n\<close>
    by (metis add.commute fareys.elims plus_1_eq_Suc subseq_order.lift_Suc_mono_le)
qed

lemma farey_step_increasing: "set xs \<subseteq> set (farey_step bd xs)"
  by (induction xs rule: farey_step.induct) auto

lemma fareys_Suc_increasing: "set (fareys n) \<subseteq> set (fareys (Suc n))"
  using farey_step_increasing by (cases n) auto

lemma fareys_mono: "m\<le>n \<Longrightarrow> set (fareys m) \<subseteq> set (fareys n)"
  by (meson fareys_Suc_increasing lift_Suc_mono_le)

lemma farey_step_eq_Nil_iff [simp]: "farey_step bd xs = [] \<longleftrightarrow> xs = []"
  by (induction bd xs rule: farey_step.induct) auto

lemma hd_farey_step [simp]: "hd (farey_step bd xs) = hd xs"
  by (induction bd xs rule: farey_step.induct) auto

lemma farey_consecutive_0_1 [simp, intro]: "farey_consecutive 0 1"
  by (auto simp: farey_consecutive_def)

lemma farey_consecutive_step:
  assumes "successively farey_consecutive xs"
  shows   "successively farey_consecutive (farey_step bd xs)"
  using assms
  by (induction bd xs rule: farey_step.induct)
     (auto simp: algebra_simps successively_Cons farey_consecutive_mediant)

lemma farey_consecutive_fareys: "successively farey_consecutive (fareys n)"
  by (induction n rule: fareys.induct) (auto intro: farey_consecutive_step)

lemma A: "x \<in> set (fareys n) \<Longrightarrow> denom_farey x \<le> n"
proof (induction n rule: fareys.induct)
  case 1
  then show ?case
    by (simp add: denom_farey_pos linorder_not_le)
next
  case 2
  then show ?case
    using denom_farey_le1_cases by fastforce
next
  case (3 n)
  with farey_step_denom_le show ?case
      by force
qed

(* Theorem 5.2 for integers*)
lemma mediant_lies_betw_int:
  fixes a b c d::int
  assumes "rat_of_int a / of_int b < of_int c / of_int d" "b>0" "d>0"
  shows "rat_of_int a / of_int b < (of_int a + of_int c) / (of_int b + of_int d)" 
        "(rat_of_int a + of_int c) / (of_int b + of_int d) < of_int c / of_int d"
    using assms by (simp_all add: field_split_simps)

(* Theorem 5.2 *)
theorem
  fixes x y::farey
  assumes "x < y"
  shows "x < mediant x y" "mediant x y < y"
  using assms mediant_lies_betw_int Fract_of_int_quotient quotient_of_denom_pos'
      quotient_of_div
  by (transfer, metis (no_types, lifting)  of_int_add prod.collapse)+

(* this result has a proof online: https://en.wikipedia.org/wiki/Bézout%27s_identity*)
lemma 
  fixes a b::int
  assumes "gcd a b = d" and a: "a\<noteq>0" "\<not> a dvd b" and b: "b\<noteq>0" "\<not> b dvd a"
  obtains x y where "a*x - b*y = 1" "abs x \<le> abs (b div d)" "abs y \<le> abs (a div d)"
  sorry

lemma coprime_consecutive_int:
  fixes a b::int
  assumes "coprime a b" "a>1" "b>1"
  obtains x y where "a*x - b*y = 1" "0 < x" "x < b" "0 < y" "y < a"
proof -
  obtain u v where 1: "a*u + b*v = 1"
    by (metis \<open>coprime a b\<close> cong_iff_lin coprime_iff_invertible_int)
  define k where "k \<equiv> u div b"
  define x where "x \<equiv> u - k*b"
  define y where "y \<equiv> -(v + k*a)"
  show thesis
  proof
    show *: "a*x - b*y = 1" 
      using 1 by (simp add: x_def y_def algebra_simps)
    have "u \<noteq> k*b" "b>0"
      using assms "*"  by (auto simp: k_def x_def y_def zmult_eq_neg1_iff) 
    moreover have "u - k*b \<ge> 0"
      by (simp add: k_def \<open>b>0\<close> minus_div_mult_eq_mod)
    ultimately show "x > 0"
      by (fastforce simp: x_def)
    show "x < b"
      by (simp add: \<open>0 < b\<close> k_def minus_div_mult_eq_mod x_def)
    have "a*x > 1"
      by (metis \<open>0 < x\<close> \<open>a>1\<close> int_one_le_iff_zero_less less_1_mult linorder_not_less
          mult.right_neutral nle_le)
    then have "\<not> b * y \<le> 0"
      using "*" by linarith
    then show "y > 0"
      by (simp add: \<open>0 < b\<close> mult_less_0_iff order_le_less)
    show "y < a"
      using "*" \<open>0 < x\<close> \<open>x < b\<close>
      by (smt (verit, best) \<open>a>1\<close> mult.commute mult_less_le_imp_less)
  qed
qed

lemma get_consecutive_parents:
  fixes m n::int
  assumes "coprime m n" "0<m" "m<n"
  obtains a b c d where "m = a+c" "n = b+d" "b*c - a*d = 1" "a\<ge>0" "b>0" "c>0" "d>0" "a<b" "c\<le>d"
proof (cases "m=1")
  case True
  show ?thesis
  proof
    show "m = 0 + 1" "n = 1 + (n-1)"
      by (auto simp: True)
  qed (use True \<open>m<n\<close> in auto)
next
  case False
  then obtain d c where *: "n*c - m*d = 1" "0 < d" "d < n" "0 < c" "c < m"
    using coprime_consecutive_int [of n m] coprime_commute assms by (smt (verit) coprime_commute)
  then have **: "n * (c - d) + (n - m) * d = 1"
    by (metis mult_diff_mult)
  show ?thesis
  proof
    show "c\<le>d"
      using * ** \<open>m<n\<close> by (smt (verit) mult_le_0_iff)
    show "(n-d) * c - (m-c) * d = 1"
      using * by (simp add: algebra_simps)
    with * \<open>m<n\<close> show "m-c < n-d"
      by (smt (verit, best) mult_mono)
  qed (use * in auto)
qed

(* probably not needed, but interesting nonetheless -- Manuel *)
lemma length_fareys_Suc: "length (fareys (Suc n)) = length (fareys n) + totient (Suc n)"
proof (induction n rule: fareys.induct)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case
    using less_Suc_eq_0_disj totient_less by force
next
  case (3 n)
  then show ?case
    apply (auto simp: )
    sorry
qed

lemma length_fareys: "length (fareys n) = 1 + (\<Sum>k=1..n. totient k)"
proof (induction n rule: fareys.induct)
  case (3 n)
  then show ?case 
    by (auto simp: length_fareys_Suc simp del: fareys.simps)
qed auto

(* Theorem 5.3 *)

theorem
  fixes a b c d::int
  assumes "b>0" 
    and "0 \<le> a/b"
    and "a/b < c/d"
    and "b*c - a*d = 1"
    and "max b d \<le> n" "n < b+d"
  shows 
(* Theorem 5.3 *)



theorem
  assumes "farey_consecutive x y"
  assumes "max (denom_farey x) (denom_farey y) \<le> n"
  assumes "n < denom_farey x + denom_farey y"
  assumes "z \<in> {x<..<y}"
  shows   "denom_farey z > n"
  using assms
  apply (simp add: farey_consecutive_def)
  apply transfer
  subgoal for x y n z
    apply (cases x; cases y; cases z)
    using quotient_of_denom_pos' [of x] quotient_of_denom_pos' [of y] quotient_of_denom_pos' [of z]
    apply  (auto simp: quotient_of_Fract normalize_def Let_def consecutive_imp_coprime algebra_simps)
    subgoal for a b c d e f

  done


  sorry


lemma B: "denom_farey x \<le> int n \<Longrightarrow> x \<in> set (fareys n)"
proof (induction n arbitrary: x rule: fareys.induct)
  case 1
  then show ?case
    by (metis denom_farey.rep_eq int_ops(1) less_le_not_le quotient_of_denom_pos')
next
  case 2
  then show ?case
    using denom_farey_le1_cases by fastforce
next
  case (3 n x)
  show ?case
  proof (cases "x \<in> set (fareys (Suc n))")
    case True
    then show ?thesis
      using fareys_Suc_increasing by blast
  next
    case False
    with 3 have denx: "denom_farey x = 2 + int n"
      by force
    have "x \<noteq> 0" "x \<noteq> 1"
      using "3.IH" False by auto
    then have "num_farey x > 0"
      by (metis num_farey_0_iff num_farey_nonneg order_le_less)
    then have "num_farey x < denom_farey x"
      using num_farey_le_denom[of x] \<open>x \<noteq> 1\<close>
      by (metis Farey.rat_of_farey div_self farey_num_denom_eq of_int_0_eq_iff one_farey.rep_eq order_le_less)
    then obtain a b c d 
      where *: "num_farey x = a+c" "denom_farey x = b+d" "b*c - a*d = 1" "a\<ge>0" "b>0" "c>0" "d>0" "a<b" "c\<le>d"
               and "coprime a b" and "coprime c d"
      by (metis \<open>0 < num_farey x\<close> coprime_num_denom_farey get_consecutive_parents consecutive_imp_both_coprime)
    with denx have **: "b \<le> Suc n" "d \<le> Suc n"
      by linarith+
    with \<open>a<b\<close> * have ab_in: "farey a b \<in> set (fareys (Suc n))"
      using "3.IH" \<open>coprime a b\<close> denom_farey_eq by presburger
    have cd_in: "farey c d \<in> set (fareys (Suc n))"
    proof (cases "c=d")
      case True
      with \<open>c>0\<close> have "farey c d = 1"
        by (simp add: farey_def one_farey.abs_eq one_le_Fract_iff)
      then show ?thesis
        by (simp add: "3.IH")
    next
      case False
      then show ?thesis
        using "*"(6,9) "**"(2) "3.IH" \<open>coprime c d\<close> by force
    qed
    have "c<d"
      sorry
    then have "x = mediant (farey a b) (farey c d)"
      using * ** \<open>coprime a b\<close> \<open>coprime c d\<close> coprime_num_denom_farey [of x]
      by (intro farey_eqI) (simp_all add: mediant_eq_farey less_imp_le)
    have "mediant (farey a b) (farey c d) \<in> set (fareys (Suc (Suc n)))"

    sorry
    show ?thesis
      using ab_in cd_in
      using "3"
      apply (auto simp: )
      sorry
  qed
qed

(*A half-proved reformulation of the result above*)
lemma
  assumes "denom_farey x \<le> n"
  shows "x \<in> set (fareys n)"
  using assms
proof (induction n rule: fareys.induct)
  case 1
  with denom_farey_pos[of x] show ?case
    by linarith
next
  case Suc: 2
  then show ?case
    using denom_farey_le1_cases by fastforce
next
  case SS: (3 n)
  then consider "denom_farey x \<le> int (Suc n)" | "denom_farey x = int (Suc (Suc n))"
    by linarith
  then show ?case
  proof cases
    case 1
    with SS show ?thesis
      apply (auto simp: )
      sorry
  next
    case 2
    then show ?thesis sorry
  qed
    sorry
qed




lemma num_mediant [simp]: 
  assumes xy: "x \<in> F" "y \<in> F" and "F = set (fareys n)"
  shows "num_farey (mediant x y) = num_farey x + num_farey y"
  using xy
  apply-
  apply transfer

   apply (auto simp: add_pos_pos quotient_of_Fract quotient_of_denom_pos')


proof -
  have "fst (quotient_of (Rat.Fract (fst (quotient_of x) + fst (quotient_of y))
                                    (snd (quotient_of x) + snd (quotient_of y)))) =
               fst (quotient_of x) + fst (quotient_of y)"
    if  x: "0 \<le> x" "x \<le> 1" and y: "0 \<le> y" "y \<le> 1" for x y::rat
  proof -
    have *: "coprime (fst (quotient_of x) + fst (quotient_of y)) (snd (quotient_of x) + snd (quotient_of y))" 
      if "0 < snd (quotient_of x) + snd (quotient_of y)"
      using that x y
      sorry
    show ?thesis
      using that * by (simp add: add_pos_pos quotient_of_Fract quotient_of_denom_pos')
  qed
  then show ?thesis by transfer auto
qed


lemma denom_mediant [simp]: "denom_farey (mediant x y) = denom_farey x + denom_farey y"
  apply transfer
  apply (simp add: Fract_of_int_quotient rat_divide_code split: prod.split)
  apply (auto simp: )
  apply (simp add: normalize_def rat_plus_code)
  apply (auto simp: Let_def rat_plus_code)
    apply (metis le_add_same_cancel2 less_le not_le quotient_of_nonzero(1))
   defer
   apply (meson add_pos_nonneg less_le quotient_of_nonzero(1))
  sorry

lemma mediant_inbetween:
  assumes "x < y"
  shows   "mediant x y \<in> {x<..<y}"
proof -
  define a b c d where "a = num_farey x" "b = denom_farey x" "c = num_farey y" "d = denom_farey y"
  have bd: "b > 0" "d > 0"
    unfolding a_b_c_d_def by auto
  note [simp] = a_b_c_d_def [symmetric]
  show ?thesis using bd assms
    by (auto simp: less_farey_iff rat_of_farey_conv_num_denom divide_simps)
       (auto simp: algebra_simps simp flip: of_int_mult)
qed

lemma denom_fareys_le:
  assumes "x \<in> set (fareys n)" "n > 0"
  shows   "denom_farey x \<le> n"
  sorry

lemma in_set_fareys:
  assumes "denom_farey x \<le> n"
  shows   "x \<in> set (fareys n)"
  sorry

(*NEEDS TO BE A THEOREM NOT A DEFINITION*)
fun fareys :: "nat \<Rightarrow> farey list" where
  "fareys 0 = []"
| "fareys (Suc 0) = [0, 1]"
| "fareys (Suc (Suc n)) = farey_step (Suc (Suc n)) (fareys (Suc n))"

end
