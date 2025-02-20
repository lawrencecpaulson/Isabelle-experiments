theory Farey
  imports Complex_Main "HOL-Number_Theory.Totient" "HOL-Library.Sublist"
    "HOL-ex.Sketch_and_Explore"
begin

(*MOVE*)
lemma quotient_of_rat_of_int [simp]: "quotient_of (rat_of_int i) = (i, 1)"
  using Rat.of_int_def quotient_of_int by force

thm int_div_less_self
lemma int_div_le_self: 
  \<open>x div k \<le> x\<close> if \<open>0 < x\<close>  for x k :: int
  by (metis div_by_1 int_div_less_self less_le_not_le nle_le nonneg1_imp_zdiv_pos_iff order.trans that)

section \<open>Farey Fractions\<close>

typedef farey = "{0..1} :: rat set"
  morphisms rat_of_farey farey_of_rat
  by auto

setup_lifting type_definition_farey

lift_definition num_farey :: "farey \<Rightarrow> int" is "\<lambda>x. fst (quotient_of x)" .
lift_definition denom_farey :: "farey \<Rightarrow> int" is "\<lambda>x. snd (quotient_of x)" .

lift_definition farey :: "[int,int] \<Rightarrow> farey" is "\<lambda>a b. max 0 (min 1 (Fract a b))"
  by simp 

lemma num_farey_nonneg: "num_farey x \<ge> 0"
proof (transfer, goal_cases)
  case (1 x)
  show ?case
    by (cases x) (use 1 in \<open>auto simp: quotient_of_Fract Rat.zero_le_Fract_iff\<close>)
qed

lemma num_farey_le_denom: "num_farey x \<le> denom_farey x"
proof (transfer, goal_cases)
  case (1 x)
  show ?case
    by (cases x) (use 1 in \<open>auto simp: quotient_of_Fract Rat.Fract_le_one_iff\<close>)
qed

lemma denom_farey_pos: "denom_farey x > 0"
proof -
  have "\<And>x. x \<in> {0..1} \<Longrightarrow> 0 < snd (quotient_of x)"
    using quotient_of_denom_pos' by blast
  then show ?thesis
    using denom_farey.rep_eq quotient_of_denom_pos' by force
qed

lemma coprime_num_denom_farey [intro]: "coprime (num_farey x) (denom_farey x)"
  by (simp add: denom_farey.rep_eq num_farey.rep_eq quotient_of_coprime)

lemma rat_of_farey_conv_num_denom:
  "rat_of_farey x = rat_of_int (num_farey x) / rat_of_int (denom_farey x)"
  by (simp add: Rat.of_int_def denom_farey.rep_eq num_farey.rep_eq quotient_of_div
      surjective_pairing)

lemma num_denom_farey_eqI:
  assumes "rat_of_farey x = of_int a / of_int b" "b > 0" "coprime a b"
  shows   "num_farey x = a" "denom_farey x = b"
proof -
  have "num_farey x = a \<and> denom_farey x = b"
    using Fract_of_int_quotient assms denom_farey.rep_eq num_farey.rep_eq quotient_of_Fract by auto
  thus "num_farey x = a" "denom_farey x = b" by blast+
qed

lemma farey_cases [cases type, case_names farey]:
  fixes x :: farey
  obtains a b where "0\<le>a" "a\<le>b" "coprime a b" "rat_of_farey x = of_int a / of_int b"
  using denom_farey_pos num_farey_le_denom num_farey_nonneg rat_of_farey_conv_num_denom by blast

lemma rat_of_farey: "rat_of_farey x = of_int a / of_int b \<Longrightarrow> x = farey a b"
  by transfer (simp add: Fract_of_int_quotient)

lemma farey_num_denom_eq [simp]: "farey (num_farey x) (denom_farey x) = x"
  using rat_of_farey rat_of_farey_conv_num_denom by fastforce


instantiation farey :: zero
begin
lift_definition zero_farey :: farey is "0 :: rat"
  by auto
instance ..
end

instantiation farey :: one
begin
lift_definition one_farey :: farey is "1 :: rat"
  by auto
instance ..
end 

instantiation farey :: linorder
begin
lift_definition less_eq_farey :: "farey \<Rightarrow> farey \<Rightarrow> bool" is "(\<le>) :: rat \<Rightarrow> _" .
lift_definition less_farey :: "farey \<Rightarrow> farey \<Rightarrow> bool" is "(<) :: rat \<Rightarrow> _" .
instance
  by standard (transfer; linarith; fail)+
end

lemma num_farey_0 [simp]: "num_farey 0 = 0"
  and denom_farey_0 [simp]: "denom_farey 0 = 1"
  and num_farey_1 [simp]: "num_farey 1 = 1"
  and denom_farey_1 [simp]: "denom_farey 1 = 1"
  by (transfer; simp; fail)+

lemma num_farey_0_iff [simp]: "num_farey x = 0 \<longleftrightarrow> x = 0"
  by transfer (metis Rat_cases fst_conv normalize_stable quotient_of_Fract rat_number_collapse(1) rat_zero_code)

lemma le_farey_iff: "x \<le> y \<longleftrightarrow> rat_of_farey x \<le> rat_of_farey y"
  by (simp add: less_eq_farey.rep_eq)

lemma less_farey_iff: "x < y \<longleftrightarrow> rat_of_farey x < rat_of_farey y"
  by transfer auto

lemma denom_farey_le1_cases:
  assumes "denom_farey x \<le> 1"
  shows "x = 0 \<or> x = 1"
proof -
  consider "num_farey x = 0" | "num_farey x = 1" "denom_farey x = 1"
    using assms num_farey_le_denom [of x] num_farey_nonneg [of x] by linarith
  then show ?thesis
    by (metis denom_farey_1 farey_num_denom_eq num_farey_0_iff num_farey_1)
qed

lift_definition mediant :: "farey \<Rightarrow> farey \<Rightarrow> farey" is 
  "\<lambda>x y. Rat.Fract (fst (quotient_of x) + fst (quotient_of y)) 
                   (snd (quotient_of x) + snd (quotient_of y))"
proof goal_cases
  case (1 x y)
  show ?case
    by (cases x; cases y; use 1 Fract_of_int_quotient quotient_of_Fract zero_le_Fract_iff in simp)
qed

lemma rat_of_mediant:
  "rat_of_farey (mediant x y) = of_int (num_farey x + num_farey y) / of_int (denom_farey x + denom_farey y)"
  by transfer (simp add: Fract_of_int_quotient rat_divide_code)

lemma mediant_eq: "mediant x y = farey (num_farey x + num_farey y) (denom_farey x + denom_farey y)"
  by (simp add: Farey.rat_of_farey rat_of_mediant)

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
  by (auto simp: farey_consecutive_def less_farey_iff rat_less_code 
                 rat_of_farey_conv_num_denom rat_divide_code coprime_num_denom_farey denom_farey_pos)

fun farey_step :: "nat \<Rightarrow> farey list \<Rightarrow> farey list" where
  "farey_step bd [] = []"
| "farey_step bd [x] = [x]"
| "farey_step bd (x # y # xs) =
     (if denom_farey x + denom_farey y \<le> bd
      then x # mediant x y # farey_step bd (y # xs)
      else x # farey_step bd (y # xs))"

fun fareys :: "nat \<Rightarrow> farey list" where
  "fareys 0 = []"
| "fareys (Suc 0) = [0, 1]"
| "fareys (Suc (Suc n)) = farey_step (Suc (Suc n)) (fareys (Suc n))"

lemma denom_mediant: "denom_farey (mediant x y) \<le> denom_farey x + denom_farey y"
  apply transfer
  subgoal for x y
    using quotient_of_denom_pos' [of x] quotient_of_denom_pos' [of y]
    by (simp add: quotient_of_Fract normalize_def Let_def int_div_le_self split: if_splits)
  done

lemma farey_step_denom_le:
  assumes "x \<in> set (farey_step bd xs)" "x \<notin> set xs"
  shows "denom_farey x \<le> bd"
  using assms
proof (induction xs rule: farey_step.induct)
  case (3 bd x y xs)
  then show ?case
    using denom_mediant by (auto intro: order.trans split: if_splits)
qed auto

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

lemma mediant_1: 
  assumes "farey_consecutive x y"
  shows "farey_consecutive x (mediant x y)"
  using assms
  apply (clarsimp simp: farey_consecutive_def)
  apply transfer
  subgoal for x y
    using quotient_of_denom_pos' [of x] quotient_of_denom_pos' [of y]
    by (auto simp: quotient_of_Fract normalize_def Let_def consecutive_imp_coprime algebra_simps)
  done

lemma mediant_2: 
  assumes "farey_consecutive x y"
  shows "farey_consecutive (mediant x y) y"
  using assms
  apply (clarsimp simp: farey_consecutive_def)
  apply transfer
  subgoal for x y
    using quotient_of_denom_pos' [of x] quotient_of_denom_pos' [of y]
    by (auto simp: quotient_of_Fract normalize_def Let_def consecutive_imp_coprime algebra_simps)
  done

(* Theorem 5.4 *)
lemmas farey_consecutive_mediant = mediant_1 mediant_2

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
    with 3 have "denom_farey x = 2 + int n"
      by force
    then show ?thesis
      using "3"
      apply (auto simp: )
apply (auto simp: farey_step)
      sorry
  qed
qed


lemma farey_step_eq_Nil_iff [simp]: "farey_step bd xs = [] \<longleftrightarrow> xs = []"
  by (induction bd xs rule: farey_step.induct) auto

lemma hd_farey_step [simp]: "hd (farey_step bd xs) = hd xs"
  by (induction bd xs rule: farey_step.induct) auto

lemma farey_consecutive_0_1 [simp, intro]: "farey_consecutive 0 1"
  by (auto simp: farey_consecutive_def)

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

(* Theorem 5.3 *)

theorem
  fixes a b c d::int
  assumes "b>0" 
    and "0 \<le> a/b"
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
  


lemma farey_consecutive_step:
  assumes "successively farey_consecutive xs"
  shows   "successively farey_consecutive (farey_step bd xs)"
  using assms
  by (induction bd xs rule: farey_step.induct)
     (auto simp: algebra_simps successively_Cons farey_consecutive_mediant)

lemma farey_consecutive_fareys: "successively farey_consecutive (fareys n)"
  by (induction n rule: fareys.induct) (auto intro: farey_consecutive_step)

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

end
