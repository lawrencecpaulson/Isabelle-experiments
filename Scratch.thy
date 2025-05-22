theory Scratch

imports "HOL-Library.Multiset"

begin

instantiation list :: (type) minus
begin

definition "minus_list xs ys \<equiv> foldr remove1 ys xs"

instance ..

end

lemma minus_Nil [simp]: "xs - [] = xs"
  by (simp add: minus_list_def)

lemma minus_Cons [simp]: "xs - (y#ys) = remove1 y (xs - ys)"
  by (simp add: minus_list_def)

lemma minus_Cons_alt: "xs - (y#ys) = remove1 y xs - ys"
  by (induction ys) (auto simp add: remove1_commute)

lemma minus_Nil_left [simp]: "[] - xs = []"
  by (induction xs) auto

lemma minus_Cons_left: "(x#xs) - ys = (if x \<in> set ys then xs - (remove1 x ys) else x # (xs - ys))"
proof (induction ys)
  case Nil
  then show ?case by simp
next
  case (Cons a ys)
  then show ?case
    by (metis in_set_remove1 list.set_intros(1) minus_Cons minus_Cons_alt
        remove1.simps(2))
qed

lemma mset_minus: "mset (xs - ys) = mset xs - mset ys"
  by (induction ys) auto

lemma "xs - (as@xs) = []"
proof -
  have "mset (xs - (as@xs)) = {#}"
    by (simp add: mset_minus)
  then show ?thesis
    by simp
qed

lemma minus_list_Nil: "xs - xs = []"
  by (metis Multiset.diff_cancel mset_minus mset_zero_iff)

