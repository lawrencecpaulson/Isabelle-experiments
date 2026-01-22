theory Scratch

imports "HOL-Library.Multiset"

begin


fun decimalDigits :: "nat \<Rightarrow> nat list" where
  "decimalDigits n = (if n\<le>0 then [] else n mod 10 # decimalDigits (n div 10))"

value "(2::int)^31"

value "decimalDigits (2^29)"

  oops

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

lemma append_minus_cancel: "(xs@ys) - (xs@zs) = ys - zs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (metis append_Cons minus_Cons_alt remove1.simps(2))
qed

lemma "(xs@ys) - xs = ys"
  by (metis append_minus_cancel append_Nil2 minus_Nil)

instantiation list :: (type) monoid_diff
begin

lemma  "(xs@ys) - zs = (xs-zs) @ (ys - (zs-xs))"



value "[1..400] - [350..400] "

lemma "[1..100] - [50..100] = [1..49]"
  by (simp add: upto.simps)

end
