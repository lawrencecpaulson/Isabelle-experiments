theory Sup_Inf 
  imports Complex_Main

begin

context
  fixes f::"'a \<Rightarrow> 'b::{conditionally_complete_linorder,linordered_field}"
begin

lemma Sup_mult_eq:
  assumes "bdd_above (f ` A)" "A \<noteq> {}" "a \<ge> 0"
  shows  "(SUP x\<in>A. a * f x) = a * (SUP x\<in>A. f x)"
proof (cases "a=0")
  case False
  have bdd: "bdd_above ((\<lambda>x. a * f x) ` A)"
    using assms by (metis bdd_above.I2 bdd_above.unfold imageI mult_left_mono)
  show ?thesis 
  proof (rule antisym)
    show "(SUP x\<in>A. a * f x) \<le> a * Sup (f ` A)"
      using assms bdd by (auto simp add: cSup_le_iff cSup_upper mult_left_mono)
    have "\<And>x. x \<in> A \<Longrightarrow> f x \<le> (SUP x\<in>A. a * f x) / a"
      by (simp add: False assms bdd cSup_upper less_le mult_imp_le_div_pos)
    then have "Sup (f ` A) \<le> (SUP x\<in>A. a * f x) / a"
      using assms by (auto simp add: cSup_le_iff)
    with False assms show "a * Sup (f ` A) \<le> (SUP x\<in>A. a * f x)"
      by (auto simp: field_simps)
  qed 
qed (use assms in auto)

lemma Inf_mult_eq:
  assumes "bdd_below (f ` A)" "A \<noteq> {}" "a \<ge> 0"
  shows  "(INF x\<in>A. a * f x) = a * (INF x\<in>A. f x)"
proof (cases "a=0")
  case False
  have bdd: "bdd_below ((\<lambda>x. a * f x) ` A)"
    by (metis assms bdd_below.unfold bdd_belowI2 imageI mult_left_mono)
  show ?thesis 
  proof (rule antisym)
    show "a * Inf (f ` A) \<le> (INF x\<in>A. a * f x)"
      by (simp add: assms cINF_greatest cINF_lower2 ordered_comm_semiring_class.comm_mult_left_mono)
    have "\<And>x. x\<in>A \<Longrightarrow> (INF x\<in>A. a * f x) / a \<le> f x"
      by (metis (full_types) False \<open>a \<ge> 0\<close> bdd cINF_lower divide_le_eq less_le mult.commute)
    then have "(INF x\<in>A. a * f x)/a \<le> Inf (f ` A)"
      using assms by (auto simp add: le_cInf_iff)
    with False assms show "(INF x\<in>A. a * f x) \<le> a * Inf (f ` A)"
      by (auto simp: field_simps)
  qed 
qed (use assms in auto)

end

end
