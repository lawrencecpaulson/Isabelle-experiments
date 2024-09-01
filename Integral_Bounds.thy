theory Integral_Bounds
  imports "HOL-Analysis.Analysis"
begin

context ord begin

abbreviation antimono_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b :: ord) \<Rightarrow> bool"
  where "antimono_on A \<equiv> monotone_on A (\<le>) (\<ge>)"

end

lemma integrable_antimono_on:
  fixes f :: "real \<Rightarrow> real"
  assumes "antimono_on {a..b} f"
  shows "integrable (lebesgue_on {a..b}) f" 
proof -
  have "mono_on {a..b} (\<lambda>x. f x * (-1))"
    using assms by (simp add: monotone_on_def)
  then have "integrable (lebesgue_on {a..b}) (\<lambda>x. f x * (-1))"
    using integrable_mono_on by presburger
  then show ?thesis
    by simp
qed

lemma integrable_on_antimono_on:
  fixes f :: "real \<Rightarrow> real"
  assumes "antimono_on {a..b} f"
  shows "f integrable_on {a..b}"
  by (simp add: assms integrable_antimono_on integrable_on_lebesgue_on) 

lemma integral_const_le:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" and \<section>: "mono_on {a..b} f"
  shows "f a * (b-a) \<le> integral {a..b} f"
proof -
  have "integral {a..b} (\<lambda>x. f a) \<le> integral {a..b} f"
  proof (rule integral_le)
    show "f integrable_on {a..b}"
      using \<section> integrable_on_mono_on by blast
  qed (use assms in \<open>auto simp: monotone_on_def\<close>)
  then show ?thesis
    by (simp add: assms mult.commute)
qed

lemma integral_const_ge:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" and \<section>: "antimono_on {a..b} f"
  shows "f b * (b-a) \<le> integral {a..b} f"
proof -
  have "integral {a..b} (\<lambda>x. f b) \<le> integral {a..b} f"
  proof (rule integral_le)
    show "f integrable_on {a..b}"
      using \<section> integrable_on_antimono_on by blast
  qed (use assms in \<open>auto simp: monotone_on_def\<close>)
  then show ?thesis
    by (simp add: assms mult.commute)
qed


lemma sum_le_integral:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "n\<noteq>0" and ant: "antimono_on {a..b} f"
  shows "(\<Sum>i=1..n. f(a + (real i / real n) * (b-a))) * (b-a) / n \<le> integral {a..b} f"
proof -
  have "(\<Sum>i=1..k. f(a + (real i / real n) * (b-a))) * (b-a) / n \<le> integral {a .. a + (real k / real n) * (b-a)} f" 
    if "k \<le> n" for k
    using that
  proof (induction k)
    case 0
    then show ?case
      by auto
  next
    case (Suc k)
    then obtain j where j: "n = Suc (j+k)"
      by (metis Suc_le_eq add.commute less_imp_Suc_add)
    have "(\<Sum>i = 1..Suc k. f (a + real i / real n * (b - a))) * (b - a) / real n
         = (\<Sum>i = 1..k. f (a + real i / real n * (b - a))) * (b - a) / real n + 
           f (a + real (Suc k) / real n * (b - a)) * (b - a) / real n"
      by (simp add: field_split_simps)
    also have "\<dots> \<le> integral {a .. a + (real k / real n) * (b-a)} f + 
                 f (a + real (Suc k) / real n * (b - a)) * (b - a) / real n"
      using Suc by simp
    also have "\<dots> \<le> integral {a .. a + (real k / real n) * (b-a)} f + 
                 integral {a + (real k / real n) * (b-a) .. a + (Suc k / real n) * (b-a)} 
                          (\<lambda>x. f (a + real (Suc k) / real n * (b - a)))"
      using \<open>a \<le> b\<close> by (simp add: field_split_simps)
    also have "\<dots> \<le> integral {a .. a + (real k / real n) * (b-a)} f + 
                 integral {a + (real k / real n) * (b-a) .. a + (Suc k / real n) * (b-a)} f"
      using \<open>a \<le> b\<close> \<open>n \<noteq> 0\<close> 
      apply (clarsimp simp add: j)
      apply (rule order_trans [OF _ integral_const_ge])
        apply (auto simp: field_split_simps)
       apply (rule monotone_on_subset [OF ant])
      apply (auto simp: field_split_simps mult_right_mono)
      done
    also have "\<dots> = integral {a..a + real (Suc k) / real n * (b - a)} f"
    proof (rule Henstock_Kurzweil_Integration.integral_combine)
      have "{a..a + real (Suc k) / real n * (b - a)} \<subseteq> {a..b}"
        using \<open>a \<le> b\<close> by (auto simp: field_split_simps mult_right_mono j)
      then show "f integrable_on {a..a + real (Suc k) / real n * (b - a)}"
        by (intro integrable_on_antimono_on monotone_on_subset [OF ant])
      show "a \<le> a + real k / real n * (b - a)""a + real k / real n * (b - a) \<le> a + real (Suc k) / real n * (b - a)"
        using \<open>a \<le> b\<close> by (auto simp: field_split_simps add_mono mult_right_mono j)
    qed
    finally show ?case .
  qed
  then show ?thesis
    using \<open>n\<noteq>0\<close> by force
qed

end
