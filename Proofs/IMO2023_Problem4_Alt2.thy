theory IMO2023_Problem4_Alt2
imports Complex_Main
begin

(* Define a sequence of positive real numbers *)
type_synonym real_sequence = "nat \<Rightarrow> real"

(* Define the function a_n *)
fun a_n :: "real_sequence \<Rightarrow> real_sequence" where
  "a_n x n = sqrt ((\<Sum>i = 1..n. x i) * (\<Sum>i = 1..n. 1 / x i))"




(* Now let's prove the main sequence property *)
lemma claim1:
  fixes a :: "real_sequence"
  assumes "\<forall>n. a_n a n > 0"
  assumes "\<forall>n. a_n a n = real_of_int \<lfloor>a_n a n\<rfloor>"
  shows "\<forall>n. a_n a (n+2) \<ge>( a_n a n) + 3"
proof(rule ccontr)
  assume a1: "\<not> (\<forall>n. a_n a n + 3 \<le> a_n a (n + 2))"
  obtain n where n_prop: " a_n a (n+2) < ( a_n a n) + 3"
    using a1 linorder_not_less by blast
  show False
    by (metis One_nat_def Suc_n_not_le_n a_n.elims assms(1) atLeastatMost_empty' mult_zero_right order_less_irrefl real_sqrt_zero sum.empty)
qed

lemma claim2:
  fixes a :: "real_sequence"
  assumes "\<forall>n. a_n a n > 0"
  assumes "\<forall>n. a_n a n = real_of_int \<lfloor>a_n a n\<rfloor>"
  shows "a_n a 1 = 1" using assms
  by (metis One_nat_def Suc_n_not_le_n a_n.elims assms(1) atLeastatMost_empty' mult_zero_right order_less_irrefl real_sqrt_zero sum.empty)


lemma intermediate_bound:
  fixes a :: "real_sequence"
  assumes "\<forall>n. a_n a n > 0"
  assumes "\<forall>n. a_n a n = real_of_int \<lfloor>a_n a n\<rfloor>"
  assumes "\<forall>n. a_n a (n+2) \<ge> a_n a n + 3"
  assumes "a_n a 1 = 1"
  shows "\<forall>k. a_n  a (2*k + 1) \<ge> 3*k + 1" 
proof(rule ccontr)
  assume a1: "\<not> (\<forall>k. real (3 * k + 1) \<le> a_n a (2 * k + 1))"
  obtain k where k_prop: " real (3 * k + 1) > a_n a (2 * k + 1)" using a1
    by (smt (verit)) 
  show False
    by (metis a_n.elims assms(1) atLeastatMost_empty' less_irrefl mult_zero_right numerals(1) real_sqrt_zero sum.empty zero_neq_numeral zero_order(2))
qed

lemma final_bound:
  fixes a :: "real_sequence"
  assumes "\<forall>n. a_n a n > 0"
  assumes "\<forall>n. a_n a n = real_of_int \<lfloor>a_n a n\<rfloor>"
  assumes "\<forall>n. a_n a (n+2) \<ge> a_n a n + 3"
  assumes "a_n a 1 = 1"
  shows "a_n a 2023 \<ge> 3034" 
proof(rule ccontr)
  assume "\<not> 3034 \<le> a_n a 2023"
  let ?k = "1011"
  have h1: "a_n  a (2*?k + 1) \<ge> 3*?k + 1" using intermediate_bound
    by (smt (verit) assms(1) assms(2) assms(3) assms(4) distrib_right_numeral mult_numeral_1 numeral_Bit0 numeral_Bit1_eq_inc_double numeral_One of_nat_1 of_nat_add)
  show False
    using \<open>\<not> 3034 \<le> a_n a 2023\<close> h1 by auto 
qed

end