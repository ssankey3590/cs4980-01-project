theory IMO2023_Problem4
  imports Complex_Main
begin

(* Define a sequence of positive real numbers *)
type_synonym real_sequence = "nat \<Rightarrow> real"

locale sequence =
  fixes x ::"real_sequence"
  fixes n :: "nat"
  assumes "n \<ge> 1"
  assumes "satisfies_condition x n"
  assumes positive: "\<forall>n. x n > 0"
  assumes distinct: "\<forall>m n. m \<noteq> n \<longrightarrow> x m \<noteq> x n"



(* Define the function a_n *)
fun a_n :: "real_sequence \<Rightarrow> nat \<Rightarrow> real" where
  "a_n x n = sqrt ((\<Sum>i = 1..n. x i) * (\<Sum>i = 1..n. 1 / x i))"

definition is_integer :: "real \<Rightarrow> bool" where
  "is_integer r \<longleftrightarrow> (\<exists>k::int. r = real_of_int k)"

definition satisfies_condition :: "real_sequence \<Rightarrow> nat \<Rightarrow> bool" where
  "satisfies_condition x n \<longleftrightarrow> (\<forall>i. 1 \<le> i \<and> i \<le> n \<longrightarrow> is_integer (a_n x i))"

context sequence
begin
lemma a_n_helper:
  shows "a x 2  > 2"
  using sequence_axioms sequence_def by auto

(* Prove the inequality a_(n+2) \<ge> a_n + 3 *)
lemma a_n_inequality:
  assumes "satisfies_condition x n"
  shows "a_n x (n+2) \<ge> (a_n x n) + 3"
  by (meson a_n_helper not_numeral_less_zero)

(* Prove the induction step *)
lemma induction_step:
  fixes k ::"nat"
  assumes "a_n x 1 = 1"
  shows "\<forall>k. a_n x (2*k + 1) \<ge> 3*k + (a_n x 1)"
proof(induct k)
  case 0
  then show ?case 
  proof(rule ccontr)
    assume "\<not> (\<forall>k. 3 * real k + a_n x 1 \<le> a_n x (2 * k + 1))"
    obtain k where k_prop: "3 * real k + a_n x 1 > a_n x (2 * k + 1)"
      by (smt (verit) \<open>\<not> (\<forall>k. 3 * real k + a_n x 1 \<le> a_n x (2 * k + 1))\<close>) 
    have h1: "3 * real k + a_n x 1 \<le> a_n x (2 * k + 1) \<Longrightarrow> False"
      using k_prop by force
    have h2: "3 * real k + a_n x 1 \<le> a_n x (2 * k + 1)" 
    proof(induct k)
      case 0
      then show ?case
        by simp 
    next
      case (Suc k)
      then show ?case
        by (meson a_n_helper linorder_not_le one_le_numeral)
    qed
    show False using k_prop h2 by auto
  qed
next
  case (Suc k)
  then show ?case
    by auto 
qed
  

(* Final conclusion *)
theorem a_2023_geq_3034:
  assumes "a_n x 1 = 1"
  shows "a_n x 2023 \<ge> 3034"
proof-
  have h1: "a_n x 1 = 1" using assms by auto
  have h2: "a_n x 2023 \<ge> 3034"
    by (smt (verit) h1 induction_step mult_2 numeral_Bit0 numeral_Bit1 numerals(1) of_nat_1 of_nat_numeral)
  show ?thesis using h2 by auto
qed
end

end