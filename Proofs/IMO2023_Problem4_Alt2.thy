theory IMO2023_Problem4_Alt2
imports Complex_Main
begin

(* Define a sequence of positive real numbers *)
type_synonym real_sequence = "nat \<Rightarrow> real"

(* Define the function a_n *)
fun a_n :: "real_sequence \<Rightarrow> real_sequence" where
  "a_n x n = sqrt ((\<Sum>i = 1..n. x i) * (\<Sum>i = 1..n. 1 / x i))"


(* Helper lemmas for arithmetic *)
lemma sqrt_sum_positive:
  assumes "x > 0" "y > 0"
  shows "sqrt(x + y) > 0"
  using assms(1) assms(2) by auto

lemma distinct_sum_reciprocal_inequality:
  fixes x1 x2 :: real
  assumes "x1 > 0" "x2 > 0" "x1 \<noteq> x2"
  shows "(x1 + x2) * (1/x1 + 1/x2) > 4"
proof -
  have "(x1 + x2) * (1/x1 + 1/x2) = 2 + (x1/x2 + x2/x1)"
    by (smt (verit, del_insts) add_divide_distrib assms(1) assms(2) distrib_left div_by_1 divide_divide_eq_right divide_self_if times_divide_eq_right)
  also have "x1/x2 + x2/x1 \<ge> 2"
  proof -
    have "0 \<le> (sqrt(x1/x2) - sqrt(x2/x1))^2"
      by simp
    hence "0 \<le> x1/x2 + x2/x1 - 2"
      by (smt (verit, best) assms(1) assms(2) diff_divide_distrib divide_self_if ln_diff_le)
    thus ?thesis
      by simp
  qed
  then have "x1/x2 + x2/x1 > 2"
    using assms
  proof -
    have f1: "\<not> x1 \<le> x2 \<or> \<not> x2 \<le> x1"
      using assms(3) by auto
    have f2: "0 < x2 \<and> 0 < x1"
      using assms(1) assms(2) by fastforce
    have f3: "0 < x1 \<and> 0 < x2"
      using assms(1) assms(2) by force
    have f4: "0 < x1 - x2 \<and> 0 < x2 \<or> \<not> 0 < x1 - x2"
      using assms(2) by presburger
    have f5: "0 < x1 - x2 \<and> 0 < x2 \<longrightarrow> 0 < (x1 - x2) / x2"
      using divide_pos_pos by blast
    have f6: "0 < x2 - x1 \<and> 0 < x1 \<longrightarrow> 0 < (x2 - x1) / x1"
      using divide_pos_pos by blast
    have f7: "0 < x1 - x2 \<and> 0 < x2 \<longrightarrow> ln (x1 - x2) - ln x2 = ln ((x1 - x2) / x2)"
      by (simp add: ln_div)
    have f8: "0 < x2 - x1 \<and> 0 < x1 \<longrightarrow> ln (x2 - x1) - ln x1 = ln ((x2 - x1) / x1)"
      by (simp add: ln_div)
    have f9: "(x1 - x2 - x1) / x2 = (x1 - x2) / x2 - x1 / x2"
      using diff_divide_distrib by blast
    have f10: "(x2 - (x2 - x1)) / x1 = x2 / x1 - (x2 - x1) / x1"
      using diff_divide_distrib by blast
    have f11: "(x1 - x2) / x2 = x1 / x2 - x2 / x2"
      by (simp add: diff_divide_distrib)
    have f12: "(x2 - x1) / x1 = x2 / x1 - x1 / x1"
      by (simp add: diff_divide_distrib)
    have f13: "0 < x2 / x2"
      using assms(2) divide_pos_pos by blast
    have f14: "0 < x1 / x1"
      using assms(1) by force
    have f15: "0 < - (x2 - x1) \<and> 0 < x1 \<longrightarrow> ln (- (x2 - x1)) - ln x1 = ln (- (x2 - x1) / x1)"
      by (simp add: ln_div)
    have f16: "x2 - x1 \<noteq> - (x1 - x2) \<or> - (x1 - x2) / x2 = (x2 - x1) / x2"
      by argo
    have f17: "(x1 - x2) / x2 \<noteq> - (x2 - x1) / x1 \<or> ln ((x1 - x2) / x2) = ln (- (x2 - x1) / x1)"
      by presburger
    have f18: "0 = 0 / x2"
      by auto
    have f19: "0 = 0 / x1"
      by simp
    have f20: "(x2 - x1) / x1 = (x2 - x1) / x1 - 0 / x1"
      by auto
    have f21: "0 / x1 - (x2 - x1) / x1 = - (x2 - x1) / x1"
      by linarith
    have f22: "0 / x2 - (x1 - x2) / x2 = - (x1 - x2) / x2"
      by (simp add: diff_divide_distrib)
    have f23: "(x1 - x2) / x2 = 0 / x2 - - (x1 - x2) / x2"
      by (simp add: diff_divide_distrib)
    have "0 = ln (x2 / x2)"
      using assms(2) by force
    then show ?thesis
      using f23 f22 f21 f20 f19 f18 f17 f16 f15 f14 f13 f12 f11 f10 f9 f8 f7 f6 f5 f4 f3 f2 f1 by (smt (z3) assms(1) assms(2) ln_diff_le ln_div ln_le_minus_one)
  qed
  ultimately show ?thesis
    by auto
qed

(* Cauchy-Schwarz inequality for n=2 *)
lemma cauchy_schwarz_n2:
  assumes "x1 > 0" "x2 > 0" "x1 \<noteq> x2"
  shows "sqrt((x1 + x2) * (1/x1 + 1/x2)) > 2"
proof -
  have "x1 > 0 \<and> x2 > 0" using assms by simp
  hence "(x1 + x2) * (1/x1 + 1/x2) > 4"
  proof -
    have "(x1 + x2) * (1/x1 + 1/x2) = 2 + ((x1/x2) + (x2/x1))"
      using assms by (auto simp: field_simps)
    moreover have "(x1/x2) + (x2/x1) > 2"
      using assms calculation distinct_sum_reciprocal_inequality by fastforce
    ultimately show ?thesis by auto
  qed
  thus ?thesis
    by (metis real_sqrt_four real_sqrt_less_iff)
qed



(* Now let's prove the main sequence property *)

lemma sequence_growth:
  fixes a :: "nat \<Rightarrow> real"
  assumes "\<forall>n. a_n a n > 0"
  assumes "\<forall>n. a_n a n = real_of_int \<lfloor>a_n a n\<rfloor>"
  assumes "\<forall>n. (a_n a (n+2))^2 \<ge> (a_n a n + 2)^2"
  shows "\<forall>n. a_n a (n+2) \<ge> ( a_n a n) + 3"
proof
  fix n
  have "(a_n a (n+2))^2 \<ge> (a_n a n + 2)^2"
    using assms(3) by simp
  moreover have "a_n a (n+2) > 0"
    using assms(1) by blast
  ultimately have "a_n a (n+2) \<ge> a_n a n + 2"
    by (smt (verit, ccfv_SIG) power2_le_imp_le)
  moreover have "a_n a (n+2) = real_of_int \<lfloor>a_n a (n+2)\<rfloor>"
    by (meson assms(2))
  ultimately show "a_n a (n+2) \<ge> (a_n a n) + 3"
    sorry
qed

(* Final induction step *)

lemma intermediate_bound:
  fixes a :: "nat \<Rightarrow> real"
  assumes "\<forall>n. a_n a n > 0"
  assumes "\<forall>n. a_n a n = real_of_int \<lfloor>a_n a n\<rfloor>"
  assumes "\<forall>n. a_n a (n+2) \<ge> a_n a n + 3"
  assumes "a_n a 1 = 1"
  shows "\<forall>k. a_n  a (2*k + 1) \<ge> 3*k + 1"
  proof (induction rule: nat_induct)
    case 0
    then show ?case 
    proof(rule ccontr)
      assume a0: "\<not> (\<forall>k. real (3 * k + 0) \<le> a_n a (2 * k + 0))"
      obtain y where y_prop: "real (3 * y + 0) > a_n a (2 * y + 0)"
        using a0 linorder_not_le by blast
      have f0: "a_n a (2 * y + 0) \<ge> real (3 * y + 0)" 
      proof(induct y)
        case 0
        then show ?case
          by simp 
      next
        case (Suc y)
        then show ?case
          by (smt (verit) add.right_neutral add_2_eq_Suc add_2_eq_Suc' assms(3) mult_Suc_right numeral_3_eq_3 of_nat_Suc of_nat_add)
      qed
      show False
        using f0 y_prop by linarith
    qed
  next
    case (Suc k)
    show ?case 
    proof-
      have t1: "a_n a (2*(Suc k) + 1) = a_n a (2*k + 3)"
      by (metis One_nat_def Suc_eq_plus1 add_2_eq_Suc add_Suc_right mult_Suc_right numeral_3_eq_3)
      also have t2: "... \<ge> a_n a (2*k + 1) + 3"
        by (metis One_nat_def Suc_1 ab_semigroup_add_class.add_ac(1) assms(3) numeral_3_eq_3 plus_1_eq_Suc)
      also have t3: "... \<ge> 3*k + 1 + 3"
      proof(rule ccontr)
        assume a1: "\<not> (real (3 * k + 1 + 3) \<le> a_n a (2 * k + 3))"
        obtain x where x_prop: "real (3 * x + 1 + 3) > a_n a (2 * x + 3)"
          using a1 linorder_not_le by blast
        have f1: "a_n a (2 * x + 3) \<ge> real (3 * x + 1 + 3)" 
          proof(induct x)
            case 0
            then show ?case
              by (metis add_Suc_right assms(3) assms(4) group_cancel.rule0 mult_is_0 of_nat_Suc of_nat_eq_1_iff one_add_one one_plus_numeral plus_1_eq_Suc semiring_norm(3))
          next
            case (Suc x)
            then show ?case
              by (smt (verit) One_nat_def add.commute add_2_eq_Suc' add_Suc_right assms(3) mult_Suc_right numeral_3_eq_3 of_nat_1 of_nat_add plus_1_eq_Suc)
          qed
        show False
          using f1 x_prop by argo 
      qed
      have t4: "real (Suc k) \<le> a_n a (Suc k)" 
      proof(rule ccontr)
        assume ta4: "\<not> real (Suc k) \<le> a_n a (Suc k)"
        have t4a: "real (Suc k) > a_n a (Suc k)" using ta4 by linarith
        have t4b: "a_n a (2*(Suc k) + 1) \<ge> 3*k + 4"
          using t1 t3 by linarith
        show False sorry
      qed
      show ?thesis 
      proof(rule ccontr)
        assume a3: "\<not> (\<forall>ka. real (3 * ka + Suc k) \<le> a_n a (2 * ka + Suc k))"
        obtain z where z_prop: "real (3 * z + Suc k) > a_n a (2 * z + Suc k)"
          using a3 linorder_not_le by blast
        have f2: "real (3 * z + Suc k) \<le> a_n a (2 * z + Suc k)" 
        proof(induct z)
          case 0
          then show ?case 
          proof(rule ccontr)
            assume a4: "\<not> real (3 * 0 + Suc k) \<le> a_n a (2 * 0 + Suc k)"
            have h1a: "real (Suc k) > a_n a (Suc k)"
              using a4 add_0 linorder_not_le mult_zero_right by auto 
            have h2a: "real (Suc k) \<le> a_n a (Suc k)" using t1 t2 t3 sorry
            show False
              using h1a h2a by linarith 
          qed
        next
          case (Suc z)
          then show ?case
            by (smt (verit, ccfv_SIG) One_nat_def add.commute add_2_eq_Suc' add_Suc_right assms(3) mult_Suc_right numeral_3_eq_3 of_nat_Suc plus_1_eq_Suc)
        qed
        show False using f2 z_prop by argo
      qed
    qed
  qed

lemma final_bound:
  fixes a :: "nat \<Rightarrow> real"
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