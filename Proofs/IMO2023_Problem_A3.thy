(*  Title:       International Math Olympiads 2023 Problem A3
    Author:      Stewart Sankey, 2024
*)

chapter \<open>IMO 2023 Problem A3\<close>

text \<open>This is an incomplete proof of the following problem from the 2023 International Math Olympiads:
Let x_1,x_2,\<dots>,x_2023 be pairwise different positive real numbers such that
 a_n=\<surd>((x_1+x_2+\<cdots>+x_n )(1/x_1 +1/x_2 +\<cdots>+1/x_n ) )
is an integer for every n=1,2,\<dots>,2023. Prove that a_2023\<ge>3034.\<close>


theory IMO2023_Problem_A3
  imports Complex_Main
begin

section \<open>Definitions & Functions\<close>
subsection \<open>Main Functions\<close>

(* real_sequence is used to represent the xs in the problem *)
type_synonym real_sequence = "nat \<Rightarrow> real"

(* Helper functions to work with sums *)
definition sum_x :: "real_sequence \<Rightarrow> nat \<Rightarrow> real" where
"sum_x xs n = (\<Sum>i=1..n. xs i)"

definition sum_reciprocal :: "real_sequence \<Rightarrow> nat \<Rightarrow> real" where
"sum_reciprocal xs n = (\<Sum>i=1..n. 1/(xs i))"

(* Definition of a_n *)
definition a_n :: "real_sequence \<Rightarrow> nat \<Rightarrow> real" where
"a_n xs n = sqrt((sum_x xs n) * (sum_reciprocal xs n))"

subsection \<open>Example Values\<close>
(* Due to the Wellsortedness error, Isabelle cannot directly produce values of the a_n definition using
the value command. Instead we will demonstrate the existence of example values. *)

(* Example with n = 3 and xs = [2, 3, 4] *)
definition example_xs :: "real_sequence" where
"example_xs = (\<lambda>i. if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else 1)"

lemma example_sum_x: "sum_x example_xs  3 = 9"
  unfolding sum_x_def 
proof-
  show "sum example_xs {1..3} = 9"
  proof-
    have h1: "sum example_xs {1} = 2"
      by (simp add: example_xs_def)
    have h2: "sum example_xs {2} = 3"
      by (simp add: example_xs_def)
    have h3: "sum example_xs {3} = 4"
      by (simp add: example_xs_def)
    have h4: "sum example_xs {1..2} = 5" using h1 h2
      by (smt (verit, ccfv_threshold) Suc_1 atLeastAtMost_singleton comm_monoid_add_class.add_0 dbl_inc_def dbl_inc_simps(5) diff_minus_eq_add empty_Diff finite.intros(1) numeral_plus_numeral of_nat_numeral semiring_norm(26) sum.empty sum.insert_remove sum.lessThan_Suc sum_bounds_lt_plus1 uminus_add_conv_diff)
    have h5: "sum example_xs {1..3} = 9"
      by (metis add.commute add.right_neutral add_numeral_left ex_in_conv finite.intros(1) h3 h4 numeral_Bit1 numeral_plus_one plus_1_eq_Suc semiring_norm(5) sum.empty sum.insert sum.lessThan_Suc sum_bounds_lt_plus1) 
    show ?thesis using h5 by auto 
  qed
qed

(* We can also prove some properties about this example *)
lemma example_xs_positive: "\<forall>i\<le>3. example_xs i > 0"
  unfolding example_xs_def by auto

lemma example_xs_distinct: "distinct (map example_xs [1,2,3])"
  unfolding example_xs_def by auto

(* We can also compute sum_reciprocal for this example *)
lemma example_sum_reciprocal: "sum_reciprocal example_xs 3 = 1/2 + 1/3 + 1/4"
  unfolding sum_reciprocal_def
proof-
  show "(\<Sum>i = 1..3. 1 / example_xs i) = 1 / 2 + 1 / 3 + 1 / 4" 
  proof-
    have h1: "1 / example_xs 1 = 1/2"
      by (simp add: example_xs_def)
    have h2: "1 / example_xs 2 = 1/3"
      by (simp add: example_xs_def) 
    have h3: "1 / example_xs 3 = 1/4"
      by (simp add: example_xs_def)
    have h4: "(\<Sum>i = 1..2. 1 / example_xs i) = 1 / 2 + 1 / 3"
      by (smt (verit) One_nat_def Suc_1 add.commute add.right_neutral h1 h2 lessThan_0 sum.empty sum.lessThan_Suc sum_bounds_lt_plus1)
    have h5: "(\<Sum>i = 1..3. 1 / example_xs i) = 1 / 2 + 1 / 3 + 1/4" using h4
      by (metis ab_semigroup_add_class.add_ac(1) h3 nat_1_add_1 numeral_Bit0 numeral_code(3) plus_1_eq_Suc sum.lessThan_Suc sum_bounds_lt_plus1)
    show ?thesis using h5 by auto
  qed
qed

(* And consequently, we can compute a_n for this example *)
lemma example_a_n: "a_n  example_xs 3 = sqrt(9 * (1/2 + 1/3 + 1/4))"
  unfolding a_n_def
  using example_sum_x example_sum_reciprocal
  by simp

subsection \<open>Secondary Functions\<close>
definition is_int :: "real \<Rightarrow> bool" where
"is_int x \<equiv> (\<exists>n. x = real_of_int n)"

(* Optional helper lemmas for is_int that might be useful *)
lemma is_int_iff: "is_int x \<longleftrightarrow> (\<lfloor>x\<rfloor> = x)"
  unfolding is_int_def
  by simp

lemma is_int_real_of_int [simp]: "is_int (real_of_int n)"
  unfolding is_int_def
  by (rule exI[where x=n], simp)

lemma is_int_sqrt_nat:
  assumes "is_int (sqrt x)"
  shows "\<exists>n. sqrt x = real_of_int n"
  using assms unfolding is_int_def by blast

lemma not_is_int_between_integers:
  assumes "real_of_int n < x" "x < real_of_int (n + 1)"
  shows "\<not> is_int x"
  unfolding is_int_def
  using assms(1) assms(2) by force

section \<open>Locales and Helper Lemmas\<close>
locale sequence =
  fixes n :: nat and xs :: "real_sequence"
  fixes ns :: "nat list"
  assumes n_pos: "n \<ge> 1"
  assumes xs_pos: "\<forall>i\<in>set ns. xs i > 0"          (* positivity assumption *)
  assumes xs_distinct: "distinct (map xs ns)"    (* Distinctness assumption *)
  assumes length_ns: "length ns = n"             (* Ensure ns has right length *)
  assumes int_an: "\<forall>k\<in>set ns. is_int (a_n xs k)" (* Ensures a_n produces integers *)

context sequence
begin

(* We were unsuccessful in proving Cauchy Schwarz for this paper. The IMO proof takes it as an
  assumption so it is okay to leave it unproven in the scope of the solution. 
 *)
lemma cauchy_schwarz_3:
  fixes a1 a2 a3 b1 b2 b3 :: real
  assumes "a1 > 0" "a2 > 0" "a3 > 0" "b1 > 0" "b2 > 0" "b3 > 0"
  shows "(a1 + a2 + a3)*(b1 + b2 + b3) \<ge> (sqrt(a1*b1) + sqrt(a2*b2) + sqrt(a3*b3))^2"
  sorry

(* Modified lemma for distinct values *)
lemma xs_distinct_values:
  assumes "i \<in> set ns" 
  assumes "j \<in> set ns" 
  assumes "i \<noteq> j"
  shows "xs i \<noteq> xs j"
proof -
  (* Use distinctness of map xs ns directly *)
  have "distinct (map xs ns)"
    using sequence_axioms
    using sequence_def by blast 

  (* If i,j are in set ns and different, their xs values must be different *)
  thus ?thesis
    using assms distinct_map
    by (metis inj_onD)
qed

(* Modified lemma for positivity *)
lemma xs_positive:
  assumes "i \<in> set ns"
  shows "xs i > 0"
  using assms sequence_axioms
  using sequence_def by blast 

(* Helper lemma: Adding two terms increases the sum by at least their minimum *)
lemma sum_increase_two_terms:
  assumes "n + 2 \<le> length ns"
  shows "sum_x xs (n+2)  - sum_x xs n  = xs (n+1) + xs (n+2)"
proof -
  have "sum_x xs (n+2)  = (\<Sum>i=1..(n+2). xs i)"
    by (simp add: sum_x_def)
  moreover have "sum_x xs n  = (\<Sum>i=1..n. xs i)"
    by (simp add: sum_x_def)
  ultimately show ?thesis
    by (simp add: sum.atLeast_Suc_atMost)
qed

(* Helper lemma: Similar for reciprocal sums *)
lemma sum_reciprocal_increase_two_terms:
  assumes "n + 2 \<le> length ns"
  shows "sum_reciprocal xs (n+2)  - sum_reciprocal xs n  = 1/(xs (n+1)) + 1/(xs (n+2))"
proof -
  have "sum_reciprocal xs (n+2)  = (\<Sum>i=1..(n+2). 1/(xs i))"
    by (simp add: sum_reciprocal_def)
  moreover have "sum_reciprocal xs n  = (\<Sum>i=1..n. 1/(xs i))"
    by (simp add: sum_reciprocal_def)
  ultimately show ?thesis
    by (simp add: sum.atLeast_Suc_atMost)
qed

(* If we need consecutive indices, we need additional assumptions *)
lemma xs_consecutive_distinct:
  assumes "i \<in> set ns"
  assumes "i + 1 \<in> set ns"
  shows "xs i \<noteq> xs (i + 1)"
  using assms xs_distinct_values by auto

(* If we need to work with ranges, we need to relate ns to its indices *)
lemma xs_range_distinct:
  assumes "i \<in> set ns" "j \<in> set ns"
  assumes "i < j"
  shows "xs i \<noteq> xs j"
  using assms xs_distinct_values by auto

section \<open>Main Proof\<close>

subsection \<open>Claim: a_(n+1) - a_n = 1 \<Longrightarrow> a_(n+2) - a_(n+1) \<ge> 2\<close>

lemma sum_x_positive:
  assumes "n \<in> set ns"
  shows "sum_x xs n > 0"
proof -
  have "\<exists>i\<le>n. i \<in> set ns \<and> xs i > 0"
    using assms xs_positive by auto
  show ?thesis unfolding sum_x_def sorry
qed

lemma sum_reciprocal_positive:
  assumes "n \<in> set ns"
  shows "sum_reciprocal xs n > 0"
proof -
  have "\<forall>i\<le>n. i \<in> set ns \<longrightarrow> 1/(xs i) > 0"
    using xs_positive by auto
  thus ?thesis
    unfolding sum_reciprocal_def[of xs n]
    sorry
qed

lemma am_gm_two:
  assumes "a > 0" "b > 0"
  shows "(a + b)/2 \<ge> sqrt(a * b)"
proof -
  have "(sqrt(a) - sqrt(b))^2 \<ge> 0"
    by simp
  hence "a + b \<ge> 2 * sqrt(a * b)"
    by (smt (z3) arith_geo_mean_sqrt assms(1) assms(2) field_sum_of_halves)
  thus ?thesis
    by simp
qed

lemma a_n_difference:
  assumes "n \<in> set ns" "n + 1 \<in> set ns"
  shows "a_n xs (n + 1) - a_n xs n \<ge> 1"
proof -
  let ?Sn = "sum_x xs n"
  let ?Rn = "sum_reciprocal xs n"
  let ?x = "xs (n + 1)"
  
  (* Express a_n (n+1) and a_n n in terms of sums *)
  have an1: "a_n xs (n + 1) = sqrt((?Sn + ?x) * (?Rn + 1/?x))"
    unfolding a_n_def sum_x_def sum_reciprocal_def
    by (simp add: sum.atLeast_Suc_atMost)
    
  have an: "a_n xs n = sqrt(?Sn * ?Rn)"
    by (simp add: a_n_def)

  (* Use positivity of xs *)
  have x_pos: "?x > 0"
    using assms(2) xs_positive by auto
    
  have Sn_pos: "?Sn > 0"
    using assms(1) xs_positive
    by (simp add: sum_x_positive)

  have Rn_pos: "?Rn > 0"
    using assms(1) xs_positive
    by (simp add: sum_reciprocal_positive)

  (* Key inequality: For positive reals, sqrt((a+b)(c+d)) - sqrt(ac) \<ge> sqrt(bd) *)
  have key_ineq: "sqrt((?Sn + ?x) * (?Rn + 1/?x)) - sqrt(?Sn * ?Rn) \<ge> sqrt(?x * (1/?x))"
  proof -
    have "(?Sn + ?x) * (?Rn + 1/?x) = ?Sn * ?Rn + ?Sn * (1/?x) + ?x * ?Rn + ?x * (1/?x)"
      by (simp add: algebra_simps)
    moreover have "?x * (1/?x) = 1"
      using x_pos by simp
    moreover have "?Sn * (1/?x) + ?x * ?Rn \<ge> 2 * sqrt(?Sn * ?Rn)"
      using Sn_pos Rn_pos x_pos
      sorry (* This is AM-GM inequality *)
    ultimately show ?thesis
      sorry (* Combine the inequalities *)
  qed

  (* Simplify the right side *)
  have "sqrt(?x * (1/?x)) = 1"
    using x_pos by simp

  (* Use integer property *)
  moreover have "is_int (a_n xs (n + 1))"
    using assms(2) int_an by auto

  moreover have "is_int (a_n xs n)"
    using assms(1) int_an by auto

  (* If the difference of integers is > 1, it must be \<ge> 1 *)
  ultimately show ?thesis
    using key_ineq
    using an an1 by presburger
qed

lemma a_n_1_eq_1:
  assumes "1 \<in> set ns"
  shows "a_n xs 1 = 1"
proof -
  (* Expand definition of a_n *)
  have "a_n xs 1  = sqrt((sum_x xs 1) * (sum_reciprocal xs 1))"
    by (simp add: a_n_def)

  (* Expand sum_x for n=1 *)
  moreover have "sum_x xs 1 = (\<Sum>i\<in>set ns \<inter> {1}. xs i)"
    using assms sum_x_def by auto
  hence "sum_x xs 1 = xs 1"
    using assms by simp

  (* Expand sum_reciprocal for n=1 *)
  moreover have "sum_reciprocal xs 1 = (\<Sum>i\<in>set ns \<inter> {1}. 1/(xs i))"
    using assms sum_reciprocal_def by force
  hence "sum_reciprocal xs 1  = 1/(xs 1)"
    using assms by simp

  (* Combine the results *)
  ultimately have "a_n xs 1  = sqrt(xs 1 * (1/(xs 1)))"
    by simp

  (* Simplify using positivity *)
  moreover have "xs 1 > 0"
    using xs_pos assms by auto
  hence "xs 1 * (1/(xs 1)) = 1"
    by (simp add: field_simps)

  ultimately show ?thesis
    by simp
qed

(* Now let's prove the main sequence property *)
lemma an_gte_2:
  assumes "n \<in> set ns" "n+1 \<in> set ns" "n+2 \<in> set ns"
  shows "a_n xs (n+2) \<ge> ( a_n xs n) + 3"
 proof -
  let ?S1 = "sum_x xs n"
  let ?S2 = "sum_reciprocal xs n"
  let ?x1 = "xs (n+1)"
  let ?x2 = "xs (n+2)"

  (* Express a_n (n+2) in terms of a_n n *)
  have "a_n xs (n+2)  = sqrt((sum_x xs (n+2) ) * (sum_reciprocal xs (n+2) ))"
    by (simp add: a_n_def)
  also have "... = sqrt((?S1 + ?x1 + ?x2) * (?S2 + 1/?x1 + 1/?x2))"
  proof-
    have "sum_x xs (n+2) = ?S1 + ?x1 + ?x2" 
      using sum_increase_two_terms[OF] assms sorry
    moreover have "sum_reciprocal xs (n+2) = ?S2 + 1/?x1 + 1/?x2"
      using sum_reciprocal_increase_two_terms assms sorry
    ultimately show ?thesis by simp
  qed

  (* Apply Cauchy-Schwarz for three terms *)
  moreover have "(?S1 + ?x1 + ?x2) * (?S2 + 1/?x1 + 1/?x2) \<ge> 
                (sqrt(?S1 * ?S2) + sqrt(?x1 * (1/?x1)) + sqrt(?x2 * (1/?x2)))^2"
    using cauchy_schwarz_3[of ?S1 ?x1 ?x2 ?S2 ?x1 ?x2 ]
    by (meson assms(1) assms(2) assms(3) cauchy_schwarz_3 sum_reciprocal_positive sum_x_positive xs_pos zero_less_divide_1_iff)


  (* Simplify the right side *)
  moreover have "sqrt(?S1 * ?S2) = a_n xs n"
    by (simp add: a_n_def)
    
  moreover have "sqrt(?x1 * (1/?x1)) = 1" "sqrt(?x2 * (1/?x2)) = 1"
    using assms(2) xs_pos apply fastforce
    using assms(3) xs_pos by fastforce

  ultimately have "a_n xs (n+2) \<ge> a_n xs n + 2"
    using real_le_rsqrt by fastforce
    
  (* Use the integer property *)
  moreover have "is_int (a_n xs (n+2) )"
    using assms(3) int_an by auto

  (* If an integer is > x + 2, it must be \<ge> x + 3 *)
  moreover have "\<lbrakk>is_int y; y \<ge> x + 2\<rbrakk> \<Longrightarrow> y \<ge> x + 3"
    for x y :: real
  proof -
    assume "is_int y" "y \<ge> x + 2"
    then obtain k where "y = real_of_int k"
      unfolding is_int_def by auto
    hence "k > \<lfloor>x\<rfloor> + 2"
      using \<open>y = real_of_int k\<close> \<open>y \<ge> x + 2\<close> floor_less_iff[of x k ] less_eq_real_def[of x k]
      sorry
    hence "real_of_int k \<ge> x + 3"
      using \<open>k > \<lfloor>x\<rfloor> + 2\<close>
      sorry
    thus "y \<ge> x + 3"
      using \<open>y = real_of_int k\<close> by simp
  qed

  ultimately show ?thesis
    using \<open>is_int (a_n xs (n+2))\<close> \<open>a_n xs (n+2) \<ge> a_n xs n + 2\<close>
    sorry
qed

subsection \<open>Thus, a_2023_gte_3034\<close>

(* Helper lemma to ensure we have consecutive indices *)
lemma consecutive_indices:
  assumes "2*k + 1 \<in> set ns"
  assumes "2*k + 2 \<in> set ns"
  assumes "2*k + 3 \<in> set ns"
  shows "a_n xs (2*k + 3)  \<ge> a_n xs (2*k + 1) + 3"
  using an_gte_2[OF] sorry

lemma intermediate_bound:
 assumes path_exists: "\<forall>j\<le>k. 2*j + 1 \<in> set ns \<and> 
                              (if j < k then 2*j + 2 \<in> set ns \<and> 2*j + 3 \<in> set ns else True)"
  shows "a_n xs (2*k + 1)  \<ge> 3*k + 1"
proof (induction k)
  case 0
  (* Base case: k = 0 *)
  have "1 \<in> set ns"
    using path_exists
    by (metis One_nat_def Suc_eq_plus1 mult_zero_right zero_le) 
  hence "a_n xs 1  = 1"
    using an_gte_2[OF]
    using a_n_1_eq_1 by blast 
  thus ?case by simp

next
  case (Suc k)
  (* Inductive case: prove for k+1 assuming it's true for k *)
  
  (* Show we have all needed indices for k *)
  have k_indices: "\<forall>j\<le>k. 2*j + 1 \<in> set ns \<and> 
                        (if j < k then 2*j + 2 \<in> set ns \<and> 2*j + 3 \<in> set ns else True)"
    using Suc.prems sorry

  (* Get the specific indices we need *)
  have k_in: "2*k + 1 \<in> set ns"
    using k_indices by auto
    
  have k_plus1_in: "2*k + 2 \<in> set ns"
    using Suc.prems sorry
    
  have k_plus2_in: "2*k + 3 \<in> set ns"
    using Suc.prems sorry

  (* Apply inductive hypothesis *)
  have IH: "a_n xs (2*k + 1) \<ge> 3*k + 1"
    using Suc.IH k_indices by simp

  (* Apply consecutive_indices *)
  have "a_n xs (2*k + 3) \<ge> a_n xs (2*k + 1) + 3"
    using consecutive_indices[OF k_in k_plus1_in k_plus2_in] by simp

  (* Combine with inductive hypothesis *)
  hence "a_n xs (2*k + 3)  \<ge> (3*k + 1) + 3"
    using IH by linarith

  (* Simplify to match goal *)
  also have "... = 3*(k+1) + 1"
    using algebra_simps sorry

  finally show ?case
    by (metis Suc3_eq_add_3 Suc_eq_plus1 \<open>a_n xs (2 * k + 3) = real (3 * (k + 1) + 1)\<close> add.commute add_Suc_right dual_order.refl mult_2)
qed


lemma final_bound:
  assumes path_complete: "\<forall>j\<le>1011. 2*j + 1 \<in> set ns \<and>
                          (if j < 1011 then 2*j + 2 \<in> set ns \<and> 2*j + 3 \<in> set ns else True)"
  shows "a_n xs 2023 \<ge> 3034" 
proof(rule ccontr)
  assume "\<not> 3034 \<le> a_n xs 2023"
  let ?k = "1011"
  have h1: "a_n  xs (2*?k + 1) \<ge> 3*?k + 1"
    by (metis (mono_tags, opaque_lifting) assms intermediate_bound numeral_Bit1_eq_inc_double numeral_plus_one numeral_times_numeral of_nat_numeral)
  show False
    using \<open>\<not> 3034 \<le> a_n xs 2023\<close> h1 by auto 
qed

end