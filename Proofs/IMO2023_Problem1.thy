theory IMO2023_Problem1
imports Main "HOL-Computational_Algebra.Factorial_Ring"


(*

IMO 2023 Problem 1:
Determine all positive, composite integers n that satisfy the following property: if
the positive divisors of n are 1 = d_1 < d_2 < ... < d_k = n, 
then d_i divides d_(i+1) + d_(i+2) for every 1 \<le> i \<le> k-2.


*)
begin


fun is_composite :: "int \<Rightarrow> bool" where
  "is_composite n = (\<exists>a b. 1 < a \<and> a < n \<and> 1 < b \<and> b < n \<and> a * b = n)"

fun divisors :: "int \<Rightarrow> int list" where
  "divisors n = [d. d \<leftarrow> [1..n], n mod d = 0]"

fun satisfies_condition :: "int \<Rightarrow> bool" where
  "satisfies_condition n =
    (let divs = divisors n
    in \<forall>i. 1 \<le> i \<and> i \<le> length divs - 2 \<longrightarrow> divs!i dvd (divs!(i+1) + divs!(i+2)))"

fun find_valid_numbers :: "int \<Rightarrow> int list" where
  "find_valid_numbers limit = [n. n \<leftarrow> [1..limit], is_composite n \<and> satisfies_condition n]"

lemma solution_02:
  fixes n i k::"int"
  assumes "n \<ge> 1"
  assumes "prime p"
  assumes "r \<ge> 2"
  assumes "\<forall>n. n \<in> set (find_valid_numbers limit)" 
  shows "n = p^r"
  sorry

end
