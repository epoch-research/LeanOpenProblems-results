import FormalConjectures.Util.ProblemImports

open Nat

/--
A180017: Difference of sums of digits of $n$ in ternary and in binary.
$$a(n) = \left(\sum \text{digits}_3(n)\right) - \left(\sum \text{digits}_2(n)\right)$$
-/
def a (n : ℕ) : ℤ :=
  Int.ofNat (Nat.digits 3 n |>.sum) - Int.ofNat (Nat.digits 2 n |>.sum)

lemma sum_digits_le (b n : ℕ) (hb : 2 ≤ b) : (Nat.digits b n).sum ≤ n := by
  induction' n using Nat.strong_induction_on with n ih
  rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn
  · simp
  · rw [Nat.digits_def' hb hn]
    simp only [List.sum_cons]
    have h1 : (Nat.digits b (n / b)).sum ≤ n / b := ih (n / b) (Nat.div_lt_self hn hb)
    have h2 : b * (n / b) + n % b = n := Nat.div_add_mod n b
    have h3 : n / b ≤ b * (n / b) := by
      calc n / b = 1 * (n / b) := by rw [Nat.one_mul]
      _ ≤ b * (n / b) := Nat.mul_le_mul_right (n / b) (by omega)
    omega

lemma a_eq_val (n : ℕ) : a n = (n.factorial.factorization 2 : ℤ) - 2 * (n.factorial.factorization 3 : ℤ) := by
  have h2 : (2 - 1) * n.factorial.factorization 2 = n - (Nat.digits 2 n).sum := Nat.sub_one_mul_factorization_factorial Nat.prime_two
  have h3 : (3 - 1) * n.factorial.factorization 3 = n - (Nat.digits 3 n).sum := Nat.sub_one_mul_factorization_factorial Nat.prime_three
  change ((Nat.digits 3 n).sum : ℤ) - ((Nat.digits 2 n).sum : ℤ) = _
  have H2 : (Nat.digits 2 n).sum ≤ n := sum_digits_le 2 n (by decide)
  have H3 : (Nat.digits 3 n).sum ≤ n := sum_digits_le 3 n (by decide)
  have h2' : n.factorial.factorization 2 = n - (Nat.digits 2 n).sum := by omega
  have h3' : 2 * n.factorial.factorization 3 = n - (Nat.digits 3 n).sum := by omega
  have i2 : (n.factorial.factorization 2 : ℤ) = (n : ℤ) - ((Nat.digits 2 n).sum : ℤ) := by omega
  have i3 : 2 * (n.factorial.factorization 3 : ℤ) = (n : ℤ) - ((Nat.digits 3 n).sum : ℤ) := by omega
  omega

theorem a_infinite (z : ℤ) : Set.Infinite { n : ℕ | a n = z } := by
  sorry

/--
%C A180017 This sequence is positive on average, since 1/log(3) > 1/log(4). Do all integers appear infinitely often? - _Charles R Greathouse IV_, Feb 07 2013
The conjecture asks if for every integer $z$, the set of natural numbers $n$ such that $a(n) = z$ is infinite.
-/
theorem oeis_180017_conjecture_0 :
  ∀ z : ℤ, Set.Infinite { n : ℕ | a n = z } := by sorry

theorem oeis_180017_conjecture_0.disproof : ¬ (type_of% @oeis_180017_conjecture_0) := sorry
