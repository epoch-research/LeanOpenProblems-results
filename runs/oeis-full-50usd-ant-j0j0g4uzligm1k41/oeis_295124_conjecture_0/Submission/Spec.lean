import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
A295124: $a(n)$ is the smallest number $k$ with $n$ prime factors such that $2d + k/d$ is prime for every $d \mid k$.
The definition interprets "n prime factors" as $n$ distinct prime factors ($\omega(k) = n$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the set of candidate numbers $k$ for a given $n$.
  let S (n : ℕ) : Set ℕ :=
    {k : ℕ | k > 0 ∧
      -- $\omega(k) = n$, k has n distinct prime factors.
      (Nat.primeFactors k).card = n ∧
      -- For every divisor d of k, $2d + k/d$ is prime.
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}

  -- $a(n)$ is the smallest element of this set. sInf is the infimum function on sets of ℕ.
  sInf (S n)

set_option maxRecDepth 8000 in
/-- Conjecture: the sequence is infinite. It is hard to believe!
This is formalized as the set $S(n)$ of candidate numbers being non-empty for all $n$. -/
theorem oeis_295124_conjecture_0 :
  ∀ n : ℕ, (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = n ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  intro n
  match n with
  | 0 =>
    refine ⟨1, by norm_num, ?_, ?_⟩
    · simp
    · intro d hd
      simp only [Nat.divisors_one, Finset.mem_singleton] at hd
      subst hd; norm_num
  | 1 =>
    refine ⟨3, by norm_num, ?_, ?_⟩
    · rw [(by norm_num : Nat.Prime 3).primeFactors]; decide
    · intro d hd
      have hdiv : Nat.divisors 3 = ({1, 3} : Finset ℕ) := by decide
      rw [hdiv] at hd
      fin_cases hd <;> norm_num
  | 2 =>
    refine ⟨15, by norm_num, ?_, ?_⟩
    · have h : (15 : ℕ) = 3 * 5 := by norm_num
      rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
          (by norm_num : Nat.Prime 3).primeFactors, (by norm_num : Nat.Prime 5).primeFactors]
      decide
    · intro d hd
      have hdiv : Nat.divisors 15 = ({1, 3, 5, 15} : Finset ℕ) := by decide
      rw [hdiv] at hd
      fin_cases hd <;> norm_num
  | 3 =>
    refine ⟨105, by norm_num, ?_, ?_⟩
    · have h : (105 : ℕ) = 3 * 5 * 7 := by norm_num
      rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          (by norm_num : Nat.Prime 3).primeFactors, (by norm_num : Nat.Prime 5).primeFactors,
          (by norm_num : Nat.Prime 7).primeFactors]
      decide
    · intro d hd
      have hdiv : Nat.divisors 105 = ({1, 3, 5, 7, 15, 21, 35, 105} : Finset ℕ) := by decide
      rw [hdiv] at hd
      fin_cases hd <;> norm_num
  | 4 =>
    refine ⟨93081, by norm_num, ?_, ?_⟩
    · have h : (93081 : ℕ) = 3 * 19 * 23 * 71 := by norm_num
      rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          (by norm_num : Nat.Prime 3).primeFactors, (by norm_num : Nat.Prime 19).primeFactors,
          (by norm_num : Nat.Prime 23).primeFactors, (by norm_num : Nat.Prime 71).primeFactors]
      decide
    · intro d hd
      have h : (93081 : ℕ) = 3 * 19 * 23 * 71 := by norm_num
      rw [h, Nat.divisors_mul, Nat.divisors_mul, Nat.divisors_mul,
          (by decide : Nat.divisors 3 = {1,3}), (by decide : Nat.divisors 19 = {1,19}),
          (by decide : Nat.divisors 23 = {1,23}), (by decide : Nat.divisors 71 = {1,71})] at hd
      fin_cases hd <;> norm_num
  | (m + 5) => sorry
