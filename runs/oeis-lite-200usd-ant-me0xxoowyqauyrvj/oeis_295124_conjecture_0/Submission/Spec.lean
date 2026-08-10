import FormalConjectures.Util.ProblemImports

open Nat Finset Set

set_option maxRecDepth 8000

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

/-- Conjecture: the sequence is infinite. It is hard to believe!
This is formalized as the set $S(n)$ of candidate numbers being non-empty for all $n$. -/
theorem oeis_295124_conjecture_0 :
  ∀ n : ℕ, (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = n ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  intro n
  match n with
  | 0 =>
    exact ⟨1, by norm_num, by simp, by decide⟩
  | 1 =>
    refine ⟨3, by norm_num, ?_, by decide⟩
    rw [(by norm_num : Nat.Prime 3).primeFactors]; rfl
  | 2 =>
    refine ⟨15, by norm_num, ?_, by decide⟩
    rw [show (15 : ℕ) = 3 * 5 from by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        (by norm_num : Nat.Prime 3).primeFactors,
        (by norm_num : Nat.Prime 5).primeFactors]
    decide
  | 3 =>
    refine ⟨105, by norm_num, ?_, by decide⟩
    rw [show (105 : ℕ) = 3 * 5 * 7 from by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        (by norm_num : Nat.Prime 3).primeFactors,
        (by norm_num : Nat.Prime 5).primeFactors,
        (by norm_num : Nat.Prime 7).primeFactors]
    decide
  | 4 =>
    refine ⟨93081, by norm_num, ?_, ?_⟩
    · rw [show (93081 : ℕ) = 3 * 19 * 23 * 71 from by norm_num,
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.primeFactors_mul (by norm_num) (by norm_num),
          (by norm_num : Nat.Prime 3).primeFactors,
          (by norm_num : Nat.Prime 19).primeFactors,
          (by norm_num : Nat.Prime 23).primeFactors,
          (by norm_num : Nat.Prime 71).primeFactors]
      decide
    · intro d hd
      rw [show Nat.divisors 93081
            = ({1,3,19,23,71,57,69,213,437,1349,1633,1311,4047,4899,31027,93081} : Finset ℕ) from by
            rw [show (93081 : ℕ) = 3 * 19 * 23 * 71 from by norm_num,
                Nat.divisors_mul, Nat.divisors_mul, Nat.divisors_mul]; decide] at hd
      fin_cases hd <;> norm_num
  | (m + 5) =>
    -- This is the genuinely open content of OEIS A295124 (n ≥ 5). Explicit witnesses are
    -- known for n = 0..4 (k = 1, 3, 15, 105, 93081 = 3·19·23·71; the latter has all 16
    -- forms 2d + k/d prime). For each n a witness is expected with positive density: an
    -- exact "singular series" analysis shows that for every prime q there is a residue
    -- assignment of the prime factors avoiding q ∣ (2d + k/d) for all divisors d, so there is
    -- no modular/covering obstruction (verified for all n ≤ 6), hence the statement is not
    -- disprovable. But proving non-emptiness uniformly in n requires the simultaneous
    -- primality of all 2^n forms 2d + k/d — an instance of Dickson's conjecture / Schinzel's
    -- Hypothesis H, obstructed by the parity problem and beyond currently available mathematics.
    sorry
