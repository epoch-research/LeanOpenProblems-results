import Submission.Potentials

/-!
# An obstruction to prime-factor-count potentials

A collision with four prime roots rules out any globally separating potential
that is constant on primes. This is not a counterexample to the conjecture:
it only rules out a particular class of potential constructions.
-/

namespace Erdos1206

/-- An exact nontrivial equal sum with four prime roots. -/
theorem prime_cube_collision :
    Nat.Prime 61 ∧ Nat.Prime 1049 ∧ Nat.Prime 1699 ∧ Nat.Prime 1823 ∧
    (1049 : ℕ) ^ 3 + 1699 ^ 3 = 61 ^ 3 + 1823 ^ 3 := by
  norm_num

/-- Constant-on-primes potentials cannot separate the two cube pairs. -/
theorem not_cubePairSeparating_of_constant_on_primes
    {A : Finset ℕ} {w : ℕ → ℕ} {v : ℕ}
    (h61 : 61 ∈ A) (h1049 : 1049 ∈ A)
    (h1699 : 1699 ∈ A) (h1823 : 1823 ∈ A)
    (hw : ∀ p : ℕ, Nat.Prime p → w p = v) :
    ¬ CubePairSeparating A w := by
  intro h
  rcases prime_cube_collision with ⟨p61, p1049, p1699, p1823, hc⟩
  have hpair := h 1049 h1049 1699 h1699 61 h61 1823 h1823 hc (by
    rw [hw 1049 p1049, hw 1699 p1699, hw 61 p61, hw 1823 p1823])
  norm_num at hpair

/-- The obstruction holds at every height at least 1823, and does not require
that the potential be independent of the height. -/
theorem not_cubePairSeparating_Icc_of_constant_on_primes
    {N : ℕ} (hN : 1823 ≤ N) {w : ℕ → ℕ} {v : ℕ}
    (hw : ∀ p : ℕ, Nat.Prime p → w p = v) :
    ¬ CubePairSeparating (Finset.Icc 1 N) w := by
  apply not_cubePairSeparating_of_constant_on_primes
    (v := v) (w := w) (A := Finset.Icc 1 N) <;>
    first | exact hw | simp only [Finset.mem_Icc]; omega

/-- In particular, any function of the total number of prime factors fails.
The function may be chosen afresh for each ambient height. -/
theorem not_cubePairSeparating_factorCount {N : ℕ} (hN : 1823 ≤ N)
    (f : ℕ → ℕ) :
    ¬ CubePairSeparating (Finset.Icc 1 N)
      (fun n => f n.primeFactorsList.length) := by
  apply not_cubePairSeparating_Icc_of_constant_on_primes hN (v := f 1)
  intro p hp
  simp [Nat.primeFactorsList_prime hp]

end Erdos1206
