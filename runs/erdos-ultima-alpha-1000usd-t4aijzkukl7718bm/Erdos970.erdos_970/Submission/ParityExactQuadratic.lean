import Submission.ParitySquarePadding
import Submission.PrimeCountingDyadicDiscrepancy

/-! Parity imbalance cannot be O(k), even at length exactly k^2, for sieves
by k odd primes. This is a counting obstruction, NOT an interval cover or a
negation of the quadratic Jacobsthal conjecture. -/
namespace Erdos970.ParityDiscrepancy
open Finset

lemma four_scale_rough_identity (s : ℕ) (hs : 2 ≤ s) :
    alternatingCount (oddPrimes (2 * s)) 1 (4 * s ^ 2) +
      alternatingCount (oddPrimes (2 * s)) 1 (2 * s ^ 2) -
        2 * alternatingCount (oddPrimes (2 * s)) 1 (s ^ 2) =
      ((4 * s ^ 2).primeCounting : ℚ) - 4 * (s ^ 2).primeCounting +
        3 * (2 * s).primeCounting - 3 := by
  let P := oddPrimes (2 * s)
  have h1 := alternating_doubling_difference P (oddPrimes_properties _) (s ^ 2)
  have h2 := alternating_doubling_difference P (oddPrimes_properties _) (2 * s ^ 2)
  have hlo : 2 * s ≤ s ^ 2 := by nlinarith
  have hhy : 2 ≤ 2 * s := by omega
  have hc1 := oddSurvivorCount_eq (2 * s) (s ^ 2) hhy hlo (by nlinarith)
  have hc2 := oddSurvivorCount_eq (2 * s) (2 * s ^ 2) hhy (by omega) (by nlinarith)
  have hc4 := oddSurvivorCount_eq (2 * s) (4 * s ^ 2) hhy (by omega) (by nlinarith)
  have heq : 2 * (2 * s ^ 2) = 4 * s ^ 2 := by ring
  rw [heq] at h2
  dsimp only [P] at h1 h2
  rw [hc1, hc2] at h1
  rw [hc2, hc4] at h2
  linarith

lemma square_bound_controls_prime_difference (A : ℕ) (hA : SquareParityBound A)
    (s : ℕ) (hs : 2 ≤ s) :
    |((4 * s ^ 2).primeCounting : ℚ) - 4 * (s ^ 2).primeCounting| ≤
      (12 * (A : ℚ) + 40) * s := by
  let P := oddPrimes (2 * s)
  have hP := oddPrimes_properties (2 * s)
  have hcard := oddPrimes_card_le s
  have h1 := square_bound_in_window A hA P hP s (s ^ 2) (by omega) hcard le_rfl (by omega)
  have h2 := square_bound_in_window A hA P hP s (2 * s ^ 2) (by omega) hcard (by omega) (by omega)
  have h4 := square_bound_in_window A hA P hP s (4 * s ^ 2) (by omega) hcard (by omega) le_rfl
  have heq := four_scale_rough_identity s hs
  change alternatingCount P 1 (4 * s ^ 2) + alternatingCount P 1 (2 * s ^ 2) -
    2 * alternatingCount P 1 (s ^ 2) = _ at heq
  have hpi : (2 * s).primeCounting ≤ 2 * s + 1 := Nat.count_le _
  have hpiQ : ((2 * s).primeCounting : ℚ) ≤ 2 * s + 1 := by exact_mod_cast hpi
  have hpi0 : (0 : ℚ) ≤ (2 * s).primeCounting := by positivity
  have hsQ : (2 : ℚ) ≤ s := by exact_mod_cast hs
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h2l, h2u⟩ := abs_le.mp h2
  obtain ⟨h4l, h4u⟩ := abs_le.mp h4
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A square-scale parity bound would force an impossible square-root estimate
for prime-counting differences. -/
theorem not_squareParityBound (A : ℕ) : ¬SquareParityBound A := by
  intro hA
  apply PrimeCountingDyadic.not_bounded_four_adic_difference
  refine ⟨12 * A + 40, fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    have hpi4 : (4 : ℕ).primeCounting = 2 := by decide +kernel
    norm_num [hpi4]
    have hA0 : (0 : ℝ) ≤ A := by positivity
    linarith
  · have hn1 : 1 ≤ n := by omega
    have hs : 2 ≤ 2 ^ n := Nat.le_self_pow hn 2
    have h := square_bound_controls_prime_difference A hA (2 ^ n) hs
    have hp : (2 ^ n) ^ 2 = (4 : ℕ) ^ n := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    have hp' : 4 * (2 ^ n) ^ 2 = (4 : ℕ) ^ (n + 1) := by rw [hp, pow_succ]; ring
    rw [hp', hp] at h
    exact_mod_cast h

/-- The O(k) parity-balance estimate fails at EXACTLY k^2 positions, even after
any finite initial range of cardinalities is discarded. All residue classes here
are zero classes and the interval starts at one. There are still survivors. -/
theorem unbounded_parity_at_exact_square (A K : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ Odd p) ∧ K ≤ P.card ∧ 0 < P.card ∧
      (A : ℚ) * P.card < |alternatingCount P 1 (P.card ^ 2)| := by
  by_contra hbad
  push_neg at hbad
  apply not_squareParityBound (A + K)
  intro P hP
  by_cases hk : K ≤ P.card
  · by_cases hp0 : P.card = 0
    · simp [hp0, alternatingCount]
    · have hh := hbad P hP hk (Nat.pos_of_ne_zero hp0)
      push_cast
      have hnonneg : (0 : ℚ) ≤ (K : ℚ) * P.card := by positivity
      nlinarith
  · have hlen := abs_alternatingCount_le P 1 (P.card ^ 2)
    have hc : P.card ^ 2 ≤ K * P.card := by nlinarith
    have hcQ : ((P.card ^ 2 : ℕ) : ℚ) ≤ (K : ℚ) * P.card := by exact_mod_cast hc
    push_cast
    have hnonneg : (0 : ℚ) ≤ (A : ℚ) * P.card := by positivity
    linarith

#print axioms not_squareParityBound
#print axioms unbounded_parity_at_exact_square
end Erdos970.ParityDiscrepancy
