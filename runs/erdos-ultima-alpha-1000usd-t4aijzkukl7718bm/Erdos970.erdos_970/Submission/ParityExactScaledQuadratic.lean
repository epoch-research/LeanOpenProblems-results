import Submission.ParityExactQuadratic
import Submission.ParityScaledSquarePadding

/-! Unbounded parity imbalance at EVERY fixed positive quadratic scale.
This does not assert the existence of a covered interval. -/
namespace Erdos970.ParityDiscrepancy
open Finset Filter

lemma scaled_square_bound_controls_prime_difference (C A : ℕ) (hC : 0 < C)
    (hA : ScaledSquareParityBound C A) (s : ℕ) (hs : 2 ≤ s)
    (hcard : C * (oddPrimes (2 * s)).card ≤ s) :
    |((4 * s ^ 2).primeCounting : ℚ) - 4 * (s ^ 2).primeCounting| ≤
      (12 * (A : ℚ) + 24 * C + 40) * s := by
  let P := oddPrimes (2 * s)
  have hP := oddPrimes_properties (2 * s)
  have h1 := scaled_square_bound_in_window C A hC hA P hP s (s ^ 2) (by omega) hcard le_rfl (by omega)
  have h2 := scaled_square_bound_in_window C A hC hA P hP s (2 * s ^ 2) (by omega) hcard (by omega) (by omega)
  have h4 := scaled_square_bound_in_window C A hC hA P hP s (4 * s ^ 2) (by omega) hcard (by omega) le_rfl
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

/-- No fixed positive multiple of a square admits a uniform O(k) parity bound. -/
theorem not_scaledSquareParityBound (C A : ℕ) (hC : 0 < C) :
    ¬ScaledSquareParityBound C A := by
  intro hA
  apply PrimeCountingDyadic.not_eventually_bounded_four_adic_difference
    (12 * A + 24 * C + 40)
  have hevent : ∀ᶠ n : ℕ in atTop, C * (oddPrimes (2 * 2 ^ n)).card ≤ 2 ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).eventually
      (eventually_small_oddPrime_core C hC)
  filter_upwards [hevent, eventually_ge_atTop 1] with n hcard hn
  have hn0 : n ≠ 0 := by omega
  have hs : 2 ≤ 2 ^ n := Nat.le_self_pow hn0 2
  have h := scaled_square_bound_controls_prime_difference C A hC hA (2 ^ n) hs hcard
  have hp : (2 ^ n) ^ 2 = (4 : ℕ) ^ n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hp' : 4 * (2 ^ n) ^ 2 = (4 : ℕ) ^ (n + 1) := by rw [hp, pow_succ]; ring
  rw [hp', hp] at h
  exact_mod_cast h

/-- The disproved counting estimate remains false at EXACT length C*k^2 for
any fixed natural C>0, and after discarding any finite range of k. This is NOT
a disproof of Erdős970: the integer one survives every sieve displayed here. -/
theorem unbounded_parity_at_exact_quadratic (A C K : ℕ) (hC : 0 < C) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ Odd p) ∧ K ≤ P.card ∧ 0 < P.card ∧
      (A : ℚ) * P.card < |alternatingCount P 1 (C * P.card ^ 2)| := by
  by_contra hbad
  push_neg at hbad
  apply not_scaledSquareParityBound C (A + C * K) hC
  intro P hP
  by_cases hk : K ≤ P.card
  · by_cases hp0 : P.card = 0
    · simp [hp0, alternatingCount]
    · have hh := hbad P hP hk (Nat.pos_of_ne_zero hp0)
      push_cast
      have hnonneg : (0 : ℚ) ≤ (C : ℚ) * K * P.card := by positivity
      nlinarith
  · have hlen := abs_alternatingCount_le P 1 (C * P.card ^ 2)
    have hc : C * P.card ^ 2 ≤ C * K * P.card := by
      have hh := Nat.mul_le_mul_right P.card (show P.card ≤ K by omega)
      have hhh := Nat.mul_le_mul_left C hh
      nlinarith
    have hcQ : ((C * P.card ^ 2 : ℕ) : ℚ) ≤ (C : ℚ) * K * P.card := by exact_mod_cast hc
    push_cast
    have hnonneg : (0 : ℚ) ≤ (A : ℚ) * P.card := by positivity
    linarith

lemma one_survives (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) : survivorIndicator P 1 = 1 := by
  simp only [survivorIndicator, if_pos (fun p hp => (hP p hp).not_dvd_one)]

/-- The counterexamples to parity balance explicitly retain a survivor. -/
theorem unbounded_parity_with_survivor (A C K : ℕ) (hC : 0 < C) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ Odd p) ∧ K ≤ P.card ∧ 0 < P.card ∧
      (A : ℚ) * P.card < |alternatingCount P 1 (C * P.card ^ 2)| ∧
      survivorIndicator P 1 = 1 := by
  obtain ⟨P, hP, hK, hk, hdisc⟩ := unbounded_parity_at_exact_quadratic A C K hC
  exact ⟨P, hP, hK, hk, hdisc, one_survives P (fun p hp => (hP p hp).1)⟩

/-- The obstruction applies to real constants as well as natural ones. -/
theorem no_real_uniform_parity_estimate (C K : ℕ) (hC : 0 < C) :
    ¬∃ A : ℝ, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ Odd p) → K ≤ P.card →
      |(alternatingCount P 1 (C * P.card ^ 2) : ℝ)| ≤ A * P.card := by
  rintro ⟨A, hA⟩
  obtain ⟨B, hB⟩ := exists_nat_gt A
  obtain ⟨P, hP, hK, hk, hlarge⟩ := unbounded_parity_at_exact_quadratic B C K hC
  have hreal : (B : ℝ) * P.card < |(alternatingCount P 1 (C * P.card ^ 2) : ℝ)| := by
    exact_mod_cast hlarge
  have hsmall := hA P hP hK
  have hm := mul_le_mul_of_nonneg_right hB.le (Nat.cast_nonneg (α := ℝ) P.card)
  linarith

#print axioms no_real_uniform_parity_estimate
#print axioms not_scaledSquareParityBound
#print axioms unbounded_parity_at_exact_quadratic
#print axioms unbounded_parity_with_survivor
end Erdos970.ParityDiscrepancy
