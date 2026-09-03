import Submission.IndexDependentTelescoping
import Submission.LambertTwicePrimeSquare

/-!
A different rational factorial series preserving the original Lambert
coefficients modulo n^2(n-1), including their twice-prime square congruences.
This is NOT the series in Spec.lean and does not disprove Erdős 68.
-/

namespace PolynomialModulusRational

open Erdos68Development Filter
open scoped Topology

/-- `tail r` belongs to the original index `r+3`. -/
def tail : ℕ → ℤ
  | 0 => 27
  | r+1 =>
    let n : ℤ := r+4
    if (r+4).Prime then n * tail r - 1
    else 3*n^2 + (n*tail r - lambertCoeff (r+4) - 3*n^2) % (n^2*(n-1))

def coeffRow (r : ℕ) : ℤ := (r+4)*tail r - tail (r+1)

def coeff (n : ℕ) : ℤ := if n < 4 then 0 else coeffRow (n-4)

lemma coeff_add_four (r : ℕ) : coeff (r+4) = coeffRow r := by simp [coeff]

lemma modulus_pos (n : ℤ) (hn : 4 ≤ n) : 0 < n^2*(n-1) := by
  exact mul_pos (sq_pos_of_pos (by omega)) (by omega)

lemma prime_step_lower (n t : ℤ) (hn : 4 ≤ n) (ht : 3*(n-1)^2 ≤ t) :
    3*n^2 ≤ n*t-1 := by
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ n by omega)
  have hh : 0 ≤ n^2*(n-3) := mul_nonneg (sq_nonneg n) (by omega)
  nlinarith

lemma composite_step_positive (n t v : ℤ) (hn : 4 ≤ n)
    (ht : 3*(n-1)^2 ≤ t) (hv : v < n^2*(n+2)) : 0 < n*t-v := by
  have hm := mul_le_mul_of_nonneg_left ht (show 0 ≤ n by omega)
  have hh : 0 ≤ n^2*(n-4) := mul_nonneg (sq_nonneg n) (by omega)
  nlinarith

lemma tail_lower (r : ℕ) : 3*(r+3 : ℤ)^2 ≤ tail r := by
  induction r with
  | zero => norm_num [tail]
  | succ r ih =>
    simp only [tail]
    split_ifs with hp
    · have ht : 3*((r+4 : ℤ)-1)^2 ≤ tail r := by convert ih using 1; ring
      simpa only [Nat.cast_add, Nat.cast_one] using
        prime_step_lower (r+4) (tail r) (by omega) ht
    · have hm := Int.emod_nonneg
        ((r+4 : ℤ)*tail r - lambertCoeff (r+4) - 3*(r+4 : ℤ)^2)
        (ne_of_gt (modulus_pos (r+4) (by omega)))
      push_cast
      nlinarith

lemma tail_nonprime_upper (r : ℕ) (hp : ¬(r+3).Prime) :
    tail r < (r+3 : ℤ)^2*(r+5) := by
  cases r with
  | zero => norm_num [tail]
  | succ r =>
    have hp' : ¬(r+4).Prime := by simpa only [Nat.add_assoc] using hp
    simp only [tail, if_neg hp']
    have hm := Int.emod_lt_of_pos
      ((r+4 : ℤ)*tail r - lambertCoeff (r+4) - 3*(r+4 : ℤ)^2)
      (modulus_pos (r+4) (by omega))
    push_cast
    nlinarith

lemma prime_predecessor_nonprime (r : ℕ) (hp : (r+4).Prime) : ¬(r+3).Prime := by
  have ho := hp.eq_two_or_odd.resolve_left (by omega)
  intro h
  have ho' := h.eq_two_or_odd.resolve_left (by omega)
  omega

lemma tail_upper (r : ℕ) : tail r < (r+3 : ℤ)^4 := by
  cases r with
  | zero => norm_num [tail]
  | succ r =>
    by_cases hp : (r+4).Prime
    · have ht := tail_nonprime_upper r (prime_predecessor_nonprime r hp)
      have hm := mul_lt_mul_of_pos_left ht (show (0 : ℤ) < r+4 by omega)
      have hh : (0 : ℤ) ≤ (r+4)^2*(r+3) := by positivity
      simp only [tail, if_pos hp]
      push_cast
      nlinarith [sq_nonneg (r : ℤ)]
    · have ht := tail_nonprime_upper (r+1) (by simpa only [Nat.add_assoc] using hp)
      have hn : (r+1+3 : ℤ)+2 ≤ (r+1+3 : ℤ)^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hn (sq_nonneg (r+1+3 : ℤ))
      push_cast at ht ⊢
      nlinarith

lemma coeffRow_positive (r : ℕ) : 0 < coeffRow r := by
  by_cases hp : (r+4).Prime
  · simp [coeffRow, tail, hp]
  · have ht := tail_lower r
    have hu := tail_nonprime_upper (r+1) (by simpa only [Nat.add_assoc] using hp)
    apply composite_step_positive (r+4) (tail r) (tail (r+1)) (by omega)
    · convert ht using 1; ring
    · simpa only [Nat.cast_add, Nat.cast_one] using hu

lemma coeff_positive (n : ℕ) (hn : 4 ≤ n) : 0 < coeff n := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+4 := ⟨n-4, by omega⟩
  simpa only [coeff_add_four] using coeffRow_positive r

lemma coeff_prime (p : ℕ) (hp4 : 4 ≤ p) (hp : p.Prime) : coeff p = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r+4 := ⟨p-4, by omega⟩
  simp [coeff_add_four, coeffRow, tail, hp]

lemma modular_correction (n t a : ℤ) :
    n^2*(n-1) ∣ n*t - (3*n^2 + (n*t-a-3*n^2) % (n^2*(n-1))) - a := by
  have h := Int.emod_add_mul_ediv (n*t-a-3*n^2) (n^2*(n-1))
  refine ⟨(n*t-a-3*n^2) / (n^2*(n-1)), ?_⟩
  linarith

/-- Unlike a congruence just to one, this also preserves nonunit residues. -/
lemma full_congruence (n : ℕ) (hn : 4 ≤ n) :
    (n : ℤ)^2*((n : ℤ)-1) ∣ coeff n - lambertCoeff n := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+4 := ⟨n-4, by omega⟩
  by_cases hp : (r+4).Prime
  · rw [coeff_prime _ (by omega) hp, lambertCoeff_prime hp]
    simp
  · rw [coeff_add_four, coeffRow, tail, if_neg hp]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      modular_correction (r+4) (tail r) (lambertCoeff (r+4))

lemma predecessor_congruence (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℤ)-1) ∣ coeff n-1 := by
  have hd : ((n : ℤ)-1) ∣ (n : ℤ)^2*((n : ℤ)-1) := ⟨(n : ℤ)^2, by ring⟩
  have hc := hd.trans (full_congruence n hn)
  have ha := Nat.modEq_iff_dvd.mp (lambertCoeff_modEq_pred (show 2 ≤ n by omega)).symm
  have ha' : ((n : ℤ)-1) ∣ (lambertCoeff n : ℤ)-1 := by
    simpa only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] using ha
  convert dvd_add hc ha' using 1
  ring

lemma twice_prime_square_congruence (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (p : ℤ)^2 ∣ coeff (2*p)-3 := by
  have hd : (p : ℤ)^2 ∣ ((2*p : ℕ) : ℤ)^2*(((2*p : ℕ) : ℤ)-1) := by
    refine ⟨4*(2*(p : ℤ)-1), ?_⟩
    push_cast
    ring
  have hc := hd.trans (full_congruence (2*p) (by have := hp.two_le; omega))
  have ha := Nat.modEq_iff_dvd.mp
    (LambertTwicePrimeSquare.lambertCoeff_twice_prime_square p hp hodd).symm
  have ha' : (p : ℤ)^2 ∣ (lambertCoeff (2*p) : ℤ)-3 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ha
  convert dvd_add hc ha' using 1
  ring

noncomputable def normalizedTail (r : ℕ) : ℝ := (tail r : ℝ)/(r+3).factorial

lemma summable_normalizedTail : Summable normalizedTail := by
  have hs := (summable_nat_add_iff 3).mpr
    (IndexDependentTelescoping.summable_nat_pow_div_factorial 4)
  apply hs.of_norm_bounded
  intro r
  have hl : (0 : ℝ) ≤ tail r := by
    exact_mod_cast (show (0 : ℤ) ≤ tail r by have := tail_lower r; nlinarith)
  have hu : (tail r : ℝ) ≤ (r+3 : ℝ)^4 := by exact_mod_cast (tail_upper r).le
  dsimp [normalizedTail]
  rw [abs_of_nonneg (div_nonneg hl (by positivity))]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    div_le_div_of_nonneg_right hu (show (0 : ℝ) ≤ (r+3).factorial by positivity)

lemma coeffRow_div (r : ℕ) :
    (coeffRow r : ℝ)/(r+4).factorial = normalizedTail r-normalizedTail (r+1) := by
  have hf : ((r+3).factorial : ℝ) ≠ 0 := by positivity
  have hn : (r+4 : ℝ) ≠ 0 := by positivity
  simp only [coeffRow, normalizedTail, show r+1+3 = r+4 by omega]
  rw [show r+4 = (r+3)+1 by omega, Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma hasSum_coeffRow :
    HasSum (fun r : ℕ => (coeffRow r : ℝ)/(r+4).factorial) (9/2 : ℝ) := by
  have hs := summable_normalizedTail
  have ht := (summable_nat_add_iff 1).mpr hs
  have he := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at he
  have h0 : normalizedTail 0 = (9/2 : ℝ) := by norm_num [normalizedTail, tail]
  rw [h0] at he
  have he' : (∑' r, normalizedTail r) - (∑' r, normalizedTail (r+1)) = (9/2 : ℝ) := by
    linarith
  simpa only [coeffRow_div, he'] using hs.hasSum.sub ht.hasSum

lemma summable_coeff : Summable (fun n : ℕ => (coeff n : ℝ)/n.factorial) := by
  apply (summable_nat_add_iff 4).mp
  simpa only [coeff_add_four] using hasSum_coeffRow.summable

/-- This different series is rational, despite the stated congruences. -/
theorem sum_coeff : (∑' n : ℕ, (coeff n : ℝ)/n.factorial) = (9/2 : ℝ) := by
  have he := summable_coeff.sum_add_tsum_nat_add 4
  have hz : (∑ n ∈ Finset.range 4, (coeff n : ℝ)/n.factorial) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [coeff, Finset.mem_range.mp hn]
  rw [hz, zero_add] at he
  simpa only [coeff_add_four, hasSum_coeffRow.tsum_eq] using he.symm

lemma prefix_identity (r : ℕ) :
    (∑ k ∈ Finset.range (r+4), (coeff k : ℝ)/k.factorial) =
      (9/2 : ℝ)-normalizedTail r := by
  induction r with
  | zero => norm_num [Finset.sum_range_succ, coeff, normalizedTail, tail]
  | succ r ih =>
      rw [show r+1+4 = (r+4)+1 by omega, Finset.sum_range_succ, ih,
        coeff_add_four, coeffRow_div]
      ring

lemma scaled_tail_identity (r : ℕ) :
    ((r+3).factorial : ℝ) * ((∑' n : ℕ, (coeff n : ℝ)/n.factorial) -
      ∑ k ∈ Finset.range (r+4), (coeff k : ℝ)/k.factorial) = tail r := by
  rw [sum_coeff, prefix_identity, sub_sub_cancel, normalizedTail]
  exact mul_div_cancel₀ _ (by positivity)

lemma coeff_nonneg (n : ℕ) : 0 ≤ coeff n := by
  by_cases hn : n < 4
  · simp [coeff, hn]
  · exact (coeff_positive n (by omega)).le

lemma scaledTail_bounds (n : ℕ) (hn : 3 ≤ n) :
    0 < FactorialTailCriterion.scaledTail coeff n ∧
      FactorialTailCriterion.scaledTail coeff n < (n : ℝ)^4 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+3 := ⟨n-3, by omega⟩
  have he : FactorialTailCriterion.scaledTail coeff (r+3) = (tail r : ℝ) := by
    simpa only [FactorialTailCriterion.scaledTail, Nat.add_assoc] using scaled_tail_identity r
  rw [he]
  constructor
  · exact_mod_cast (show (0 : ℤ) < tail r by have := tail_lower r; nlinarith)
  · exact_mod_cast tail_upper r

lemma different_coefficients : coeff 4 = 55 ∧ lambertCoeff 4 = 7 := by decide

/-- The larger polynomial tail bound permits both the predecessor and
nonunit twice-prime square congruences in a positive rational series. -/
theorem comparison_properties :
    (∀ n : ℕ, 0 ≤ coeff n) ∧
    (∀ n : ℕ, 4 ≤ n → 0 < coeff n) ∧
    (∀ n : ℕ, 4 ≤ n → (n : ℤ)^2*((n : ℤ)-1) ∣ coeff n-lambertCoeff n) ∧
    (∀ n : ℕ, 4 ≤ n → ((n : ℤ)-1) ∣ coeff n-1) ∧
    (∀ p : ℕ, 4 ≤ p → p.Prime → coeff p = 1) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ)^2 ∣ coeff (2*p)-3) ∧
    (∀ n : ℕ, 3 ≤ n → 0 < FactorialTailCriterion.scaledTail coeff n ∧
      FactorialTailCriterion.scaledTail coeff n < (n : ℝ)^4) ∧
    (∑' n : ℕ, (coeff n : ℝ)/n.factorial) = (9/2 : ℝ) :=
  ⟨coeff_nonneg, coeff_positive, full_congruence, predecessor_congruence,
    coeff_prime, twice_prime_square_congruence, scaledTail_bounds, sum_coeff⟩

end PolynomialModulusRational

#print axioms PolynomialModulusRational.full_congruence
#print axioms PolynomialModulusRational.sum_coeff
#print axioms PolynomialModulusRational.scaled_tail_identity

#print axioms PolynomialModulusRational.twice_prime_square_congruence
#print axioms PolynomialModulusRational.comparison_properties
