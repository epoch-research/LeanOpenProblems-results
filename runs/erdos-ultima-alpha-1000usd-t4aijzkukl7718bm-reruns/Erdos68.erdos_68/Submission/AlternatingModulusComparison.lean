import Submission.LambertMinFactorCongruence
import Submission.LambertPrimeBand
import Submission.IndexDependentTelescoping

/-!
A rational comparison with quadratic tails, predecessor and least-prime-factor
factorial congruences, and all original coefficient-to-one congruences at odd
indices. This is NOT a proof or disproof of the series in Spec.lean.
-/

namespace AlternatingModulusComparison

open Erdos68Development Filter
open scoped Topology

def modulus (n : ℕ) : ℕ :=
  if n % 2 = 0 then 2*(n-1) else lambertCoeff n-1

/-- `tail r` is the integral tail at original index r+3. -/
def tail : ℕ → ℕ
  | 0 => 1
  | r+1 => 1 + ((r+4)*tail r-2) % (modulus (r+4))

def coeffRow (r : ℕ) : ℕ := (r+4)*tail r-tail (r+1)

def coeff (n : ℕ) : ℕ := if n < 4 then 0 else coeffRow (n-4)

lemma tail_pos (r : ℕ) : 0 < tail r := by cases r <;> simp [tail]

lemma tail_succ_le (r : ℕ) : tail (r+1) ≤ (r+4)*tail r-1 := by
  have hp := tail_pos r
  have hm := Nat.mod_le ((r+4)*tail r-2) (modulus (r+4))
  have ht : 4 ≤ (r+4)*tail r := by nlinarith
  simp only [tail]
  omega

lemma coeffRow_formula (r : ℕ) :
    coeffRow r = 1 + (modulus (r+4)) *
      (((r+4)*tail r-2) / (modulus (r+4))) := by
  have hp := tail_pos r
  have ht : 4 ≤ (r+4)*tail r := by nlinarith
  have hd := Nat.mod_add_div ((r+4)*tail r-2) (modulus (r+4))
  simp only [coeffRow, tail]
  omega

lemma coeffRow_pos (r : ℕ) : 0 < coeffRow r := by rw [coeffRow_formula]; omega

lemma coeff_add_four (r : ℕ) : coeff (r+4) = coeffRow r := by simp [coeff]

lemma coeff_prime (p : ℕ) (hp4 : 4 ≤ p) (hp : p.Prime) : coeff p = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r+4 := ⟨p-4, by omega⟩
  have ho : (r+4) % 2 ≠ 0 := by
    have h := hp.eq_two_or_odd.resolve_left (by omega)
    omega
  rw [coeff_add_four, coeffRow_formula, modulus, if_neg ho, lambertCoeff_prime hp]
  simp

lemma modulus_congruence (n : ℕ) (hn : 4 ≤ n) : modulus n ∣ coeff n-1 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+4 := ⟨n-4, by omega⟩
  rw [coeff_add_four, coeffRow_formula]
  simp

lemma odd_full_congruence (n : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1) :
    lambertCoeff n-1 ∣ coeff n-1 := by
  have h := modulus_congruence n hn
  simpa only [modulus, if_neg (by omega : ¬n % 2 = 0)] using h

lemma odd_inherited_congruence (n m : ℕ) (hn : 4 ≤ n) (ho : n % 2 = 1)
    (h : Nat.ModEq m (lambertCoeff n) 1) : Nat.ModEq m (coeff n) 1 := by
  have ha := lambertCoeff_one_le (show 2 ≤ n by omega)
  have hc : 1 ≤ coeff n := by
    obtain ⟨r, rfl⟩ : ∃ r, n = r+4 := ⟨n-4, by omega⟩
    simpa only [coeff_add_four] using coeffRow_pos r
  have hm : m ∣ lambertCoeff n-1 := (Nat.modEq_iff_dvd' ha).mp h.symm
  exact ((Nat.modEq_iff_dvd' hc).mpr
    (hm.trans (odd_full_congruence n hn ho))).symm

lemma tail_even_upper (r : ℕ) (he : (r+3) % 2 = 0) : tail r ≤ 2*(r+2) := by
  cases r with
  | zero => norm_num at he
  | succ r =>
    have he' : (r+4) % 2 = 0 := by simpa only [Nat.add_assoc] using he
    have hm := Nat.mod_lt ((r+4)*tail r-2) (show 0 < 2*(r+3) by omega)
    simp only [tail, modulus, if_pos he', show r+4-1 = r+3 by omega]
    omega

lemma tail_upper (r : ℕ) : tail r < 2*(r+3)^2 := by
  cases r with
  | zero => norm_num [tail]
  | succ r =>
    rcases Nat.mod_two_eq_zero_or_one (r+1+3) with he | ho
    · have h := tail_even_upper (r+1) he
      nlinarith
    · have he : (r+3) % 2 = 0 := by omega
      have ht := tail_even_upper r he
      have hs := (tail_succ_le r).trans (Nat.sub_le ((r+4)*tail r) 1)
      have hm := Nat.mul_le_mul_left (r+4) ht
      have hp := tail_pos r
      nlinarith

noncomputable def normalizedTail (r : ℕ) : ℝ := (tail r : ℝ)/(r+3).factorial

lemma summable_normalizedTail : Summable normalizedTail := by
  have hs := ((summable_nat_add_iff 3).mpr
    (IndexDependentTelescoping.summable_nat_pow_div_factorial 2)).mul_left (2 : ℝ)
  apply hs.of_norm_bounded
  intro r
  dsimp only [normalizedTail]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ht : (tail r : ℝ) ≤ 2*(r+3 : ℝ)^2 := by exact_mod_cast (tail_upper r).le
  calc
    _ ≤ (2*(r+3 : ℝ)^2)/(r+3).factorial :=
      div_le_div_of_nonneg_right ht (by positivity)
    _ = _ := by push_cast; ring

lemma coeffRow_div (r : ℕ) :
    (coeffRow r : ℝ)/(r+4).factorial = normalizedTail r-normalizedTail (r+1) := by
  have hl : tail (r+1) ≤ (r+4)*tail r := (tail_succ_le r).trans (Nat.sub_le _ _)
  have hf : ((r+3).factorial : ℝ) ≠ 0 := by positivity
  have hn : (r+4 : ℝ) ≠ 0 := by positivity
  simp only [coeffRow, Nat.cast_sub hl, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
    normalizedTail, show r+1+3 = r+4 by omega]
  rw [show r+4 = (r+3)+1 by omega, Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma hasSum_coeffRow :
    HasSum (fun r : ℕ => (coeffRow r : ℝ)/(r+4).factorial) (1/6 : ℝ) := by
  have hs := summable_normalizedTail
  have ht := (summable_nat_add_iff 1).mpr hs
  have he := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at he
  have h0 : normalizedTail 0 = (1/6 : ℝ) := by norm_num [normalizedTail, tail]
  rw [h0] at he
  have he' : (∑' r, normalizedTail r) - (∑' r, normalizedTail (r+1)) = (1/6 : ℝ) := by
    linarith
  simpa only [coeffRow_div, he'] using hs.hasSum.sub ht.hasSum

lemma summable_coeff : Summable (fun n : ℕ => (coeff n : ℝ)/n.factorial) := by
  apply (summable_nat_add_iff 4).mp
  simpa only [coeff_add_four] using hasSum_coeffRow.summable

/-- This different coefficient series has rational sum 1/6. -/
theorem sum_coeff : (∑' n : ℕ, (coeff n : ℝ)/n.factorial) = (1/6 : ℝ) := by
  have he := summable_coeff.sum_add_tsum_nat_add 4
  have hz : (∑ n ∈ Finset.range 4, (coeff n : ℝ)/n.factorial) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [coeff, Finset.mem_range.mp hn]
  rw [hz, zero_add] at he
  simpa only [coeff_add_four, hasSum_coeffRow.tsum_eq] using he.symm

lemma coeff_positive (n : ℕ) (hn : 4 ≤ n) : 0 < coeff n := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+4 := ⟨n-4, by omega⟩
  simpa only [coeff_add_four] using coeffRow_pos r

lemma predecessor_congruence (n : ℕ) (hn : 4 ≤ n) :
    Nat.ModEq (n-1) (coeff n) 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hd : n-1 ∣ modulus n := by simp [modulus, he]
    exact ((Nat.modEq_iff_dvd' (coeff_positive n hn)).mpr
      (hd.trans (modulus_congruence n hn))).symm
  · exact odd_inherited_congruence n (n-1) hn ho (lambertCoeff_modEq_pred (by omega))

lemma minFac_factorial_congruence (n : ℕ) (hn : 4 ≤ n) :
    Nat.ModEq n.minFac.factorial (coeff n) 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero he
    rw [(Nat.minFac_eq_two_iff n).mpr hd, Nat.factorial_two]
    have hm : 2 ∣ modulus n := by simp [modulus, he]
    exact ((Nat.modEq_iff_dvd' (coeff_positive n hn)).mpr
      (hm.trans (modulus_congruence n hn))).symm
  · exact odd_inherited_congruence n n.minFac.factorial hn ho
      (lambertCoeff_modEq_minFac_factorial (by omega))

lemma prefix_identity (r : ℕ) :
    (∑ k ∈ Finset.range (r+4), (coeff k : ℝ)/k.factorial) =
      (1/6 : ℝ)-normalizedTail r := by
  induction r with
  | zero => norm_num [Finset.sum_range_succ, coeff, normalizedTail, tail]
  | succ r ih =>
      rw [show r+1+4 = (r+4)+1 by omega, Finset.sum_range_succ, ih,
        coeff_add_four, coeffRow_div]
      ring

/-- The recursively constructed positive integers really are the
factorial-scaled tails of the rational comparison series. -/
lemma scaled_tail_identity (r : ℕ) :
    ((r+3).factorial : ℝ) * ((∑' n : ℕ, (coeff n : ℝ)/n.factorial) -
      ∑ k ∈ Finset.range (r+4), (coeff k : ℝ)/k.factorial) = tail r := by
  rw [sum_coeff, prefix_identity, sub_sub_cancel, normalizedTail]
  exact mul_div_cancel₀ _ (by positivity)

lemma different_coefficients : coeff 4 = 1 ∧ lambertCoeff 4 = 7 := by
  decide

/-- These simultaneous congruences are compatible with positive quadratic
tails and a rational total. No assertion about the original sum follows. -/
theorem comparison_properties :
    (∀ n : ℕ, 4 ≤ n → 0 < coeff n) ∧
    (∀ p : ℕ, 4 ≤ p → p.Prime → coeff p = 1) ∧
    (∀ n : ℕ, 4 ≤ n → Nat.ModEq (n-1) (coeff n) 1) ∧
    (∀ n : ℕ, 4 ≤ n → Nat.ModEq n.minFac.factorial (coeff n) 1) ∧
    (∀ n : ℕ, 4 ≤ n → n % 2 = 1 → lambertCoeff n-1 ∣ coeff n-1) ∧
    (∀ r : ℕ, 0 < tail r ∧ tail r < 2*(r+3)^2) ∧
    (∑' n : ℕ, (coeff n : ℝ)/n.factorial) = (1/6 : ℝ) :=
  ⟨coeff_positive, coeff_prime, predecessor_congruence, minFac_factorial_congruence,
    odd_full_congruence, fun r => ⟨tail_pos r, tail_upper r⟩, sum_coeff⟩

end AlternatingModulusComparison

#print axioms AlternatingModulusComparison.sum_coeff
#print axioms AlternatingModulusComparison.scaled_tail_identity
#print axioms AlternatingModulusComparison.minFac_factorial_congruence
#print axioms AlternatingModulusComparison.comparison_properties
