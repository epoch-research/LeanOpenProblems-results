import Submission.LambertMinFactorCongruence
import Submission.LambertPrimeBand

/-!
A different, rational factorial series preserving every congruence of the
Lambert coefficients to one. This is NOT the coefficient sequence or the
series in Spec.lean, and is not a disproof of that conjecture.
-/

namespace LambertCongruenceComparison

open Erdos68Development Filter
open scoped Topology

/-- `tail r` is the integral tail at original index r+3. -/
def tail : ℕ → ℕ
  | 0 => 1
  | r+1 => 1 + ((r+4)*tail r-2) % (lambertCoeff (r+4)-1)

def coeffRow (r : ℕ) : ℕ := (r+4)*tail r-tail (r+1)

def coeff (n : ℕ) : ℕ := if n < 4 then 0 else coeffRow (n-4)

lemma tail_pos (r : ℕ) : 0 < tail r := by cases r <;> simp [tail]

lemma tail_succ_le (r : ℕ) : tail (r+1) ≤ (r+4)*tail r-1 := by
  have hp := tail_pos r
  have hm := Nat.mod_le ((r+4)*tail r-2) (lambertCoeff (r+4)-1)
  have ht : 4 ≤ (r+4)*tail r := by nlinarith
  simp only [tail]
  omega

lemma coeffRow_formula (r : ℕ) :
    coeffRow r = 1 + (lambertCoeff (r+4)-1) *
      (((r+4)*tail r-2) / (lambertCoeff (r+4)-1)) := by
  have hp := tail_pos r
  have ht : 4 ≤ (r+4)*tail r := by nlinarith
  have hd := Nat.mod_add_div ((r+4)*tail r-2) (lambertCoeff (r+4)-1)
  simp only [coeffRow, tail]
  omega

lemma coeffRow_pos (r : ℕ) : 0 < coeffRow r := by rw [coeffRow_formula]; omega

lemma coeff_add_four (r : ℕ) : coeff (r+4) = coeffRow r := by simp [coeff]

lemma coeff_prime (p : ℕ) (hp4 : 4 ≤ p) (hp : p.Prime) : coeff p = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r+4 := ⟨p-4, by omega⟩
  rw [coeff_add_four, coeffRow_formula, lambertCoeff_prime hp]
  simp

/-- The comparison coefficient is one modulo the ENTIRE original
coefficient minus one, not just the previously known smaller moduli. -/
lemma full_congruence (n : ℕ) (hn : 4 ≤ n) :
    lambertCoeff n-1 ∣ coeff n-1 := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r+4 := ⟨n-4, by omega⟩
  rw [coeff_add_four, coeffRow_formula]
  simp

lemma inherited_congruence (n m : ℕ) (hn : 4 ≤ n)
    (h : Nat.ModEq m (lambertCoeff n) 1) : Nat.ModEq m (coeff n) 1 := by
  have ha := lambertCoeff_one_le (show 2 ≤ n by omega)
  have hc : 1 ≤ coeff n := by
    obtain ⟨r, rfl⟩ : ∃ r, n = r+4 := ⟨n-4, by omega⟩
    simpa only [coeff_add_four] using coeffRow_pos r
  have hm : m ∣ lambertCoeff n-1 := (Nat.modEq_iff_dvd' ha).mp h.symm
  exact ((Nat.modEq_iff_dvd' hc).mpr (hm.trans (full_congruence n hn))).symm

lemma lambert_even_ge_two (n : ℕ) (hn : 4 ≤ n) (he : n % 2 = 0) :
    2 ≤ lambertCoeff n := by
  have hn' : n = 2*(n/2-2+2) := by omega
  have h := lambertCoeff_even_ge (n/2-2)
  rw [← hn'] at h
  omega

lemma tail_le_at_nonunit (r : ℕ) (hr : 0 < r)
    (ha : 2 ≤ lambertCoeff (r+3)) : tail r ≤ lambertCoeff (r+3) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hm := Nat.mod_lt ((s+4)*tail s-2)
    (show 0 < lambertCoeff (s+4)-1 by simpa only [Nat.add_assoc] using Nat.sub_pos_of_lt ha)
  simp only [tail]
  simpa only [Nat.add_assoc] using (show 1 + ((s+4)*tail s-2) %
    (lambertCoeff (s+4)-1) ≤ lambertCoeff (s+4) by omega)

lemma tail_upper (r : ℕ) (hr : 2 ≤ r) :
    tail r ≤ lambertCoeff (r+3) + (r+3)*lambertCoeff (r+2) := by
  rcases Nat.mod_two_eq_zero_or_one (r+3) with he | ho
  · exact (tail_le_at_nonunit r (by omega)
      (lambert_even_ge_two (r+3) (by omega) he)).trans (Nat.le_add_right _ _)
  · have hp : (r+2) % 2 = 0 := by omega
    have ht : tail (r-1) ≤ lambertCoeff (r+2) := by
      simpa only [show r-1+3 = r+2 by omega] using
        tail_le_at_nonunit (r-1) (by omega)
          (by simpa only [show r-1+3 = r+2 by omega] using
            lambert_even_ge_two (r+2) (by omega) hp)
    have hs := tail_succ_le (r-1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r), show r-1+4 = r+3 by omega] at hs
    have hh := Nat.mul_le_mul_left (r+3) ht
    omega

noncomputable def normalizedTail (r : ℕ) : ℝ := (tail r : ℝ)/(r+3).factorial

lemma summable_normalizedTail : Summable normalizedTail := by
  have hs3 := (summable_nat_add_iff 3).mpr summable_factorial_lambert
  have hs2 := (summable_nat_add_iff 2).mpr summable_factorial_lambert
  apply (hs3.add hs2).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 2] with r hr
  have h := tail_upper r hr
  have hf : (0 : ℝ) < (r+3).factorial := by positivity
  have hf2 : ((r+2).factorial : ℝ) ≠ 0 := by positivity
  have hn : (r+3 : ℝ) ≠ 0 := by positivity
  dsimp only [normalizedTail]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((lambertCoeff (r+3) : ℝ) + (r+3 : ℝ)*lambertCoeff (r+2))/(r+3).factorial := by
      apply div_le_div_of_nonneg_right _ hf.le
      exact_mod_cast h
    _ = _ := by
      rw [show r+3 = (r+2)+1 by omega, Nat.factorial_succ]
      push_cast
      field_simp
      ring

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
    Nat.ModEq (n-1) (coeff n) 1 :=
  inherited_congruence n (n-1) hn (lambertCoeff_modEq_pred (by omega))

lemma minFac_factorial_congruence (n : ℕ) (hn : 4 ≤ n) :
    Nat.ModEq n.minFac.factorial (coeff n) 1 :=
  inherited_congruence n n.minFac.factorial hn
    (lambertCoeff_modEq_minFac_factorial (by omega))

lemma prime_band_congruence (n : ℕ) (hn : 4 ≤ n) :
    Nat.ModEq (primeBandProduct n) (coeff n) 1 := by
  apply Nat.ModEq.symm
  apply (Nat.modEq_iff_dvd' (coeff_positive n hn)).mpr
  exact (primeBandProduct_dvd_lambertCoeff_sub_one n).trans (full_congruence n hn)

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

/-- All previously used coefficient-to-one congruences and prime-unit
values hold for this different positive sequence, whose total is rational. -/
theorem comparison_properties :
    (∀ n : ℕ, 4 ≤ n → 0 < coeff n) ∧
    (∀ n : ℕ, 4 ≤ n → lambertCoeff n-1 ∣ coeff n-1) ∧
    (∀ p : ℕ, 4 ≤ p → p.Prime → coeff p = 1) ∧
    (∀ n : ℕ, 4 ≤ n → Nat.ModEq (n-1) (coeff n) 1) ∧
    (∀ n : ℕ, 4 ≤ n → Nat.ModEq n.minFac.factorial (coeff n) 1) ∧
    (∀ n : ℕ, 4 ≤ n → Nat.ModEq (primeBandProduct n) (coeff n) 1) ∧
    (∑' n : ℕ, (coeff n : ℝ)/n.factorial) = (1/6 : ℝ) :=
  ⟨coeff_positive, full_congruence, coeff_prime, predecessor_congruence,
    minFac_factorial_congruence, prime_band_congruence, sum_coeff⟩

end LambertCongruenceComparison

#print axioms LambertCongruenceComparison.full_congruence
#print axioms LambertCongruenceComparison.inherited_congruence
#print axioms LambertCongruenceComparison.coeff_prime
#print axioms LambertCongruenceComparison.sum_coeff

#print axioms LambertCongruenceComparison.comparison_properties
#print axioms LambertCongruenceComparison.scaled_tail_identity
