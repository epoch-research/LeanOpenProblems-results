import Submission.LambertPrimePowerScaling
import Submission.LambertDifferenceOperators

/-!
Prime congruences of the binomially filtered Lambert coefficients.
These are exact row-cancellation coefficients, not small-tail carries.
This file does not settle Erdos 68.
-/

namespace BinomialFilteredLambert

open Erdos68Development LambertDifferenceOperators LambertPrimePowerScaling

/-- Multiplication of the exponential generating series by `1-z^k/k!`. -/
def filterStep (k : ℕ) (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  a n - (n.choose k : ℤ)*a (n-k)

def filterSteps : List ℕ → (ℕ → ℤ) → (ℕ → ℤ)
  | [], a => a
  | k::ks, a => filterStep k (filterSteps ks a)

def filtered (ks : List ℕ) : ℕ → ℤ :=
  filterSteps ks (fun n => (lambertCoeff n : ℤ))

lemma filterStep_modEq (p k n : ℕ) (a : ℕ → ℤ) (hk : p ∣ n.choose k) :
    Int.ModEq p (filterStep k a n) (a n) := by
  have hc : Int.ModEq p (n.choose k : ℤ) 0 :=
    Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast hk)
  simpa only [filterStep, zero_mul, sub_zero] using
    (Int.ModEq.refl (a n)).sub (hc.mul_right (a (n-k)))

lemma filterSteps_modEq (ks : List ℕ) (p n : ℕ) (a : ℕ → ℤ)
    (hks : ∀ k ∈ ks, p ∣ n.choose k) :
    Int.ModEq p (filterSteps ks a n) (a n) := by
  induction ks with
  | nil => exact Int.ModEq.refl _
  | cons k ks ih =>
    exact (filterStep_modEq p k n (filterSteps ks a) (hks k (by simp))).trans
      (ih (fun j hj => hks j (by simp [hj])))

/-- At a prime power larger than every filter degree, the filtered coefficient
is still one modulo that prime. Its exact value need not be one. -/
theorem filtered_prime_power (ks : List ℕ) (p r : ℕ) (hp : p.Prime)
    (hks : ∀ k ∈ ks, 0 < k ∧ k < p^(r+1)) :
    Int.ModEq p (filtered ks (p^(r+1))) 1 := by
  have hf := filterSteps_modEq ks p (p^(r+1)) (fun n => (lambertCoeff n : ℤ))
    (fun k hk => hp.dvd_choose_pow (hks k hk).1.ne' (ne_of_lt (hks k hk).2))
  apply hf.trans
  exact Int.natCast_modEq_iff.mpr (lambertCoeff_prime_power_modEq_one p r hp)

lemma choose_dvd_at_pred (p n k : ℕ) (hp : p.Prime) (hn : 2 ≤ n)
    (hpn : p ∣ n-1) (hk : 2 ≤ k) (hkp : k < p) : p ∣ n.choose k := by
  letI : Fact p.Prime := ⟨hp⟩
  have he : Nat.ModEq p 1 n := (Nat.modEq_iff_dvd' (by omega : 1 ≤ n)).mpr hpn
  have hnmod : n % p = 1 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using he.symm
  have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := p) (n := n) (k := k)
  have hz : Nat.ModEq p (n.choose k) 0 := by
    simpa only [hnmod, Nat.mod_eq_of_lt hkp,
      Nat.choose_eq_zero_of_lt (by omega : 1 < k), zero_mul] using hl
  exact Nat.modEq_zero_iff_dvd.mp hz

/-- The predecessor congruence survives modulo primes larger than all filter
degrees. No analogous assertion is made here for the small prime factors. -/
theorem filtered_at_pred (ks : List ℕ) (p n : ℕ) (hp : p.Prime)
    (hn : 2 ≤ n) (hpn : p ∣ n-1)
    (hks : ∀ k ∈ ks, 2 ≤ k ∧ k < p) :
    Int.ModEq p (filtered ks n) 1 := by
  have hf := filterSteps_modEq ks p n (fun n => (lambertCoeff n : ℤ))
    (fun k hk => choose_dvd_at_pred p n k hp hn hpn (hks k hk).1 (hks k hk).2)
  apply hf.trans
  exact Int.natCast_modEq_iff.mpr ((lambertCoeff_modEq_pred hn).of_dvd hpn)

lemma rowShift_applyShifts (k : ℕ) (ks : List ℕ) (r : ℕ → ℝ) :
    rowShift k (applyShifts ks r) = applyShifts ks (rowShift k r) := by
  induction ks generalizing r with
  | nil => rfl
  | cons j ks ih =>
    simp only [applyShifts]
    rw [ih, rowShift_commute]

/-- This identifies the filtered coefficients with the factorial-scaled
normalized row-cancelling operator, not just a formal generating series. -/
theorem filterSteps_scaled_identity (ks : List ℕ) (a : ℕ → ℤ) (n : ℕ) :
    ((n+ks.sum).factorial : ℝ)*
      applyShifts ks (fun m => (a m : ℝ)/m.factorial) n =
      (filterSteps ks a (n+ks.sum) : ℤ) := by
  induction ks generalizing n with
  | nil =>
    simp only [List.sum_nil, Nat.add_zero, applyShifts, filterSteps]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  | cons k ks ih =>
    rw [applyShifts, ← rowShift_applyShifts]
    rw [List.sum_cons, show n+(k+ks.sum)=n+ks.sum+k by omega, scaled_rowShift]
    rw [ih (n+k), mul_assoc, ih n]
    simp only [filterSteps, filterStep]
    push_cast
    rw [show n+ks.sum+k-k=n+ks.sum by omega,
      show n+k+ks.sum=n+ks.sum+k by omega]

/-- The preceding arithmetic therefore applies to the actual normalized
Lambert coefficient operator used in row cancellation. -/
theorem filtered_lambert_scaled_identity (ks : List ℕ) (n : ℕ) :
    ((n+ks.sum).factorial : ℝ)*
      applyShifts ks (fun m => (lambertCoeff m : ℝ)/m.factorial) n =
      (filtered ks (n+ks.sum) : ℝ) := by
  simpa only [filtered, Int.cast_natCast] using
    filterSteps_scaled_identity ks (fun m => (lambertCoeff m : ℤ)) n

end BinomialFilteredLambert

#print axioms BinomialFilteredLambert.filtered_prime_power
#print axioms BinomialFilteredLambert.filtered_at_pred
#print axioms BinomialFilteredLambert.filtered_lambert_scaled_identity
