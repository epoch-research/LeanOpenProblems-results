import Submission.LambertDifferenceCheck

/-!
# Prime-index boundary shifts for Lambert-row annihilators

A prime-index difference annihilates every earlier geometric row but changes
an affine boundary by one, without changing its coefficient of the series
value. This is an auxiliary identity, not a settlement of Erdős 68.
-/

namespace PrimeWindowBoundary

open Erdos68Development LambertDifferenceOperators

noncomputable def primeJump (p : ℕ) (r : ℕ → ℝ) : ℝ :=
  (p.factorial : ℝ) * r p -
    (p : ℝ) * ((p - 1).factorial : ℝ) * r (p - 1)

lemma primeJump_eq (p : ℕ) (hp : 0 < p) (r : ℕ → ℝ) :
    primeJump p r = (p.factorial : ℝ) * (r p - r (p - 1)) := by
  have hf : p.factorial = p * (p - 1).factorial := by
    simpa only [Nat.sub_add_cancel hp] using Nat.factorial_succ (p - 1)
  have hfR : (p.factorial : ℝ) = (p : ℝ) * ((p - 1).factorial : ℝ) := by
    exact_mod_cast hf
  unfold primeJump
  rw [hfR]
  ring

lemma primeJump_const (p : ℕ) (hp : 0 < p) (x : ℝ) :
    primeJump p (fun _ => x) = 0 := by
  rw [primeJump_eq p hp]
  simp

lemma div_pred_of_not_dvd (p d : ℕ) (hp : 0 < p) (hd : 0 < d)
    (hnd : ¬ d ∣ p) : (p - 1) / d = p / d := by
  have hm : 0 < p % d := by
    by_contra h
    have he : p % d = 0 := by omega
    exact hnd (Nat.dvd_iff_mod_eq_zero.mpr he)
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel hp
  apply Nat.div_eq_of_lt_le
  · have hh := Nat.div_add_mod p d
    nlinarith
  · have hh := Nat.mod_lt p hd
    have he := Nat.div_add_mod p d
    nlinarith

lemma primeJump_geometricRowTail (p d : ℕ) (hp : p.Prime)
    (hd : 2 ≤ d) (hdp : d < p) :
    primeJump p (geometricRowTail d) = 0 := by
  have hnd : ¬ d ∣ p := by
    intro hh
    have he := (hp.dvd_iff_eq (by omega : d ≠ 1)).mp hh
    omega
  have hdiv := div_pred_of_not_dvd p d hp.pos (by omega) hnd
  rw [primeJump_eq p hp.pos]
  simp only [geometricRowTail, hdiv, sub_self, mul_zero]

lemma prefixQ_succ (n : ℕ) :
    prefixQ (n + 1) = prefixQ n +
      (lambertCoeff (n + 1) : ℚ) / (n + 1).factorial := by
  simp only [prefixQ, Finset.sum_range_succ]

/-- This operation has zero coefficient of `x`, but boundary one. -/
theorem primeJump_affine_tail (p : ℕ) (hp : p.Prime) (x : ℝ) :
    primeJump p (fun n => x - (prefixQ n : ℝ)) = -1 := by
  have hq := prefixQ_succ (p - 1)
  rw [Nat.sub_add_cancel hp.pos, lambertCoeff_prime hp] at hq
  have hqR : (prefixQ p : ℝ) = (prefixQ (p - 1) : ℝ) +
      1 / (p.factorial : ℝ) := by
    have hh := congrArg (fun q : ℚ => (q : ℝ)) hq
    push_cast at hh
    exact hh
  rw [primeJump_eq p hp.pos, hqR]
  have hf : (p.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma add_primeJump_preserves_row (p d : ℕ) (hp : p.Prime)
    (hd : 2 ≤ d) (hdp : d < p) (z : ℤ) (op : (ℕ → ℝ) → ℝ)
    (hop : op (geometricRowTail d) = 0) :
    op (geometricRowTail d) + (z : ℝ) * primeJump p (geometricRowTail d) = 0 := by
  rw [hop, primeJump_geometricRowTail p d hp hd hdp]
  simp

/-- Adding an integral multiple of the prime-index difference permits an
arbitrary integral boundary shift without changing the coefficient `A`.
The preceding lemma shows that all rows below `p` remain annihilated. -/
theorem shift_affine_boundary (p : ℕ) (hp : p.Prime) (A B z : ℤ)
    (op : (ℕ → ℝ) → ℝ)
    (hop : ∀ x : ℝ, op (fun n => x - (prefixQ n : ℝ)) = (A : ℝ) * x - B)
    (x : ℝ) :
    op (fun n => x - (prefixQ n : ℝ)) +
        (z : ℝ) * primeJump p (fun n => x - (prefixQ n : ℝ)) =
      (A : ℝ) * x - ((B + z : ℤ) : ℝ) := by
  rw [hop, primeJump_affine_tail p hp]
  push_cast
  ring

#print axioms primeJump_geometricRowTail
#print axioms primeJump_affine_tail
#print axioms shift_affine_boundary

end PrimeWindowBoundary
