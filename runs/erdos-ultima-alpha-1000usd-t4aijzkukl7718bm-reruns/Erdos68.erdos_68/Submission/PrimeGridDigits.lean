import Submission.PrimeBoundaryLifting

/-!
Factorial-grid digits for a correction distributed across prime increments.
Auxiliary arithmetic only: this does not settle the conjecture in Spec.lean.
-/

namespace PrimeGridDigits

open Finset PrimeBoundaryLifting PrimeLeadingForms Erdos68Development

/-- The ratio of two consecutive factorial grids. -/
def radix (p : ℕ → ℕ) (n : ℕ) : ℕ := (p (n+1)).factorial/(p n).factorial

def gridFloor (p : ℕ → ℕ) (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(p n).factorial*x⌋

def digit (p : ℕ → ℕ) (x : ℚ) : ℕ → ℤ
  | 0 => gridFloor p x 0
  | n+1 => gridFloor p x (n+1)-(radix p n : ℤ)*gridFloor p x n

lemma radix_identity (p : ℕ → ℕ) (hp : Monotone p) (n : ℕ) :
    (p (n+1)).factorial = radix p n*(p n).factorial := by
  exact (Nat.div_mul_cancel (Nat.factorial_dvd_factorial (hp (by omega)))).symm

lemma radix_pos (p : ℕ → ℕ) (hp : Monotone p) (n : ℕ) : 0 < radix p n := by
  have h := Nat.factorial_pos (p (n+1))
  rw [radix_identity p hp n] at h
  by_contra hn
  have hz : radix p n = 0 := by omega
  simp only [hz, zero_mul, lt_self_iff_false] at h

lemma next_floor_div (p : ℕ → ℕ) (hp : Monotone p) (x : ℚ) (n : ℕ) :
    gridFloor p x (n+1)/(radix p n : ℤ) = gridFloor p x n := by
  unfold gridFloor
  rw [radix_identity p hp n, Nat.cast_mul, mul_assoc]
  exact Int.natCast_mul_floor_div_cancel (Nat.ne_of_gt (radix_pos p hp n)) _

/-- Every digit after the first is an ordinary bounded radix digit. -/
theorem digit_succ_bounds (p : ℕ → ℕ) (hp : Monotone p) (x : ℚ) (n : ℕ) :
    0 ≤ digit p x (n+1) ∧ digit p x (n+1) < radix p n := by
  have hr : (0 : ℤ) < radix p n := by exact_mod_cast radix_pos p hp n
  have hd : digit p x (n+1) = gridFloor p x (n+1) % (radix p n : ℤ) := by
    rw [digit, ← next_floor_div p hp x n]
    have h := Int.emod_add_mul_ediv (gridFloor p x (n+1)) (radix p n)
    omega
  rw [hd]
  exact ⟨Int.emod_nonneg _ (ne_of_gt hr), Int.emod_lt_of_pos _ hr⟩

/-- Telescoping holds before any exact-grid or primality assumption. -/
theorem sum_digits (p : ℕ → ℕ) (hp : Monotone p) (x : ℚ) (m : ℕ) :
    (∑ i ∈ range (m+1), (digit p x i : ℚ)/(p i).factorial) =
      (gridFloor p x m : ℚ)/(p m).factorial := by
  induction m with
  | zero => simp [digit]
  | succ m ih =>
    rw [show m+1+1=(m+1)+1 by omega, sum_range_succ, ih, digit]
    push_cast
    have hfac : ((p m).factorial : ℚ) ≠ 0 := by positivity
    have hr : (radix p m : ℚ) ≠ 0 := by exact_mod_cast (radix_pos p hp m).ne'
    rw [radix_identity p hp m, Nat.cast_mul]
    field_simp
    ring

/-- Exact representation of any point on the final factorial grid. -/
theorem sum_digits_exact (p : ℕ → ℕ) (hp : Monotone p) (x : ℚ) (m : ℕ)
    (hx : ∃ z : ℤ, ((p m).factorial : ℚ)*x=z) :
    (∑ i ∈ range (m+1), (digit p x i : ℚ)/(p i).factorial) = x := by
  obtain ⟨z, hz⟩ := hx
  rw [sum_digits p hp, gridFloor, hz, Int.floor_intCast]
  have hfac : ((p m).factorial : ℚ) ≠ 0 := by positivity
  rw [← hz]
  field_simp

lemma first_digit_bounds (p : ℕ → ℕ) (x : ℚ) :
    ((p 0).factorial : ℚ)*x-1 < digit p x 0 ∧
      (digit p x 0 : ℚ) ≤ ((p 0).factorial : ℚ)*x := by
  constructor
  · have h := Int.lt_floor_add_one (((p 0).factorial : ℚ)*x)
    change ((p 0).factorial : ℚ)*x-1 < (⌊((p 0).factorial : ℚ)*x⌋ : ℚ)
    linarith
  · exact Int.floor_le _

lemma digits_nonneg (p : ℕ → ℕ) (hp : Monotone p) (x : ℚ) (hx : 0 ≤ x) :
    ∀ i, 0 ≤ digit p x i := by
  intro i
  cases i with
  | zero => exact Int.floor_nonneg.mpr (mul_nonneg (by positivity) hx)
  | succ i => exact (digit_succ_bounds p hp x i).1

/-- A small nonnegative correction has no digits on any earlier coarser grid. -/
theorem early_digits_zero (p : ℕ → ℕ) (hp : Monotone p) (x : ℚ)
    (hx : 0 ≤ x) (j : ℕ) (hj : ((p j).factorial : ℚ)*x < 1) :
    ∀ i ≤ j, digit p x i = 0 := by
  have hf (i : ℕ) (hi : i ≤ j) : gridFloor p x i = 0 := by
    apply Int.floor_eq_zero_iff.mpr
    constructor
    · exact mul_nonneg (by positivity) hx
    · have hfac : ((p i).factorial : ℚ) ≤ (p j).factorial := by
        exact_mod_cast Nat.factorial_le (hp hi)
      exact (mul_le_mul_of_nonneg_right hfac hx).trans_lt hj
  intro i hi
  cases i with
  | zero => exact hf 0 hi
  | succ i => rw [digit, hf (i+1) hi, hf i (by omega), mul_zero, sub_self]

/-- For a nonnegative correction there is no cancellation between the digits:
the sum of their individual absolute boundary changes is exactly the correction. -/
theorem absolute_boundary_cost (p : ℕ → ℕ) (hp : Monotone p) (x : ℚ)
    (hx : 0 ≤ x) (m : ℕ) (hgrid : ∃ z : ℤ, ((p m).factorial : ℚ)*x=z) :
    (∑ i ∈ range (m+1), |(digit p x i : ℚ)/(p i).factorial|) = x := by
  calc
    _ = ∑ i ∈ range (m+1), (digit p x i : ℚ)/(p i).factorial := by
      apply sum_congr rfl
      intro i _
      apply abs_of_nonneg
      apply div_nonneg _ (by positivity)
      exact_mod_cast digits_nonneg p hp x hx i
    _ = x := sum_digits_exact p hp x m hgrid

/-- A distributed correction, expressed as a linear operation on a prefix. -/
def correction (p : ℕ → ℕ) (x : ℚ) (m : ℕ) (f : ℕ → ℚ) : ℚ :=
  ∑ i ∈ range (m+1), (digit p x i : ℚ)*(f (p i)-f (p i-1))

lemma correction_const (p : ℕ → ℕ) (x : ℚ) (m : ℕ) (a : ℚ) :
    correction p x m (fun _ => a) = 0 := by
  simp [correction]

/-- Unit coefficients make the distributed correction exactly the prescribed value. -/
theorem correction_partialSum (p : ℕ → ℕ) (hp : Monotone p)
    (c : ℕ → ℤ) (x : ℚ) (m : ℕ)
    (hpos : ∀ i ≤ m, 0 < p i) (hc : ∀ i ≤ m, c (p i)=1)
    (hx : ∃ z : ℤ, ((p m).factorial : ℚ)*x=z) :
    correction p x m (partialSum c) = x := by
  rw [correction]
  calc
    _ = ∑ i ∈ range (m+1), (digit p x i : ℚ)/(p i).factorial := by
      apply sum_congr rfl
      intro i hi
      have hi' : i ≤ m := by have := mem_range.mp hi; omega
      rw [partialSum_step c (p i) (hpos i hi'), hc i hi']
      simp only [Int.cast_one, add_sub_cancel_left, mul_one_div]
    _ = x := sum_digits_exact p hp x m hx

/-- All selected prime increments preserve every row below the first prime. -/
theorem correction_row_zero (p : ℕ → ℕ) (hp : Monotone p)
    (x : ℚ) (m : ℕ) (hprime : ∀ i ≤ m, (p i).Prime)
    (d : ℕ) (hd : 2 ≤ d) (hdp : d < p 0) :
    correction p x m
      (fun n => (1 : ℚ)/((d.factorial : ℚ)^(n/d)*(d.factorial-1))) = 0 := by
  apply sum_eq_zero
  intro i hi
  have hi' : i ≤ m := by have := mem_range.mp hi; omega
  have h := prime_row_constant (hprime i hi') hd (hdp.trans_le (hp (by omega)))
  dsimp only
  rw [h, sub_self, mul_zero]

/-- The preceding identities apply to the exact original Lambert prefixes. -/
theorem lambert_correction (p : ℕ → ℕ) (hp : Monotone p)
    (x : ℚ) (m : ℕ) (hprime : ∀ i ≤ m, (p i).Prime)
    (hx : ∃ z : ℤ, ((p m).factorial : ℚ)*x=z) :
    correction p x m (partialSum (fun n => (lambertCoeff n : ℤ))) = x ∧
    correction p x m (fun _ => (1 : ℚ)) = 0 ∧
    ∀ d, 2 ≤ d → d < p 0 →
      correction p x m
        (fun n => (1 : ℚ)/((d.factorial : ℚ)^(n/d)*(d.factorial-1))) = 0 := by
  refine ⟨?_, correction_const p x m 1, ?_⟩
  · apply correction_partialSum p hp _ x m
      (fun i hi => (hprime i hi).pos) _ hx
    intro i hi
    simp only [lambertCoeff_prime (hprime i hi), Nat.cast_one]
  · exact fun d hd hdp => correction_row_zero p hp x m hprime d hd hdp

end PrimeGridDigits

#print axioms PrimeGridDigits.digit_succ_bounds
#print axioms PrimeGridDigits.sum_digits_exact
#print axioms PrimeGridDigits.early_digits_zero
#print axioms PrimeGridDigits.absolute_boundary_cost
#print axioms PrimeGridDigits.lambert_correction
