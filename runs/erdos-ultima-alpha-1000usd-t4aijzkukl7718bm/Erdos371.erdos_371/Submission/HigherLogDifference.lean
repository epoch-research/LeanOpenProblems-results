import Submission.PolynomialMultiplierChirpExclusion

/-! Positive higher differences of log, with an explicit reciprocal-product
integral. These estimates will distinguish polynomial-range stability from
fixed-multiplier stability in the chirp countermodel. -/
namespace Erdos371.HigherChirp
open Finset Filter MeasureTheory
open scoped Topology
set_option autoImplicit false

noncomputable def ascendingProduct (r : ℕ) (x : ℝ) : ℝ := ∏ j ∈ range r, (x+j)

lemma ascendingProduct_pos (r : ℕ) (x : ℝ) (hx : 0<x) : 0<ascendingProduct r x := by
  apply prod_pos
  intro j _
  exact add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg j)

lemma ascendingProduct_succ (r : ℕ) (x : ℝ) :
    ascendingProduct (r+1) x=ascendingProduct r x*(x+r) := prod_range_succ _ _

lemma ascendingProduct_shift (r : ℕ) (x : ℝ) :
    ascendingProduct (r+1) x=ascendingProduct r (x+1)*x := by
  rw [ascendingProduct,prod_range_succ']
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero]
  congr 1
  apply prod_congr rfl
  intro j _
  ring

noncomputable def reciprocalDifferenceKernel (r : ℕ) (x : ℝ) : ℝ :=
  (r.factorial : ℝ)/ascendingProduct (r+1) x

lemma reciprocalDifferenceKernel_sub (r : ℕ) (x : ℝ) (hx : 0<x) :
    reciprocalDifferenceKernel r x-reciprocalDifferenceKernel r (x+1)=
      reciprocalDifferenceKernel (r+1) x := by
  have hA := (ascendingProduct_pos (r+1) x hx).ne'
  have hB := (ascendingProduct_pos (r+1) (x+1) (by linarith)).ne'
  have hC := (ascendingProduct_pos (r+2) x hx).ne'
  have he1 := ascendingProduct_succ (r+1) x
  have he2 := ascendingProduct_shift (r+1) x
  have heA : (r.factorial : ℝ)/ascendingProduct (r+1) x =
      (r.factorial : ℝ)*(x+(r+1))/ascendingProduct (r+2) x := by
    rw [he1]
    field_simp
    push_cast
    ring
  have heB : (r.factorial : ℝ)/ascendingProduct (r+1) (x+1) =
      (r.factorial : ℝ)*x/ascendingProduct (r+2) x := by
    rw [he2]
    field_simp
  unfold reciprocalDifferenceKernel
  rw [heA,heB,Nat.factorial_succ]
  push_cast
  ring

lemma reciprocalDifferenceKernel_intervalIntegrable (r : ℕ) (x : ℝ) (hx : 0<x) :
    IntervalIntegrable (fun t => reciprocalDifferenceKernel r (x+t)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · unfold ascendingProduct
    fun_prop
  · intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    exact (ascendingProduct_pos (r+1) (x+t) (by linarith [ht.1])).ne'

noncomputable def positiveLogDifference : ℕ → ℝ → ℝ
  | 0, x => Real.log (x+1)-Real.log x
  | r+1, x => positiveLogDifference r x-positiveLogDifference r (x+1)

lemma positiveLogDifference_integral (r : ℕ) (x : ℝ) (hx : 0<x) :
    positiveLogDifference r x=∫ t in (0 : ℝ)..1, reciprocalDifferenceKernel r (x+t) := by
  induction r generalizing x with
  | zero =>
    simp only [positiveLogDifference,reciprocalDifferenceKernel,Nat.factorial_zero,Nat.cast_one,
      ascendingProduct,Nat.zero_add,prod_range_one,Nat.cast_zero,add_zero]
    rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => 1/t) x]
    simp only [add_zero]
    rw [integral_one_div_of_pos hx (by linarith),Real.log_div (by linarith) hx.ne']
  | succ r ih =>
    rw [positiveLogDifference,ih x hx,ih (x+1) (by linarith),
      ← intervalIntegral.integral_sub (reciprocalDifferenceKernel_intervalIntegrable r x hx)
        (reciprocalDifferenceKernel_intervalIntegrable r (x+1) (by linarith))]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    dsimp only
    rw [show x+1+t=x+t+1 by ring,reciprocalDifferenceKernel_sub r (x+t) (by linarith [ht.1])]

lemma reciprocalDifferenceKernel_bounds (r : ℕ) (x t : ℝ) (hx : 0<x) (ht0 : 0≤t) (ht1 : t≤1) :
    (r.factorial : ℝ)/(x+r+1)^(r+1) ≤ reciprocalDifferenceKernel r (x+t) ∧
      reciprocalDifferenceKernel r (x+t) ≤ (r.factorial : ℝ)/x^(r+1) := by
  have hp := ascendingProduct_pos (r+1) (x+t) (by linarith)
  have hlo : x^(r+1)≤ascendingProduct (r+1) (x+t) := by
    calc
      _ = ∏ _j ∈ range (r+1), x := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro j _; exact hx.le
        · intro j _; dsimp; have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hhi : ascendingProduct (r+1) (x+t)≤(x+r+1)^(r+1) := by
    calc
      _ ≤ ∏ _j ∈ range (r+1), (x+r+1) := by
        apply Finset.prod_le_prod
        · intro j _; dsimp; positivity
        · intro j hj
          have hjr : (j : ℝ)≤r := by exact_mod_cast (show j≤r by have := mem_range.mp hj; omega)
          linarith
      _ = _ := by simp
  exact ⟨div_le_div_of_nonneg_left (Nat.cast_nonneg _) hp hhi,
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hx _) hlo⟩

/-- The r+1-st alternating forward difference of log is positive and has
its expected factorial / x^(r+1) scale. -/
theorem positiveLogDifference_bounds (r : ℕ) (x : ℝ) (hx : 0<x) :
    (r.factorial : ℝ)/(x+r+1)^(r+1) ≤ positiveLogDifference r x ∧
      positiveLogDifference r x ≤ (r.factorial : ℝ)/x^(r+1) := by
  rw [positiveLogDifference_integral r x hx]
  have hi := reciprocalDifferenceKernel_intervalIntegrable r x hx
  constructor
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ)≤1)
      intervalIntegrable_const hi (fun t ht => (reciprocalDifferenceKernel_bounds r x t hx ht.1 ht.2).1)
    simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using h
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ)≤1)
      hi intervalIntegrable_const (fun t ht => (reciprocalDifferenceKernel_bounds r x t hx ht.1 ht.2).2)
    simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using h

#print axioms positiveLogDifference_bounds
end Erdos371.HigherChirp
