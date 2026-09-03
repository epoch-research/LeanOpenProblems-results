import Submission.RealChain

/-! Positive finite-tail refinement for exact-retention compression.
The scalar values may be signed; the weights in a refinement are nonnegative. -/
namespace Erdos7FiniteRetainedMixture
open scoped BigOperators
open Erdos7RealChain
set_option maxHeartbeats 1000000

noncomputable def mixture (h : ℝ) (q f : ℕ → ℝ) (R : ℕ) : ℝ :=
  h*f 0 + ∑ j ∈ Finset.range R, q j*(f (j+1)-f j)

lemma mixture_positive_form (h : ℝ) (q f : ℕ → ℝ) (R : ℕ) :
    mixture h q f R = (h-q 0)*f 0 +
      (∑ j ∈ Finset.range R, (q j-q (j+1))*f (j+1)) + q R*f R := by
  have hh := chain_summation_by_parts f q R
  dsimp only [mixture]
  linarith

/-- Increasing the finite exponent cap moves the terminal mass to larger
arguments. This comparison does not require nonnegative scalar values. -/
lemma mixture_monotone (h : ℝ) (q f : ℕ → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hf : Monotone f) : Monotone (mixture h q f) := by
  intro R T hRT
  apply add_le_add_right
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hRT)
  intro j _ _
  exact mul_nonneg (hq j) (sub_nonneg.mpr (hf (Nat.le_succ j)))

/-- The extra mass at a truncation endpoint can be replaced by any positive
finite refinement of the same mass at larger scalar values. -/
lemma tail_atom_refinement {ι : Type*} (S : Finset ι) (w y : ι → ℝ)
    (mass x : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hmass : (∑ i ∈ S, w i) = mass) (hy : ∀ i ∈ S, x ≤ y i) :
    mass*x ≤ ∑ i ∈ S, w i*y i := by
  rw [← hmass, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hy i hi) (hw i hi))

/-- Refinement of normalized complete-family counts only uses monotonicity
of the test. Convexity is needed earlier for the chain bound, not here. -/
lemma test_tail_atom_refinement {ι : Type*} (S : Finset ι) (w d : ι → ℝ)
    (mass D n : ℝ) (hn : 0 ≤ n) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hmass : (∑ i ∈ S, w i) = mass) (hd : ∀ i ∈ S, D ≤ d i)
    (φ : ℝ → ℝ) (hmφ : Monotone φ) :
    mass*φ (D*n) ≤ ∑ i ∈ S, w i*φ (d i*n) :=
  tail_atom_refinement S w (fun i => φ (d i*n)) mass (φ (D*n)) hw hmass
    (fun i hi => hmφ (mul_le_mul_of_nonneg_right (hd i hi) hn))

/-- The infinite increment expression, when summable, dominates every finite
cap. Nonnegative increments, rather than a positive comparison law, justify
this passage. -/
lemma mixture_le_infinite (h : ℝ) (q f : ℕ → ℝ)
    (hq : ∀ j, 0 ≤ q j) (hf : Monotone f)
    (hs : Summable (fun j => q j*(f (j+1)-f j))) (R : ℕ) :
    mixture h q f R ≤ h*f 0 + ∑' j, q j*(f (j+1)-f j) := by
  apply add_le_add_right
  exact Summable.sum_le_tsum (Finset.range R)
    (fun j _ => mul_nonneg (hq j) (sub_nonneg.mpr (hf (Nat.le_succ j)))) hs

#print axioms mixture_monotone
#print axioms test_tail_atom_refinement
#print axioms mixture_le_infinite
end Erdos7FiniteRetainedMixture
