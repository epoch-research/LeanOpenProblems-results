import Submission.RectangularVarianceIteration

/-! A one-sided version of the rectangular variance proposal. Its uniform
bound remains an explicit premise in this file. The positive row deviations
alone imply an upper discrepancy bound for rough-number counts. -/
namespace Erdos970.GapAverages
open Finset Real Filter Erdos970.Resampling
open scoped Topology

noncomputable def positiveRowVariance (P : Finset ℕ) (m p : ℕ) (r : Phase P) : ℝ :=
  residueMean p (fun a => max (rowCount P m p a r - intervalCount P m r / p) 0 ^ 2)

def UniformPositiveRectangularCubeBound (C : ℝ) : Prop :=
  ∀ (P : Finset ℕ) (_hP : ∀ q ∈ P, q.Prime) (p : ℕ), p.Prime →
    (∀ q ∈ P, q < p) → ∀ n : ℕ, p ≤ n → ∀ r : Phase P,
      positiveRowVariance P (p*n) p r ^ 3 ≤ C * (n : ℝ)^4

lemma UniformPositiveRectangularCubeBound.mono {C D : ℝ}
    (hC : UniformPositiveRectangularCubeBound C) (hCD : C ≤ D) :
    UniformPositiveRectangularCubeBound D := by
  intro P hP p hp hlt n hn r
  exact (hC P hP p hp hlt n hn r).trans
    (mul_le_mul_of_nonneg_right hCD (by positivity))

lemma positive_row_deviation_sq_le (P : Finset ℕ) (m p : ℕ) (hp : 0 < p)
    (r : Phase P) (a : Fin p) :
    max (rowCount P m p a r - intervalCount P m r / p) 0 ^ 2 ≤
      (p : ℝ) * positiveRowVariance P m p r := by
  have hh := single_le_sum (s := (univ : Finset (Fin p)))
    (f := fun a => max (rowCount P m p a r - intervalCount P m r / p) 0 ^ 2)
    (fun a _ => sq_nonneg _) (mem_univ a)
  unfold positiveRowVariance residueMean
  rw [mul_div_cancel₀ _ (by exact_mod_cast hp.ne')]
  exact hh

lemma roughCount_positive_gap_sixth_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (n p : ℕ) (hp : 0 < p) (hc : ∀ q ∈ P, p.Coprime q) (C : ℝ)
    (hV : positiveRowVariance P (p*n) p (zeroPhase P hP)^3 ≤ C * (n : ℝ)^4) :
    max (roughCount P n - roughCount P (p*n) / p) 0 ^ 6 ≤
      (p : ℝ)^3 * (C * (n : ℝ)^4) := by
  have hs := positive_row_deviation_sq_le P (p*n) p hp (zeroPhase P hP) ⟨0,hp⟩
  rw [row_zeroPhase_rectangle P hP n p hp hc, intervalCount_zeroPhase] at hs
  have hh := pow_le_pow_left₀ (sq_nonneg _) hs 3
  rw [← pow_mul, mul_pow] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hV (by positivity))

/-- Only positive row deviations enter this upper discrepancy estimate. -/
theorem roughCount_upper_of_positive_variance_cube (P : Finset ℕ)
    (hP : ∀ q ∈ P, q.Prime) (n p : ℕ) (hp : 8 ≤ p)
    (hc : ∀ q ∈ P, p.Coprime q) (C D : ℝ) (hD : 0 ≤ D)
    (hbudget : (p : ℝ)^3 * (C * (n : ℝ)^4) ≤ D^6)
    (hV : ∀ j : ℕ, positiveRowVariance P (p * (n * p^j)) p (zeroPhase P hP)^3 ≤
      C * (n * p^j : ℕ)^4) :
    roughCount P n ≤ (n : ℝ) * density P + 2*D := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hh := upper_of_halving_recurrence
    (fun j => roughCount P (n*p^j)) (p : ℝ) D ((n : ℝ)*density P) hpR
    (roughCount_scaled_limit P hP n p (by omega)) ?_
  · simpa only [pow_zero, Nat.mul_one] using hh
  intro j
  have hbound := roughCount_positive_gap_sixth_le P hP (n*p^j) p hp0 hc C (hV j)
  have hmul : p*(n*p^j) = n*p^(j+1) := by rw [pow_succ]; ring
  rw [hmul] at hbound
  have hpower : (p : ℝ)^(4*j) ≤ ((p : ℝ)/2)^(6*j) := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (p : ℝ)^4)
      (sixth_halving_growth (p : ℝ) (by exact_mod_cast hp)) j
    simpa only [← pow_mul] using hh
  have hbudget' : (p : ℝ)^3*(C*(n*p^j : ℕ)^4) ≤ (D*((p : ℝ)/2)^j)^6 := by
    calc
      _ = ((p : ℝ)^3*(C*(n : ℝ)^4)) * (p : ℝ)^(4*j) := by push_cast; ring
      _ ≤ D^6*((p : ℝ)/2)^(6*j) :=
        mul_le_mul hbudget hpower (by positivity) (by positivity)
      _ = _ := by ring
  apply (le_max_left _ 0).trans
  apply le_of_pow_le_pow_left₀ (by norm_num : (6 : ℕ) ≠ 0) (by positivity)
  exact hbound.trans hbudget'

#print axioms roughCount_upper_of_positive_variance_cube
end Erdos970.GapAverages
