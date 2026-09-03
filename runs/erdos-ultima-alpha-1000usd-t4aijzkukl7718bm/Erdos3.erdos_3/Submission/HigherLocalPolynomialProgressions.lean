import Submission.HigherPolynomialFlattening

/-! Local polynomiality on complete cubes implies controlled phase oscillation
on a shorter progression, in arbitrary degree. This file supplies no inverse
theorem producing such phases and no density-preserving partition. -/
namespace Erdos3HigherLocalPolynomialProgressions
open Finset Erdos3HigherPhaseDifferences Erdos3HigherPolynomialFlattening
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- Additive difference over all vertices of a cube, with the specified ordered directions. -/
def cubeDifference : (k : ℕ) → (G → H) → (Fin k → G) → G → H
  | 0,f,_,x => f x
  | k+1,f,h,x => cubeDifference k (fwdDiff (h 0) f) (fun i ↦ h i.succ) x

/-- Every complete (k+1)-dimensional cube in the domain has zero difference. -/
def IsLocallyPolynomial (R : Set G) (k : ℕ) (f : G → H) : Prop :=
  ∀ x : G, ∀ h : Fin (k+1) → G,
    (∀ S : Finset (Fin (k+1)), x+∑ i ∈ S, h i ∈ R) → cubeDifference (k+1) f h x = 0

lemma cubeDifference_same (k : ℕ) (f : G → H) (h x : G) :
    cubeDifference k f (fun _ ↦ h) x = (fwdDiff h)^[k] f x := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih =>
    rw [cubeDifference,ih,Function.iterate_succ_apply]

lemma diffIter_progression_pullback (k : ℕ) (f : G → H) (a h : G) (n : ℕ) :
    diffIter k (fun m : ℕ ↦ f (a+m • h)) n = (fwdDiff h)^[k] f (a+n • h) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    rw [diffIter,Function.iterate_succ_apply']
    change diffIter k (fun m : ℕ ↦ f (a+m • h)) (n+1)-
      diffIter k (fun m : ℕ ↦ f (a+m • h)) n = _
    rw [ih,ih,Function.iterate_succ_apply']
    simp only [fwdDiff,add_nsmul,one_nsmul,add_assoc]

/-- Only vertices inside the supplied finite progression are used. -/
theorem local_polynomial_progression_differences (R : Set G) (k : ℕ) (f : G → H)
    (hf : IsLocallyPolynomial R k f) (a h : G) (N : ℕ)
    (hR : ∀ n ≤ N, a+n • h ∈ R) :
    ∀ n, n+(k+1) ≤ N → diffIter (k+1) (fun m : ℕ ↦ f (a+m • h)) n = 0 := by
  intro n hn
  rw [diffIter_progression_pullback,← cubeDifference_same]
  apply hf
  intro S
  have hc : S.card ≤ k+1 := by
    exact (Finset.card_le_univ S).trans_eq (Fintype.card_fin _)
  have hh := hR (n+S.card) (by omega)
  simpa only [sum_const,add_nsmul,add_assoc] using hh

/-- Simultaneous local higher-degree flattening on a complete progression. -/
theorem local_polynomial_progression_flattening {I : Type*} [Fintype I]
    (R : Set G) (K : ℕ) (f : I → G → Additive Circle)
    (hf : ∀ i, IsLocallyPolynomial R K (f i)) (a h : G) (N L s : ℕ) (hL : 0 < L)
    (hR : ∀ n ≤ N, a+n • h ∈ R)
    (hN : L*higherFlattenBound K (Fintype.card I) L s ≤ N) :
    ∃ d : ℕ, 0 < d ∧ d ≤ higherFlattenBound K (Fintype.card I) L s ∧
      ∀ i, ∀ n ≤ L, ‖phase (f i (a+(n*d) • h))-phase (f i a)‖ ≤ (1/2 : ℝ)^s := by
  obtain ⟨d,hd,hbound,hflat⟩ := simultaneous_polynomial_flattening_dyadic
    (fun i m ↦ f i (a+m • h)) K N L s hL
    (fun i ↦ local_polynomial_progression_differences R K (f i) (hf i) a h N hR) hN
  exact ⟨d,hd,hbound,by simpa only [zero_nsmul,add_zero] using hflat⟩

#print axioms local_polynomial_progression_differences
#print axioms local_polynomial_progression_flattening
end Erdos3HigherLocalPolynomialProgressions
