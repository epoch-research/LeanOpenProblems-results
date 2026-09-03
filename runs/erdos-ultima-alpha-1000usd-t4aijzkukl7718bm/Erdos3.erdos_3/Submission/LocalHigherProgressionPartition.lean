import Submission.HigherPolynomialProgressionPartition
import Submission.HigherLocalPolynomialProgressions

/-! Density-preserving flat partitions under finite-window or local-cube
polynomiality hypotheses. No assumptions outside the prescribed domain are used. -/
namespace Erdos3LocalHigherProgressionPartition
open Finset Erdos3HigherPolynomialProgressionPartition Erdos3HigherPartitionParameters
  Erdos3HigherPhaseDifferences Erdos3LocalPolynomialPhaseExtension
  Erdos3HigherLocalPolynomialProgressions Erdos3FinitePartitionIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

/-- Finite-window version of the arbitrary-degree flat progression partition. -/
theorem finite_window_polynomial_partition {I : Type*} [Fintype I]
    (k : ℕ) (f : I → ℕ → Additive Circle) (N L s : ℕ) (hL : 0 < L)
    (hf : ∀ i n, n+(k+1) < N → diffIter (k+1) (f i) n = 0)
    (hN : higherPartitionThreshold k (Fintype.card I) L s ≤ N) :
    ∃ c : Fin N → Option (Fin N), ∃ w : I → Fin N → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧ cellMass c none ≤ (1/2 : ℝ)^s ∧
      (∀ x j, c x = some j → ∀ i, ‖phase (f i x.val)-w i j‖ ≤ (1/2 : ℝ)^s) ∧
      ∀ j, (cell c (some j)).Nonempty →
        ∃ a d : ℕ, 0 < d ∧ d ≤ higherPartitionStride k (Fintype.card I) L s ∧
          (∀ n < L, a+n*d < N) ∧
          ∀ x : Fin N, c x = some j ↔ ∃ n : Fin L, x.val = a+n.val*d := by
  have hN0 : 0 < N := (higherPartitionThreshold_pos k (Fintype.card I) L s hL).trans_le hN
  let F : I → ℕ → Additive Circle := fun i ↦ newtonExtension k (f i)
  have hF (i : I) : diffIter (k+1) (F i) = 0 := newtonExtension_difference_zero k (f i)
  have hFeq (i : I) (n : ℕ) (hn : n < N) : F i n = f i n :=
    newtonExtension_eq (f i) (N := N-1) (fun m hm ↦ hf i m (by omega)) n (by omega)
  obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := higher_polynomial_progression_partition k F hF N L s hL hN
  refine ⟨c,w,hw,hbad,?_,hgeom⟩
  intro x j hx i
  simpa only [hFeq i x.val x.isLt] using hflat x j hx i

/-- Restricting a locally polynomial phase to a progression entirely inside
its local domain gives an almost-complete flat partition in natural coordinates. -/
theorem local_polynomial_progression_partition {G I : Type*} [AddCommGroup G] [Fintype I]
    (R : Set G) (k : ℕ) (f : I → G → Additive Circle)
    (hf : ∀ i, IsLocallyPolynomial R k (f i)) (a h : G) (N L s : ℕ) (hL : 0 < L)
    (hR : ∀ n < N, a+n • h ∈ R)
    (hN : higherPartitionThreshold k (Fintype.card I) L s ≤ N) :
    ∃ c : Fin N → Option (Fin N), ∃ w : I → Fin N → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧ cellMass c none ≤ (1/2 : ℝ)^s ∧
      (∀ x j, c x = some j → ∀ i, ‖phase (f i (a+x.val • h))-w i j‖ ≤ (1/2 : ℝ)^s) ∧
      ∀ j, (cell c (some j)).Nonempty →
        ∃ b d : ℕ, 0 < d ∧ d ≤ higherPartitionStride k (Fintype.card I) L s ∧
          (∀ n < L, b+n*d < N) ∧
          ∀ x : Fin N, c x = some j ↔ ∃ n : Fin L, x.val = b+n.val*d := by
  have hN0 : 0 < N := (higherPartitionThreshold_pos k (Fintype.card I) L s hL).trans_le hN
  apply finite_window_polynomial_partition k (fun i n ↦ f i (a+n • h)) N L s hL _ hN
  intro i n hn
  exact local_polynomial_progression_differences R k (f i) (hf i) a h (N-1)
    (fun m hm ↦ hR m (by omega)) n (by omega)

#print axioms finite_window_polynomial_partition
#print axioms local_polynomial_progression_partition
end Erdos3LocalHigherProgressionPartition
