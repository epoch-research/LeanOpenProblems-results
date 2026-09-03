import Submission.QuadraticProgressionPartition

/-! Almost complete flat progression partitions for local quadratic phases.
All coarse progression points must lie in the domain of local quadraticity. -/
namespace Erdos3LocalQuadraticProgressionPartition
open Finset Erdos3QuadraticProgressionPartition Erdos3LocalQuadraticProgressions
  Erdos3LocalQuadraticInverse Erdos3FiniteUniformity Erdos3SimultaneousQuadraticRecurrence
  Erdos3FinitePartitionIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

variable {G I : Type*} [AddCommGroup G] [Fintype I]

/-- This is a genuine partition with controlled exceptional mass, not merely
existence of a flat progression through each point. Properness of the image
in G additionally requires injectivity of the original progression map. -/
theorem local_quadratic_progression_partition (R : Set G) (q : I → G → ℂ)
    (hq : ∀ i x, ‖q i x‖ = 1) (hquad : ∀ i, IsLocallyQuadratic R (q i)) (a h : G)
    (N M L n t : ℕ) (hN : 0 < N) (hM : 0 < M) (hL : 0 < L) (hn : 0 < n)
    (hR : ∀ k < N, a+k • h ∈ R) :
    ∃ c : Fin N → Option (Fin N × Fin M), ∃ w : I → (Fin N × Fin M) → ℂ,
      (∀ i ab, ‖w i ab‖ = 1) ∧
      cellMass c none ≤ (recurrenceBound (Fintype.card I) t : ℝ)*(M : ℝ)/(N : ℝ)+
        (((2*n+1)^(2*Fintype.card I) : ℕ) : ℝ)*(L : ℝ)/(M : ℝ) ∧
      (∀ k ab, c k = some ab → ∀ i,
        ‖q i (a+k.val • h)-w i ab‖ ≤
          2*(M : ℝ)^2*(1/2 : ℝ)^t+2*(L : ℝ)/(n : ℝ)) ∧
      (∀ ab, (cell c (some ab)).Nonempty →
        ∃ b d : ℕ, 0 < d ∧ d ≤ recurrenceBound (Fintype.card I) t*(2*n+1)^(2*Fintype.card I) ∧
          (∀ j < L, b+j*d < N) ∧
          ∀ k : Fin N, c k = some ab ↔ ∃ j : Fin L, k.val = b+j.val*d) := by
  let A : I → ℂ := fun i ↦ q i a
  let u : I → ℂ := fun i ↦ derivative (q i) h a
  let v : I → ℂ := fun i ↦ derivative (derivative (q i) h) h a
  have hu (i : I) : ‖u i‖ = 1 := derivative_norm_one (q i) (hq i) h a
  have hv (i : I) : ‖v i‖ = 1 := derivative_norm_one (derivative (q i) h)
    (derivative_norm_one (q i) (hq i) h) h a
  obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := quadratic_progression_partition A u v (fun i ↦ hq i a)
    hu hv N M L n t hN hM hL hn
  refine ⟨c,w,hw,hbad,?_,hgeom⟩
  intro k ab hk i
  have he := local_quadratic_progression_formula (hq i) (hquad i) a h
    (N := N-1) (fun k hk ↦ hR k (by omega)) k.val (by omega : k.val ≤ N-1)
  rw [he]
  exact hflat k ab hk i

#print axioms local_quadratic_progression_partition
end Erdos3LocalQuadraticProgressionPartition
