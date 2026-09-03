import Submission.SubsetLocalQuadraticPartition
import Submission.BohrCoarseProgressionPartition

/-! A complete assembly of the coarse Bohr partition with local quadratic
refinement, including exceptional mass, phase error, and exact AP fibers. -/
namespace Erdos3BohrLocalQuadraticPartition
open Finset Erdos3SubsetLocalQuadraticPartition Erdos3BohrCoarseProgressionPartition
  Erdos3RestrictedPartialPartition Erdos3IntervalProgressionPartition
  Erdos3FiniteBohr Erdos3BohrCovering Erdos3LocalQuadraticInverse
  Erdos3SimultaneousQuadraticRecurrence Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I]

/-- A flat AP partition of the Bohr indices. The exceptional mass is explicitly
bounded by the coarse terminal block, the inner Bohr boundary, and the two
local quadratic partition endpoint losses. -/
theorem bohr_local_quadratic_partition (C : Finset (AddChar G ℂ))
    (q : I → G → ℂ) (hq : ∀ i x, ‖q i x‖ = 1) {R R' η : ℝ}
    (hquad : ∀ i, IsLocallyQuadratic (bohr C R' : Set G) (q i)) (hRR' : R ≤ R') (a h : G)
    (N K M L n n₀ t : ℕ) (hK : 0 < K) (hM : 0 < M) (hL : 0 < L) (hn : 0 < n) (hn₀ : 0 < n₀)
    (hmesh : 4*(K : ℝ)/(n₀ : ℝ) ≤ η) (hB : (bohrIndices C R a h N).Nonempty) :
    ∃ c : bohrIndices C R a h N → Option (Fin N × (Fin K × Fin M)),
    ∃ w : I → (Fin N × (Fin K × Fin M)) → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧
      cellMass c none ≤
        (((((2*n₀+1)^(2*C.card)*K : ℕ) : ℝ)+
          ((bohrIndices C R a h N \ bohrIndices C (R-η) a h N).card : ℝ)) /
          ((bohrIndices C R a h N).card : ℝ))+
        ((recurrenceBound (Fintype.card I) t : ℝ)*(M : ℝ)/(K : ℝ)+
          (((2*n+1)^(2*Fintype.card I) : ℕ) : ℝ)*(L : ℝ)/(M : ℝ)) ∧
      (∀ x j, c x = some j → ∀ i,
        ‖q i (a+x.val.val • h)-w i j‖ ≤ 2*(M : ℝ)^2*(1/2 : ℝ)^t+2*(L : ℝ)/(n : ℝ)) ∧
      (∀ j, (cell c (some j)).Nonempty →
        ∃ b d : ℕ, 0 < d ∧
          d ≤ (recurrenceBound (Fintype.card I) t*(2*n+1)^(2*Fintype.card I))*(2*n₀+1)^(2*C.card) ∧
          (∀ k < L, ∃ x : bohrIndices C R a h N, x.val.val = b+k*d) ∧
          ∀ x : bohrIndices C R a h N, c x = some j ↔ ∃ k : Fin L, x.val.val = b+k.val*d) := by
  letI : Nonempty (bohrIndices C R a h N) := hB.to_subtype
  obtain ⟨d₀,hd₀,hd₀bound,hcoarse⟩ := bohr_coarse_progression_partition C a h K n₀ hK hn₀ (R := R) hmesh
  obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := subset_local_quadratic_partition
    (bohr C R' : Set G) q hq hquad a h N K M L n t d₀ hK hM hL hn hd₀
    (bohrIndices C R a h N) hB
    (fun x hx ↦ bohr_mono C hRR' ((mem_bohrIndices C R a h N x).mp hx))
  refine ⟨c,w,hw,?_,hflat,?_⟩
  · apply hbad.trans
    refine add_le_add ?_ le_rfl
    rw [cellMass_eq_card,Fintype.card_coe]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (hcoarse N).2
  · intro j hj
    obtain ⟨b,d,hd,hdb,hpoints,hfiber⟩ := hgeom j hj
    exact ⟨b,d,hd,hdb.trans (Nat.mul_le_mul_left _ hd₀bound),hpoints,hfiber⟩

#print axioms bohr_local_quadratic_partition
end Erdos3BohrLocalQuadraticPartition
