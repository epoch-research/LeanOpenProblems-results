import Submission.TripleSparsePowerProfileExplore
import Submission.CentralTripleDeletionExplore

/-! An infinite harmonic rounding supports exact one-target downward moves
with constant off-target loss on every fixed polynomial horizon. This does
not bound the cumulative loss from an unbounded family of moves. -/
namespace Erdos66TripleSparseDownwardCorrection
open AdditiveCombinatorics Erdos66CentralTripleCounts Erdos66CentralTripleDeletion
  Erdos66TripleSparsePowerProfile Erdos66Generating Erdos66Rounding
  Erdos66PowerExceptionalProfile
open scoped Classical
set_option maxHeartbeats 1600000

lemma fiber_mono {A B : Set ℕ} (hAB : A ⊆ B) (N n z : ℕ) :
    fiber A N n z ⊆ fiber B N n z := by
  intro a ha
  obtain ⟨han,hNa,hNb,haz,ha,hb,hc⟩ := mem_fiber.mp ha
  exact mem_fiber.mpr ⟨han,hNa,hNb,haz,hAB ha,hAB hb,hAB hc⟩

 theorem exists_rounding_with_downward_corrections : ∃ (A : Set ℕ) (N₀ : ℕ → ℕ),
    (∀ n, |prefixSum (roundingError A) n| ≤ 1) ∧
    (∀ j : ℕ, Summable (fun n ↦ powerCost 1 (1/((j:ℝ)+1)) n (sumRep A n))) ∧
    (∀ (B : Set ℕ), B ⊆ A → ∀ h N n k, N₀ h ≤ N → n ≤ 4*N →
      k ≤ (upperEndpoints B N n).card →
      ∃ D : Finset ℕ, D ⊆ upperEndpoints B N n ∧ D.card=k ∧
        sumRep B n=sumRep (B\(D : Set ℕ)) n+2*k ∧
        ∀ z, z ≤ N^h → n≠z →
          sumRep B z-sumRep (B\(D : Set ℕ)) z ≤ 72*(h+4)+4) := by
  obtain ⟨A,N₀,hbr,htr,hcost⟩ := exists_triple_sparse_power_potentials
  refine ⟨A,N₀,hbr,hcost,?_⟩
  intro B hBA h N n k hN₀ hn hk
  obtain ⟨D,hD,hcard,hexact,hloss⟩ := exists_exact_downward_correction B N n k hk
  refine ⟨D,hD,hcard,hexact,?_⟩
  intro z hz hnz
  have hmono := Finset.card_le_card (fiber_mono hBA N n z)
  have hbound := htr h N n z hN₀ hn hz hnz
  have hh := hloss z
  omega

end Erdos66TripleSparseDownwardCorrection
