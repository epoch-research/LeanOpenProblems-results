import Submission.TernaryTwoMixedComparison
import Submission.TernaryTwoSliceDomination

/-! The root comparison applies to whole real-valued slice sequences whose
individual slices have full ternary profile majorants. -/
namespace Erdos7TernaryTwoSequenceComparison
open scoped BigOperators
open Erdos7TernaryTwoSharedPrefix Erdos7TernaryTwoSharedComparison
open Erdos7TernaryTwoCoherentMixture Erdos7TernaryTwoSliceDomination
set_option maxHeartbeats 3000000

noncomputable def observedCount (E : ℕ) (K : ℕ → Fin 5 → ℝ) :
    Fin 5 ⊕ (Fin (E+1) × Fin 5) → ℝ :=
  Sum.elim (K 0) (fun z => ∑ j∈Finset.range (geometricLength E z.1),K j z.2)

lemma sum_extendReal (D d : ℕ) (hd : d≤D) (K : ℕ → Fin 5 → ℝ) (x : Fin 5) :
    (∑ j∈Finset.range d,extendReal (fun k : Fin D => K k.val) j x)=
      ∑ j∈Finset.range d,K j x := by
  apply Finset.sum_congr rfl
  intro j hj
  have hh : j<D := lt_of_lt_of_le (Finset.mem_range.mp hj) hd
  simp only [extendReal,dif_pos hh]

/-- The sequence for each test can be different. A coherent mixture is
constructed within that sequence, so its first slice is shared across all
cumulative prefixes exactly as required by the sharper comparison. -/
theorem sequence_comparison (E : ℕ) (K : ℕ → Fin 5 → ℝ)
    (hK : ∀ j<E+2,∃ g : Fin 5 → ℝ,g∈convexHull ℝ (Set.range corner) ∧ ∀ x,K j x≤g x)
    (w : Fin 10 → ℝ) (hw : ∀ c,0≤w c)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ z,Erdos7TernaryTwoMixedComparison.actualWeight w (geometricWeight E) z *
      φ (observedCount E K z)) ≤
      ∑ z,Erdos7TernaryTwoMixedComparison.refWeight w (geometricWeight E) z *
        φ (refCount (geometricLength E) z) := by
  obtain ⟨I,inst,v,a,hv,hm,ha⟩ := coherent_prefix_bound
    (fun j : Fin (E+2) => K j.val) (fun j => hK j.val j.isLt)
  letI : Fintype I := inst
  have hpre (d : ℕ) (hd : d≤E+2) (x : Fin 5) :
      (∑ j∈Finset.range d,K j x) ≤ ∑ i,v i*(prefixCount (a i) d x : ℝ) := by
    simpa only [sum_extendReal (E+2) d hd K x] using ha d hd x
  have hdom : ∀ z,observedCount E K z ≤
      ∑ i∈Finset.univ,v i*(actualCount (a i) (geometricLength E) z : ℝ) := by
    intro z; cases z with
    | inl x =>
      simpa only [observedCount,actualCount,Sum.elim_inl,Finset.sum_range_one,prefixCount]
        using hpre 1 (by omega) x
    | inr z =>
      exact hpre (geometricLength E z.1) (by dsimp [geometricLength]; have := z.1.isLt; omega) z.2
  exact Erdos7TernaryTwoMixedComparison.dominated_comparison Finset.univ v
    (fun i _ => hv i) hm w hw a (geometricWeight E) (geometricLength E)
    (geometric_nonneg E) (fun j => by dsimp [geometricLength]; omega) (geometric_mass E)
    (observedCount E K) hdom φ hφ hmφ

#print axioms sequence_comparison
end Erdos7TernaryTwoSequenceComparison
