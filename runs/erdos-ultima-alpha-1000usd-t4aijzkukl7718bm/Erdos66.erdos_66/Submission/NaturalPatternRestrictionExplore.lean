import Submission.CentralTripleCountsExplore
import Submission.BoundaryPairCountsExplore

/-! Finite coordinate restrictions preserve all pair and triple tests whose
natural target bounds lie below the coordinate cutoff. -/
namespace Erdos66NaturalPatternRestriction
open Erdos66FiniteRepBernoulli Erdos66CentralTripleCounts Erdos66BoundaryPairCounts
open scoped Classical
set_option maxHeartbeats 1200000

noncomputable def restrict (A : Set ℕ) (L : ℕ) : Fin (L+1) → Bool := fun i ↦ decide (i.val∈A)

lemma selected_restrict (A : Set ℕ) (L : ℕ) : selected L (restrict A L)=A∩Set.Iic L := by
  ext a
  constructor
  · rintro ⟨i,rfl,hi⟩
    refine ⟨?_,by change i.val ≤ L; have := i.isLt; omega⟩
    simpa only [restrict,decide_eq_true_eq] using hi
  · rintro ⟨ha,hL⟩
    change a ≤ L at hL
    exact ⟨⟨a,by omega⟩,rfl,by simpa only [restrict,decide_eq_true_eq] using ha⟩

lemma fiber_restrict (A : Set ℕ) (L N n z : ℕ) (hn : n ≤ L) (hz : z ≤ L) :
    fiber (selected L (restrict A L)) N n z=fiber A N n z := by
  rw [selected_restrict]
  ext a
  simp only [mem_fiber,Set.mem_inter_iff,Set.mem_Iic]
  constructor
  · rintro ⟨han,hNa,hNb,haz,⟨ha,_⟩,⟨hb,_⟩,⟨hc,_⟩⟩
    exact ⟨han,hNa,hNb,haz,ha,hb,hc⟩
  · rintro ⟨han,hNa,hNb,haz,ha,hb,hc⟩
    exact ⟨han,hNa,hNb,haz,⟨ha,by omega⟩,⟨hb,by omega⟩,⟨hc,by omega⟩⟩

lemma boundary_restrict (A : Set ℕ) (L d n : ℕ) (hn : n ≤ L) :
    boundary (selected L (restrict A L)) d n=boundary A d n := by
  rw [selected_restrict]
  ext a
  simp only [boundary,Finset.mem_filter,Finset.mem_range,Set.mem_inter_iff,Set.mem_Iic]
  have hdiv := Nat.div_le_self n (d^2)
  constructor
  · rintro ⟨ha,⟨h1,_⟩,⟨h2,_⟩⟩; exact ⟨ha,h1,h2⟩
  · rintro ⟨ha,h1,h2⟩; exact ⟨ha,⟨h1,by omega⟩,⟨h2,by omega⟩⟩

end Erdos66NaturalPatternRestriction
