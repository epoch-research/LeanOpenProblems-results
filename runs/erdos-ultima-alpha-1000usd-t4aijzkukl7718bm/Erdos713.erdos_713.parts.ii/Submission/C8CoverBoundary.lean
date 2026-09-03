import FormalConjecturesUtil
import Submission.C8CoverCriterion

/-! Bipartiteness of the base is essential in the C8 cover criterion.
This finite example is not a counterexample to Erdős 713. -/
open SimpleGraph Finset
namespace Erdos713C8CoverBoundary
open Erdos713ProductCover
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-- A triangle and a pentagon with their vertex zero identified. -/
def base : SimpleGraph (Fin 7) :=
  fromRel fun x y => (x,y) ∈ ({(0,1),(1,2),(2,0),(0,3),(3,4),(4,5),(5,6),(6,0)} :
    Finset (Fin 7 × Fin 7))

instance : DecidableRel base.Adj := by unfold base; infer_instance

def doubleCover : SimpleGraph (Fin 7 × Fin 2) := tensor base ⊤

instance : DecidableRel doubleCover.Adj := by
  unfold doubleCover tensor
  infer_instance

def projection : doubleCover →g base := ⟨Prod.fst,fun {_ _} h => h.1⟩

lemma projection_isCover : IsCover projection := by
  unfold IsCover
  decide

lemma base_four_free : (cycleGraph 4).Free base := by
  have hfour : ∀ a b c d : Fin 7, base.Adj a b → base.Adj b c →
      base.Adj c d → base.Adj d a → a=c ∨ b=d := by decide
  rintro ⟨f⟩
  have hh := hfour (f 0) (f 1) (f 2) (f 3)
    (f.toHom.map_adj (by decide)) (f.toHom.map_adj (by decide))
    (f.toHom.map_adj (by decide)) (f.toHom.map_adj (by decide))
  rcases hh with hh | hh
  · exact (by decide : (0 : Fin 4) ≠ 2) (f.injective hh)
  · exact (by decide : (1 : Fin 4) ≠ 3) (f.injective hh)

lemma base_eight_free : (cycleGraph 8).Free base := by
  rintro ⟨f⟩
  have hh := Fintype.card_le_of_injective f f.injective
  norm_num at hh

lemma base_not_bipartite : ¬ base.IsBipartite := by
  rintro ⟨χ⟩
  have h01 := χ.valid (show base.Adj 0 1 by decide)
  have h12 := χ.valid (show base.Adj 1 2 by decide)
  have h20 := χ.valid (show base.Adj 2 0 by decide)
  omega

lemma doubleCover_bipartite : doubleCover.IsBipartite := by
  refine ⟨⟨Prod.snd,?_⟩⟩
  intro x y h
  exact h.2

/-- Going around the two odd cycles changes sheets twice, giving a
simple eight-cycle in the bipartite double cover. -/
def octagon : Copy (cycleGraph 8) doubleCover :=
  ⟨⟨![(0,0),(1,1),(2,0),(0,1),(3,0),(4,1),(5,0),(6,1)],by decide⟩,by decide⟩

lemma doubleCover_not_eight_free : ¬ (cycleGraph 8).Free doubleCover :=
  fun h => h ⟨octagon⟩

/-- Removing only the base-bipartiteness assumption from the preservation
criterion is invalid, even for a finite two-sheeted cover. -/
theorem boundary_example :
    (cycleGraph 4).Free base ∧ (cycleGraph 8).Free base ∧
    ¬ base.IsBipartite ∧ IsCover projection ∧ doubleCover.IsBipartite ∧
    ¬ (cycleGraph 8).Free doubleCover :=
  ⟨base_four_free,base_eight_free,base_not_bipartite,projection_isCover,
    doubleCover_bipartite,doubleCover_not_eight_free⟩

#print axioms projection_isCover
#print axioms base_four_free
#print axioms octagon
#print axioms boundary_example
end Erdos713C8CoverBoundary
