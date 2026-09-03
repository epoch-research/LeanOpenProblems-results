import Submission.MarkedCycleSegmentation

/-! Numbered junctions for the recursive cyclic-order enumeration. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleSegments
set_option maxHeartbeats 1500000
variable {V W W' : Type*} {G : SimpleGraph V}

namespace Segmentation
variable {a : V} {c : G.Walk a a} {vertex : W → V} {next : W → W}

def reindex (S : Segmentation c vertex id next) (e : W' ≃ W) :
    Segmentation c (vertex ∘ e) id (e.symm ∘ next ∘ e) where
  path j := (S.path (e j)).copy rfl (by simp)
  isPath j := by simp only [Walk.isPath_copy]; exact S.isPath (e j)
  disjoint i j hij := by
    simp only [Walk.edges_copy]
    exact S.disjoint (e i) (e j) (fun h => hij (e.injective h))
  cover x := by
    simp only [Walk.edges_copy]
    rw [S.cover x]
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨e.symm i,?_⟩
      have he := congrArg (fun j => (S.path j).edges) (e.apply_symm_apply i)
      dsimp only at he
      rw [he]
      exact hi
    · rintro ⟨j,hj⟩
      exact ⟨e j,hj⟩
end Segmentation

namespace Marked
def unitEquivFinOne : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := Subsingleton.elim _ _
  right_inv i := Subsingleton.elim _ _

def markerEquiv : (n : ℕ) → Marker n ≃ Fin (n+2)
  | 0 => Equiv.refl (Fin 2)
  | n+1 => (Equiv.sumCongr (markerEquiv n) unitEquivFinOne).trans finSumFinEquiv

def nextFin (n : ℕ) (o : Order n) : Fin (n+2) → Fin (n+2) :=
  markerEquiv n ∘ next n o ∘ (markerEquiv n).symm

lemma nextFin_ne (n : ℕ) (o : Order n) (i : Fin (n+2)) : i ≠ nextFin n o i := by
  intro h
  have hh := congrArg (markerEquiv n).symm h
  simp only [nextFin,Function.comp_apply,Equiv.symm_apply_apply] at hh
  exact next_ne n o _ hh

lemma exists_numbered_segmentation {a : V} (c : G.Walk a a) (hc : c.IsCycle)
    (n : ℕ) (vertex : Fin (n+2) → V) (hinj : Function.Injective vertex)
    (hmem : ∀ i, vertex i ∈ c.support) :
    ∃ o : Order n, Nonempty (Segmentation c vertex id (nextFin n o)) := by
  obtain ⟨o,⟨S⟩⟩ := exists_segmentation c hc n (vertex ∘ markerEquiv n)
    (hinj.comp (markerEquiv n).injective) (fun i => hmem _)
  have S' := S.reindex (markerEquiv n).symm
  have hv : (vertex ∘ markerEquiv n) ∘ (markerEquiv n).symm = vertex := by
    funext i
    simp
  rw [hv] at S'
  exact ⟨o,⟨S'⟩⟩

#print axioms exists_numbered_segmentation
end Marked
end Erdos184Work.CycleSegments
