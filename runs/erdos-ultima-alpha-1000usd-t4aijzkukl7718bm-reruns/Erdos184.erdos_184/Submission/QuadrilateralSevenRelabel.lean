import Submission.QuadrilateralOutsideModels

/-! Explicit relabelings of the six single-root order-seven patterns. -/
open SimpleGraph
namespace Erdos184.QuadrilateralSevenRelabel
open SmallGraphEncoding
set_option maxHeartbeats 1000000

def codes : Fin 6 → ℕ := ![14164,15242,22188,23154,26034,26988]

def perm : Fin 6 → Equiv.Perm (Fin 7) :=
  ![{ toFun := ![0,1,2,5,6,3,4], invFun := ![0,1,2,5,6,3,4], left_inv := by decide, right_inv := by decide },
    { toFun := ![0,1,2,3,4,5,6], invFun := ![0,1,2,3,4,5,6], left_inv := by decide, right_inv := by decide },
    { toFun := ![0,1,2,4,6,3,5], invFun := ![0,1,2,5,3,6,4], left_inv := by decide, right_inv := by decide },
    { toFun := ![0,1,2,3,5,4,6], invFun := ![0,1,2,3,5,4,6], left_inv := by decide, right_inv := by decide },
    { toFun := ![0,1,2,3,6,4,5], invFun := ![0,1,2,3,5,6,4], left_inv := by decide, right_inv := by decide },
    { toFun := ![0,1,2,4,5,3,6], invFun := ![0,1,2,5,3,4,6], left_inv := by decide, right_inv := by decide }]

lemma adjacency_checked : ∀ i : Fin 6, ∀ u v : Fin 7,
    (graph 7 2 15242).Adj u v ↔ (graph 7 2 (codes i)).Adj (perm i u) (perm i v) := by
  decide +kernel

lemma canonical_iso (i : Fin 6) : Nonempty ((graph 7 2 15242) ≃g (graph 7 2 (codes i))) := by
  exact ⟨{ toEquiv := perm i, map_rel_iff' := fun {u v} => (adjacency_checked i u v).symm }⟩

lemma exists_iso (code : ℕ) (h : code ∈ QuadrilateralOutsideData.patterns 7) :
    Nonempty ((graph 7 2 15242) ≃g (graph 7 2 code)) := by
  simp only [QuadrilateralOutsideData.patterns,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h
  · subst code; exact canonical_iso 0
  · subst code; exact canonical_iso 1
  · subst code; exact canonical_iso 2
  · subst code; exact canonical_iso 3
  · subst code; exact canonical_iso 4
  · subst code; exact canonical_iso 5

end Erdos184.QuadrilateralSevenRelabel
