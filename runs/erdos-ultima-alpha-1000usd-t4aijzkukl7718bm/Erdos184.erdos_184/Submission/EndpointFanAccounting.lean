import Submission.EndpointFamilyRotation

/-! Exact accounting for the simultaneous rotation of a finite list of
selected endpoints, and the telescoping identity along a fan. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
namespace FanRotation

lemma flatMap_marked (E : List V) (S : Finset V) (f : V → Sym2 V) :
    E.flatMap (fun a => markedEdge S a (f a)) =
      (E.filter (fun a => decide (a ∈ S))).map f := by
  induction E with
  | nil => rfl
  | cons a E ih =>
    rw [List.flatMap_cons,ih]
    by_cases ha : a ∈ S <;> simp [markedEdge,ha]

lemma selected_endpoints_perm {L : List (Piece G)} (hL : Admissible L)
    (A : List V) (hA : A.Nodup) :
    ((endpoints L).filter (fun a => decide (a ∈ A.toFinset))).Perm A := by
  apply (List.perm_ext_iff_of_nodup (hL.2.1.filter _) hA).mpr
  intro a
  simp only [List.mem_filter,decide_eq_true_eq,List.mem_toFinset]
  exact ⟨And.right,fun h => ⟨hL.2.2 a,h⟩⟩

lemma endpoint_map_account (L : List (Piece G)) (v : V) (S : Finset V) (E : List V) :
    (E.map (movedEndpoint L v S) ++ E.filter (fun a => decide (a ∈ S))).Perm
      (E ++ (E.filter (fun a => decide (a ∈ S))).map (fanStep L v)) := by
  apply List.perm_iff_count.mpr
  intro x
  induction E with
  | nil => simp
  | cons a E ih =>
    by_cases ha : a ∈ S
    all_goals
      simp [List.count_append,List.count_cons,movedEndpoint,ha] at ih ⊢
      omega

lemma marked_moved_eq (L : List (Piece G)) (v : V) (S : Finset V) (a : V) :
    markedEdge S a s(v,movedEndpoint L v S a) = markedEdge S a s(v,fanStep L v a) := by
  by_cases ha : a ∈ S <;> simp [markedEdge,movedEndpoint,ha]

lemma addedStar_perm {L : List (Piece G)} (hL : Admissible L)
    (A : List V) (hA : A.Nodup) (v : V) :
    (addedStar L v A.toFinset).Perm (A.map (fun a => s(v,a))) := by
  rw [addedStar,flatMap_marked]
  exact (selected_endpoints_perm hL A hA).map _

lemma removedStar_perm {L : List (Piece G)} (hL : Admissible L)
    (A : List V) (hA : A.Nodup) (v : V) :
    (removedStar L L v A.toFinset).Perm ((A.map (fanStep L v)).map (fun a => s(v,a))) := by
  have he : removedStar L L v A.toFinset =
      (endpoints L).flatMap (fun a => markedEdge A.toFinset a s(v,fanStep L v a)) := by
    simp only [removedStar,marked_moved_eq]
  rw [he,flatMap_marked,List.map_map]
  exact (selected_endpoints_perm hL A hA).map _

/-- Rotate any duplicate-free list of eligible endpoints simultaneously.
The selected old and new endpoint lists also describe the edge exchange. -/
lemma list_rotation {L : List (Piece G)} (hL : Admissible L) (v : V)
    (A : List V) (hA : A.Nodup)
    (hS : A.toFinset ⊆ (touchingEndpoints L v).erase v)
    (hSN : ∀ a ∈ A.toFinset, G.Adj v a) :
    ∃ M : List (Piece G),
      (edgeList M ++ (A.map (fanStep L v)).map (fun a => s(v,a))).Perm
        (edgeList L ++ A.map (fun a => s(v,a))) ∧
      (endpoints M ++ A).Perm (endpoints L ++ A.map (fanStep L v)) ∧
      (∀ p ∈ L, v ∉ p.walk.support → p ∈ M) := by
  let M := moveFamily hL A.toFinset hS hSN
  have he := moveFamily_edges hL A.toFinset hS hSN
  have ha := addedStar_perm hL A hA v
  have hr := removedStar_perm hL A hA v
  have hv := moveFamily_endpoints hL A.toFinset hS hSN
  refine ⟨M,?_,?_,fun p hp hpv => moveFamily_avoiding hL A.toFinset hS hSN hp hpv⟩
  · apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq he e
    have h₂ := List.Perm.count_eq ha e
    have h₃ := List.Perm.count_eq hr e
    simp only [List.count_append] at h₁ ⊢
    change (edgeList M).count e + _ = _ at h₁
    omega
  · have hc := endpoint_map_account L v A.toFinset (endpoints L)
    have hp := selected_endpoints_perm hL A hA
    apply List.perm_iff_count.mpr
    intro x
    have h₁ := List.Perm.count_eq hc x
    have h₂ := List.Perm.count_eq hp x
    have h₃ := List.Perm.count_eq (hp.map (fanStep L v)) x
    change endpoints M = _ at hv
    rw [hv]
    simp only [List.count_append] at h₁ ⊢
    omega

/-- A shifted iteration list differs from the original only at its ends. -/
lemma iterate_prefix_perm (f : V → V) (x : V) (n : ℕ) :
    (((List.range n).map (fun i => f^[i] x)).map f ++ [x]).Perm
      ((List.range n).map (fun i => f^[i] x) ++ [f^[n] x]) := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply List.perm_iff_count.mpr
    intro y
    have hh := List.Perm.count_eq ih y
    simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil,
      List.count_append,List.count_cons,List.count_nil,Function.iterate_succ_apply'] at hh ⊢
    omega

lemma cancel_fan_accounting {L M : List (Piece G)} {v x t : V} {A : List V}
    (he : (edgeList M ++ (A.map (fanStep L v)).map (fun a => s(v,a))).Perm
      (edgeList L ++ A.map (fun a => s(v,a))))
    (hv : (endpoints M ++ A).Perm (endpoints L ++ A.map (fanStep L v)))
    (ht : (A.map (fanStep L v) ++ [x]).Perm (A ++ [t])) :
    (edgeList M ++ [s(v,t)]).Perm (edgeList L ++ [s(v,x)]) ∧
      (endpoints M ++ [x]).Perm (endpoints L ++ [t]) := by
  constructor
  · apply List.perm_iff_count.mpr
    intro e
    have h₁ := List.Perm.count_eq he e
    have h₂ := List.Perm.count_eq (ht.map (fun a => s(v,a))) e
    simp only [List.map_append,List.map_cons,List.map_nil,List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega
  · apply List.perm_iff_count.mpr
    intro a
    have h₁ := List.Perm.count_eq hv a
    have h₂ := List.Perm.count_eq ht a
    simp only [List.count_append,List.count_cons,List.count_nil] at h₁ h₂ ⊢
    omega

end FanRotation
end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.FanRotation.list_rotation
#print axioms Erdos184Work.OddPaths.FanRotation.cancel_fan_accounting
