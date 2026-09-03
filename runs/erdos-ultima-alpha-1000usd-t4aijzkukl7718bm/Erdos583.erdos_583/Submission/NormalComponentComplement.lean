import Submission.MatchingIntegrated

/-! Removing a normal component leaves the distinguished member connected to every remaining member. -/
namespace Erdos583NormalComponentComplementDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion Erdos583Work.MemberComponents
open scoped Classical
set_option maxHeartbeats 2400000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

lemma outside_member_avoids (T : TrailFamily G k) (i : Fin k)
    (A : (normalGraph T i).ConnectedComponent) {j : Fin k}
    (hji : j ≠ i) (hjA : j ∉ componentMembers T i A) :
    Disjoint (T.walk j).toSubgraph.verts (selectedGraph T (componentMembers T i A)).support := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨y,l,hl,hxy⟩
  obtain ⟨hli,hlA⟩ := (mem_componentMembers T i l A).mp hl
  have he := same_component_of_intersection T i hji hli
    ((T.walk j).mem_verts_toSubgraph.mp hx) (Walk.mem_support_of_adj_toSubgraph hxy)
  exact hjA ((mem_componentMembers T i j A).mpr ⟨hji,he.trans hlA⟩)

lemma complement_adj_at (T : TrailFamily G k) (i : Fin k)
    (A : (normalGraph T i).ConnectedComponent) {x y : V}
    (hx : x ∈ (selectedGraph T (componentMembers T i A)).support) :
    (selectedGraph T (Finset.univ \ componentMembers T i A)).Adj x y ↔ (T.walk i).toSubgraph.Adj x y := by
  constructor
  · rintro ⟨j,hj,hxy⟩
    have hji : j=i := by
      by_contra hh
      exact Set.disjoint_left.mp (outside_member_avoids T i A hh (Finset.mem_sdiff.mp hj).2)
        ((T.walk j).toSubgraph.edge_vert hxy) hx
    subst j
    exact hxy
  · intro hxy
    exact ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,removed_not_mem T i A⟩,hxy⟩

lemma component_members_disjoint (T : TrailFamily G k) (i : Fin k)
    {A B : (normalGraph T i).ConnectedComponent} (hAB : A ≠ B) :
    Disjoint (componentMembers T i A) (componentMembers T i B) := by
  apply Finset.disjoint_left.mpr
  intro j hjA hjB
  obtain ⟨hji,hjA⟩ := (mem_componentMembers T i j A).mp hjA
  obtain ⟨_,hjB⟩ := (mem_componentMembers T i j B).mp hjB
  exact hAB (hjA.symm.trans hjB)

lemma complement_connected (T : TrailFamily G k) (hG : G.Connected) (i : Fin k)
    (hn : ∀ j, ¬(T.walk j).Nil) (A : (normalGraph T i).ConnectedComponent) :
    SupportConnected (selectedGraph T (Finset.univ \ componentMembers T i A)) := by
  let B := Finset.univ \ componentMembers T i A
  let F := selectedGraph T B
  have hiB : i ∈ B := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,removed_not_mem T i A⟩
  have link (x : V) (hx : x ∈ F.support) : F.Reachable x (T.start i) := by
    obtain ⟨y,j,hj,hxy⟩ := hx
    by_cases hji : j=i
    · subst j
      exact selected_reachable T B i hiB (Walk.mem_support_of_adj_toSubgraph hxy) (T.walk i).start_mem_support
    · let C := (normalGraph T i).connectedComponentMk ⟨j,hji⟩
      have hjC : j ∈ componentMembers T i C := (mem_componentMembers T i j C).mpr ⟨hji,rfl⟩
      have hCA : C ≠ A := by
        rintro rfl
        exact (Finset.mem_sdiff.mp hj).2 hjC
      have hCB : componentMembers T i C ⊆ B := by
        intro l hl
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hlA ↦
          Finset.disjoint_left.mp (component_members_disjoint T i hCA) hl hlA⟩
      have hle : selectedGraph T (componentMembers T i C) ≤ F := CycleGroupDisjoint.selectedGraph_mono T hCB
      obtain ⟨z,hzi,hzC⟩ := component_meets_removed T hG i hn C
      have hxC : x ∈ (selectedGraph T (componentMembers T i C)).support := ⟨y,j,hjC,hxy⟩
      exact ((component_support_connected T i C x hxC z hzC).mono hle).trans
        (selected_reachable T B i hiB ((T.walk i).mem_verts_toSubgraph.mp hzi) (T.walk i).start_mem_support)
  intro x hx y hy
  exact (link x hx).trans (link y hy).symm

end Erdos583NormalComponentComplementDevelopment
