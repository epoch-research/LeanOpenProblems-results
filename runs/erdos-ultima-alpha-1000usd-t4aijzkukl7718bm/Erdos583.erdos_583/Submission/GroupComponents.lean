import Submission.Work

/-! Connected components of an arbitrary selected member family. -/
namespace Erdos583GroupComponentsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.MemberExpansion
open scoped Classical
set_option maxHeartbeats 1800000
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

def inducedGraph (T : TrailFamily G k) (B : Finset (Fin k)) : SimpleGraph {j : Fin k // j ∈ B} :=
  (intersectionGraph T).induce {j | j ∈ B}

noncomputable def componentMembers (T : TrailFamily G k) (B : Finset (Fin k))
    (C : (inducedGraph T B).ConnectedComponent) : Finset (Fin k) :=
  C.supp.toFinset.image Subtype.val

lemma mem_componentMembers (T : TrailFamily G k) (B : Finset (Fin k)) (j : Fin k)
    (C : (inducedGraph T B).ConnectedComponent) :
    j ∈ componentMembers T B C ↔ ∃ h : j ∈ B, (⟨j,h⟩ : {j // j ∈ B}) ∈ C.supp := by
  classical
  simp only [componentMembers,Finset.mem_image,Set.mem_toFinset]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,hx⟩
  · rintro ⟨h,hj⟩
    exact ⟨⟨j,h⟩,hj,rfl⟩

lemma componentMembers_subset (T : TrailFamily G k) (B : Finset (Fin k))
    (C : (inducedGraph T B).ConnectedComponent) : componentMembers T B C ⊆ B := by
  intro j hj
  exact ((mem_componentMembers T B j C).mp hj).1

lemma componentMembers_nonempty (T : TrailFamily G k) (B : Finset (Fin k))
    (C : (inducedGraph T B).ConnectedComponent) : (componentMembers T B C).Nonempty := by
  obtain ⟨j,hj⟩ := C.nonempty_supp
  exact ⟨j.val,(mem_componentMembers T B j.val C).mpr ⟨j.property,hj⟩⟩

lemma componentMembers_card (T : TrailFamily G k) (B : Finset (Fin k))
    (C : (inducedGraph T B).ConnectedComponent) : (componentMembers T B C).card=C.supp.ncard := by
  classical
  rw [componentMembers,Finset.card_image_of_injective _ Subtype.val_injective,Set.toFinset_card]
  rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]

lemma component_support_connected (T : TrailFamily G k) (B : Finset (Fin k))
    (C : (inducedGraph T B).ConnectedComponent) :
    SupportConnected (selectedGraph T (componentMembers T B C)) := by
  let A := componentMembers T B C
  have link {j l : {j : Fin k // j ∈ B}} (hj : j ∈ C.supp) (hl : l ∈ C.supp) :
      (selectedGraph T A).Reachable (T.start j.val) (T.start l.val) := by
    have hreach := C.reachable_toSimpleGraph hj hl
    apply reachable_map_to_reachable (fun z : C.supp ↦ T.start z.val.val) _ hreach
    intro a b hab
    obtain ⟨_,v,hva,hvb⟩ := hab
    have ha : a.val.val ∈ A := (mem_componentMembers T B a.val.val C).mpr ⟨a.val.property,a.property⟩
    have hb : b.val.val ∈ A := (mem_componentMembers T B b.val.val C).mpr ⟨b.val.property,b.property⟩
    exact (selected_reachable T A a.val.val ha (T.walk a.val.val).start_mem_support hva).trans
      (selected_reachable T A b.val.val hb hvb (T.walk b.val.val).start_mem_support)
  rintro x ⟨u,j,hj,hxu⟩ y ⟨v,l,hl,hyv⟩
  obtain ⟨hji,hjC⟩ := (mem_componentMembers T B j C).mp hj
  obtain ⟨hli,hlC⟩ := (mem_componentMembers T B l C).mp hl
  exact (selected_reachable T A j hj (Walk.mem_support_of_adj_toSubgraph hxu)
    (T.walk j).start_mem_support).trans ((link hjC hlC).trans
      (selected_reachable T A l hl (T.walk l).start_mem_support
        (Walk.mem_support_of_adj_toSubgraph hyv)))

lemma same_component_of_intersection (T : TrailFamily G k) (B : Finset (Fin k))
    {j l : Fin k} (hji : j ∈ B) (hli : l ∈ B) {v : V}
    (hj : v ∈ (T.walk j).support) (hl : v ∈ (T.walk l).support) :
    (inducedGraph T B).connectedComponentMk ⟨j,hji⟩ =
      (inducedGraph T B).connectedComponentMk ⟨l,hli⟩ := by
  by_cases h : j=l
  · subst l; rfl
  · exact ConnectedComponent.sound (Adj.reachable (show (inducedGraph T B).Adj ⟨j,hji⟩ ⟨l,hli⟩
      from ⟨h,v,hj,hl⟩))

lemma component_support_disjoint (T : TrailFamily G k) (B : Finset (Fin k))
    {C D : (inducedGraph T B).ConnectedComponent} (hCD : C ≠ D) :
    Disjoint (selectedGraph T (componentMembers T B C)).support
      (selectedGraph T (componentMembers T B D)).support := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u,j,hj,hxu⟩ ⟨v,l,hl,hxv⟩
  obtain ⟨hji,hjC⟩ := (mem_componentMembers T B j C).mp hj
  obtain ⟨hli,hlD⟩ := (mem_componentMembers T B l D).mp hl
  have he := same_component_of_intersection T B hji hli
    (Walk.mem_support_of_adj_toSubgraph hxu) (Walk.mem_support_of_adj_toSubgraph hxv)
  exact hCD (hjC.symm.trans (he.trans hlD))

lemma component_support_closed (T : TrailFamily G k) (B : Finset (Fin k))
    (C : (inducedGraph T B).ConnectedComponent) {x y : V}
    (hx : x ∈ (selectedGraph T (componentMembers T B C)).support) (hxy : G.Adj x y) :
    (∃ l, l ∉ B ∧ x ∈ (T.walk l).support) ∨ y ∈ (selectedGraph T (componentMembers T B C)).support := by
  obtain ⟨u,j,hj,hxu⟩ := hx
  obtain ⟨hjB,hjC⟩ := (mem_componentMembers T B j C).mp hj
  obtain ⟨l,hl⟩ := (T.cover s(x,y)).mp hxy
  by_cases hlB : l ∈ B
  · have hxl := Walk.mem_support_of_adj_toSubgraph hl
    have he := same_component_of_intersection T B hjB hlB (Walk.mem_support_of_adj_toSubgraph hxu) hxl
    have hlC : (⟨l,hlB⟩ : {j // j ∈ B}) ∈ C.supp := he.symm.trans hjC
    exact Or.inr ⟨x,l,(mem_componentMembers T B l C).mpr ⟨hlB,hlC⟩,hl.symm⟩
  · exact Or.inl ⟨l,hlB,Walk.mem_support_of_adj_toSubgraph hl⟩

lemma component_meets_outside (T : TrailFamily G k) (hG : G.Connected) (B : Finset (Fin k))
    (hout : ∃ i, i ∉ B) (hn : ∀ j, ¬(T.walk j).Nil) (C : (inducedGraph T B).ConnectedComponent) :
    ∃ l, l ∉ B ∧ ∃ x ∈ (T.walk l).support, x ∈ (selectedGraph T (componentMembers T B C)).support := by
  classical
  by_contra hno
  let S := (selectedGraph T (componentMembers T B C)).support
  have hdis : ∀ l, l ∉ B → ∀ x ∈ S, x ∉ (T.walk l).support := by
    intro l hl x hx hi
    exact hno ⟨l,hl,x,hi,hx⟩
  have hclosed {x y : V} (hx : x ∈ S) (hxy : G.Adj x y) : y ∈ S := by
    rcases component_support_closed T B C hx hxy with ⟨l,hl,hxl⟩|hy
    · exact (hdis l hl x hx hxl).elim
    · exact hy
  have transport {x y : V} (p : G.Walk x y) : x ∈ S → y ∈ S := by
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hx ↦ ih (hclosed hx h)
  obtain ⟨j,hj⟩ := componentMembers_nonempty T B C
  have hx : T.start j ∈ S := by
    dsimp only [S]
    rw [selected_support_eq T _ (fun j _ ↦ hn j)]
    exact ⟨j,hj,(T.walk j).start_mem_support⟩
  obtain ⟨i,hi⟩ := hout
  obtain ⟨p⟩ := hG (T.start j) (T.start i)
  exact hdis i hi _ (transport p hx) (T.walk i).start_mem_support

lemma sum_component_members [Fintype V] (T : TrailFamily G k) (B : Finset (Fin k)) :
    ∑ C : (inducedGraph T B).ConnectedComponent, (componentMembers T B C).card=B.card := by
  classical
  simp_rw [componentMembers_card]
  convert (ComponentBudget.sum_component_orders (inducedGraph T B)) using 1
  · apply Finset.sum_congr
    · ext C
      simp only [Finset.mem_univ]
    · intro C _
      rfl
  · simp only [Fintype.card_coe]


lemma component_support_union (T : TrailFamily G k) (B : Finset (Fin k)) :
    (⋃ C : (inducedGraph T B).ConnectedComponent,
      (selectedGraph T (componentMembers T B C)).support)=
      (selectedGraph T B).support := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨C,y,j,hj,hxy⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hji,_⟩ := (mem_componentMembers T B j C).mp hj
    exact ⟨y,j,hji,hxy⟩
  · rintro ⟨y,j,hj,hxy⟩
    have hji := hj
    let C := (inducedGraph T B).connectedComponentMk ⟨j,hji⟩
    exact Set.mem_iUnion.mpr ⟨C,y,j,(mem_componentMembers T B j C).mpr ⟨hji,rfl⟩,hxy⟩

lemma sum_component_support [Fintype V] (T : TrailFamily G k) (B : Finset (Fin k)) :
    ∑ C : (inducedGraph T B).ConnectedComponent,
      (selectedGraph T (componentMembers T B C)).support.ncard =
      (selectedGraph T B).support.ncard := by
  classical
  rw [←component_support_union]
  rw [Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) (fun _ _ h ↦ component_support_disjoint T B h)]
  exact (finsum_eq_sum_of_fintype _).symm


end Erdos583GroupComponentsDevelopment
