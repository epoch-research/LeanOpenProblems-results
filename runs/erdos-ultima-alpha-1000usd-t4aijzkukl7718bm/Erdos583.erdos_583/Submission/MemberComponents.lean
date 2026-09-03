import Submission.CycleGroupDisjoint

/-! Connected components of the normal members after removing a whole-cycle
member, with exact support and member-count sums. -/
namespace Erdos583MemberComponentsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.VertexCritical Erdos583Work.BridgeGlue
open Erdos583MemberExpansionDevelopment Erdos583MemberNormalExpansionDevelopment
open Erdos583CycleGroupDisjointDevelopment
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

def normalGraph (T : TrailFamily G k) (i : Fin k) : SimpleGraph {j : Fin k // j ≠ i} :=
  (intersectionGraph T).induce {j | j ≠ i}

noncomputable def componentMembers (T : TrailFamily G k) (i : Fin k)
    (C : (normalGraph T i).ConnectedComponent) : Finset (Fin k) :=
  C.supp.toFinset.image Subtype.val

lemma mem_componentMembers (T : TrailFamily G k) (i j : Fin k)
    (C : (normalGraph T i).ConnectedComponent) :
    j ∈ componentMembers T i C ↔ ∃ h : j ≠ i, (⟨j,h⟩ : {j // j ≠ i}) ∈ C.supp := by
  classical
  simp only [componentMembers,Finset.mem_image,Set.mem_toFinset]
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,hx⟩
  · rintro ⟨h,hj⟩
    exact ⟨⟨j,h⟩,hj,rfl⟩

lemma removed_not_mem (T : TrailFamily G k) (i : Fin k)
    (C : (normalGraph T i).ConnectedComponent) : i ∉ componentMembers T i C := by
  intro hi
  obtain ⟨h,_⟩ := (mem_componentMembers T i i C).mp hi
  exact h rfl

lemma componentMembers_nonempty (T : TrailFamily G k) (i : Fin k)
    (C : (normalGraph T i).ConnectedComponent) : (componentMembers T i C).Nonempty := by
  obtain ⟨j,hj⟩ := C.nonempty_supp
  exact ⟨j.val,(mem_componentMembers T i j.val C).mpr ⟨j.property,hj⟩⟩

lemma componentMembers_card (T : TrailFamily G k) (i : Fin k)
    (C : (normalGraph T i).ConnectedComponent) : (componentMembers T i C).card=C.supp.ncard := by
  classical
  rw [componentMembers,Finset.card_image_of_injective _ Subtype.val_injective,Set.toFinset_card]
  rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]

lemma component_support_connected (T : TrailFamily G k) (i : Fin k)
    (C : (normalGraph T i).ConnectedComponent) :
    SupportConnected (selectedGraph T (componentMembers T i C)) := by
  let A := componentMembers T i C
  have link {j l : {j : Fin k // j ≠ i}} (hj : j ∈ C.supp) (hl : l ∈ C.supp) :
      (selectedGraph T A).Reachable (T.start j.val) (T.start l.val) := by
    have hreach := C.reachable_toSimpleGraph hj hl
    apply reachable_map_to_reachable (fun z : C.supp ↦ T.start z.val.val) _ hreach
    intro a b hab
    obtain ⟨_,v,hva,hvb⟩ := hab
    have ha : a.val.val ∈ A := (mem_componentMembers T i a.val.val C).mpr ⟨a.val.property,a.property⟩
    have hb : b.val.val ∈ A := (mem_componentMembers T i b.val.val C).mpr ⟨b.val.property,b.property⟩
    exact (selected_reachable T A a.val.val ha (T.walk a.val.val).start_mem_support hva).trans
      (selected_reachable T A b.val.val hb hvb (T.walk b.val.val).start_mem_support)
  rintro x ⟨u,j,hj,hxu⟩ y ⟨v,l,hl,hyv⟩
  obtain ⟨hji,hjC⟩ := (mem_componentMembers T i j C).mp hj
  obtain ⟨hli,hlC⟩ := (mem_componentMembers T i l C).mp hl
  exact (selected_reachable T A j hj (Walk.mem_support_of_adj_toSubgraph hxu)
    (T.walk j).start_mem_support).trans ((link hjC hlC).trans
      (selected_reachable T A l hl (T.walk l).start_mem_support
        (Walk.mem_support_of_adj_toSubgraph hyv)))

lemma same_component_of_intersection (T : TrailFamily G k) (i : Fin k)
    {j l : Fin k} (hji : j ≠ i) (hli : l ≠ i) {v : V}
    (hj : v ∈ (T.walk j).support) (hl : v ∈ (T.walk l).support) :
    (normalGraph T i).connectedComponentMk ⟨j,hji⟩ =
      (normalGraph T i).connectedComponentMk ⟨l,hli⟩ := by
  by_cases h : j=l
  · subst l; rfl
  · exact ConnectedComponent.sound (Adj.reachable (show (normalGraph T i).Adj ⟨j,hji⟩ ⟨l,hli⟩
      from ⟨h,v,hj,hl⟩))

lemma component_support_disjoint (T : TrailFamily G k) (i : Fin k)
    {C D : (normalGraph T i).ConnectedComponent} (hCD : C ≠ D) :
    Disjoint (selectedGraph T (componentMembers T i C)).support
      (selectedGraph T (componentMembers T i D)).support := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u,j,hj,hxu⟩ ⟨v,l,hl,hxv⟩
  obtain ⟨hji,hjC⟩ := (mem_componentMembers T i j C).mp hj
  obtain ⟨hli,hlD⟩ := (mem_componentMembers T i l D).mp hl
  have he := same_component_of_intersection T i hji hli
    (Walk.mem_support_of_adj_toSubgraph hxu) (Walk.mem_support_of_adj_toSubgraph hxv)
  exact hCD (hjC.symm.trans (he.trans hlD))

lemma component_support_closed (T : TrailFamily G k) (i : Fin k)
    (C : (normalGraph T i).ConnectedComponent) {x y : V}
    (hx : x ∈ (selectedGraph T (componentMembers T i C)).support) (hxy : G.Adj x y) :
    x ∈ (T.walk i).support ∨ y ∈ (selectedGraph T (componentMembers T i C)).support := by
  obtain ⟨u,j,hj,hxu⟩ := hx
  obtain ⟨hji,hjC⟩ := (mem_componentMembers T i j C).mp hj
  obtain ⟨l,hl⟩ := (T.cover s(x,y)).mp hxy
  by_cases hli : l=i
  · subst l
    exact Or.inl (Walk.mem_support_of_adj_toSubgraph hl)
  · have hxl := Walk.mem_support_of_adj_toSubgraph hl
    have he := same_component_of_intersection T i hji hli (Walk.mem_support_of_adj_toSubgraph hxu) hxl
    have hlC : (⟨l,hli⟩ : {j // j ≠ i}) ∈ C.supp := he.symm.trans hjC
    exact Or.inr ⟨x,l,(mem_componentMembers T i l C).mpr ⟨hli,hlC⟩,hl.symm⟩

/-- In a connected graph, every nonempty normal component meets the removed
member. No hypothesis of a cycle or of maximality is used here. -/
lemma component_meets_removed (T : TrailFamily G k) (hG : G.Connected) (i : Fin k)
    (hn : ∀ j, ¬(T.walk j).Nil) (C : (normalGraph T i).ConnectedComponent) :
    ((T.walk i).toSubgraph.verts ∩ (selectedGraph T (componentMembers T i C)).support).Nonempty := by
  classical
  by_contra hno
  let S := (selectedGraph T (componentMembers T i C)).support
  have hdis : ∀ x ∈ S, x ∉ (T.walk i).support := by
    intro x hx hi
    exact hno ⟨x,(T.walk i).mem_verts_toSubgraph.mpr hi,hx⟩
  have hclosed {x y : V} (hx : x ∈ S) (hxy : G.Adj x y) : y ∈ S :=
    (component_support_closed T i C hx hxy).resolve_left (hdis x hx)
  have transport {x y : V} (p : G.Walk x y) : x ∈ S → y ∈ S := by
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hx ↦ ih (hclosed hx h)
  obtain ⟨j,hj⟩ := componentMembers_nonempty T i C
  have hx : T.start j ∈ S := by
    dsimp only [S]
    rw [selected_support_eq T _ (fun j _ ↦ hn j)]
    exact ⟨j,hj,(T.walk j).start_mem_support⟩
  obtain ⟨p⟩ := hG (T.start j) (T.start i)
  exact hdis _ (transport p hx) (T.walk i).start_mem_support

lemma sum_component_members [Fintype V] (T : TrailFamily G k) (i : Fin k) :
    ∑ C : (normalGraph T i).ConnectedComponent, (componentMembers T i C).card=k-1 := by
  classical
  simp_rw [componentMembers_card]
  convert (ComponentBudget.sum_component_orders (normalGraph T i)) using 1
  · apply Finset.sum_congr
    · ext C
      simp only [Finset.mem_univ]
    · intro C _
      rfl
  · simp only [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_unique]


lemma component_support_union (T : TrailFamily G k) (i : Fin k) :
    (⋃ C : (normalGraph T i).ConnectedComponent,
      (selectedGraph T (componentMembers T i C)).support)=
      (selectedGraph T (Finset.univ.erase i)).support := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨C,y,j,hj,hxy⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hji,_⟩ := (mem_componentMembers T i j C).mp hj
    exact ⟨y,j,by simp [hji],hxy⟩
  · rintro ⟨y,j,hj,hxy⟩
    have hji := (Finset.mem_erase.mp hj).1
    let C := (normalGraph T i).connectedComponentMk ⟨j,hji⟩
    exact Set.mem_iUnion.mpr ⟨C,y,j,(mem_componentMembers T i j C).mpr ⟨hji,rfl⟩,hxy⟩

lemma sum_component_support [Fintype V] (T : TrailFamily G k) (i : Fin k) :
    ∑ C : (normalGraph T i).ConnectedComponent,
      (selectedGraph T (componentMembers T i C)).support.ncard =
      (selectedGraph T (Finset.univ.erase i)).support.ncard := by
  classical
  rw [←component_support_union]
  rw [Set.ncard_iUnion_of_finite (fun _ ↦ Set.toFinite _) (fun _ _ h ↦ component_support_disjoint T i h)]
  exact (finsum_eq_sum_of_fintype _).symm

lemma cycle_component_expands {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n}
    (P : G.Walk a a) (hp : P.IsCycle) (hi : (T.walk i).toSubgraph=P.toSubgraph)
    (C : (normalGraph T i).ConnectedComponent) :
    2*(componentMembers T i C).card ≤ (selectedGraph T (componentMembers T i C)).support.ncard := by
  have hnp := CycleEar.cycle_member_not_path T i P hp hi
  have hconn := component_support_connected T i C
  have hia := removed_not_mem T i C
  have hb := normal_group_expands hsmall hfail T hs i hnp _ hia hconn
  have hneq : 2*(componentMembers T i C).card ≠
      (selectedGraph T (componentMembers T i C)).support.ncard+1 := by
    intro heq
    have hd := tight_normal_group_disjoint_cycle hsmall hfail T hs hm i P hp hi _ hia hconn heq
    obtain ⟨x,hxi,hxC⟩ := component_meets_removed T hG i (NilSlot.max_score_nonpath_no_nil T hm ⟨i,hnp⟩) C
    exact Set.disjoint_left.mp hd (hi ▸ hxi) hxC
  omega

lemma cycle_normal_support_bound {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hs : T.score+1=G.edgeSet.ncard+⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hm : ∀ U : TrailFamily G ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊, U.score ≤ T.score)
    (i : Fin ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) {a : Fin n}
    (P : G.Walk a a) (hp : P.IsCycle) (hi : (T.walk i).toSubgraph=P.toSubgraph) :
    2*(⌈(Fintype.card (Fin n) : ℚ)/2⌉₊-1) ≤
      (selectedGraph T (Finset.univ.erase i)).support.ncard := by
  classical
  rw [←sum_component_support,←sum_component_members T i,Finset.mul_sum]
  exact Finset.sum_le_sum (fun C _ ↦ cycle_component_expands hsmall hG hfail T hs hm i P hp hi C)

end Erdos583MemberComponentsDevelopment
