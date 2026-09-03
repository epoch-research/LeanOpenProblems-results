import Submission.EmbeddingPathFamily

/-! A universal vertex closes the odd part after a sparse parity correction. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UniversalCycles
open OddPaths Critical
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable (v : V) (hv : ∀ x : V, x ≠ v → G.Adj v x)

include hv in
lemma odd_base_budget (R : SimpleGraph (Rest v)) (hR : R ≤ Base (G := G) v)
    (ho : ∀ x, Odd (Nat.card (R.neighborSet x))) (F : Finset (Sym2 (Rest v)))
    (hcov : ∀ a b, (Base (G := G) v).Adj a b → R.Adj a b ∨ s(a,b) ∈ F) :
    2 * number G ≤ Fintype.card (Rest v) + 2 * F.card := by
  let f : R →g G := ⟨Subtype.val, fun h => hR h⟩
  have hf : Function.Injective f := Subtype.val_injective
  obtain ⟨L,hL,hcover,hcard⟩ := all_odd_path_partition R ho
  let M := L.map (Piece.map f hf)
  have hME : edgeList M = (edgeList L).map (Sym2.map Subtype.val) := edgeList_map f hf L
  have hMV : endpoints M = (endpoints L).map Subtype.val := endpoints_map f hf L
  have hnM : (edgeList M).Nodup := by
    rw [hME]
    exact hL.1.map (Sym2.map.injective Subtype.val_injective)
  have hvM : (endpoints M).Nodup := by
    rw [hMV]
    exact hL.2.1.map Subtype.val_injective
  have havoid (p : Piece G) (hp : p ∈ M) : v ∉ p.walk.support := by
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    simp only [Piece.map,Walk.support_map,List.mem_map]
    rintro ⟨x,_,hx⟩
    exact x.property hx
  have hend (a : V) (ha : a ≠ v) : a ∈ endpoints M := by
    rw [hMV]
    exact List.mem_map.mpr ⟨⟨a,ha⟩,hL.2.2 _,rfl⟩
  let F' := F.image (Sym2.map Subtype.val)
  have hb := Avoiding.packing_bound v hv M hnM hvM havoid F' (by
    intro e he
    induction e using Sym2.ind with | h a b =>
    by_cases ha : a = v
    · subst a
      exact Or.inr (Or.inl ⟨b,hend b he.ne.symm,rfl⟩)
    · by_cases hb : b = v
      · subst b
        exact Or.inr (Or.inl ⟨a,hend a ha,Sym2.eq_swap⟩)
      · let a' : Rest v := ⟨a,ha⟩
        let b' : Rest v := ⟨b,hb⟩
        rcases hcov a' b' he with heR | heF
        · apply Or.inl
          rw [hME]
          exact List.mem_map.mpr ⟨s(a',b'),(hcover _).mp heR,rfl⟩
        · exact Or.inr (Or.inr (Finset.mem_image.mpr ⟨s(a',b'),heF,rfl⟩)))
  have hF : F'.card ≤ F.card := Finset.card_image_le
  have hM : M.length = L.length := by simp [M]
  omega

include hv in
lemma leaf_base_budget (R : SimpleGraph (Rest v)) (hR : R ≤ Base (G := G) v) (r : Rest v)
    (hr : Even (R.degree r)) (ho : ∀ x, x ≠ r → Odd (R.degree x))
    (F : Finset (Sym2 (Rest v)))
    (hcov : ∀ a b, (Base (G := G) v).Adj a b → R.Adj a b ∨ s(a,b) ∈ F) :
    2 * number G ≤ 3 * Fintype.card V + 2 * F.card := by
  let H := attachLeaf v R r
  have hHG : H ≤ G := by
    intro a b hab
    rcases hab with hab | ⟨_,hab | hab⟩
    · obtain ⟨ha,hb,hab⟩ := (spanning_adj_iff v R).mp hab
      exact hR hab
    · rcases hab with ⟨rfl,rfl⟩
      exact hv _ r.property
    · rcases hab with ⟨rfl,rfl⟩
      exact (hv _ r.property).symm
  obtain ⟨M,t,P,hnM,hvM,havoid,hend,hcover,hcard,hP⟩ :=
    remove_leaf_path hHG v (attach_all_odd v R r hr ho) (by
      intro a ha b hb
      exact ((attach_leaf_adj v R r a).mp ha).trans ((attach_leaf_adj v R r b).mp hb).symm)
  let F' := F.image (Sym2.map Subtype.val) ∪ P ∪ {s(v,t)}
  have hb := Avoiding.packing_bound v hv M hnM hvM havoid F' (by
    intro e he
    induction e using Sym2.ind with | h a b =>
    by_cases ha : a = v
    · subst a
      by_cases hbt : b = t
      · exact Or.inr (Or.inr (by simp [F',hbt]))
      · exact Or.inr (Or.inl ⟨b,hend b he.ne.symm hbt,rfl⟩)
    · by_cases hb : b = v
      · subst b
        by_cases hat : a = t
        · exact Or.inr (Or.inr (by simp [F',hat,Sym2.eq_swap]))
        · exact Or.inr (Or.inl ⟨a,hend a ha hat,Sym2.eq_swap⟩)
      · let a' : Rest v := ⟨a,ha⟩
        let b' : Rest v := ⟨b,hb⟩
        rcases hcov a' b' he with heR | heF
        · have heH : s(a,b) ∈ H.edgeSet := Or.inl ((spanning_adj_iff v R).mpr ⟨ha,hb,heR⟩)
          rcases hcover _ heH with hm | hp
          · exact Or.inl hm
          · exact Or.inr (Or.inr (by simp [F',hp]))
        · exact Or.inr (Or.inr (by
            apply Finset.mem_union_left
            apply Finset.mem_union_left
            exact Finset.mem_image.mpr ⟨s(a',b'),heF,rfl⟩)))
  have hc₁ := Finset.card_union_le (F.image (Sym2.map Subtype.val)) P
  have hc₂ := Finset.card_union_le (F.image (Sym2.map Subtype.val) ∪ P) {s(v,t)}
  have hc₃ : (F.image (Sym2.map Subtype.val)).card ≤ F.card := Finset.card_image_le
  simp only [Finset.card_singleton] at hc₂
  change F'.card ≤ _ at hc₂
  omega

end Erdos184Work.UniversalCycles
#print axioms Erdos184Work.UniversalCycles.odd_base_budget
#print axioms Erdos184Work.UniversalCycles.leaf_base_budget
