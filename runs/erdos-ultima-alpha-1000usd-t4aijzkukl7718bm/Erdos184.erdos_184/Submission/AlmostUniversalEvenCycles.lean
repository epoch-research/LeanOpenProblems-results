import Submission.OneEvenPaths
import Submission.CloseAdjacentEndpoints

/-! The sharp degree bound for an even graph with an almost-universal vertex.
This is a special case, not a uniform bound for arbitrary graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.AlmostUniversalCycles
open Critical OddPaths UniversalCycles
set_option maxHeartbeats 1600000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma base_even_at_non_neighbor {v w : V} (hw : w ≠ v) (hn : ¬ G.Adj v w)
    (he : ∀ x, Even (Nat.card (G.neighborSet x))) :
    Even (Nat.card ((Base (G := G) v).neighborSet ⟨w,hw⟩)) := by
  have hd := SimpleGraph.degree_induce_of_neighborSet_subset
    (G := G) (s := {x | x ≠ v}) (v := ⟨w,hw⟩) (by
      intro x hx hxv
      subst x
      exact hn hx.symm)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd
  change Nat.card ((Base (G := G) v).neighborSet ⟨w,hw⟩) = Nat.card (G.neighborSet w) at hd
  rw [hd]
  exact he w

/-- A single non-neighbor is permitted, and no extra cycle is needed. -/
lemma almost_universal_even_bound (v w : V) (hvw : v ≠ w) (hn : ¬ G.Adj v w)
    (hv : ∀ x, x ≠ v → x ≠ w → G.Adj v x)
    (he : ∀ x, Even (Nat.card (G.neighborSet x))) :
    2 * number G ≤ Fintype.card V - 2 := by
  let z : Rest v := ⟨w,hvw.symm⟩
  have hz : Even (Nat.card ((Base (G := G) v).neighborSet z)) :=
    base_even_at_non_neighbor hvw.symm hn he
  have ho (x : Rest v) (hx : x ≠ z) :
      Odd (Nat.card ((Base (G := G) v).neighborSet x)) := by
    have hxw : x.val ≠ w := fun h => hx (Subtype.ext h)
    have hd := degree_induce_except (G := G) (v := v) x (hv x.val x.property hxw).symm
    have h := Nat.even_iff.mp (he x.val)
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd
    change Nat.card ((Base (G := G) v).neighborSet x) + 1 = Nat.card (G.neighborSet x.val) at hd
    rw [Nat.odd_iff]
    omega
  obtain ⟨L,hLe,hLv,hcover,hcard⟩ := OneEven.full_partition z hz ho
  let f : Base (G := G) v →g G := (emb v).toHom
  have hf : Function.Injective f := (emb (G := G) v).injective
  let M := L.map (Piece.map f hf)
  have hME : edgeList M = (edgeList L).map (Sym2.map Subtype.val) := edgeList_map f hf L
  have hMV : endpoints M = (endpoints L).map Subtype.val := endpoints_map f hf L
  have hnM : (edgeList M).Nodup := by
    rw [hME]
    exact hLe.map (Sym2.map.injective Subtype.val_injective)
  have hvM : (endpoints M).Nodup := by
    rw [hMV]
    exact hLv.1.of_append_left.map Subtype.val_injective
  have havoid (p : Piece G) (hp : p ∈ M) : v ∉ p.walk.support := by
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    simp only [Piece.map,Walk.support_map,List.mem_map]
    rintro ⟨x,_,hx⟩
    exact x.property hx
  have hroot (a : V) (ha : a ∈ endpoints M) : G.Adj v a := by
    rw [hMV] at ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact hv x.val x.property (fun hxw => hLv.mem_iff.mp hx (Subtype.ext hxw))
  have hend (a : V) (ha : G.Adj v a) : a ∈ endpoints M := by
    rw [hMV]
    let x : Rest v := ⟨a,ha.ne.symm⟩
    refine List.mem_map.mpr ⟨x,hLv.mem_iff.mpr ?_,rfl⟩
    intro hx
    have haw : a = w := congrArg Subtype.val hx
    exact hn (haw ▸ ha)
  have hb := RootedClosure.packing_bound v M hnM hvM havoid hroot ∅ (by
    intro e heG
    induction e using Sym2.ind with | h a b =>
    by_cases ha : a = v
    · subst a
      exact Or.inr (Or.inl ⟨b,hend b heG,rfl⟩)
    · by_cases hb : b = v
      · subst b
        exact Or.inr (Or.inl ⟨a,hend a heG.symm,Sym2.eq_swap⟩)
      · let a' : Rest v := ⟨a,ha⟩
        let b' : Rest v := ⟨b,hb⟩
        apply Or.inl
        rw [hME]
        exact List.mem_map.mpr ⟨s(a',b'),(hcover _).mp heG,rfl⟩)
  have hM : M.length = L.length := by simp [M]
  have hrest : Fintype.card (Rest v) = Fintype.card V - 1 := by
    simp only [Rest,Fintype.card_subtype_compl,Fintype.card_unique]
  rw [hrest] at hcard
  simp only [Finset.card_empty,add_zero,hM] at hb
  omega

end Erdos184Work.AlmostUniversalCycles
#print axioms Erdos184Work.AlmostUniversalCycles.almost_universal_even_bound
