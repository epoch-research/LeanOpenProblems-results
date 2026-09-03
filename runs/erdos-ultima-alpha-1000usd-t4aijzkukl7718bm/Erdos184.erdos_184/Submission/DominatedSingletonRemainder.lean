import Submission.TransferParitySplit

/-! The even remainder at a dominated best-singleton edge contains a complete
bipartite two-hub subgraph. This is structural only: no bounded deletion loss
or hull comparison is asserted. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SingletonExchange
open Critical
set_option maxHeartbeats 800000
variable {V : Type*} [Fintype V]

lemma Best.dominated_neighbor_even {G F : SimpleGraph V} (hb : Best G F)
    {u v w : V} (huv : F.Adj u v)
    (hd : ∀ x, x ≠ u → G.Adj v x → G.Adj u x)
    (hwu : w ≠ u) (hvw : G.Adj v w) :
    (G \ F).Adj v w ∧ (G \ F).Adj u w := by
  have hvwF : ¬ F.Adj v w := by
    intro h
    exact hwu (hb.dominated_leaf huv hd w h)
  refine ⟨⟨hvw,hvwF⟩,hd w hwu hvw,?_⟩
  intro huw
  exact hb.singleton_neighbor_private huv.symm huw hvw.ne.symm hvw

lemma Best.dominated_even_neighborhood {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v)
    (hd : ∀ w, w ≠ u → G.Adj v w → G.Adj u w) :
    (G \ F).neighborSet v = G.neighborSet v \ {u} ∧
      (G \ F).neighborSet v ⊆ (G \ F).neighborSet u := by
  constructor
  · ext w
    constructor
    · rintro ⟨hG,hF⟩
      exact ⟨hG,fun h => hF (Set.mem_singleton_iff.mp h ▸ huv.symm)⟩
    · rintro ⟨hG,hn⟩
      exact (hb.dominated_neighbor_even huv hd (fun h => hn h) hG).1
  · intro w hw
    have hwu : w ≠ u := fun h => hw.2 (h ▸ huv.symm)
    exact (hb.dominated_neighbor_even huv hd hwu hw.1).2

/-- Two hubs joined to the same neighbor set, without an edge between hubs. -/
def doubleStar (u v : V) (S : Set V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => (x = u ∨ x = v) ∧ y ∈ S)

lemma doubleStar_neighbor_left {u v : V} {S : Set V}
    (hu : u ∉ S) (hv : v ∉ S) : (doubleStar u v S).neighborSet u = S := by
  ext w
  simp only [SimpleGraph.mem_neighborSet, doubleStar, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_,h | h⟩
    · exact h.2
    · exact (hu h.2).elim
  · intro hw
    exact ⟨fun h => hu (h ▸ hw),Or.inl ⟨Or.inl trivial,hw⟩⟩

lemma doubleStar_neighbor_right {u v : V} {S : Set V}
    (hu : u ∉ S) (hv : v ∉ S) : (doubleStar u v S).neighborSet v = S := by
  ext w
  simp only [SimpleGraph.mem_neighborSet, doubleStar, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_,h | h⟩
    · exact h.2
    · exact (hv h.2).elim
  · intro hw
    exact ⟨fun h => hv (h ▸ hw),Or.inl ⟨Or.inr trivial,hw⟩⟩

lemma doubleStar_neighbor_other {u v w : V} {S : Set V}
    (hu : u ∉ S) (hv : v ∉ S) (hwu : w ≠ u) (hwv : w ≠ v) :
    (doubleStar u v S).neighborSet w = if w ∈ S then {u,v} else ∅ := by
  ext x
  simp only [SimpleGraph.mem_neighborSet, doubleStar, SimpleGraph.fromRel_adj]
  by_cases hw : w ∈ S
  · rw [if_pos hw]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨_,h | h⟩
      · exact (h.1.elim hwu hwv).elim
      · exact h.1
    · intro hx
      exact ⟨fun he => hx.elim (fun h => hwu (he.trans h))
        (fun h => hwv (he.trans h)),Or.inr ⟨hx,hw⟩⟩
  · rw [if_neg hw]
    simp only [Set.mem_empty_iff_false,iff_false]
    intro h
    exact h.2.elim (fun h => h.1.elim hwu hwv) (fun h => hw h.2)

lemma doubleStar_even {u v : V} {S : Set V} (huv : u ≠ v)
    (hu : u ∉ S) (hv : v ∉ S) (hs : Even (Nat.card S)) :
    ∀ w, Even (Nat.card ((doubleStar u v S).neighborSet w)) := by
  intro w
  by_cases hwu : w = u
  · subst w
    rwa [doubleStar_neighbor_left hu hv]
  by_cases hwv : w = v
  · subst w
    rwa [doubleStar_neighbor_right hu hv]
  rw [doubleStar_neighbor_other hu hv hwu hwv]
  split_ifs <;> simp [huv]

lemma Best.dominated_doubleStar {G F : SimpleGraph V} (hb : Best G F)
    {u v : V} (huv : F.Adj u v)
    (hd : ∀ w, w ≠ u → G.Adj v w → G.Adj u w) :
    let E := G \ F
    let M := doubleStar u v (E.neighborSet v)
    M ≤ E ∧ (∀ w, Even (Nat.card (M.neighborSet w))) ∧
      (∀ w, Even (Nat.card ((E \ M).neighborSet w))) := by
  dsimp only
  have hn := (hb.dominated_even_neighborhood huv hd).2
  have hu : u ∉ (G \ F).neighborSet v := fun h => h.2 huv.symm
  have hv : v ∉ (G \ F).neighborSet v := (G \ F).loopless v
  have hME : doubleStar u v ((G \ F).neighborSet v) ≤ G \ F := by
    intro x y hxy
    rcases hxy with ⟨_,⟨hx,hy⟩ | ⟨hy,hx⟩⟩
    · rcases hx with rfl | rfl
      · exact hn hy
      · exact hy
    · rcases hy with rfl | rfl
      · exact (hn hx).symm
      · exact hx.symm
  have hM := doubleStar_even huv.ne hu hv (hb.1.2.1 v)
  refine ⟨hME,hM,?_⟩
  intro w
  have h := degree_sdiff_add (G \ F) _ hME w
  have hE := Nat.even_iff.mp (hb.1.2.1 w)
  have hM' := Nat.even_iff.mp (hM w)
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at h
  rw [Nat.even_iff]
  omega

end Erdos184Work.SingletonExchange
#print axioms Erdos184Work.SingletonExchange.Best.dominated_doubleStar
