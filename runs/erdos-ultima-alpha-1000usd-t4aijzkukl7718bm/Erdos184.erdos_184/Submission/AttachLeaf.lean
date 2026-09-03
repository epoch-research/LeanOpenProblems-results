import Submission.LeafPathRemoval

/-! Attaching a single leaf to a spanning induced-type graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.UniversalCycles
open OddPaths Critical
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] (v : V) (R : SimpleGraph (Rest v)) (r : Rest v)

noncomputable def attachLeaf : SimpleGraph V :=
  R.spanningCoe ⊔ SimpleGraph.fromRel (fun x y => x = v ∧ y = r.val)

lemma spanning_adj_iff {x y : V} : R.spanningCoe.Adj x y ↔
    ∃ (hx : x ≠ v) (hy : y ≠ v), R.Adj ⟨x,hx⟩ ⟨y,hy⟩ := by
  simp only [SimpleGraph.spanningCoe,SimpleGraph.map_adj]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    subst x; subst y
    exact ⟨a.property,b.property,hab⟩
  · rintro ⟨hx,hy,hxy⟩
    exact ⟨⟨x,hx⟩,⟨y,hy⟩,hxy,rfl,rfl⟩

lemma attach_leaf_adj (x : V) : (attachLeaf v R r).Adj v x ↔ x = r.val := by
  simp only [attachLeaf,SimpleGraph.sup_adj,spanning_adj_iff,ne_eq,not_true_eq_false,
    exists_false,SimpleGraph.fromRel_adj]
  constructor
  · rintro (h | ⟨_,h | h⟩)
    · exact h.choose.elim
    · exact h.2
    · exact (r.property h.2.symm).elim
  · intro h
    subst x
    exact Or.inr ⟨r.property.symm,Or.inl ⟨True.intro,rfl⟩⟩

lemma attach_leaf_degree : (attachLeaf v R r).degree v = 1 := by
  have hn : (attachLeaf v R r).neighborFinset v = {r.val} := by
    ext x
    simp [attach_leaf_adj]
  rw [← SimpleGraph.card_neighborFinset_eq_degree,hn,Finset.card_singleton]

lemma attach_base_neighbors (x : Rest v) :
    (attachLeaf v R r).neighborFinset x.val =
      (R.neighborFinset x).map (Function.Embedding.subtype _) ∪ (if x = r then {v} else ∅) := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_union,Finset.mem_map,
    Function.Embedding.subtype_apply]
  constructor
  · intro h
    rcases h with h | ⟨_,h | h⟩
    · obtain ⟨hx,hy,hxy⟩ := (spanning_adj_iff v R).mp h
      exact Or.inl ⟨⟨y,hy⟩,hxy,rfl⟩
    · exact (x.property h.1).elim
    · have hx : x = r := Subtype.ext h.2
      exact Or.inr (by simp [hx,h.1])
  · rintro (⟨z,hz,rfl⟩ | h)
    · exact Or.inl ((spanning_adj_iff v R).mpr ⟨x.property,z.property,hz⟩)
    · by_cases hx : x = r
      · have hy : y = v := by simpa only [if_pos hx,Finset.mem_singleton] using h
        subst y
        exact (attach_leaf_adj v R r x.val).mpr (congrArg Subtype.val hx) |>.symm
      · exact (show False by simpa [hx] using h).elim

lemma attach_base_degree (x : Rest v) :
    (attachLeaf v R r).degree x.val = R.degree x + if x = r then 1 else 0 := by
  have hd : Disjoint ((R.neighborFinset x).map (Function.Embedding.subtype _))
      (if x = r then {v} else ∅) := by
    by_cases hx : x = r
    · rw [if_pos hx,Finset.disjoint_singleton_right]
      simp only [Finset.mem_map,Function.Embedding.subtype_apply,not_exists,not_and]
      intro y _
      exact y.property
    · simp [hx]
  rw [← SimpleGraph.card_neighborFinset_eq_degree,attach_base_neighbors,
    Finset.card_union_of_disjoint hd,Finset.card_map,SimpleGraph.card_neighborFinset_eq_degree]
  split_ifs <;> simp

lemma attach_all_odd (hr : Even (R.degree r)) (ho : ∀ x, x ≠ r → Odd (R.degree x)) :
    ∀ x, Odd (Nat.card ((attachLeaf v R r).neighborSet x)) := by
  intro x
  have h : Odd ((attachLeaf v R r).degree x) := by
    by_cases hx : x = v
    · subst x
      rw [attach_leaf_degree]
      decide
    · let x' : Rest v := ⟨x,hx⟩
      have hd := attach_base_degree v R r x'
      change (attachLeaf v R r).degree x = _ at hd
      rw [hd]
      by_cases hxr : x' = r
      · rw [if_pos hxr,hxr]
        exact hr.add_odd (by decide)
      · rw [if_neg hxr,add_zero]
        exact ho x' hxr
  simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h

end Erdos184Work.UniversalCycles
#print axioms Erdos184Work.UniversalCycles.attach_all_odd
