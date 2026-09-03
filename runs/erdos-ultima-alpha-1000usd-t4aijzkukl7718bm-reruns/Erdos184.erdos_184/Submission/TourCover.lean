import Submission.Euler

/-! Unrolling a closed Euler tour into a cycle graph. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

lemma cycleGraph_adj_successor {n : ℕ} (i j : Fin (n + 3)) :
    (cycleGraph (n + 3)).Adj i j ↔ j = i + 1 ∨ i = j + 1 := by
  change j ∈ (cycleGraph (n + 3)).neighborSet i ↔ _
  rw [cycleGraph_neighborSet]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr (by simp [h])
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (by simp [h])

lemma cycleGraph_edge_successor {n : ℕ} {e : Sym2 (Fin (n + 3))}
    (he : e ∈ (cycleGraph (n + 3)).edgeSet) :
    ∃ i : Fin (n + 3), e = s(i, i + 1) := by
  induction e using Sym2.ind with
  | h i j =>
    rcases (cycleGraph_adj_successor i j).mp he with h | h
    · exact ⟨i, by rw [h]⟩
    · exact ⟨j, by rw [h, Sym2.eq_swap]⟩

lemma getVert_cyclic_successor {V : Type*} {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) {n : ℕ} (hl : p.length = n + 3) (i : Fin (n + 3)) :
    p.getVert (i + 1).val = p.getVert (i.val + 1) := by
  rw [Fin.val_add_one]
  split_ifs with hi
  · subst i
    simp only [Fin.val_last, ← hl, Walk.getVert_zero, Walk.getVert_length]
  · rfl

/-- The vertex map records the original vertex at each occurrence in the tour. -/
def tourCycleHom {V : Type*} {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) {n : ℕ} (hl : p.length = n + 3) : cycleGraph (n + 3) →g G where
  toFun i := p.getVert i.val
  map_rel' {i j} hij := by
    rcases (cycleGraph_adj_successor i j).mp hij with h | h
    · subst j
      rw [getVert_cyclic_successor p hl]
      exact p.adj_getVert_succ (by omega)
    · subst i
      rw [getVert_cyclic_successor p hl]
      exact (p.adj_getVert_succ (by omega)).symm

lemma walk_edges_get_eq_getVert {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (i : Fin p.edges.length) :
    p.edges.get i = s(p.getVert i.val, p.getVert (i.val + 1)) := by
  change p.edges[i.val] = _
  simp only [Walk.edges, List.getElem_map, Walk.darts_getElem_eq_getVert]
  rfl

lemma tourCycleHom_edge {V : Type*} {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) {n : ℕ} (hl : p.length = n + 3) (i : Fin (n + 3)) :
    Sym2.map (tourCycleHom p hl) s(i, i + 1) =
      p.edges.get ⟨i.val, by simpa only [Walk.length_edges, hl] using i.isLt⟩ := by
  rw [walk_edges_get_eq_getVert]
  change s(p.getVert i.val, p.getVert (i + 1).val) = s(p.getVert i.val, p.getVert (i.val + 1))
  rw [getVert_cyclic_successor p hl]

lemma tourCycleHom_edge_bijective {V : Type*} {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) {n : ℕ} (hl : p.length = n + 3) (hp : p.IsEulerian) :
    Set.InjOn (Sym2.map (tourCycleHom p hl)) (cycleGraph (n + 3)).edgeSet ∧
      Set.SurjOn (Sym2.map (tourCycleHom p hl)) (cycleGraph (n + 3)).edgeSet G.edgeSet := by
  constructor
  · intro e he d hd hed
    obtain ⟨i, rfl⟩ := cycleGraph_edge_successor he
    obtain ⟨j, rfl⟩ := cycleGraph_edge_successor hd
    rw [tourCycleHom_edge p hl, tourCycleHom_edge p hl] at hed
    have hij := (List.nodup_iff_injective_get.mp hp.isTrail.edges_nodup) hed
    have hv : i.val = j.val := congrArg (fun x : Fin p.edges.length => x.val) hij
    rw [Fin.ext hv]
  · intro e he
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (hp.mem_edges_iff.mpr he)
    let i : Fin (n + 3) := ⟨j.val, by simpa only [Walk.length_edges, hl] using j.isLt⟩
    refine ⟨s(i, i + 1), (cycleGraph_adj_successor i (i + 1)).mpr (Or.inl rfl), ?_⟩
    rw [tourCycleHom_edge p hl]
    exact hj

lemma edge_surjective_vertex_surjective {V W : Type*} {G : SimpleGraph V}
    {K : SimpleGraph W} (f : G →g K)
    (hs : Set.SurjOn (Sym2.map f) G.edgeSet K.edgeSet)
    (hn : ∀ w, ∃ z, K.Adj w z) : Function.Surjective f := by
  intro w
  obtain ⟨z, hwz⟩ := hn w
  obtain ⟨e, he, heq⟩ := hs (show s(w, z) ∈ K.edgeSet from hwz)
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.map_pair_eq, Sym2.eq_iff] at heq
    rcases heq with ⟨ha, _⟩ | ⟨_, hb⟩
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩

end Erdos184
