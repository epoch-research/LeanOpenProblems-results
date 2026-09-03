import Submission.CyclicModel
import Submission.CountThreeOrder

/-! Labeling the vertices of a genuine cycle by a finite cyclic interval. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.CycleVertexLabeling
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
set_option maxHeartbeats 1000000

lemma exists_labels (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    {n : ℕ} (hlen : C.verts.ncard = n+3) :
    ∃ f : Fin (n+3) ↪ V, Set.range f = C.verts ∧
      ∀ i, G.Adj (f i) (f (i+1)) := by
  obtain ⟨v,hv⟩ := hc.1.nonempty
  obtain ⟨p,hp,hpC⟩ := CycleRing.cycle_piece_walk_at C hc.1 hc.2 v hv
  obtain ⟨m,M,hM⟩ := CyclicModel.model_of_cycle p hp
  have hcard := Set.ncard_range_of_injective M.injective
  rw [hM,hpC,hlen] at hcard
  simp only [Nat.card_fin] at hcard
  have hmn : m = n := by omega
  subst m
  refine ⟨⟨M.vertex,M.injective⟩,hM.trans (congrArg Subgraph.verts hpC),?_⟩
  intro i
  simpa only [finRotate_succ_apply] using M.adj i

lemma independent_four_card :
    ∀ s : Finset (Fin 4), (∀ i ∈ s, i+1 ∉ s) → s.card ≤ 2 := by
  decide +kernel

lemma quadrilateral_neighbor_card (C : G.Subgraph)
    (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2) (hlen : C.verts.ncard = 4)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False) (v : V) :
    (G.neighborSet v ∩ C.verts).ncard ≤ 2 := by
  obtain ⟨f,hf,ha⟩ := exists_labels C hc (n := 1) hlen
  let s : Finset (Fin 4) := Finset.univ.filter (fun i => G.Adj v (f i))
  have hmem (i : Fin 4) : i ∈ s ↔ G.Adj v (f i) := by simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
  have hs : s.card ≤ 2 := independent_four_card s (by
    intro i hi hj
    have hvi := (hmem i).mp hi
    have hvj := (hmem (i+1)).mp hj
    exact htri v (f i) (f (i+1)) hvi (ha i) hvj.symm)
  have heq : G.neighborSet v ∩ C.verts = f '' (s : Set (Fin 4)) := by
    ext x
    constructor
    · rintro ⟨hx,hC⟩
      obtain ⟨i,rfl⟩ := hf.symm ▸ hC
      refine ⟨i,?_,rfl⟩
      change G.Adj v (f i) at hx
      exact (hmem i).mpr hx
    · rintro ⟨i,hi,rfl⟩
      have ha : G.Adj v (f i) := (hmem i).mp hi
      exact ⟨ha,hf ▸ Set.mem_range_self i⟩
  rw [heq,Set.ncard_image_of_injective _ f.injective]
  simpa only [Set.ncard_coe_finset] using hs

end Erdos184.CycleVertexLabeling
