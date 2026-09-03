import FormalConjecturesUtil
import Submission.CompactFamiliesAudit

open Filter SimpleGraph Asymptotics

namespace Erdos713SmallCore

open Finset

open scoped Classical in
theorem exists_two_neighbors {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (v : W) (hd : 2 ≤ H.degree v) :
    ∃ x y, H.Adj v x ∧ H.Adj v y ∧ x ≠ y := by
  have hc : 1 < (H.neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree]
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp hc
  exact ⟨x, y, by simpa using hx, by simpa using hy, hxy⟩

open scoped Classical in
theorem adjacent_of_left_right {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] {t : ℕ} (f : Copy H (Erdos713K2t.K2t t))
    {u v : W} {i : Fin 2} {j : Fin t}
    (hu : f u = Sum.inl i) (hv : f v = Sum.inr j) (hd : 2 ≤ H.degree v) :
    H.Adj u v := by
  classical
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_neighbors H v hd
  have hfx := f.toHom.map_rel' hx
  have hfy := f.toHom.map_rel' hy
  change (Erdos713K2t.K2t t).Adj (f v) (f x) at hfx
  change (Erdos713K2t.K2t t).Adj (f v) (f y) at hfy
  cases hX : f x with
  | inr a => simp [hX, hv, Erdos713K2t.K2t, completeBipartiteGraph] at hfx
  | inl a =>
    cases hY : f y with
    | inr b => simp [hY, hv, Erdos713K2t.K2t, completeBipartiteGraph] at hfy
    | inl b =>
      have hab : a ≠ b := by
        intro he
        exact hxy (f.injective (hX.trans ((congrArg Sum.inl he).trans hY.symm)))
      have hi : i = a ∨ i = b := by omega
      rcases hi with hi | hi
      · have he : u = x := f.injective (hu.trans ((congrArg Sum.inl hi).trans hX.symm))
        exact he ▸ hx.symm
      · have he : u = y := f.injective (hu.trans ((congrArg Sum.inl hi).trans hY.symm))
        exact he ▸ hy.symm

open scoped Classical in
theorem contains_K22_of_degree_two {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {t : ℕ}
    (hd : ∀ v, 2 ≤ H.degree v) (hH : H ⊑ Erdos713K2t.K2t t) : Erdos713C4.K22 ⊑ H := by
  classical
  obtain ⟨f⟩ := hH
  have hleft : ∃ (u : W) (i : Fin 2), f u = Sum.inl i := by
    let v : W := Classical.choice inferInstance
    obtain ⟨w, hw⟩ := (H.degree_pos_iff_exists_adj v).mp (by have := hd v; omega)
    have hfw := f.toHom.map_rel' hw
    change (Erdos713K2t.K2t t).Adj (f v) (f w) at hfw
    cases hv : f v with
    | inl i => exact ⟨v, i, hv⟩
    | inr j =>
      cases hw' : f w with
      | inl i => exact ⟨w, i, hw'⟩
      | inr k => simp [hv, hw', Erdos713K2t.K2t, completeBipartiteGraph] at hfw
  obtain ⟨u, i, hu⟩ := hleft
  obtain ⟨x, y, hux, huy, hxy⟩ := exists_two_neighbors H u (hd u)
  have hright {z : W} (hz : H.Adj u z) : ∃ j : Fin t, f z = Sum.inr j := by
    have hF := f.toHom.map_rel' hz
    change (Erdos713K2t.K2t t).Adj (f u) (f z) at hF
    cases hZ : f z with
    | inl j => simp [hu, hZ, Erdos713K2t.K2t, completeBipartiteGraph] at hF
    | inr j => exact ⟨j, rfl⟩
  obtain ⟨j, hX⟩ := hright hux
  obtain ⟨k, hY⟩ := hright huy
  obtain ⟨a, b, hxa, hxb, hab⟩ := exists_two_neighbors H x (hd x)
  have hv : ∃ v, v ≠ u ∧ H.Adj x v := by
    by_cases hau : a = u
    · exact ⟨b, fun hbu => hab (hau.trans hbu.symm), hxb⟩
    · exact ⟨a, hau, hxa⟩
  obtain ⟨v, hvu, hxv⟩ := hv
  have hV : ∃ l : Fin 2, f v = Sum.inl l := by
    have hF := f.toHom.map_rel' hxv
    change (Erdos713K2t.K2t t).Adj (f x) (f v) at hF
    cases hV : f v with
    | inl l => exact ⟨l, rfl⟩
    | inr l => simp [hX, hV, Erdos713K2t.K2t, completeBipartiteGraph] at hF
  obtain ⟨l, hV⟩ := hV
  have hvy : H.Adj v y := adjacent_of_left_right H f hV hY (hd y)
  apply completeBipartiteGraph_isContained_iff.mpr
  refine ⟨{u, v}, {x, y}, by simp [hvu.symm], by simp [hxy], ?_⟩
  intro a ha b hb
  simp only [mem_coe, mem_insert, mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hux
  · exact huy
  · exact hxv.symm
  · exact hvy

open scoped Classical in
theorem contained_of_small_bipartition {W : Type*} [Fintype W]
    (H : SimpleGraph W) (S : Set W) (hS : Nat.card S ≤ 2)
    (hB : H.IsBipartiteWith S Sᶜ) : H ⊑ Erdos713K2t.K2t (Fintype.card W) := by
  classical
  let eL : S ↪ Fin 2 := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hS))
  let eR : ↥(Sᶜ) ↪ Fin (Fintype.card W) :=
    (Function.Embedding.subtype _).trans (Fintype.equivFin W).toEmbedding
  let e := (Equiv.Set.sumCompl S).symm.toEmbedding.trans (eL.sumMap eR)
  refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
  intro u v huv
  rcases hB.2 huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hv' : v ∉ S := hv
    simp [e, Equiv.Set.sumCompl_symm_apply_of_mem hu,
      Equiv.Set.sumCompl_symm_apply_of_notMem hv', Erdos713K2t.K2t, completeBipartiteGraph]
  · have hu' : u ∉ S := hu
    simp [e, Equiv.Set.sumCompl_symm_apply_of_mem hv,
      Equiv.Set.sumCompl_symm_apply_of_notMem hu', Erdos713K2t.K2t, completeBipartiteGraph]

open scoped Classical in
theorem small_bipartite_contained {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hB : H.IsBipartite) (hcard : Fintype.card W ≤ 5) :
    H ⊑ Erdos713K2t.K2t (Fintype.card W) := by
  classical
  obtain ⟨χ⟩ := hB
  let S : Set W := {v | χ v = 0}
  have hS : H.IsBipartiteWith S Sᶜ := by
    refine ⟨disjoint_compl_right, ?_⟩
    intro u v huv
    have hχ := χ.valid huv
    simp only [S, Set.mem_setOf_eq, Set.mem_compl_iff]
    omega
  by_cases hcS : Nat.card S ≤ 2
  · exact contained_of_small_bipartition H S hcS hS
  · have hcSc : Nat.card ↥(Sᶜ) ≤ 2 := by
      have he : Nat.card ↥(Sᶜ) = Fintype.card W - Nat.card S := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_compl_set]
      rw [he]
      omega
    apply contained_of_small_bipartition H Sᶜ hcSc
    simpa only [compl_compl] using hS.symm

theorem contains_K22_of_not_acyclic {W : Type*} [Fintype W]
    (G : SimpleGraph W) {t : ℕ} (hcyc : ¬ G.IsAcyclic)
    (hhi : G ⊑ Erdos713K2t.K2t t) : Erdos713C4.K22 ⊑ G := by
  classical
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hcyc
  obtain ⟨v, p, hp⟩ := hcyc
  let C := p.toSubgraph
  have hv : v ∈ C.verts := by simp [C]
  letI : Nonempty C.verts := ⟨⟨v, hv⟩⟩
  have hd : ∀ w, 2 ≤ C.coe.degree w := by
    intro w
    rw [Subgraph.coe_degree, Subgraph.degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact (hp.ncard_neighborSet_toSubgraph_eq_two (by simpa [C] using w.property)).ge
  exact (contains_K22_of_degree_two C.coe (fun w => by simpa using hd w)
    (C.coe_isContained.trans hhi)).trans C.coe_isContained

open scoped Classical in
theorem rational_exponent_of_contained {q : ℕ} (G : SimpleGraph (Fin q))
    {t : ℕ} (hhi : G ⊑ Erdos713K2t.K2t t) (hEdges : 2 ≤ G.edgeFinset.card)
    {a c : ℝ} (ha : a ∈ Set.Ico 1 2) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  by_cases hForest : G.IsAcyclic
  · exact Erdos713Forest.rational_exponent_of_acyclic q G hForest hEdges a c ha hc h
  exact Erdos713K2t.rational_exponent_of_containment
    (contains_K22_of_not_acyclic G hForest hhi) hhi hc h

open scoped Classical in
theorem rational_exponent_of_small_bipartition {q : ℕ} (G : SimpleGraph (Fin q))
    (S : Set (Fin q)) (hS : Nat.card S ≤ 2) (hB : G.IsBipartiteWith S Sᶜ)
    (hEdges : 2 ≤ G.edgeFinset.card) {a c : ℝ} (ha : a ∈ Set.Ico 1 2) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) :=
  rational_exponent_of_contained G (contained_of_small_bipartition G S hS hB) hEdges ha hc h

open scoped Classical in
theorem rational_exponent_of_card_le_five {q : ℕ} (G : SimpleGraph (Fin q))
    (hB : G.IsBipartite) (hcard : q ≤ 5) (hEdges : 2 ≤ G.edgeFinset.card)
    {a c : ℝ} (ha : a ∈ Set.Ico 1 2) (hc : 0 < c)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) :=
  rational_exponent_of_contained G
    (small_bipartite_contained G hB (by simpa using hcard)) hEdges ha hc h

end Erdos713SmallCore

#print axioms Erdos713SmallCore.contains_K22_of_not_acyclic

#print axioms Erdos713SmallCore.rational_exponent_of_contained
#print axioms Erdos713SmallCore.rational_exponent_of_small_bipartition
#print axioms Erdos713SmallCore.rational_exponent_of_card_le_five
