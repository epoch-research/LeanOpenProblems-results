import FormalConjecturesUtil

/-! Auxiliary long-cycle estimates under development for Erdős Problem 184. -/

open SimpleGraph
namespace Erdos184LongCycles

lemma take_isPath {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (j : ℕ) : (p.take j).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [SimpleGraph.Walk.take_support_eq_support_take_succ]
  exact hp.support_nodup.take

lemma endpoint_edge_notMem {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (hlen : 2 ≤ p.length) : s(u,v) ∉ p.edges := by
  intro h
  have hs := hp.eq_snd_of_mem_edges h
  have heq : p.getVert 1 = p.getVert p.length := by
    simpa [SimpleGraph.Walk.snd] using hs.symm
  have := hp.getVert_injOn (show 1 ≤ p.length by omega) (show p.length ≤ p.length by rfl) heq
  omega

lemma close_prefix_isCycle {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) (j : ℕ) (hj : j ≤ p.length) (hj2 : 2 ≤ j)
    (hadj : G.Adj u (p.getVert j)) :
    (SimpleGraph.Walk.cons hadj (p.take j).reverse).IsCycle := by
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨(take_isPath hp j).reverse, ?_⟩
  rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse]
  apply endpoint_edge_notMem (take_isPath hp j)
  simpa [SimpleGraph.Walk.take_length, Nat.min_eq_left hj] using hj2

open scoped Classical in
lemma exists_long_cycle_of_min_degree {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k) (hdeg : ∀ v, k ≤ G.degree v) :
    ∃ u : V, ∃ p : G.Walk u u, p.IsCycle ∧ k + 1 ≤ p.length := by
  classical
  obtain ⟨u, v, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hneigh : ∀ w, G.Adj u w → w ∈ p.support := by
    intro w hw
    by_contra hnot
    have hq : (SimpleGraph.Walk.cons hw.symm p).IsPath :=
      (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hp, hnot⟩
    have hlen := hmax w v (.cons hw.symm p) hq
    simp only [SimpleGraph.Walk.length_cons] at hlen
    omega
  have hex : ∃ j, j ≤ p.length ∧ k ≤ j ∧ G.Adj u (p.getVert j) := by
    by_contra! hn
    have hsub : G.neighborFinset u ⊆ (Finset.Ico 1 k).image p.getVert := by
      intro w hw
      have hw' := (G.mem_neighborFinset u w).mp hw
      obtain ⟨j, hjw, hj⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hneigh w hw')
      have hjpos : 1 ≤ j := by
        by_contra! hjzero
        have hj0 : j = 0 := by omega
        have huw : u = w := by simpa [hj0] using hjw
        exact hw'.ne huw
      have hjlt : j < k := by
        by_contra! hjge
        exact hn j hj hjge (hjw ▸ hw')
      exact Finset.mem_image.mpr ⟨j, Finset.mem_Ico.mpr ⟨hjpos, hjlt⟩, hjw⟩
    have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
    have hdu := hdeg u
    simp only [SimpleGraph.card_neighborFinset_eq_degree, Nat.card_Ico] at hc
    omega
  obtain ⟨j, hj, hjk, hadj⟩ := hex
  refine ⟨u, .cons hadj (p.take j).reverse, close_prefix_isCycle hp j hj (by omega) hadj, ?_⟩
  simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse,
    SimpleGraph.Walk.take_length, Nat.min_eq_left hj]
  omega

universe u

open scoped Classical in
lemma edges_le_of_no_long_cycle {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hk : 2 ≤ k)
    (hno : ∀ u (p : G.Walk u u), p.IsCycle → p.length ≤ k) :
    G.edgeFinset.card ≤ (k - 1) * Fintype.card V := by
  classical
  have main : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n →
      (∀ u (p : H.Walk u u), p.IsCycle → p.length ≤ k) →
      H.edgeFinset.card ≤ (k - 1) * n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ H hcard hnoH
      cases isEmpty_or_nonempty W with
      | inl he =>
        have hbot : H = ⊥ := by ext a; exact isEmptyElim a
        subst H
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card,
          SimpleGraph.edgeSet_bot]
        simp
      | inr he =>
        obtain ⟨v, hv⟩ : ∃ v, H.degree v < k := by
          by_contra! hn
          obtain ⟨v, p, hp, hlen⟩ := exists_long_cycle_of_min_degree H k hk hn
          have := hnoH v p hp
          omega
        let S : Set W := {v}ᶜ
        let K := H.induce S
        have hc : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card ↑({v}ᶜ : Set W) = _
          rw [Fintype.card_compl_set]
          simp only [Fintype.card_unique]
        have hpos : 0 < n := hcard ▸ Fintype.card_pos
        have hsmall : Fintype.card S < n := by omega
        have hnoK : ∀ u (p : K.Walk u u), p.IsCycle → p.length ≤ k := by
          intro u p hp
          let e : K ↪g H := SimpleGraph.Embedding.induce S
          have hp' := SimpleGraph.Walk.IsCycle.map (f := e.toHom) e.injective hp
          have hlen := hnoH (e u) (p.map e.toHom) hp'
          simpa using hlen
        have hb := ih (Fintype.card S) hsmall K rfl hnoK
        have hem : K.edgeFinset.card + H.degree v = H.edgeFinset.card := by
          change (H.induce {v}ᶜ).edgeFinset.card + H.degree v = H.edgeFinset.card
          rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
            SimpleGraph.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel (H.degree_le_card_edgeFinset v)]
        rw [hc, hcard] at hb
        have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hb hem ⊢
        simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hv hem
        have hksub : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
        nlinarith
  exact main _ G rfl hno

#print axioms edges_le_of_no_long_cycle
#print axioms exists_long_cycle_of_min_degree
end Erdos184LongCycles
