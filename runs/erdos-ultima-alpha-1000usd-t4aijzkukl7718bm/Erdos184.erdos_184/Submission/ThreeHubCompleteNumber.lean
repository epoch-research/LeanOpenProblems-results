import Submission.ThreeHubFullStructure

/-! Sharp upper bounds for the complete bipartite graph with three hubs.
This is an auxiliary family, not a solution of the general conjecture. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ThreeHubCompleteNumber
open Critical EvenCore
set_option maxHeartbeats 1600000

lemma number_map_le {V W : Type*} [Fintype V] [Fintype W]
    (e : V ↪ W) (G : SimpleGraph V) : number (G.map e) ≤ number G := by
  obtain ⟨D,hD,hd,hc⟩ := exists_minimum G
  let f := (SimpleGraph.Embedding.map e G).toHom
  obtain ⟨E,hE,hp,he,hn⟩ := SparseCuts.map_decomposition_injective f e.injective D hD hd
  have hdec : IsDecomposition (G.map e) E :=
    ⟨hp, he.trans (SimpleGraph.edgeSet_map e G).symm⟩
  exact (number_le E hE hdec).trans (hn.trans_eq hc)

lemma bipartite_sum_right {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] :
    number (completeBipartiteGraph A (B ⊕ C)) ≤
      number (completeBipartiteGraph A B) + number (completeBipartiteGraph A C) := by
  let e₁ : A ⊕ B ↪ A ⊕ (B ⊕ C) :=
    ⟨Sum.map id Sum.inl, by intro x y h; cases x <;> cases y <;> simpa using h⟩
  let e₂ : A ⊕ C ↪ A ⊕ (B ⊕ C) :=
    ⟨Sum.map id Sum.inr, by intro x y h; cases x <;> cases y <;> simpa using h⟩
  let G₁ := (completeBipartiteGraph A B).map e₁
  let G₂ := (completeBipartiteGraph A C).map e₂
  have h₁ (x y : A ⊕ (B ⊕ C)) : G₁.Adj x y ↔
      (∃ a b, x = .inl a ∧ y = .inr (.inl b)) ∨
        (∃ a b, y = .inl a ∧ x = .inr (.inl b)) := by
    rcases x with a | b | c <;> rcases y with d | e | f <;>
      simp [G₁, e₁, SimpleGraph.map_adj, completeBipartiteGraph, Sum.exists]
  have h₂ (x y : A ⊕ (B ⊕ C)) : G₂.Adj x y ↔
      (∃ a c, x = .inl a ∧ y = .inr (.inr c)) ∨
        (∃ a c, y = .inl a ∧ x = .inr (.inr c)) := by
    rcases x with a | b | c <;> rcases y with d | e | f <;>
      simp [G₂, e₂, SimpleGraph.map_adj, completeBipartiteGraph, Sum.exists]
  have hd : Disjoint G₁.edgeSet G₂.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.ind with
    | _ x y =>
      change G₁.Adj x y at he
      change G₂.Adj x y at hf
      rw [h₁] at he
      rw [h₂] at hf
      rcases x with a | b | c <;> rcases y with d | e | f <;> simp_all
  have he : G₁ ⊔ G₂ = completeBipartiteGraph A (B ⊕ C) := by
    ext x y
    rw [SimpleGraph.sup_adj, h₁, h₂]
    rcases x with a | b | c <;> rcases y with d | e | f <;>
      simp [completeBipartiteGraph]
  have hn := CycleForestCertificate.number_sup_le hd
  rw [he] at hn
  exact hn.trans (Nat.add_le_add (number_map_le e₁ _) (number_map_le e₂ _))

abbrev graph (n : ℕ) := completeBipartiteGraph (Fin 3) (Fin n)
instance (n : ℕ) : DecidableRel (graph n).Adj := by
  intro x y
  cases x <;> cases y <;> unfold graph completeBipartiteGraph <;> infer_instance

local instance walkAdjDecidable {V : Type*} [DecidableEq V] {H : SimpleGraph V}
    {a b : V} (p : H.Walk a b) : DecidableRel p.toSubgraph.spanningCoe.Adj := by
  intro x y
  exact decidable_of_iff (s(x,y) ∈ p.edges) p.mem_edges_toSubgraph.symm

lemma number_add (m n : ℕ) : number (graph (m+n)) ≤ number (graph m) + number (graph n) := by
  have hi := BlockRestriction.number_eq_of_iso
    (Subfamilies.bipartiteIso (Equiv.refl (Fin 3)) (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m+n)))
  rw [← hi]
  exact bipartite_sum_right

lemma delete_cycle_card_add {V : Type*} [Fintype V] {H : SimpleGraph V}
    {a : V} {p : H.Walk a a} (hp : p.IsCycle) :
    Nat.card (H \ p.toSubgraph.spanningCoe).edgeSet + p.length = Nat.card H.edgeSet := by
  have h := Finset.card_sdiff_add_card_eq_card
    (SimpleGraph.edgeFinset_mono p.toSubgraph.spanningCoe_le)
  rw [← SimpleGraph.edgeFinset_sdiff] at h
  have hc := cycle_edge_count H hp
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h hc
  omega

private def c₂ : (graph 2).Walk (.inl 0) (.inl 0) :=
  .cons (by decide) (.cons (show (graph 2).Adj (.inr 0) (.inl 1) by decide)
    (.cons (show (graph 2).Adj (.inl 1) (.inr 1) by decide) (.cons (by decide) .nil)))
private lemma c₂_cycle : c₂.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide +kernel
lemma number_two : number (graph 2) ≤ 3 := by
  have h := number_restore_cycle c₂_cycle
  have he := number_le_edges (graph 2 \ c₂.toSubgraph.spanningCoe)
  have hc := delete_cycle_card_add c₂_cycle
  have ht := BipartiteLower.complete_edge_card (A := Fin 3) (B := Fin 2)
  have hl : c₂.length = 4 := rfl
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_fin] at he ht
  change Nat.card (graph 2).edgeSet = 6 at ht
  omega

private def c₃ : (graph 3).Walk (.inl 0) (.inl 0) :=
  .cons (show (graph 3).Adj (.inl 0) (.inr 0) by decide)
    (.cons (show (graph 3).Adj (.inr 0) (.inl 1) by decide)
    (.cons (show (graph 3).Adj (.inl 1) (.inr 1) by decide)
    (.cons (show (graph 3).Adj (.inr 1) (.inl 2) by decide)
    (.cons (show (graph 3).Adj (.inl 2) (.inr 2) by decide) (.cons (by decide) .nil)))))
private lemma c₃_cycle : c₃.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide +kernel
lemma number_three : number (graph 3) ≤ 4 := by
  have h := number_restore_cycle c₃_cycle
  have he := number_le_edges (graph 3 \ c₃.toSubgraph.spanningCoe)
  have hc := delete_cycle_card_add c₃_cycle
  have ht := BipartiteLower.complete_edge_card (A := Fin 3) (B := Fin 3)
  have hl : c₃.length = 6 := rfl
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_fin] at he ht
  change Nat.card (graph 3).edgeSet = 9 at ht
  omega

private def c₄ : (graph 4).Walk (.inl 0) (.inl 0) :=
  .cons (show (graph 4).Adj (.inl 0) (.inr 0) by decide)
    (.cons (show (graph 4).Adj (.inr 0) (.inl 1) by decide)
    (.cons (show (graph 4).Adj (.inl 1) (.inr 1) by decide) (.cons (by decide) .nil)))
private lemma c₄_cycle : c₄.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide +kernel
private def d₄ : (graph 4 \ c₄.toSubgraph.spanningCoe).Walk (.inl 1) (.inl 1) :=
  .cons (show (graph 4 \ c₄.toSubgraph.spanningCoe).Adj (.inl 1) (.inr 2) by decide +kernel)
    (.cons (show (graph 4 \ c₄.toSubgraph.spanningCoe).Adj (.inr 2) (.inl 2) by decide +kernel)
    (.cons (show (graph 4 \ c₄.toSubgraph.spanningCoe).Adj (.inl 2) (.inr 3) by decide +kernel)
    (.cons (by decide +kernel) .nil)))
private lemma d₄_cycle : d₄.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide +kernel
lemma number_four : number (graph 4) ≤ 6 := by
  have h := number_restore_cycle c₄_cycle
  have h' := number_restore_cycle d₄_cycle
  have he := number_le_edges ((graph 4 \ c₄.toSubgraph.spanningCoe) \ d₄.toSubgraph.spanningCoe)
  have hc := delete_cycle_card_add c₄_cycle
  have hc' := delete_cycle_card_add d₄_cycle
  have ht := BipartiteLower.complete_edge_card (A := Fin 3) (B := Fin 4)
  have hl : c₄.length = 4 := rfl
  have hl' : d₄.length = 4 := rfl
  simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, Nat.card_fin] at he ht
  change Nat.card (graph 4).edgeSet = 12 at ht
  omega

/-- The sharp upper bound, except for the exceptional one-leaf star. -/
lemma upper (n : ℕ) (hn : 2 ≤ n) : number (graph n) ≤ n + (n+2)/3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 2
    · subst n; exact number_two
    by_cases h' : n = 3
    · subst n; exact number_three
    by_cases h'' : n = 4
    · subst n; exact number_four
    have hl : 2 ≤ n-3 := by omega
    have hb := ih (n-3) (by omega) hl
    have ha := number_add (n-3) 3
    rw [Nat.sub_add_cancel (by omega : 3 ≤ n)] at ha
    have h₃ := number_three
    omega

lemma lower (n : ℕ) : 4*n ≤ 3*number (graph n) := by
  obtain ⟨D,hD,hd,hc⟩ := exists_minimum (graph n)
  have h := BipartiteLower.decomposition_lower_bound 1 (by simp) D hD hd
  simp only [Fintype.card_fin] at h
  omega

lemma exact_number (n : ℕ) (hn : 2 ≤ n) : number (graph n) = n + (n+2)/3 := by
  have hu := upper n hn
  have hl := lower n
  omega

lemma upper_type (B : Type*) [Fintype B] (hB : 2 ≤ Fintype.card B) :
    number (completeBipartiteGraph (Fin 3) B) ≤ Fintype.card B + (Fintype.card B+2)/3 := by
  have hi := BlockRestriction.number_eq_of_iso
    (Subfamilies.bipartiteIso (Equiv.refl (Fin 3)) (Fintype.equivFin B))
  exact hi.le.trans (upper _ hB)

end Erdos184Work.ThreeHubCompleteNumber
#print axioms Erdos184Work.ThreeHubCompleteNumber.upper
#print axioms Erdos184Work.ThreeHubCompleteNumber.exact_number
