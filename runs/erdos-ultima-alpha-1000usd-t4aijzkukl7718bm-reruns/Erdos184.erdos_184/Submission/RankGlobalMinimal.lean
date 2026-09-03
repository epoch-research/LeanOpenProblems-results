import Submission.RankComponents

/-!
Global vertex/edge minimality for the rank charge. Component assembly makes
these counterexamples connected, so the partition cut theorem applies to an
actually extractable class rather than an assumed connected subclass.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184
namespace RankGlobalMinimal
open RankCritical RankComponents RankCriticalPartitions
universe u

/-- Global minimality of vertex count. Edges may change in the smaller graph. -/
def IsVertexMinimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  (∀ v, Even (G.degree v)) ∧ ¬ HasBound C G ∧
  ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
    Fintype.card W < Fintype.card V →
    (∀ w, Even (H.degree w)) → HasBound C H

lemma exists_vertex_minimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W), IsVertexMinimal C H := by
  let P (n : ℕ) := ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
    (∀ w, Even (H.degree w)) ∧ ¬HasBound C H ∧ Fintype.card W = n
  have hex : ∃ n, P n := ⟨_,V,inferInstance,G,he,hb,rfl⟩
  obtain ⟨W,instW,H,heH,hbH,hn⟩ := Nat.find_spec hex
  letI := instW
  refine ⟨W,instW,H,heH,hbH,?_⟩
  intro X instX A hlt heA
  by_contra hbA
  have hh := Nat.find_min' hex
    (show P (Fintype.card X) from ⟨X,instX,A,heA,hbA,rfl⟩)
  omega

/-- Lexicographic minimality: first vertex count, then edge count. The edge
comparison also ranges over arbitrary graphs, not merely spanning subgraphs. -/
def IsLexMinimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  IsVertexMinimal C G ∧
  ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
    Fintype.card W = Fintype.card V → H.edgeSet.ncard < G.edgeSet.ncard →
    (∀ w, Even (H.degree w)) → HasBound C H

lemma exists_lex_minimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W), IsLexMinimal C H := by
  obtain ⟨X,instX,A,hA⟩ := exists_vertex_minimal C G he hb
  letI := instX
  let P (m : ℕ) := ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
    (∀ w, Even (H.degree w)) ∧ ¬HasBound C H ∧
    Fintype.card W = Fintype.card X ∧ H.edgeSet.ncard = m
  have hex : ∃ m, P m := ⟨_,X,instX,A,hA.1,hA.2.1,rfl,rfl⟩
  obtain ⟨W,instW,H,heH,hbH,hn,hm⟩ := Nat.find_spec hex
  letI := instW
  refine ⟨W,instW,H,⟨heH,hbH,?_⟩,?_⟩
  · intro Y instY K hlt heK
    exact hA.2.2 K (by omega) heK
  · intro Y instY K hcard hlt heK
    by_contra hbK
    have hmin := Nat.find_min' hex
      (show P K.edgeSet.ncard from ⟨Y,instY,K,heK,hbK,hcard.trans hn,rfl⟩)
    omega


lemma IsVertexMinimal.connected {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) : G.Connected := by
  by_contra hn
  apply hG.2.1
  apply bound_of_component_bounds
  intro c
  have hex : ∃ v : V, v ∉ c.supp := by
    by_contra! hh
    apply hn
    exact c.connected_toSimpleGraph.map c.toSimpleGraph_hom
      (fun v => ⟨⟨v,hh v⟩,rfl⟩)
  obtain ⟨v,hv⟩ := hex
  apply hG.2.2 c.toSimpleGraph
  · simpa only [← Nat.card_eq_fintype_card] using Fintype.card_subtype_lt hv
  · intro x
    have hx := hG.1 x.val
    have hd := component_degree G c x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hx hd ⊢
    rwa [hd]

lemma IsLexMinimal.isCritical {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsLexMinimal C G) : RankCritical.IsCritical C G := by
  refine ⟨hG.1.1,hG.1.2.1,?_⟩
  intro H _ hlt he
  exact hG.2 H rfl hlt he

lemma exists_connected_critical {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      IsLexMinimal C H ∧ RankCritical.IsCritical C H ∧ H.Connected := by
  obtain ⟨W,instW,H,hH⟩ := exists_lex_minimal C G he hb
  letI := instW
  exact ⟨W,instW,H,hH,hH.isCritical,hH.1.connected⟩

lemma rank_le_card_sub_one {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    graphRank G ≤ Fintype.card V - 1 := by
  have hh : 0 < Nat.card G.ConnectedComponent := Nat.card_pos
  unfold graphRank
  omega

lemma IsVertexMinimal.ne_bot {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) : G ≠ ⊥ := by
  intro h
  exact hG.2.1 (h ▸ hasBound_bot C)

lemma IsVertexMinimal.degree_lower {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) (hC : 0 < C) (v : V) : 2 * (C+2) ≤ G.degree v := by
  obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG.ne_bot
  haveI : Nontrivial V := ⟨a,b,hab.ne⟩
  haveI : Nonempty (VertexSmoothing.Without v) := by
    obtain ⟨w,hw⟩ := exists_ne v
    exact ⟨⟨w,hw⟩⟩
  let B := C * (Fintype.card (VertexSmoothing.Without v) - 1)
  have hsmall : ∀ H : SimpleGraph (VertexSmoothing.Without v),
      (∀ x, Even (H.degree x)) → ExactVertexSmoothing.HasPieceBound B H := by
    intro H heH
    obtain ⟨D,hc,hd,hb⟩ := hG.2.2 H (Fintype.card_subtype_lt (x := v) (by simp)) heH
    exact ⟨D,hc,hd,hb.trans (Nat.mul_le_mul_left C (rank_le_card_sub_one H))⟩
  have hn : Fintype.card V = Fintype.card (VertexSmoothing.Without v) + 1 := by
    rw [← Fintype.card_option]
    exact Fintype.card_congr (Equiv.optionSubtypeNe v).symm
  have hr := connected_rank hG.connected
  have hn' : 0 < Fintype.card (VertexSmoothing.Without v) := Fintype.card_pos
  have hr' : graphRank G = Fintype.card (VertexSmoothing.Without v) := by omega
  have hBC : B + C = C * graphRank G := by
    change C * (Fintype.card (VertexSmoothing.Without v) - 1) + C = _
    rw [hr']
    calc
      _ = C * ((Fintype.card (VertexSmoothing.Without v) - 1) + 1) := by ring
      _ = _ := by congr 1; omega
  have hbad (D : Finset G.Subgraph)
      (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
      (hd : IsDecomposition G D) : B + C < D.card := by
    rw [hBC]
    by_contra! h
    exact hG.2.1 ⟨D,hc,hd,h⟩
  by_cases hfour : 4 ≤ G.degree v
  · obtain ⟨D,hc,hd,hb⟩ := CliqueSmoothing.general_exact_cost B G hG.1 v hfour hsmall
    have hbadD := hbad D hc hd
    obtain ⟨r,hr⟩ := hG.1 v
    omega
  · obtain ⟨D,hc,hd,hb⟩ := ExactVertexSmoothing.unconditional_exact_cost B G hG.1 v hsmall
    have hbadD := hbad D hc hd
    omega

end RankGlobalMinimal
end Erdos184
