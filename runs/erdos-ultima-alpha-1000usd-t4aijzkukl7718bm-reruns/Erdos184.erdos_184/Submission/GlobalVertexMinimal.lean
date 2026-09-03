import Submission.VertexSmoothing
import Submission.MinimalCounterexample

/-!
Counterexamples minimal in the order among ALL finite even graphs, not just
spanning subgraphs. This justifies the new vertex-smoothing reductions.
-/
open SimpleGraph Filter
open scoped Classical
namespace Erdos184
namespace GlobalVertexMinimal
open VertexSmoothing MinimalCounterexample

universe u

/-- Global minimality of vertex count. Edges may change in the smaller graph. -/
def IsVertexMinimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  (∀ v, Even (G.degree v)) ∧ ¬ HasCardBound C G ∧
  ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
    Fintype.card W < Fintype.card V →
    (∀ w, Even (H.degree w)) → HasCardBound C H

lemma exists_vertex_minimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasCardBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W), IsVertexMinimal C H := by
  let P (n : ℕ) := ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
    (∀ w, Even (H.degree w)) ∧ ¬HasCardBound C H ∧ Fintype.card W = n
  have hex : ∃ n, P n := ⟨_,V,inferInstance,G,he,hb,rfl⟩
  obtain ⟨W,instW,H,heH,hbH,hn⟩ := Nat.find_spec hex
  letI := instW
  refine ⟨W,instW,H,heH,hbH,?_⟩
  intro X instX A hlt heA
  by_contra hbA
  have hh := Nat.find_min' hex
    (show P (Fintype.card X) from ⟨X,instX,A,heA,hbA,rfl⟩)
  omega

lemma cardBound_of_supportBound {V : Type*} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hb : HasBound C G) : HasCardBound C G := by
  obtain ⟨D,hc,hd,hbD⟩ := hb
  refine ⟨D,hc,hd,hbD.trans (Nat.mul_le_mul_left C ?_)⟩
  simpa using Set.ncard_le_ncard (Set.subset_univ G.support)

lemma supportBound_of_induce {V : Type*} [Fintype V] {C : ℕ} (G : SimpleGraph V)
    (hb : HasCardBound C (G.induce G.support)) : HasBound C G := by
  let f : G.induce G.support →g G := (SimpleGraph.Embedding.induce G.support).toHom
  have hi : Set.InjOn (Sym2.map f) (G.induce G.support).edgeSet :=
    (Sym2.map.injective Subtype.val_injective).injOn
  have hs : Set.SurjOn (Sym2.map f) (G.induce G.support).edgeSet G.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h x y =>
      exact ⟨s(⟨x,⟨y,he⟩⟩,⟨y,⟨x,he.symm⟩⟩),he,rfl⟩
  obtain ⟨D,hc,hd,hbD⟩ := hb
  obtain ⟨E,hcE,hdE,hbE⟩ := project_decomposition_degree_two f hi hs ∅
    Subtype.val_injective.injOn (by simp) D (by
      intro H hH
      refine ⟨(hc H hH).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using (hc H hH).2 v) hd
  refine ⟨E,hcE,hdE,?_⟩
  have hbE' : E.card ≤ D.card := by simpa using hbE
  have hcard : Fintype.card G.support = G.support.ncard := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  exact hbE'.trans (by simpa only [hcard] using hbD)

lemma even_induce_support {V : Type*} [Fintype V] (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) : ∀ v, Even ((G.induce G.support).degree v) := by
  intro v
  have hd := G.degree_induce_support v
  have hv := he v.val
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hv ⊢
  rwa [hd]

/-- A vertex-minimal counterexample can also be made edge-critical, while
retaining the stronger global minimality. It has no isolated vertices. -/
lemma exists_joint_critical {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasCardBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      IsVertexMinimal C H ∧ IsCritical C H ∧ H.support = Set.univ := by
  obtain ⟨W,instW,A,hA⟩ := exists_vertex_minimal C G he hb
  letI := instW
  have hbad : ¬HasBound C A := fun h => hA.2.1 (cardBound_of_supportBound h)
  obtain ⟨H,hHA,hH⟩ := exists_critical_subgraph C A hA.1 hbad
  have hcard : H.support.ncard = Fintype.card W := by
    have hle : H.support.ncard ≤ Fintype.card W := by
      simpa using Set.ncard_le_ncard (Set.subset_univ H.support)
    by_contra hn
    have hlt : Fintype.card H.support < Fintype.card W := by
      rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      omega
    have hbH := hA.2.2 (H.induce H.support) hlt (by
      intro v
      have hv := even_induce_support H hH.1 v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hv)
    exact hH.2.1 (supportBound_of_induce H hbH)
  have hsup : H.support = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card,hcard] using
      (Nat.le_refl (Fintype.card W))
  refine ⟨W,instW,H,⟨hH.1,?_,hA.2.2⟩,hH,hsup⟩
  intro h
  obtain ⟨D,hc,hd,hbD⟩ := h
  exact hH.2.1 ⟨D,hc,hd,by simpa only [hcard] using hbD⟩

/-- A globally vertex-minimal counterexample cannot have a nonisolated vertex
of degree at most 2(C+1) with independent neighbors. Evenness strengthens the
strict inequality to the displayed two-unit degree gap. -/
lemma IsVertexMinimal.degree_lower_of_independent_neighbors {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    (v : V) (hv : 0 < G.degree v)
    (hind : ∀ u w, G.Adj v u → G.Adj v w → ¬G.Adj u w) :
    2 * (C+2) ≤ G.degree v := by
  have hn : ¬G.degree v ≤ 2 * (C+1) := by
    intro hdeg
    apply hG.2.1
    apply independent_neighborhood_reduction C G hG.1 v hv hdeg hind
    intro H heH
    exact hG.2.2 H (Fintype.card_subtype_lt (x := v) (by simp)) heH
  obtain ⟨r,hr⟩ := hG.1 v
  omega

/-- In particular, a triangle-free globally minimal counterexample has the
stronger positive-degree lower bound 2(C+2). This is not a uniform upper bound. -/
lemma IsVertexMinimal.degree_lower_triangle_free {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (ht : G.CliqueFree 3)
    (v : V) (hv : 0 < G.degree v) : 2 * (C+2) ≤ G.degree v := by
  apply hG.degree_lower_of_independent_neighbors v hv
  intro a b hva hvb hab
  exact (G.isIndepSet_neighborSet_of_triangleFree ht v) hva hvb hab.ne hab

/-- Every vertex attaining the old critical degree lower bound must lie in
a triangle once global vertex minimality is imposed. -/
lemma IsVertexMinimal.tight_vertex_in_triangle {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    (v : V) (hv : G.degree v = 2 * (C+1)) :
    ∃ a b, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b := by
  by_contra! hn
  have hd := hG.degree_lower_of_independent_neighbors v (by omega) hn
  omega

/-- This is only a conditional reduction: ruling out the joint global and
edge-critical class would settle the original conjecture. -/
lemma conjecture_of_no_joint_critical (C : ℕ)
    (hno : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      ¬(IsVertexMinimal C G ∧ IsCritical C G ∧ G.support = Set.univ)) :
    ∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V) := by
  apply conjecture_iff_even_cycle_bound.mpr
  refine ⟨C,?_⟩
  intro V _ _ G he
  have hb : HasCardBound C G := by
    by_contra h
    obtain ⟨W,instW,H,hH⟩ := exists_joint_critical C G he h
    letI := instW
    exact hno H hH
  obtain ⟨D,hc,hd,hbD⟩ := hb
  exact ⟨D,hc,hd,by exact_mod_cast hbD⟩

/-- Lexicographic minimality: first vertex count, then edge count. The edge
comparison also ranges over arbitrary graphs, not merely spanning subgraphs. -/
def IsLexMinimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  IsVertexMinimal C G ∧
  ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
    Fintype.card W = Fintype.card V → H.edgeSet.ncard < G.edgeSet.ncard →
    (∀ w, Even (H.degree w)) → HasCardBound C H

lemma exists_lex_minimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasCardBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W), IsLexMinimal C H := by
  obtain ⟨X,instX,A,hA⟩ := exists_vertex_minimal C G he hb
  letI := instX
  let P (m : ℕ) := ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
    (∀ w, Even (H.degree w)) ∧ ¬HasCardBound C H ∧
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

lemma IsVertexMinimal.support_eq_univ {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) : G.support = Set.univ := by
  have hle : G.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ G.support)
  have heq : G.support.ncard = Fintype.card V := by
    by_contra hn
    have hlt : Fintype.card G.support < Fintype.card V := by
      rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      omega
    have hb := hG.2.2 (G.induce G.support) hlt (by
      intro v
      have hv := even_induce_support G hG.1 v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hv)
    exact hG.2.1 (cardBound_of_supportBound (supportBound_of_induce G hb))
  apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
  simpa only [Set.ncard_univ,Nat.card_eq_fintype_card,heq] using
    (Nat.le_refl (Fintype.card V))

/-- Lexicographic minimality supplies the support-charged bound for any graph
of the same order with fewer edges, even if it adds edges absent from G. -/
lemma IsLexMinimal.support_bound_fewer_edges {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsLexMinimal C G)
    {W : Type u} [Fintype W] (H : SimpleGraph W)
    (hn : Fintype.card W = Fintype.card V)
    (hm : H.edgeSet.ncard < G.edgeSet.ncard) (he : ∀ w, Even (H.degree w)) :
    HasBound C H := by
  have hle : H.support.ncard ≤ Fintype.card W := by
    simpa using Set.ncard_le_ncard (Set.subset_univ H.support)
  rcases lt_or_eq_of_le hle with hlt | heq
  · apply supportBound_of_induce H
    apply hG.1.2.2 (H.induce H.support)
    · rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      omega
    · intro w
      have hw := even_induce_support H he w
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hw
  · obtain ⟨D,hc,hd,hbD⟩ := hG.2 H hn hm he
    exact ⟨D,hc,hd,by simpa only [heq] using hbD⟩

lemma IsLexMinimal.isCritical {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsLexMinimal C G) : IsCritical C G := by
  refine ⟨hG.1.1,fun h => hG.1.2.1 (cardBound_of_supportBound h),?_⟩
  intro H _ hlt he
  exact hG.support_bound_fewer_edges H rfl hlt he

/-- A counterexample can satisfy all three useful forms of minimality at once:
full lexicographic minimality, the earlier support-criticality, and full support. -/
lemma exists_lex_critical {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasCardBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      IsLexMinimal C H ∧ IsCritical C H ∧ H.support = Set.univ := by
  obtain ⟨W,instW,H,hH⟩ := exists_lex_minimal C G he hb
  letI := instW
  exact ⟨W,instW,H,hH,hH.isCritical,hH.1.support_eq_univ⟩

end GlobalVertexMinimal
end Erdos184
