import Submission.ActualPartialSmoothing

/-! The unrestricted one-piece cost of partial smoothing. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.PartialSmoothing
open ExactVertexSmoothing
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

/-- Deleting the marked edge makes a forest; adding the two spokes restores
parity and adds at most two independent cycles. -/
lemma marked_replacement_bound (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hna : ¬A.Adj v a) (hnb : ¬A.Adj v b) (hnab : ¬A.Adj a b)
    (H : (smooth A a b).Subgraph)
    (hc : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) (he : H.Adj a b) :
    HasPieceBound 2 (unsmooth (H.spanningCoe.deleteEdges {s(a,b)}) v a b) := by
  let T := H.spanningCoe.deleteEdges {s(a,b)}
  have hTH : T ≤ H.spanningCoe := deleteEdges_le _
  have hnT : ¬T.Adj a b := by simp [T]
  have hnva : ¬(smooth A a b).Adj v a := by
    rintro (h | h)
    · exact hna h
    · have hh := (edge_adj ..).mp h
      rcases hh.1 with h | h
      · exact hva h.1
      · exact hvb h.1
  have hnvb : ¬(smooth A a b).Adj v b := by
    rintro (h | h)
    · exact hnb h
    · have hh := (edge_adj ..).mp h
      rcases hh.1 with h | h
      · exact hva h.1
      · exact hvb h.1
  have hnaT : ¬T.Adj v a := fun h => hnva (H.adj_sub (hTH h))
  have hnbT : ¬T.Adj v b := fun h => hnvb (H.adj_sub (hTH h))
  have hsm : smooth T a b = H.spanningCoe := by
    apply SimpleGraph.edgeSet_injective
    rw [smooth_edges T hab]
    change insert s(a,b) (H.spanningCoe.deleteEdges {s(a,b)}).edgeSet = H.edgeSet
    rw [edgeSet_deleteEdges]
    change insert s(a,b) (H.edgeSet \ {s(a,b)}) = H.edgeSet
    ext e
    have hh : e = s(a,b) → e ∈ H.edgeSet := by rintro rfl; exact he
    simp only [Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff]
    tauto
  have heven : ∀ x, Even ((unsmooth T v a b).degree x) := by
    intro x
    have hd := degree_relation T hva hvb hab hnaT hnbT hnT x
    have hh := regular_two_piece_degree_even H hc.2 x
    rw [← Subgraph.degree_spanningCoe] at hh
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hh ⊢
    rw [hsm] at hd
    rw [← hd]
    apply hh.add
    split_ifs <;> decide
  obtain ⟨D,hcD,hdD⟩ := even_cycle_decomposition (unsmooth T v a b) (by
    intro x
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heven x)
  have hforest : T.IsAcyclic := proper_cycle_subgraph_acyclic H hc.1 hc.2 T hTH s(a,b) he hnT
  have hbD := cycle_decomposition_forest_bound (unsmooth T v a b) T hforest D hcD hdD
  have hsub : (unsmooth T v a b).edgeFinset \ T.edgeFinset ⊆ {s(v,a),s(v,b)} := by
    intro e he'
    simp only [Finset.mem_sdiff,mem_edgeFinset] at he'
    rw [unsmooth_edges T hva hvb] at he'
    simp only [Set.mem_insert_iff] at he'
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hcard := (Finset.card_le_card hsub).trans (show ({s(v,a),s(v,b)} : Finset (Sym2 V)).card ≤ 2 from by
    have hh := Finset.card_insert_le s(v,a) ({s(v,b)} : Finset (Sym2 V))
    simpa using hh)
  simp only [SimpleGraph.edgeFinset,← Set.toFinite_toFinset] at hbD hcard
  exact ⟨D,hcD,hdD,by omega⟩

/-- Lifting a decomposition through one smoothing costs at most one piece.
The stronger cost-zero result requires the marked piece to avoid the apex. -/
lemma lift_decomposition_one_extra (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hna : ¬A.Adj v a) (hnb : ¬A.Adj v b) (hnab : ¬A.Adj a b)
    (D : Finset (smooth A a b).Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition (smooth A a b) D) :
    HasPieceBound (D.card+1) (unsmooth A v a b) := by
  have heS : s(a,b) ∈ (smooth A a b).edgeSet := by rw [smooth_edges A hab]; exact Set.mem_insert ..
  rw [← hd.2] at heS
  obtain ⟨H,hHD,heH⟩ := Set.mem_iUnion₂.mp heS
  let T := H.spanningCoe.deleteEdges {s(a,b)}
  let K := unsmooth T v a b
  let U := unsmooth A v a b
  let R := smooth A a b \ H.spanningCoe
  obtain ⟨E,hcE,hdE,hbE⟩ := erase_cycle_piece D hc hd H hHD
  obtain ⟨F,hcF,hdF,hbF⟩ := marked_replacement_bound A hva hvb hab hna hnb hnab H (hc H hHD) heH
  have hKe : K.edgeSet = insert s(v,b) (insert s(v,a) (H.edgeSet \ {s(a,b)})) := by
    rw [unsmooth_edges T hva hvb]
    simp only [T,edgeSet_deleteEdges]
    rfl
  have hRe : R.edgeSet = (insert s(a,b) A.edgeSet) \ H.edgeSet := by
    simp only [R,edgeSet_sdiff,smooth_edges A hab]
    rfl
  have hUe : U.edgeSet = insert s(v,b) (insert s(v,a) A.edgeSet) := unsmooth_edges A hva hvb
  have hHsub : H.edgeSet ⊆ insert s(a,b) A.edgeSet := by
    rw [← smooth_edges A hab]
    exact H.edgeSet_subset
  have hKUe : K.edgeSet ⊆ U.edgeSet := by
    rw [hKe,hUe]
    intro e he
    simp only [Set.mem_insert_iff,Set.mem_diff,Set.mem_singleton_iff] at he ⊢
    rcases he with h | h | ⟨h,hne⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ((hHsub h).resolve_left hne))
  have hRUe : R.edgeSet ⊆ U.edgeSet := by
    rw [hRe,hUe]
    intro e he
    have hh : e ≠ s(a,b) := by intro heq; exact he.2 (heq.symm ▸ heH)
    exact Or.inr (Or.inr (he.1.resolve_left hh))
  have hdis : Disjoint R.edgeSet K.edgeSet := by
    rw [hRe,hKe]
    apply Set.disjoint_left.mpr
    intro e heR heK
    have hh : e ≠ s(a,b) := by intro heq; exact heR.2 (heq.symm ▸ heH)
    have heA : e ∈ A.edgeSet := heR.1.resolve_left hh
    rcases heK with h | h | h
    · exact hnb (show s(v,b) ∈ A.edgeSet from h ▸ heA)
    · exact hna (show s(v,a) ∈ A.edgeSet from h ▸ heA)
    · exact heR.2 h.1
  have hcover : R.edgeSet ∪ K.edgeSet = U.edgeSet := by
    apply Set.Subset.antisymm (Set.union_subset hRUe hKUe)
    intro e he
    rw [hUe] at he
    rcases he with h | h | h
    · right; rw [hKe]; exact Or.inl h
    · right; rw [hKe]; exact Or.inr (Or.inl h)
    · by_cases hH : e ∈ H.edgeSet
      · right; rw [hKe]
        exact Or.inr (Or.inr ⟨hH,by intro heq; exact hnab (show s(a,b) ∈ A.edgeSet from (Set.mem_singleton_iff.mp heq) ▸ h)⟩)
      · left; rw [hRe]; exact ⟨Or.inr h,hH⟩
  obtain ⟨J,hcJ,hdJ,hbJ⟩ := combine_pure_decompositions
    (edgeSet_subset_edgeSet.mp hRUe) (edgeSet_subset_edgeSet.mp hKUe) hdis hcover E F
    (by
      intro L hL
      simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using hcE L hL)
    (by
      intro L hL
      simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using hcF L hL) hdE hdF
  refine ⟨J,?_,hdJ,by omega⟩
  intro L hL
  simpa only [IsRegularOfDegree,← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using hcJ L hL

/-- In a lex-minimal counterexample, smoothing decreases the optimum by
exactly one: the smoothed optimum is C*n, not merely at most C*n. -/
lemma lex_minimal_exact_smoothing (C : ℕ) (A : SimpleGraph V) {v a b : V}
    (hva : v ≠ a) (hvb : v ≠ b) (hab : a ≠ b)
    (hna : ¬A.Adj v a) (hnb : ¬A.Adj v b) (hnab : ¬A.Adj a b)
    (hG : GlobalVertexMinimal.IsLexMinimal C (unsmooth A v a b)) :
    (∃ D : Finset (smooth A a b).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (smooth A a b) D ∧ D.card = C * Fintype.card V) ∧
    (∀ D : Finset (smooth A a b).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition (smooth A a b) D → C * Fintype.card V ≤ D.card) ∧
    HasPieceBound (C * Fintype.card V + 1) (unsmooth A v a b) := by
  have hlow (D : Finset (smooth A a b).Subgraph)
      (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
      (hd : IsDecomposition (smooth A a b) D) : C * Fintype.card V ≤ D.card := by
    by_contra hn
    obtain ⟨E,hcE,hdE,hbE⟩ := lift_decomposition_one_extra A hva hvb hab hna hnb hnab D hc hd
    exact hG.1.2.1 ⟨E,hcE,hdE,by omega⟩
  obtain ⟨D,hc,hd,hb,_⟩ := lex_minimal_smoothing_obstruction C A hva hvb hab hna hnb hnab hG
  have heq := Nat.le_antisymm hb (hlow D hc hd)
  refine ⟨⟨D,hc,hd,heq⟩,hlow,?_⟩
  obtain ⟨E,hcE,hdE,hbE⟩ := lift_decomposition_one_extra A hva hvb hab hna hnb hnab D hc hd
  exact ⟨E,hcE,hdE,by omega⟩

lemma actual_lex_minimal_exact_smoothing (C : ℕ) (G : SimpleGraph V)
    (hG : GlobalVertexMinimal.IsLexMinimal C G) {v a b : V}
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) (hn : ¬G.Adj a b) :
    let S := smooth (removeSpokes G v a b) a b
    (∃ D : Finset S.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition S D ∧ D.card = C * Fintype.card V) ∧
    (∀ D : Finset S.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition S D → C * Fintype.card V ≤ D.card) ∧
    HasPieceBound (C * Fintype.card V + 1) G := by
  have hEq := unsmooth_removeSpokes G ha hb
  have hG' : GlobalVertexMinimal.IsLexMinimal C (unsmooth (removeSpokes G v a b) v a b) := by
    rwa [hEq]
  have hh := lex_minimal_exact_smoothing C (removeSpokes G v a b) ha.ne hb.ne hab
    (removeSpokes_left G v a b) (removeSpokes_right G v a b) (removeSpokes_pair G hn) hG'
  simpa only [hEq] using hh

end Erdos184.PartialSmoothing
