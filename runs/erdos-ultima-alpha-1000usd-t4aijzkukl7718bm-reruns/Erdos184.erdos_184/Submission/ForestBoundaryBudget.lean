import Submission.CycleMixing

/-!
Boundary-degree budgets for forests even away from a designated finite set.
These are intermediate lemmas for general separator gluing.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ForestBoundaryBudget
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 400000

lemma forest_edge_card_support (A : SimpleGraph V) (ha : A.IsAcyclic) (hn : A ≠ ⊥) :
    A.edgeFinset.card + 1 ≤ A.support.ncard := by
  obtain ⟨u,v,huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hn
  letI : Nonempty A.support := ⟨⟨u,⟨v,huv⟩⟩⟩
  have h := forest_edge_card_lt_vertex_card (A.induce A.support)
    (ha.comap (Embedding.induce A.support).toHom Subtype.val_injective)
  rw [A.card_edgeFinset_induce_support] at h
  simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using h

/-- A nonempty forest even outside S has boundary-degree sum at most 2|S|-2. -/
lemma boundary_degree_upper (A : SimpleGraph V) (ha : A.IsAcyclic) (hn : A ≠ ⊥)
    (S : Set V) (he : ∀ x, x ∉ S → Even (A.degree x)) :
    (∑ x ∈ S.toFinset, A.degree x) + 2 ≤ 2*S.ncard := by
  let U := A.support.toFinset ∪ S.toFinset
  have hTU : S.toFinset ⊆ U := Finset.subset_union_right
  have hsumU : (∑ x ∈ U, A.degree x) = ∑ x, A.degree x := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    apply (A.degree_eq_zero_iff_notMem_support x).mpr
    intro hxs
    exact hx (Finset.mem_union_left _ (Set.mem_toFinset.mpr hxs))
  have hlower : 2*(U \ S.toFinset).card ≤ ∑ x ∈ U \ S.toFinset, A.degree x := by
    calc
      _ = ∑ _x ∈ U \ S.toFinset, 2 := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hxU,hxS⟩ := Finset.mem_sdiff.mp hx
        have hxS' : x ∉ S := by simpa using hxS
        have hxA : x ∈ A.support := by
          have hh := (Finset.mem_union.mp hxU).resolve_right hxS
          exact Set.mem_toFinset.mp hh
        have hpos := (A.degree_pos_iff_mem_support x).mpr hxA
        obtain ⟨k,hk⟩ := he x hxS'
        omega
  have hsplit := Finset.sum_sdiff (f := fun x => A.degree x) hTU
  rw [hsumU,A.sum_degrees_eq_twice_card_edges] at hsplit
  have hcard := Finset.card_sdiff_add_card_eq_card hTU
  have hm := forest_edge_card_support A ha hn
  have hFU : A.support.ncard ≤ U.card := by
    simpa only [Set.toFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using
      Finset.card_le_card (show A.support.toFinset ⊆ U from Finset.subset_union_left)
  have hTcard : S.toFinset.card = S.ncard := (Set.ncard_eq_toFinset_card' _).symm
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hlower hsplit hm ⊢
  omega

/-- A nonempty forest even away from S has positive even boundary-degree sum. -/
lemma boundary_degree_lower (A : SimpleGraph V) (ha : A.IsAcyclic) (hn : A ≠ ⊥)
    (S : Set V) (he : ∀ x, x ∉ S → Even (A.degree x)) :
    2 ≤ ∑ x ∈ S.toFinset, A.degree x := by
  have heout : Even (∑ x ∈ Finset.univ \ S.toFinset, A.degree x) :=
    Finset.even_sum _ (fun x hx => he x (by simpa using (Finset.mem_sdiff.mp hx).2))
  have htotal : Even (∑ x, A.degree x) := by
    rw [A.sum_degrees_eq_twice_card_edges]
    exact even_two_mul _
  rw [← Finset.sum_sdiff (f := fun x => A.degree x) (Finset.subset_univ S.toFinset)] at htotal
  have heS := (Nat.even_add.mp htotal).mp heout
  have hpos : 0 < ∑ x ∈ S.toFinset, A.degree x := by
    by_contra! hz
    apply hn
    apply even_acyclic_eq_bot A _ ha
    intro x
    by_cases hx : x ∈ S
    · have hle := Finset.single_le_sum (fun y (_ : y ∈ S.toFinset) => Nat.zero_le (A.degree y))
        (Set.mem_toFinset.mpr hx)
      have hzero : A.degree x = 0 := by omega
      rw [hzero]; decide
    · exact he x hx
  obtain ⟨k,hk⟩ := heS
  omega

/-- Degree is subadditive over an edge-disjoint graph packing in A. -/
lemma packing_degree_sum_le {J : Type*} (t : Finset J) (X : J → SimpleGraph V)
    (A : SimpleGraph V) (hsub : ∀ i ∈ t, X i ≤ A)
    (hd : Set.PairwiseDisjoint (t : Set J) (fun i => (X i).edgeSet)) (v : V) :
    (∑ i ∈ t, (X i).degree v) ≤ A.degree v := by
  have hdis : Set.PairwiseDisjoint (t : Set J) (fun i => (X i).neighborFinset v) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact Set.disjoint_left.mp (hd hi hj hij)
      (show s(v,w) ∈ (X i).edgeSet from ((X i).mem_neighborFinset _ _).mp hw)
      (show s(v,w) ∈ (X j).edgeSet from ((X j).mem_neighborFinset _ _).mp hw')
  have hU : t.biUnion (fun i => (X i).neighborFinset v) ⊆ A.neighborFinset v := by
    intro w hw
    obtain ⟨i,hi,hw⟩ := Finset.mem_biUnion.mp hw
    exact (A.mem_neighborFinset _ _).mpr (hsub i hi (((X i).mem_neighborFinset _ _).mp hw))
  have hh := Finset.card_le_card hU
  rw [Finset.card_biUnion hdis] at hh
  simpa only [card_neighborFinset_eq_degree] using hh

/-- Edge-disjoint nonempty subforests even outside S can occur at most |S|-1
times in a forest that is itself even outside S. -/
lemma forest_family_card_bound {J : Type*} (t : Finset J) (X : J → SimpleGraph V)
    (A : SimpleGraph V) (hA : A.IsAcyclic) (S : Set V)
    (heA : ∀ x, x ∉ S → Even (A.degree x))
    (hsub : ∀ i ∈ t, X i ≤ A)
    (hn : ∀ i ∈ t, X i ≠ ⊥)
    (heX : ∀ i ∈ t, ∀ x, x ∉ S → Even ((X i).degree x))
    (hd : Set.PairwiseDisjoint (t : Set J) (fun i => (X i).edgeSet)) :
    t.card ≤ S.ncard-1 := by
  by_cases ht : t.Nonempty
  · obtain ⟨i,hi⟩ := ht
    have hAn : A ≠ ⊥ := by
      intro hbot
      exact hn i hi (le_bot_iff.mp (hbot ▸ hsub i hi))
    have hupper := boundary_degree_upper A hA hAn S heA
    have hlower : 2*t.card ≤ ∑ j ∈ t, ∑ x ∈ S.toFinset, (X j).degree x := by
      calc
        _ = ∑ _j ∈ t, 2 := by simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun j hj =>
          boundary_degree_lower (X j) (hA.anti (hsub j hj)) (hn j hj) S (heX j hj))
    have hsum : (∑ j ∈ t, ∑ x ∈ S.toFinset, (X j).degree x) ≤
        ∑ x ∈ S.toFinset, A.degree x := by
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum (fun x _ => packing_degree_sum_le t X A hsub hd x)
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp ht,Finset.card_empty,Nat.zero_le]

end Erdos184.ForestBoundaryBudget
