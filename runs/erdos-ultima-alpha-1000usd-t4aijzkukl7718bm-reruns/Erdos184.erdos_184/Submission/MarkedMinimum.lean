import Submission.CycleMixing

/-! Local structure of decompositions minimizing the number of unmarked pieces.
No global marked-hitting assertion is assumed or concluded. -/
open SimpleGraph
open scoped Classical
namespace Erdos184

noncomputable def badPieces {V : Type*} {G : SimpleGraph V} (R : SimpleGraph V)
    (D : Finset G.Subgraph) : Finset G.Subgraph :=
  D.filter (fun H => Disjoint H.edgeSet R.edgeSet)

lemma minimum_bad_cycle_decomposition {V : Type*} [Fintype V] (G R : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧ IsDecomposition G D ∧
      ∀ E : Finset G.Subgraph,
        (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
        IsDecomposition G E → (badPieces R D).card ≤ (badPieces R E).card := by
  let P (n : ℕ) := ∃ D : Finset G.Subgraph,
    (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
    IsDecomposition G D ∧ (badPieces R D).card = n
  have hex : ∃ n, P n := by
    obtain ⟨D, hc, hd⟩ := even_cycle_decomposition G he
    exact ⟨(badPieces R D).card, D, hc, hd, rfl⟩
  obtain ⟨D, hc, hd, hcard⟩ := Nat.find_spec hex
  refine ⟨D, hc, hd, ?_⟩
  intro E hcE hdE
  rw [hcard]
  exact Nat.find_min' hex ⟨E, hcE, hdE, rfl⟩

/-- Replacing a subfamily containing a bad piece by wholly marked-hitting
pieces strictly decreases the number of bad pieces. -/
lemma bad_count_strict_of_replacement {V : Type*} {G : SimpleGraph V}
    (R : SimpleGraph V) (D S E : Finset G.Subgraph) (hSD : S ⊆ D)
    (hgood : ∀ H ∈ E, ¬Disjoint H.edgeSet R.edgeSet)
    (hbad : ∃ H ∈ S, Disjoint H.edgeSet R.edgeSet) :
    (badPieces R ((D \ S) ∪ E)).card < (badPieces R D).card := by
  have hsub : badPieces R ((D \ S) ∪ E) ⊆ badPieces R D := by
    intro H hH
    obtain ⟨hH, hbadH⟩ := Finset.mem_filter.mp hH
    rcases Finset.mem_union.mp hH with hD | hE
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hD).1, hbadH⟩
    · exact (hgood H hE hbadH).elim
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro heq
  obtain ⟨H, hHS, hbadH⟩ := hbad
  have hHD : H ∈ badPieces R D := Finset.mem_filter.mpr ⟨hSD hHS, hbadH⟩
  rw [← heq] at hHD
  obtain ⟨hHD, _⟩ := Finset.mem_filter.mp hHD
  rcases Finset.mem_union.mp hHD with hD | hE
  · exact (Finset.mem_sdiff.mp hD).2 hHS
  · exact hgood H hE hbadH

/-- In a bad-count-minimizing decomposition, an unmarked cycle cannot
share two vertices with any other piece if the unmarked graph is 2-regular
on its support. This is a local restriction, not a proof that no bad pieces exist. -/
lemma minimum_bad_pair_overlap {V : Type*} [Fintype V] (G R B : SimpleGraph V)
    (hb : B.IsCycles) (hcover : G.edgeSet ⊆ R.edgeSet ∪ B.edgeSet)
    (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D)
    (hm : ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → (badPieces R D).card ≤ (badPieces R E).card)
    (H K : G.Subgraph) (hH : H ∈ D) (hK : K ∈ D) (hne : H ≠ K)
    (hbadK : Disjoint K.edgeSet R.edgeSet) : (H.verts ∩ K.verts).ncard ≤ 1 := by
  by_contra! hover
  have hKB : K.edgeSet ⊆ B.edgeSet := by
    intro e he
    rcases hcover (K.edgeSet_subset he) with heR | heB
    · exact (Set.disjoint_left.mp hbadK he heR).elim
    · exact heB
  have hcover' : H.edgeSet ∪ K.edgeSet ⊆ R.edgeSet ∪ B.edgeSet :=
    fun _ he => hcover (he.elim (fun h => H.edgeSet_subset h) (fun h => K.edgeSet_subset h))
  obtain ⟨E, hcE, hdE⟩ := absorb_blue_cycle hb H K (hc H hH).1 (hc H hH).2
    (hc K hK).1 (hc K hK).2 (hd.1 hH hK hne) hover hKB hcover'
  let U := H.spanningCoe ⊔ K.spanningCoe
  let hUG : U ≤ G := sup_le H.spanningCoe_le K.spanningCoe_le
  let F := E.image (promote hUG)
  let S : Finset G.Subgraph := {H,K}
  have hSD : S ⊆ D := by
    intro L hL
    rcases Finset.mem_insert.mp hL with rfl | hL
    · exact hH
    · exact Finset.mem_singleton.mp hL ▸ hK
  have hcF : ∀ L ∈ F, L.coe.Connected ∧ L.coe.IsRegularOfDegree 2 := by
    intro L hL
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hL
    refine ⟨(hcE X hX).1, ?_⟩
    intro v
    simpa only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      using (hcE X hX).2.1 v
  have hgoodF : ∀ L ∈ F, ¬Disjoint L.edgeSet R.edgeSet := by
    intro L hL
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hL
    exact Set.not_disjoint_iff.mpr (hcE X hX).2.2
  have hdF : Set.PairwiseDisjoint (F : Set G.Subgraph) (fun L => L.edgeSet) := by
    intro L hL M hM hne
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hM
    exact hdE.1 hX hY (fun h => hne (congrArg (promote hUG) h))
  have hUS : (⋃ L ∈ S, L.edgeSet) = U.edgeSet := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton, Set.iUnion_iUnion_eq_or_left,
      Set.iUnion_iUnion_eq_left]
    exact (SimpleGraph.edgeSet_sup H.spanningCoe K.spanningCoe).symm
  have hcovF : (⋃ L ∈ F, L.edgeSet) = ⋃ L ∈ S, L.edgeSet := by
    rw [hUS, ← hdE.2]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨L, hL, heL⟩
      obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hL
      exact ⟨X, hX, heL⟩
    · rintro ⟨L, hL, heL⟩
      exact ⟨promote hUG L, Finset.mem_image.mpr ⟨L,hL,rfl⟩, heL⟩
  have hd' := (replace_decomposition G D S F hd hSD hdF hcovF).1
  have hc' : ∀ L ∈ (D \ S) ∪ F, L.coe.Connected ∧ L.coe.IsRegularOfDegree 2 := by
    intro L hL
    rcases Finset.mem_union.mp hL with hL | hL
    · exact hc L (Finset.mem_sdiff.mp hL).1
    · exact hcF L hL
  have hstrict := bad_count_strict_of_replacement R D S F hSD hgoodF
    ⟨K, by simp [S], hbadK⟩
  exact (not_lt_of_ge (hm _ hc' hd')) hstrict

end Erdos184
