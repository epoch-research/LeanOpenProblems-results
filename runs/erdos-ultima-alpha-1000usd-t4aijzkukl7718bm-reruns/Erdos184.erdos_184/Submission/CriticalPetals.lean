import Submission.CriticalRainbowTrees

/-!
A connected critical optimum splits, after reserving a cycle, into equally
sized color families with connected unions. Restoring the reserved cycle to
any one color family gives a graph violating the coefficient-one rank bound.
This is a necessary structural condition, not a proof of a uniform bound.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.CriticalPetals
open RankCritical RankCriticalPartitions CriticalRainbowTrees RainbowForests

variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V}

noncomputable def colorPieces (S : Finset G.Subgraph) (c : S → I) (i : I) :
    Finset G.Subgraph :=
  (Finset.univ.filter (fun H : S => c H = i)).image Subtype.val

lemma mem_colorPieces (S : Finset G.Subgraph) (c : S → I) (i : I) (H : G.Subgraph) :
    H ∈ colorPieces S c i ↔ ∃ J : S, J.val = H ∧ c J = i := by
  simp only [colorPieces, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨J, hJ, rfl⟩; exact ⟨J, rfl, hJ⟩
  · rintro ⟨J, rfl, hJ⟩; exact ⟨J, hJ, rfl⟩

lemma colorPieces_subset (S : Finset G.Subgraph) (c : S → I) (i : I) :
    colorPieces S c i ⊆ S := by
  intro H hH
  obtain ⟨J, rfl, _⟩ := (mem_colorPieces S c i H).mp hH
  exact J.property

lemma colorPieces_pairwise (S : Finset G.Subgraph) (c : S → I) :
    Pairwise (fun i j => Disjoint (colorPieces S c i) (colorPieces S c j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro H hi hj
  obtain ⟨A, hA, hi⟩ := (mem_colorPieces S c i H).mp hi
  obtain ⟨B, hB, hj⟩ := (mem_colorPieces S c j H).mp hj
  have he : A = B := Subtype.ext (hA.trans hB.symm)
  subst B
  exact hij (hi.symm.trans hj)

lemma colorPieces_union (S : Finset G.Subgraph) (c : S → I) :
    Finset.univ.biUnion (colorPieces S c) = S := by
  ext H
  constructor
  · intro hH
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hH
    exact colorPieces_subset S c i hi
  · intro hH
    exact Finset.mem_biUnion.mpr ⟨c ⟨H,hH⟩, Finset.mem_univ _,
      (mem_colorPieces S c _ H).mpr ⟨⟨H,hH⟩, rfl, rfl⟩⟩

lemma selected_le_color_union (S : Finset G.Subgraph) (c : S → I) (u v : S → V)
    (h : ∀ H : S, H.val.Adj (u H) (v H)) (i : I) :
    selected c u v i ≤ unionPieces G (colorPieces S c i) := by
  intro a b hab
  obtain ⟨⟨H, hc, he⟩, _⟩ := (selected_adj c u v i a b).mp hab
  have hh : s(u H,v H) ∈ H.val.edgeSet := h H
  have hh' : s(a,b) ∈ H.val.edgeSet := he.symm ▸ hh
  apply (mem_edgeSet _).mp
  rw [unionPieces_edgeSet]
  exact Set.mem_iUnion₂.mpr ⟨H.val,
    (mem_colorPieces S c i H.val).mpr ⟨H, rfl, hc⟩, hh'⟩

lemma colorPieces_card (S : Finset G.Subgraph) (c : S → I) (u v : S → V)
    (h : ∀ H, u H ≠ v H) (hinj : Function.Injective (fun H => s(u H,v H)))
    (ht : ∀ i, (selected c u v i).IsTree) (i : I) :
    (colorPieces S c i).card = Fintype.card V - 1 := by
  have hc := (ht i).card_edgeFinset
  rw [selected_edgeFinset c u v h, Finset.card_image_of_injective _ hinj] at hc
  unfold colorPieces
  rw [Finset.card_image_of_injective _ Subtype.val_injective]
  omega

lemma unionPieces_even (D S : Finset G.Subgraph) (hSD : S ⊆ D)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) : ∀ v, Even ((unionPieces G S).degree v) := by
  intro v
  rw [unionPieces_degree G S (fun H hH J hJ hne => hd.1 (hSD hH) (hSD hJ) hne)]
  apply Finset.even_sum
  intro H hH
  exact regular_two_piece_degree_even H (hc H (hSD hH)).2 v

lemma unionPieces_mono {S T : Finset G.Subgraph} (h : S ⊆ T) :
    unionPieces G S ≤ unionPieces G T := by
  apply SimpleGraph.edgeSet_subset_edgeSet.mp
  rw [unionPieces_edgeSet, unionPieces_edgeSet]
  exact Set.iUnion₂_mono' (fun H hH => ⟨H, h hH, Set.Subset.rfl⟩)

lemma critical_optimum_minimum {C : ℕ} (hG : IsCritical C G)
    (D : Finset G.Subgraph) (hsize : D.card = C * graphRank G + 1) :
    ∀ E : Finset G.Subgraph,
      (∀ H ∈ E, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) →
      IsDecomposition G E → D.card ≤ E.card := by
  intro E hc hd
  by_contra h
  exact hG.2.1 ⟨E, hc, hd, by omega⟩

/-- A connected critical optimum gives C spanning color families of exactly
n−1 cycles. With the reserved cycle restored, each color is itself a connected
even counterexample to the coefficient-one rank bound. -/
theorem exists_rank_one_petals {C : ℕ} (hG : IsCritical C G)
    (hconn : G.Connected) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hsize : D.card = C * graphRank G + 1)
    (H₀ : G.Subgraph) (hH₀ : H₀ ∈ D) :
    ∃ S : Fin C → Finset G.Subgraph,
      (∀ i, S i ⊆ D.erase H₀) ∧
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      Finset.univ.biUnion S = D.erase H₀ ∧
      (∀ i, (S i).card = Fintype.card V - 1 ∧ (unionPieces G (S i)).Connected) ∧
      ∀ i, (unionPieces G (insert H₀ (S i))).Connected ∧
        (∀ v, Even ((unionPieces G (insert H₀ (S i))).degree v)) ∧
        ¬HasBound 1 (unionPieces G (insert H₀ (S i))) := by
  obtain ⟨c, u, v, ha, hi, ht, _⟩ :=
    exists_reserved_rainbow_trees hG hconn D hc hd hsize H₀ hH₀
  let S := colorPieces (D.erase H₀) c
  have hs (i : Fin C) : S i ⊆ D.erase H₀ := colorPieces_subset _ c i
  have ht' : ∀ i, (selected c u v i).IsTree := fun i => (ht i).1
  have hne : ∀ H, u H ≠ v H := fun H => (ha H).ne
  have hn (i : Fin C) : (S i).card = Fintype.card V - 1 :=
    colorPieces_card _ c u v hne hi ht' i
  have hsc (i : Fin C) : (unionPieces G (S i)).Connected :=
    (ht' i).isConnected.mono (selected_le_color_union _ c u v ha i)
  have hsub (i : Fin C) : insert H₀ (S i) ⊆ D :=
    Finset.insert_subset hH₀ ((hs i).trans (Finset.erase_subset H₀ D))
  refine ⟨S, hs, colorPieces_pairwise _ c, colorPieces_union _ c,
    fun i => ⟨hn i, hsc i⟩, ?_⟩
  intro i
  have hconn' : (unionPieces G (insert H₀ (S i))).Connected :=
    (hsc i).mono (unionPieces_mono (Finset.subset_insert H₀ (S i)))
  refine ⟨hconn', unionPieces_even D _ (hsub i) hc hd, ?_⟩
  rintro ⟨E, hcE, hdE, hbE⟩
  have hmin := subfamily_minimum_for_union G D hc hd
    (critical_optimum_minimum hG D hsize) _ (hsub i) E hcE hdE
  have hnot : H₀ ∉ S i := fun h => (Finset.mem_erase.mp (hs i h)).1 rfl
  rw [Finset.card_insert_of_notMem hnot, hn i] at hmin
  have hr := connected_rank hconn'
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hconn.nonempty
  simp only [one_mul] at hbE
  omega

end Erdos184.CriticalPetals
