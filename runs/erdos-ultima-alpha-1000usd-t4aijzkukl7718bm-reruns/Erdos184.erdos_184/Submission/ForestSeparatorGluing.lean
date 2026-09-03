import Submission.TwoForestSeparatorBound

/-!
General separator gluing via parity-correcting forests. The two residual
side bounds are used only on even subgraphs of the original sides.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ForestBoundaryBudget
open ExactVertexSmoothing
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 800000

/-- Delete an even subgraph so that what remains is a forest. Equivalently,
the forest has the same vertex-degree parities as the original graph. -/
lemma even_part_with_forest_remainder (A : SimpleGraph V) :
    ∃ E : SimpleGraph V, E ≤ A ∧ (∀ x, Even (E.degree x)) ∧ (A \ E).IsAcyclic := by
  obtain ⟨D,hc,hd,hmax⟩ := exists_maximal_long_cycle_packing A 0
  refine ⟨unionPieces A D,unionPieces_le A D,?_,?_⟩
  · intro x
    have hh := unionPieces_degree A D hd x
    have hs : Even (∑ H ∈ D, H.degree x) := Finset.even_sum _
      (fun H hH => regular_two_piece_degree_even H (hc H hH).2.1 x)
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh ⊢
    rwa [hh]
  · intro x p hp
    have hh := hmax x p hp
    have hl := hp.three_le_length
    omega

/-- Unlike matching-completion gluing, this works for a separator of any
finite size. It requires bounds only for EVEN SUBGRAPHS of each side. -/
lemma decomposition_of_finite_separation {G A B : SimpleGraph V} (S : Set V)
    (heG : ∀ x, Even (G.degree x)) (hA : A ≤ G) (hB : B ≤ G)
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hi : A.support ∩ B.support ⊆ S) (kA kB : ℕ)
    (hbA : ∀ X : SimpleGraph V, X ≤ A → (∀ x, Even (X.degree x)) → HasPieceBound kA X)
    (hbB : ∀ X : SimpleGraph V, X ≤ B → (∀ x, Even (X.degree x)) → HasPieceBound kB X) :
    HasPieceBound (kA+kB+(S.ncard-1)) G := by
  obtain ⟨EA,hEA,heA,hFA⟩ := even_part_with_forest_remainder A
  obtain ⟨EB,hEB,heB,hFB⟩ := even_part_with_forest_remainder B
  let R := EA ⊔ EB
  let F := G \ R
  have hRG : R ≤ G := sup_le (hEA.trans hA) (hEB.trans hB)
  have hdE : Disjoint EA.edgeSet EB.edgeSet := hd.mono (edgeSet_mono hEA) (edgeSet_mono hEB)
  have heR : ∀ x, Even (R.degree x) := by
    intro x
    have hh := degree_sup_of_edge_disjoint EA EB hdE x
    have hxA := heA x
    have hxB := heB x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hxA hxB ⊢
    change Even (Nat.card ((EA ⊔ EB).neighborSet x))
    rw [hh]
    exact hxA.add hxB
  have heF : ∀ x, Even (F.degree x) := by
    intro x
    have hh := degree_sdiff_of_le hRG x
    have he := heG x
    have hr := heR x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh he hr ⊢
    change Even (Nat.card ((G \ R).neighborSet x))
    rw [hh]
    obtain ⟨a,ha⟩ := he
    obtain ⟨b,hb⟩ := hr
    exact ⟨a-b,by omega⟩
  have hdF : Disjoint (A \ EA).edgeSet (B \ EB).edgeSet :=
    hd.mono (edgeSet_mono sdiff_le) (edgeSet_mono sdiff_le)
  have huF : (A \ EA).edgeSet ∪ (B \ EB).edgeSet = F.edgeSet := by
    simp only [F,R,edgeSet_sdiff,edgeSet_sup,← hu]
    ext e
    have hea : e ∈ EA.edgeSet → e ∈ A.edgeSet := fun h => edgeSet_mono hEA h
    have heb : e ∈ EB.edgeSet → e ∈ B.edgeSet := fun h => edgeSet_mono hEB h
    have hn : ¬(e ∈ A.edgeSet ∧ e ∈ B.edgeSet) := fun h => Set.disjoint_left.mp hd h.1 h.2
    simp only [Set.mem_union,Set.mem_diff]
    tauto
  obtain ⟨DF,hcF,hdDF,hbDF⟩ := two_forest_piece_bound S
    (by
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using heF x)
    hFA hFB hdF huF (fun _ hx => hi ⟨support_mono sdiff_le hx.1,support_mono sdiff_le hx.2⟩)
  obtain ⟨DA,hcA,hdA,hbDA⟩ := hbA EA hEA heA
  obtain ⟨DB,hcB,hdB,hbDB⟩ := hbB EB hEB heB
  obtain ⟨DR,hcR,hdR,hbDR⟩ := combine_pure_decompositions
    (show EA ≤ R from le_sup_left) (show EB ≤ R from le_sup_right)
    hdE (edgeSet_sup EA EB).symm DA DB hcA hcB hdA hdB
  have hdRF : Disjoint R.edgeSet F.edgeSet := by
    dsimp only [F]
    rw [edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have huRF : R.edgeSet ∪ F.edgeSet = G.edgeSet := by
    dsimp only [F]
    rw [edgeSet_sdiff]
    exact Set.union_diff_cancel (edgeSet_mono hRG)
  obtain ⟨D,hcD,hdD,hbD⟩ := combine_pure_decompositions hRG
    (show F ≤ G from sdiff_le) hdRF huRF DR DF
    (by
      intro H hH
      refine ⟨(hcR H hH).1,?_⟩
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcR H hH).2 x)
    hcF hdR hdDF
  exact ⟨D,hcD,hdD,by omega⟩

/-- The support-bound formulation used in vertex-minimal reductions. -/
lemma decomposition_of_finite_separation_support {G A B : SimpleGraph V} (S : Set V)
    (heG : ∀ x, Even (G.degree x)) (hA : A ≤ G) (hB : B ≤ G)
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hi : A.support ∩ B.support ⊆ S) (kA kB : ℕ)
    (hbA : ∀ X : SimpleGraph V, X.support ⊆ A.support →
      (∀ x, Even (X.degree x)) → HasPieceBound kA X)
    (hbB : ∀ X : SimpleGraph V, X.support ⊆ B.support →
      (∀ x, Even (X.degree x)) → HasPieceBound kB X) :
    HasPieceBound (kA+kB+(S.ncard-1)) G :=
  decomposition_of_finite_separation S heG hA hB hd hu hi kA kB
    (fun X hX heX => hbA X (support_mono hX) heX)
    (fun X hX heX => hbB X (support_mono hX) heX)

end Erdos184.ForestBoundaryBudget
