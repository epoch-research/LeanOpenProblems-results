import Submission.RankCycleFamilies
import Submission.RainbowForests

/-!
A connected C-rank-critical cycle family, after reserving any one cycle,
has a rainbow selection of edges forming C edge-disjoint spanning trees.
This is a structural consequence of criticality, not a contradiction to it.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.CriticalRainbowTrees
open RankCritical RankCriticalPartitions RankCycleFamilies RainbowForests

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma subfamily_sup_eq (S : Finset G.Subgraph) (t : Finset S) :
    t.sup (fun H => H.val.spanningCoe) = unionPieces G (t.image Subtype.val) := by
  ext a b
  simp only [Finset.sup_eq_iSup, iSup_adj, Subgraph.spanningCoe_adj]
  rw [← mem_edgeSet (unionPieces G (t.image Subtype.val))]
  rw [unionPieces_edgeSet]
  simp only [Set.mem_iUnion, Finset.mem_image]
  constructor
  · rintro ⟨H, hHt, heH⟩
    exact ⟨H.val, ⟨H, hHt, rfl⟩, heH⟩
  · rintro ⟨H, ⟨J, hJt, rfl⟩, heH⟩
    exact ⟨J, hJt, heH⟩

lemma distinct_representatives (D S : Finset G.Subgraph) (hSD : S ⊆ D)
    (hd : IsDecomposition G D) (u v : S → V)
    (h : ∀ H : S, H.val.Adj (u H) (v H)) :
    Function.Injective (fun H => s(u H,v H)) := by
  intro H J he
  change s(u H,v H) = s(u J,v J) at he
  apply Subtype.ext
  by_contra hne
  have hmH : s(u H,v H) ∈ H.val.edgeSet := h H
  have hmJ : s(u H,v H) ∈ J.val.edgeSet := by
    rw [he]
    exact h J
  exact Set.disjoint_left.mp
    (hd.1 (hSD H.property) (hSD J.property) hne) hmH hmJ

lemma selected_disjoint {I J : Type*} [Fintype I]
    (c : J → I) (u v : J → V)
    (hinj : Function.Injective (fun j => s(u j,v j))) :
    Pairwise (fun i j => Disjoint (selected c u v i).edgeSet (selected c u v j).edgeSet) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro e hei hej
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨⟨p, hp, hep⟩, _⟩ := (selected_adj c u v i a b).mp hei
    obtain ⟨⟨q, hq, heq⟩, _⟩ := (selected_adj c u v j a b).mp hej
    have hpq := hinj (hep.symm.trans heq)
    subst q
    exact hij (hp.symm.trans hq)

/-- Every reserved cycle in a connected critical optimum is avoided by a
rainbow C-fold spanning-tree selection from the other cycles. -/
theorem exists_reserved_rainbow_trees {C : ℕ} (hG : IsCritical C G)
    (hconn : G.Connected) (D : Finset G.Subgraph)
    (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : IsDecomposition G D) (hsize : D.card = C * graphRank G + 1)
    (H₀ : G.Subgraph) (hH₀ : H₀ ∈ D) :
    ∃ (c : D.erase H₀ → Fin C) (u v : D.erase H₀ → V),
      (∀ H : D.erase H₀, H.val.Adj (u H) (v H)) ∧
      Function.Injective (fun H => s(u H,v H)) ∧
      (∀ i, (selected c u v i).IsTree ∧ selected c u v i ≤ G \ H₀.spanningCoe) ∧
      Pairwise (fun i j => Disjoint (selected c u v i).edgeSet (selected c u v j).edgeSet) := by
  let S := D.erase H₀
  have hb := reserved_subfamily_rank_bound hG D hc hd hsize H₀ hH₀
  have hhall : ∀ t : Finset S, t.card ≤ Fintype.card (Fin C) *
      (Fintype.card V - Fintype.card (t.sup (fun H => H.val.spanningCoe)).ConnectedComponent) := by
    intro t
    have hs : t.image Subtype.val ⊆ S := by
      intro H hH
      obtain ⟨J, _, rfl⟩ := Finset.mem_image.mp hH
      exact J.property
    have hh := hb (t.image Subtype.val) hs
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
    rw [subfamily_sup_eq]
    simpa only [graphRank, Nat.card_eq_fintype_card, Fintype.card_fin] using hh
  obtain ⟨c, u, v, ha, hf⟩ := exists_rainbow_forests
    (I := Fin C) (fun H : S => H.val.spanningCoe) hhall
  have ha' : ∀ H : S, H.val.Adj (u H) (v H) := ha
  have hi := distinct_representatives D S (Finset.erase_subset H₀ D) hd u v ha'
  have hne : ∀ H, u H ≠ v H := fun H => (ha H).ne
  letI : Nonempty V := hconn.nonempty
  have hr := connected_rank hconn
  have hrs : graphRank G = Fintype.card V - 1 := by omega
  have hcard : Fintype.card S = Fintype.card (Fin C) * (Fintype.card V - 1) := by
    rw [Fintype.card_coe, Fintype.card_fin]
    have he := Finset.card_erase_add_one hH₀
    rw [hsize, hrs] at he
    change S.card = _
    dsimp only [S]
    omega
  have ht := selected_isTree_of_card c u v hne hi hf hcard
  refine ⟨c, u, v, ha', hi, ?_, selected_disjoint c u v hi⟩
  intro i
  refine ⟨ht i, selected_le c u v _ ?_ i⟩
  intro H
  refine ⟨H.val.spanningCoe_le (ha H), ?_⟩
  intro hbad
  exact Set.disjoint_left.mp
    (hd.1 (Finset.mem_erase.mp H.property).2 hH₀ (Finset.mem_erase.mp H.property).1)
    (show s(u H,v H) ∈ H.val.edgeSet from ha' H)
    (show s(u H,v H) ∈ H₀.edgeSet from hbad)

end Erdos184.CriticalRainbowTrees
