import Submission.ChainRingPieces
import Submission.ParityDegreeLower

/-! Each block remaining after the closing-edge piece needs at least eight pieces. -/
open SimpleGraph
namespace Erdos184Work.ChainRing
open Critical
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 10000

def rightVertices (i : Fin 3) : Finset Vertex := Finset.univ.image (fun j : Fin 6 => Sum.inr (i,j))
lemma rightVertices_card : ∀ i, (rightVertices i).card = 6 := by decide
lemma hub_right_disjoint : ∀ i, Disjoint (hubVertices i) (rightVertices i) := by decide
lemma rightVertices_independent : ∀ i u, u ∈ rightVertices i → ∀ v, v ∈ rightVertices i →
    ¬ source.Adj u v := by decide +kernel
lemma block_right_neighbors : ∀ i j w, (block i).Adj (.inr (i,j)) w ↔ source.Adj (.inr (i,j)) w := by
  decide +kernel
lemma block_card : ∀ i, (block i).edgeFinset.card = 18 := by decide +kernel
lemma base_no_closing : ¬ base.Adj (.inl 0) (.inl 3) := by decide

open scoped Classical

def residual (H : source.Subgraph) : SimpleGraph Vertex := source \ H.spanningCoe
def rowResidual (H : source.Subgraph) (i : Fin 3) : SimpleGraph Vertex := residual H ⊓ block i

lemma rowResidual_eq_sdiff (H : source.Subgraph) (i : Fin 3) :
    rowResidual H i = block i \ (H.spanningCoe ⊓ block i) := by
  ext x y
  constructor
  · rintro ⟨⟨hs,hn⟩,hb⟩
    exact ⟨hb,fun h => hn h.1⟩
  · rintro ⟨hb,hn⟩
    exact ⟨⟨block_le_source i hb,fun h => hn ⟨h,hb⟩⟩,hb⟩

lemma rowResidual_card_add (H : source.Subgraph) (i : Fin 3) :
    (rowResidual H i).edgeFinset.card + (H.spanningCoe ⊓ block i).edgeFinset.card = 18 := by
  have hh := Finset.card_sdiff_add_card_eq_card
    (SimpleGraph.edgeFinset_mono (inf_le_right : H.spanningCoe ⊓ block i ≤ block i))
  rw [← SimpleGraph.edgeFinset_sdiff] at hh
  have hc := block_card i
  simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hh hc ⊢
  rw [← rowResidual_eq_sdiff H i] at hh
  omega

lemma restrict_right_degree {S : SimpleGraph Vertex} (hS : S ≤ source) (i : Fin 3) (j : Fin 6) :
    deg (S ⊓ block i) (.inr (i,j)) = deg S (.inr (i,j)) := by
  apply degree_eq_of_adj_iff
  intro w
  exact ⟨And.left,fun h => ⟨h,(block_right_neighbors i j w).mpr (hS h)⟩⟩

lemma rowResidual_right_odd (H : source.Subgraph) (hH : IsCycleOrEdge H.coe)
    (he : H.spanningCoe.Adj (.inl 0) (.inl 3)) (i : Fin 3) (j : Fin 6) :
    Odd (deg (rowResidual H i) (.inr (i,j))) := by
  have hd := degree_sdiff_add source H.spanningCoe H.spanningCoe_le (.inr (i,j))
  have hs := source_degree_right i j
  have hev := closing_piece_right_even H hH he i j
  have hr := restrict_right_degree (S := residual H) sdiff_le i j
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hd hs
  change deg (residual H) (.inr (i,j)) + deg H.spanningCoe (.inr (i,j)) = deg source (.inr (i,j)) at hd
  change deg (rowResidual H i) (.inr (i,j)) = deg (residual H) (.inr (i,j)) at hr
  rw [Nat.even_iff] at hev
  rw [Nat.odd_iff]
  dsimp only [deg] at hd hs hev hr ⊢
  omega

lemma rowResidual_number_ge_eight (H : source.Subgraph) (hH : IsCycleOrEdge H.coe)
    (he : H.spanningCoe.Adj (.inl 0) (.inl 3)) (i : Fin 3) : 8 ≤ number (rowResidual H i) := by
  let R := rowResidual H i
  have hRS : R ≤ source := inf_le_left.trans sdiff_le
  obtain ⟨D,hD,hdec,hcard⟩ := exists_minimum R
  have hodd : ∀ v ∈ rightVertices i, Odd (R.degree v) := by
    intro v hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using
      rowResidual_right_odd H hH he i j
  have hl := ParityDegreeLower.independent_odd_degree_bound D hD hdec
    (hubVertices i) (rightVertices i) (rightVertices i)
    (by rw [hubVertices_card]; decide) (hub_right_disjoint i)
    (fun u hu v hv huv => rightVertices_independent i u hu v hv (hRS huv)) hodd hodd
  rw [hubVertices_card,rightVertices_card,hcard] at hl
  have hsum : (∑ v ∈ hubVertices i, deg R v) = R.edgeFinset.card := by
    rw [hub_sum]
    exact (block_edge_card (show R ≤ block i from inf_le_right)).symm
  have hc := rowResidual_card_add H i
  have hb := closing_piece_block_bound H hH he i
  simp only [← SimpleGraph.card_neighborSet_eq_degree,SimpleGraph.edgeFinset_card,
    ← Nat.card_eq_fintype_card] at hl hsum hc hb
  change _ ≤ 6 * number R at hl
  change 8 ≤ number R
  dsimp only [deg, R] at hl hsum hc hb ⊢
  omega

end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.rowResidual_number_ge_eight
