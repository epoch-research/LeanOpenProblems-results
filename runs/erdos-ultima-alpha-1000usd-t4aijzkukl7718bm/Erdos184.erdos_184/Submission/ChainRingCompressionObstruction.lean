import Submission.ChainRingHullBounds
import Submission.ChainRingLower

/-! An obstruction to the auxiliary adjacent-compression rule for globally
edge-minimal graphs. This is not a disproof of Erdős Problem 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ChainRing
open Critical EdgeHull Compression
set_option maxHeartbeats 1000000

lemma no_closing_le_base {R : SimpleGraph Vertex} (hR : R ≤ source)
    (he : ¬ R.Adj (.inl 0) (.inl 3)) : R ≤ base := by
  rw [← delete_closing]
  intro x y hxy
  refine ⟨hR hxy,?_⟩
  intro hm
  have heq : s(x,y) = s(Sum.inl 0,Sum.inl 3) := Set.mem_singleton_iff.mp hm.1
  apply he
  change s(Sum.inl 0,Sum.inl 3) ∈ R.edgeSet
  rw [← heq]
  exact hxy

/-- The original global-minimal compression hypothesis fails on a subgraph
of the explicit 25-vertex source. It gives no superlinear lower bound. -/
lemma minimal_compression_obstruction :
    ∃ R : SimpleGraph Vertex, Minimal R ∧ R.Adj (.inl 0) (.inl 3) ∧
      value (transfer R (.inl 0) (.inl 3)) < number R := by
  have hs : 25 ≤ value source := source_number_ge_twenty_five.trans (number_le_value source)
  obtain ⟨R,hR,hm,hn⟩ := exists_minimal_maximizer source (by omega)
  have he : R.Adj (.inl 0) (.inl 3) := by
    by_contra he
    have hb := (le_value (no_closing_le_base hR he)).trans base_hull_le_twenty_four
    omega
  have ht : transfer R (.inl 0) (.inl 3) ≤ target := by
    rw [← transfer_eq]
    exact transfer_mono hR _ _
  have hb := (EdgeHull.monotone ht).trans target_hull_le_twenty_four
  exact ⟨R,hm,he,by omega⟩

lemma not_minimal_adjacent_compression :
    ¬ (∀ R : SimpleGraph Vertex, Minimal R → ∀ u v, R.Adj u v →
      number R ≤ value (transfer R u v)) := by
  intro h
  obtain ⟨R,hm,he,hlt⟩ := minimal_compression_obstruction
  exact (not_le_of_gt hlt) (h R hm _ _ he)

end Erdos184Work.ChainRing
#print axioms Erdos184Work.ChainRing.minimal_compression_obstruction
#print axioms Erdos184Work.ChainRing.not_minimal_adjacent_compression
