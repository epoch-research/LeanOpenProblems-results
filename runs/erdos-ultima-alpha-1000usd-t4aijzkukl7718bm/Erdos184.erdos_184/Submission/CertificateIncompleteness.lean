import Submission.CertificateNormalization
import Submission.ChainRingCompressionObstruction

/-! Single enhanced parity/degree certificates do not characterize the exact
cycle-and-edge decomposition number of globally Minimal simple graphs.
This is NOT a disproof of Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CertificateIncompleteness
open Critical EdgeHull Compression ParityDegreeLower
set_option maxHeartbeats 1000000

lemma obstruction_with_order_bound :
    ∃ R : SimpleGraph ChainRing.Vertex, Minimal R ∧
      Fintype.card ChainRing.Vertex ≤ number R ∧
      R.Adj (.inl 0) (.inl 3) ∧
      value (transfer R (.inl 0) (.inl 3)) < number R := by
  have hs : 25 ≤ value ChainRing.source :=
    ChainRing.source_number_ge_twenty_five.trans (number_le_value _)
  obtain ⟨R,hR,hm,hn⟩ := exists_minimal_maximizer ChainRing.source (by omega)
  have he : R.Adj (.inl 0) (.inl 3) := by
    by_contra he
    have hb := (le_value (ChainRing.no_closing_le_base hR he)).trans
      ChainRing.base_hull_le_twenty_four
    omega
  have ht : transfer R (.inl 0) (.inl 3) ≤ ChainRing.target := by
    rw [← ChainRing.transfer_eq]
    exact transfer_mono hR _ _
  have hb := (EdgeHull.monotone ht).trans ChainRing.target_hull_le_twenty_four
  refine ⟨R, hm, ?_, he, by omega⟩
  rw [ChainRing.card_vertex]
  omega

/-- There is a 25-vertex globally Minimal graph whose exact decomposition
number has no single enhanced independent-odd degree certificate, even when
its hub and independent sets are allowed to overlap. -/
lemma exists_minimal_without_certificate :
    ∃ R : SimpleGraph ChainRing.Vertex, Minimal R ∧
      Fintype.card ChainRing.Vertex ≤ number R ∧
      ∀ A B O : Finset ChainRing.Vertex, ¬ Certificate R (number R) A B O := by
  obtain ⟨R,hm,hn,he,ht⟩ := obstruction_with_order_bound
  refine ⟨R,hm,hn,?_⟩
  intro A B O hc
  obtain ⟨A',O',hc',hAB⟩ := hc.exists_disjoint hn
  have hge := transfer_hull_ge_of_certificate R he A' B O' hc'.positive hAB
    hc'.disjoint hc'.independent hc'.oddB hc'.oddO (number R) hc'.bound
  exact (not_le_of_gt ht) hge

lemma not_complete_on_minimal :
    ¬ (∀ R : SimpleGraph ChainRing.Vertex, Minimal R →
      ∃ A B O : Finset ChainRing.Vertex, Certificate R (number R) A B O) := by
  intro h
  obtain ⟨R,hm,_,hn⟩ := exists_minimal_without_certificate
  obtain ⟨A,B,O,hc⟩ := h R hm
  exact hn A B O hc

end Erdos184Work.CertificateIncompleteness
#print axioms Erdos184Work.CertificateIncompleteness.exists_minimal_without_certificate
#print axioms Erdos184Work.CertificateIncompleteness.not_complete_on_minimal
