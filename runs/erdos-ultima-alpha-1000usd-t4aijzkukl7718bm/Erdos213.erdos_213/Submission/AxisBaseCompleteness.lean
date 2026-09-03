import Submission.AxisBaseEnumeration
import Submission.AxisSigningEncoding

/-! Complete kernel-checked classification of normalized singular base
Pfaffians for one fixed, non-general-position seven-point metric.
This is an auxiliary result, not a settlement of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
open AxisRankObstruction
set_option maxHeartbeats 0
set_option maxRecDepth 200000

lemma zeroList_eq_ofFn : zeroList=List.ofFn baseMasks := by
  decide +kernel

lemma models_coded : ∀ b : Fin 42,
    signedBase (baseMasks b/64) (baseMasks b%64)=models b := by
  decide +kernel

/-- All normalized base matrices with zero Pfaffian appear in the explicit
42-case list. This does not assume completeness of the list as a hypothesis. -/
theorem base_classification (hi lo : ℕ) (hh : hi<32768) (hl : lo<64)
    (hz : SignedRankSix.pf8 (signedBase hi lo)=0) :
    ∃ b : Fin 42, signedBase hi lo=models b := by
  have hv : baseValue hi lo=0 := by
    have he := pfaffian_baseValue hi lo
    rw [hz] at he
    omega
  have hm : hi*64+lo∈zeroList := by
    have h := all_checked hi lo hh hl
    simpa [checked,hv] using h
  rw [zeroList_eq_ofFn,List.mem_ofFn] at hm
  obtain ⟨b,hb⟩ := hm
  refine ⟨b,?_⟩
  have hh' : baseMasks b/64=hi := by omega
  have hl' : baseMasks b%64=lo := by omega
  simpa only [hh',hl'] using models_coded b

/-- The classification covers arbitrary Boolean choices on all 21 edges,
not only an externally selected set of mask values. -/
theorem every_signing_classification (s : Fin 21 → Bool)
    (hz : SignedRankSix.pf8 (template s)=0) :
    ∃ b : Fin 42, template s=models b := by
  rw [template_coded] at hz ⊢
  exact base_classification _ _ (highBits s).isLt (lowBits s).isLt hz

#print axioms base_classification
#print axioms encode_get
#print axioms template_coded
#print axioms every_signing_classification
end Erdos213.AxisBaseCompleteness
