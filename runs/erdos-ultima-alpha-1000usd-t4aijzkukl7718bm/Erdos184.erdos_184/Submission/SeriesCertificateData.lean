import Submission.ParitySeriesCertificate

/-! Computable finite data for batch series-expansion certificates. -/
namespace Erdos184Work.LabelKernel
open Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {E F W X : Type*} [DecidableEq E] [DecidableEq F]
    [DecidableEq W] [DecidableEq X] [Fintype E] [Fintype F] [Fintype W] [Fintype X]

structure SeriesData (E F W X : Type*) where
  fiber : F → E
  representative : E → F
  vertex : W → X
  rank : F → ℕ
  parent : F → F
  link : F → X

namespace SeriesData

def Valid (d : SeriesData E F W X) (src dst : E → W) (fineSrc fineDst : F → X) : Prop :=
  (∀ e, d.fiber (d.representative e) = e) ∧ Function.Injective d.vertex ∧
  (∀ f, f = d.representative (d.fiber f) ∨
    d.rank (d.parent f) < d.rank f ∧ d.fiber (d.parent f) = d.fiber f ∧
      Finset.univ.filter (fun g => fineSrc g = d.link f ∨ fineDst g = d.link f) = {f,d.parent f}) ∧
  (∀ e x, parity fineSrc fineDst (Finset.univ.filter (fun f => d.fiber f = e)) x =
    if d.vertex (src e) = x ∨ d.vertex (dst e) = x then 1 else 0)

instance validDecidable (d : SeriesData E F W X) (src dst : E → W) (fineSrc fineDst : F → X) :
    Decidable (d.Valid src dst fineSrc fineDst) := by
  unfold Valid Function.Injective
  infer_instance

def certificate (d : SeriesData E F W X) (src dst : E → W) (fineSrc fineDst : F → X)
    (h : d.Valid src dst fineSrc fineDst) : SeriesCertificate src dst fineSrc fineDst where
  fiber := d.fiber
  representative := d.representative
  fiber_representative := h.1
  vertex := ⟨d.vertex,h.2.1⟩
  rank := d.rank
  parent := d.parent
  descent f := by
    rcases h.2.2.1 f with hf | ⟨hr,hfiber,he⟩
    · exact Or.inl hf
    · exact Or.inr ⟨hr,hfiber,d.link f,he⟩
  boundary := h.2.2.2

lemma partition_spectrum_iff {d : SeriesData E F W X} {src dst : E → W} {fineSrc fineDst : F → X}
    (h : d.Valid src dst fineSrc fineDst) (P : ℕ → Prop) :
    (∃ D, Partition (code fineSrc fineDst) Finset.univ D ∧ P D.card) ↔
      (∃ D, Partition (code src dst) Finset.univ D ∧ P D.card) :=
  (d.certificate src dst fineSrc fineDst h).partition_spectrum_iff P

lemma minimalCore_iff {d : SeriesData E F W X} {src dst : E → W} {fineSrc fineDst : F → X}
    (h : d.Valid src dst fineSrc fineDst) (k : ℕ) :
    MinimalCore (code fineSrc fineDst) Finset.univ k ↔ MinimalCore (code src dst) Finset.univ k :=
  (d.certificate src dst fineSrc fineDst h).minimalCore_iff k

#print axioms partition_spectrum_iff
#print axioms minimalCore_iff
end SeriesData
end Erdos184Work.LabelKernel
