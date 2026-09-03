import Submission.CyclicSeriesData

/-! Simultaneous suppression of private markers in an arbitrary indexed family
of cyclic words. Exact partition spectra, including every color subfamily,
are preserved. The unconditional corollaries here cover word lengths at most six. -/
open scoped Classical
namespace Erdos184Work.LabelKernel.WordCoarsening
open Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {I X : Type*} [Fintype I] [DecidableEq I] [DecidableEq X]
  {n : I → ℕ} (word : ∀ i, Fin (n i+2) ↪ X)
  (keep : ∀ i, Finset (Fin (n i+2))) (hkeep : ∀ i, 2 ≤ (keep i).card)

noncomputable local instance {m : I → ℕ} : DecidableEq (Σ i, Fin (m i)) := Classical.decEq _

def arity (i : I) : ℕ := CyclicSeries.arity (keep i)
def coarseWord (i : I) (j : Fin (arity keep i+2)) : X :=
  word i (CyclicSeries.vertex (keep i) (hkeep i) j)
def coarseSource (e : Σ i, Fin (arity keep i+2)) : X := coarseWord word keep hkeep e.1 e.2
def coarseTarget (e : Σ i, Fin (arity keep i+2)) : X := coarseWord word keep hkeep e.1 (e.2+1)
def fineSource (f : Σ i, Fin (n i+2)) : X := word f.1 f.2
def fineTarget (f : Σ i, Fin (n i+2)) : X := word f.1 (f.2+1)

variable (hvalid : ∀ i, CyclicSeries.Valid (keep i) (hkeep i))
  (hprivate : ∀ i f, f ∉ keep i → ∀ j, j ≠ i → ∀ g, word j g ≠ word i f)

noncomputable def certificate : SeriesCertificate
    (coarseSource word keep hkeep) (coarseTarget word keep hkeep)
    (fineSource word) (fineTarget word) := by
  apply SeriesAssembly.certificate (fun i => CyclicSeries.data (keep i) (hkeep i))
    (fun _ => id) (fun _ j => j+1) (fun _ => id) (fun _ j => j+1) word hvalid
  intro i f hf j hji g
  have hn : f ∉ keep i := fun h => hf (CyclicSeries.representative_of_mem
    (keep i) (hkeep i) (hvalid i) f h)
  exact ⟨hprivate i f hn j hji g,hprivate i f hn j hji (g+1)⟩

include hvalid hprivate in
lemma partition_spectrum_iff (P : ℕ → Prop) :
    (∃ D, Partition (code (fineSource word) (fineTarget word)) Finset.univ D ∧ P D.card) ↔
    (∃ D, Partition (code (coarseSource word keep hkeep) (coarseTarget word keep hkeep))
      Finset.univ D ∧ P D.card) :=
  (certificate word keep hkeep hvalid hprivate).partition_spectrum_iff P

include hvalid hprivate in
lemma color_spectrum_iff (A : Finset I) (P : ℕ → Prop) :
    (∃ D, Partition (code (fineSource word) (fineTarget word))
      (Finset.univ.filter (fun f : Σ i, Fin (n i+2) => f.1 ∈ A)) D ∧ P D.card) ↔
    (∃ D, Partition (code (coarseSource word keep hkeep) (coarseTarget word keep hkeep))
      (Finset.univ.filter (fun e : Σ i, Fin (arity keep i+2) => e.1 ∈ A)) D ∧ P D.card) :=
  (certificate word keep hkeep hvalid hprivate).partition_spectrum_colors_iff
    Sigma.fst Sigma.fst (fun _ => rfl) A P

include hvalid hprivate in
lemma number_iff (k : ℕ) :
    HasNumber (code (fineSource word) (fineTarget word)) Finset.univ k ↔
    HasNumber (code (coarseSource word keep hkeep) (coarseTarget word keep hkeep)) Finset.univ k := by
  let C := certificate word keep hkeep hvalid hprivate
  have h := C.transport.hasNumber_iff Finset.univ k
  rwa [C.expand_univ] at h

include hvalid hprivate in
lemma minimalCore_iff (k : ℕ) :
    MinimalCore (code (fineSource word) (fineTarget word)) Finset.univ k ↔
    MinimalCore (code (coarseSource word keep hkeep) (coarseTarget word keep hkeep)) Finset.univ k :=
  (certificate word keep hkeep hvalid hprivate).minimalCore_iff k

include hvalid hprivate in
lemma rigid_iff (k : ℕ) :
    Rigid (code (fineSource word) (fineTarget word)) Finset.univ k ↔
    Rigid (code (coarseSource word keep hkeep) (coarseTarget word keep hkeep)) Finset.univ k := by
  let C := certificate word keep hkeep hvalid hprivate
  have h := C.transport.rigid_iff Finset.univ k
  rwa [C.expand_univ] at h

omit hvalid in
noncomputable def certificate_of_le_six (hsmall : ∀ i, n i ≤ 4) : SeriesCertificate
    (coarseSource word keep hkeep) (coarseTarget word keep hkeep)
    (fineSource word) (fineTarget word) :=
  certificate word keep hkeep (fun i => CyclicSeries.valid (hsmall i) (keep i) (hkeep i)) hprivate

omit hvalid in
include hprivate in
lemma spectrum_of_le_six (hsmall : ∀ i, n i ≤ 4) (P : ℕ → Prop) :
    (∃ D, Partition (code (fineSource word) (fineTarget word)) Finset.univ D ∧ P D.card) ↔
    (∃ D, Partition (code (coarseSource word keep hkeep) (coarseTarget word keep hkeep))
      Finset.univ D ∧ P D.card) :=
  (certificate_of_le_six word keep hkeep hprivate hsmall).partition_spectrum_iff P

#print axioms certificate
#print axioms spectrum_of_le_six
#print axioms color_spectrum_iff
end Erdos184Work.LabelKernel.WordCoarsening
