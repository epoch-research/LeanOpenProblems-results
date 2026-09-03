import Submission.SeriesCertificateData

/-! A small ordinary-kernel check of the batch certificate format: each of two
parallel edges is replaced by a three-edge path, giving a six-cycle. -/
namespace Erdos184Work.LabelKernel.SeriesExample
open Erdos184Serial
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def src : Fin 2 → Fin 2 := id
def dst (e : Fin 2) : Fin 2 := e+1
def fineSrc : Fin 6 → Fin 6 := id
def fineDst (f : Fin 6) : Fin 6 := f+1

def data : SeriesData (Fin 2) (Fin 6) (Fin 2) (Fin 6) where
  fiber f := ⟨f.val / 3,by omega⟩
  representative e := ⟨3*e.val,by omega⟩
  vertex e := ⟨3*e.val,by omega⟩
  rank f := f.val % 3
  parent f := if f.val % 3 = 0 then f else f-1
  link f := f

lemma data_valid : data.Valid src dst fineSrc fineDst := by decide +kernel

lemma spectrum (P : ℕ → Prop) :
    (∃ D, Partition (code fineSrc fineDst) Finset.univ D ∧ P D.card) ↔
      (∃ D, Partition (code src dst) Finset.univ D ∧ P D.card) :=
  SeriesData.partition_spectrum_iff data_valid P

#print axioms data_valid
#print axioms spectrum
end Erdos184Work.LabelKernel.SeriesExample
