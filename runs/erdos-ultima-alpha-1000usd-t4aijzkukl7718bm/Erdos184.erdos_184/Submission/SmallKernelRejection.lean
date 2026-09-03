import Submission.SeriesCertificateData
import Submission.LabelCycleCertificates
import Submission.KernelMarker

/-! Finite certificates excluding a kernel of minimum three subject to color-
subfamily maximum bounds and three-color upper bounds. These are certificate
soundness lemmas, not a completeness assertion about four-color layouts. -/
namespace Erdos184Work.LabelKernel
open Erdos184Serial
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {E W K : Type*} [DecidableEq E] [DecidableEq W] [DecidableEq K]
    [Fintype E] [Fintype W] [Fintype K]

def selected (color : E → K) (A : Finset K) : Finset E :=
  Finset.univ.filter (fun e => color e ∈ A)

structure RigidThreeData (E W : Type*) where
  size : ℕ
  edge : Fin size → E
  series : SeriesData (Fin 8) (Fin size) (Fin 4) W

namespace RigidThreeData

def Valid (d : RigidThreeData E W) (src dst : E → W) (t : Finset E) : Prop :=
  Function.Injective d.edge ∧ Finset.univ.image d.edge = t ∧
    d.series.Valid NonAlternate220.src NonAlternate220.dst (src ∘ d.edge) (dst ∘ d.edge)

instance validDecidable (d : RigidThreeData E W) (src dst : E → W) (t : Finset E) :
    Decidable (d.Valid src dst t) := by
  unfold Valid Function.Injective
  infer_instance

def embedding {d : RigidThreeData E W} {src dst : E → W} {t : Finset E}
    (h : d.Valid src dst t) : Embedding (src ∘ d.edge) (dst ∘ d.edge) src dst where
  edge := ⟨d.edge,h.1⟩
  vertex := Function.Embedding.refl W
  endpoints _ := rfl

lemma hasNumber {d : RigidThreeData E W} {src dst : E → W} {t : Finset E}
    (h : d.Valid src dst t) : HasNumber (code src dst) t 3 := by
  let C := d.series.certificate NonAlternate220.src NonAlternate220.dst
    (src ∘ d.edge) (dst ∘ d.edge) h.2.2
  have hc : HasNumber (code (src ∘ d.edge) (dst ∘ d.edge)) Finset.univ 3 := by
    have hh := C.transport.hasNumber_iff Finset.univ 3
    rw [C.expand_univ] at hh
    exact hh.mpr NonAlternate220.full_number
  have he := (embedding h).hasNumber_map_iff Finset.univ 3
  have hm : Finset.univ.map (embedding h).edge = t := by
    rw [Finset.map_eq_image]
    exact h.2.1
  rw [hm] at he
  exact he.mpr hc

#print axioms hasNumber
end RigidThreeData

inductive RejectionData (E W K : Type*) where
  | low : PartitionData E W → RejectionData E W K
  | high : Finset K → PartitionData E W → RejectionData E W K
  | rigid : Finset K → RigidThreeData E W → RejectionData E W K

namespace RejectionData

def Valid (d : RejectionData E W K) (src dst : E → W) (color : E → K) : Prop :=
  match d with
  | .low p => p.Valid src dst Finset.univ ∧ p.size < 3
  | .high A p => p.Valid src dst (selected color A) ∧ A.card < p.size
  | .rigid A p => p.Valid src dst (selected color A) ∧ A.card = 3

instance validDecidable (d : RejectionData E W K) (src dst : E → W) (color : E → K) :
    Decidable (d.Valid src dst color) := by
  cases d <;> unfold Valid <;> infer_instance

lemma sound {d : RejectionData E W K} {src dst : E → W} {color : E → K}
    (hd : d.Valid src dst color)
    (hmin : HasNumber (code src dst) Finset.univ 3)
    (hmax : ∀ A : Finset K, ∀ P, Partition (code src dst) (selected color A) P → P.card ≤ A.card)
    (hthree : ∀ A : Finset K, A.card = 3 → ∃ P,
      Partition (code src dst) (selected color A) P ∧ P.card ≤ 2) : False := by
  cases d with
  | low p =>
    obtain ⟨P,hP,hcard⟩ := PartitionData.exists_partition hd.1
    have hb := hmin.2 P hP
    have hs := hd.2
    omega
  | high A p =>
    obtain ⟨P,hP,hcard⟩ := PartitionData.exists_partition hd.1
    have hb := hmax A P hP
    have hs := hd.2
    omega
  | rigid A p =>
    have hn := RigidThreeData.hasNumber hd.1
    obtain ⟨P,hP,hcard⟩ := hthree A hd.2
    have hb := hn.2 P hP
    omega

#print axioms sound
end RejectionData
end Erdos184Work.LabelKernel
