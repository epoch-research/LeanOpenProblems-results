import Submission.CountThreeAttachments

/-! Kernel-checked local facts about the twelve attachment base graphs. -/
open SimpleGraph
namespace Erdos184.AttachmentModelFacts
open CountThreeAttachmentData
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

def cycleVertex (c : Fin 4) : Fin 11 := Fin.ofNat 11 c.val

def outsideVertex (m : Model) (j : ℕ) : Fin 11 := Fin.ofNat 11 (m.girth+j)

def baseNeighbors (m : Model) (v : Fin 11) : Finset (Fin 11) :=
  Finset.univ.filter (fun w => s(v,w) ∈ m.base)

lemma model_bounds : ∀ i : Fin 12,
    3 ≤ (model i).girth ∧ (model i).girth ≤ 4 ∧
    2 ≤ (model i).outsideOrder ∧ (model i).outsideOrder ≤ 7 ∧
    (model i).girth + (model i).outsideOrder ≤ 11 := by
  decide +kernel

lemma options_length : ∀ i : Fin 12, (model i).options.length = (model i).outsideOrder := by
  decide +kernel

lemma base_loopless : ∀ i : Fin 12, ∀ v : Fin 11, s(v,v) ∉ (model i).base := by
  decide +kernel

lemma base_same_side : ∀ i : Fin 12, ∀ v w : Fin 11,
    s(v,w) ∈ (model i).base → (v.val < (model i).girth ↔ w.val < (model i).girth) := by
  decide +kernel

lemma base_cycle_degree : ∀ i : Fin 12, ∀ c : Fin 4,
    c.val < (model i).girth → (baseNeighbors (model i) (cycleVertex c)).card = 2 := by
  decide +kernel

lemma outside_pair_data : ∀ i : Fin 12, ∀ e ∈ (model i).outsidePairs,
    e.1 < (model i).outsideOrder ∧ e.2 < (model i).outsideOrder ∧
    s(outsideVertex (model i) e.1,outsideVertex (model i) e.2) ∈ (model i).base := by
  decide +kernel

lemma options_complete : ∀ i : Fin 12, ∀ j : Fin 7, ∀ s : Finset (Fin 4),
    j.val < (model i).outsideOrder →
    (∀ c ∈ s, c.val < (model i).girth) →
    (baseNeighbors (model i) (outsideVertex (model i) j.val)).card + s.card = 4 →
    ((model i).girth = 4 → ∀ c ∈ s, ∀ d ∈ s,
      s(cycleVertex c,cycleVertex d) ∉ (model i).base) →
    s ∈ (model i).options.getD j.val [] := by
  decide +kernel

end Erdos184.AttachmentModelFacts
