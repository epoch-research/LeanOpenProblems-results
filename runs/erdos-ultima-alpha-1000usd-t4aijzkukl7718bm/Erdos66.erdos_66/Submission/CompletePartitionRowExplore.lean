import Submission.CompletePartitionColorTransferExplore
import Submission.SymmetricRowPeakExplore

/-! A limitation of literal whole-row encodings of the complete parallel
partition: coarse color choices do not break horizontal reflection. -/
namespace Erdos66CompletePartitionRow
open Erdos66CompletePartitionColorTransfer Erdos66SymmetricRowPeak
open AdditiveCombinatorics
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {α H : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [AddCommGroup H] [DecidableEq H]

noncomputable def row {n : ℕ} (ρ : Fin n ≃ F) (B : α → Finset H)
    (ω : Fin n → α) (y : F) (q : H) : Finset F :=
  Finset.univ.filter (fun x ↦ ((x,y),q)∈coloredSet ρ B ω)

lemma row_neg {n : ℕ} (ρ : Fin n ≃ F) (B : α → Finset H)
    (ω : Fin n → α) (y : F) (q : H) : ∀ x∈row ρ B ω y q, -x∈row ρ B ω y q := by
  intro x hx
  simpa only [row,Finset.mem_filter,Finset.mem_univ,true_and,mem_coloredSet,
    Prod.fst,Prod.snd,neg_sq] using hx

variable {p : ℕ} [Fact p.Prime]

/-- This applies to every assignment of the coarse colors. Whole rows can
still force peaks even though the fine palette is a complete partition. -/
theorem integer_row_peak {n : ℕ} (ρ : Fin n ≃ ZMod p) (B : α → Finset H)
    (ω : Fin n → α) (y : ZMod p) (q : H) (a : ℕ) (A : Set ℕ)
    (hA : integerRow p (row ρ B ω y q) a⊆A) :
    ∃ m : ℕ, 2*a ≤ m ∧ m<2*(a+p) ∧ (row ρ B ω y q).card≤2*sumRep A m := by
  apply symmetric_row_peak p (row ρ B ω y q) 0 a _ A hA
  intro x hx
  simpa only [zero_sub] using row_neg ρ B ω y q x hx

lemma integer_row_log_envelope {n : ℕ} (ρ : Fin n ≃ ZMod p) (B : α → Finset H)
    (ω : Fin n → α) (y : ZMod p) (q : H) (a : ℕ) (A : Set ℕ)
    (hA : integerRow p (row ρ B ω y q) a⊆A) (K C : ℝ) (hC : 0≤C)
    (henv : ∀ m : ℕ, (sumRep A m:ℝ)≤K+C*Real.log (m+2)) :
    ((row ρ B ω y q).card:ℝ)≤2*(K+C*Real.log (2*(a+p)+2)) := by
  apply symmetric_row_log_envelope p (row ρ B ω y q) 0 a _ A hA K C hC henv
  intro x hx
  simpa only [zero_sub] using row_neg ρ B ω y q x hx

end Erdos66CompletePartitionRow
