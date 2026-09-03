import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5510 : ∀ i : Fin 200, Compatible (1102000 + i.val) →
    (table.lookup (1102000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5510 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1102000 1102200 :=
  FiniteIntervals.of_fin 1102000 200 complete_chunk5510

lemma complete_chunk5511 : ∀ i : Fin 200, Compatible (1102200 + i.val) →
    (table.lookup (1102200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5511 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1102200 1102400 :=
  FiniteIntervals.of_fin 1102200 200 complete_chunk5511

lemma complete_chunk5512 : ∀ i : Fin 200, Compatible (1102400 + i.val) →
    (table.lookup (1102400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5512 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1102400 1102600 :=
  FiniteIntervals.of_fin 1102400 200 complete_chunk5512

lemma complete_chunk5513 : ∀ i : Fin 200, Compatible (1102600 + i.val) →
    (table.lookup (1102600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5513 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1102600 1102800 :=
  FiniteIntervals.of_fin 1102600 200 complete_chunk5513

lemma complete_chunk5514 : ∀ i : Fin 200, Compatible (1102800 + i.val) →
    (table.lookup (1102800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5514 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1102800 1103000 :=
  FiniteIntervals.of_fin 1102800 200 complete_chunk5514

lemma complete_chunk5515 : ∀ i : Fin 200, Compatible (1103000 + i.val) →
    (table.lookup (1103000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5515 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1103000 1103200 :=
  FiniteIntervals.of_fin 1103000 200 complete_chunk5515

lemma complete_chunk5516 : ∀ i : Fin 200, Compatible (1103200 + i.val) →
    (table.lookup (1103200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5516 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1103200 1103400 :=
  FiniteIntervals.of_fin 1103200 200 complete_chunk5516

lemma complete_chunk5517 : ∀ i : Fin 200, Compatible (1103400 + i.val) →
    (table.lookup (1103400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5517 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1103400 1103600 :=
  FiniteIntervals.of_fin 1103400 200 complete_chunk5517

lemma complete_chunk5518 : ∀ i : Fin 200, Compatible (1103600 + i.val) →
    (table.lookup (1103600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5518 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1103600 1103800 :=
  FiniteIntervals.of_fin 1103600 200 complete_chunk5518

lemma complete_chunk5519 : ∀ i : Fin 200, Compatible (1103800 + i.val) →
    (table.lookup (1103800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5519 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1103800 1104000 :=
  FiniteIntervals.of_fin 1103800 200 complete_chunk5519

#print axioms interval_chunk5510
end Erdos184Work.PureFiveFilter4
