import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk960 : ∀ i : Fin 200, Compatible (192000 + i.val) →
    (table.lookup (192000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk960 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 192000 192200 :=
  FiniteIntervals.of_fin 192000 200 complete_chunk960

lemma complete_chunk961 : ∀ i : Fin 200, Compatible (192200 + i.val) →
    (table.lookup (192200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk961 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 192200 192400 :=
  FiniteIntervals.of_fin 192200 200 complete_chunk961

lemma complete_chunk962 : ∀ i : Fin 200, Compatible (192400 + i.val) →
    (table.lookup (192400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk962 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 192400 192600 :=
  FiniteIntervals.of_fin 192400 200 complete_chunk962

lemma complete_chunk963 : ∀ i : Fin 200, Compatible (192600 + i.val) →
    (table.lookup (192600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk963 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 192600 192800 :=
  FiniteIntervals.of_fin 192600 200 complete_chunk963

lemma complete_chunk964 : ∀ i : Fin 200, Compatible (192800 + i.val) →
    (table.lookup (192800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk964 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 192800 193000 :=
  FiniteIntervals.of_fin 192800 200 complete_chunk964

lemma complete_chunk965 : ∀ i : Fin 200, Compatible (193000 + i.val) →
    (table.lookup (193000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk965 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 193000 193200 :=
  FiniteIntervals.of_fin 193000 200 complete_chunk965

lemma complete_chunk966 : ∀ i : Fin 200, Compatible (193200 + i.val) →
    (table.lookup (193200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk966 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 193200 193400 :=
  FiniteIntervals.of_fin 193200 200 complete_chunk966

lemma complete_chunk967 : ∀ i : Fin 200, Compatible (193400 + i.val) →
    (table.lookup (193400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk967 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 193400 193600 :=
  FiniteIntervals.of_fin 193400 200 complete_chunk967

lemma complete_chunk968 : ∀ i : Fin 200, Compatible (193600 + i.val) →
    (table.lookup (193600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk968 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 193600 193800 :=
  FiniteIntervals.of_fin 193600 200 complete_chunk968

lemma complete_chunk969 : ∀ i : Fin 200, Compatible (193800 + i.val) →
    (table.lookup (193800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk969 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 193800 194000 :=
  FiniteIntervals.of_fin 193800 200 complete_chunk969

#print axioms interval_chunk960
end Erdos184Work.PureFiveFilter4
