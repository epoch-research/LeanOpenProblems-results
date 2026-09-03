import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5960 : ∀ i : Fin 200, Compatible (1192000 + i.val) →
    (table.lookup (1192000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5960 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1192000 1192200 :=
  FiniteIntervals.of_fin 1192000 200 complete_chunk5960

lemma complete_chunk5961 : ∀ i : Fin 200, Compatible (1192200 + i.val) →
    (table.lookup (1192200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5961 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1192200 1192400 :=
  FiniteIntervals.of_fin 1192200 200 complete_chunk5961

lemma complete_chunk5962 : ∀ i : Fin 200, Compatible (1192400 + i.val) →
    (table.lookup (1192400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5962 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1192400 1192600 :=
  FiniteIntervals.of_fin 1192400 200 complete_chunk5962

lemma complete_chunk5963 : ∀ i : Fin 200, Compatible (1192600 + i.val) →
    (table.lookup (1192600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5963 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1192600 1192800 :=
  FiniteIntervals.of_fin 1192600 200 complete_chunk5963

lemma complete_chunk5964 : ∀ i : Fin 200, Compatible (1192800 + i.val) →
    (table.lookup (1192800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5964 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1192800 1193000 :=
  FiniteIntervals.of_fin 1192800 200 complete_chunk5964

lemma complete_chunk5965 : ∀ i : Fin 200, Compatible (1193000 + i.val) →
    (table.lookup (1193000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5965 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1193000 1193200 :=
  FiniteIntervals.of_fin 1193000 200 complete_chunk5965

lemma complete_chunk5966 : ∀ i : Fin 200, Compatible (1193200 + i.val) →
    (table.lookup (1193200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5966 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1193200 1193400 :=
  FiniteIntervals.of_fin 1193200 200 complete_chunk5966

lemma complete_chunk5967 : ∀ i : Fin 200, Compatible (1193400 + i.val) →
    (table.lookup (1193400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5967 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1193400 1193600 :=
  FiniteIntervals.of_fin 1193400 200 complete_chunk5967

lemma complete_chunk5968 : ∀ i : Fin 200, Compatible (1193600 + i.val) →
    (table.lookup (1193600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5968 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1193600 1193800 :=
  FiniteIntervals.of_fin 1193600 200 complete_chunk5968

lemma complete_chunk5969 : ∀ i : Fin 200, Compatible (1193800 + i.val) →
    (table.lookup (1193800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5969 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1193800 1194000 :=
  FiniteIntervals.of_fin 1193800 200 complete_chunk5969

#print axioms interval_chunk5960
end Erdos184Work.PureFiveFilter4
