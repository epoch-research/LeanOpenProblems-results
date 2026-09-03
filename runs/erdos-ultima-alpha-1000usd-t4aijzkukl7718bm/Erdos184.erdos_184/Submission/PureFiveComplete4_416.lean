import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4160 : ∀ i : Fin 200, Compatible (832000 + i.val) →
    (table.lookup (832000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4160 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 832000 832200 :=
  FiniteIntervals.of_fin 832000 200 complete_chunk4160

lemma complete_chunk4161 : ∀ i : Fin 200, Compatible (832200 + i.val) →
    (table.lookup (832200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4161 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 832200 832400 :=
  FiniteIntervals.of_fin 832200 200 complete_chunk4161

lemma complete_chunk4162 : ∀ i : Fin 200, Compatible (832400 + i.val) →
    (table.lookup (832400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4162 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 832400 832600 :=
  FiniteIntervals.of_fin 832400 200 complete_chunk4162

lemma complete_chunk4163 : ∀ i : Fin 200, Compatible (832600 + i.val) →
    (table.lookup (832600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4163 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 832600 832800 :=
  FiniteIntervals.of_fin 832600 200 complete_chunk4163

lemma complete_chunk4164 : ∀ i : Fin 200, Compatible (832800 + i.val) →
    (table.lookup (832800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4164 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 832800 833000 :=
  FiniteIntervals.of_fin 832800 200 complete_chunk4164

lemma complete_chunk4165 : ∀ i : Fin 200, Compatible (833000 + i.val) →
    (table.lookup (833000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4165 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 833000 833200 :=
  FiniteIntervals.of_fin 833000 200 complete_chunk4165

lemma complete_chunk4166 : ∀ i : Fin 200, Compatible (833200 + i.val) →
    (table.lookup (833200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4166 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 833200 833400 :=
  FiniteIntervals.of_fin 833200 200 complete_chunk4166

lemma complete_chunk4167 : ∀ i : Fin 200, Compatible (833400 + i.val) →
    (table.lookup (833400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4167 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 833400 833600 :=
  FiniteIntervals.of_fin 833400 200 complete_chunk4167

lemma complete_chunk4168 : ∀ i : Fin 200, Compatible (833600 + i.val) →
    (table.lookup (833600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4168 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 833600 833800 :=
  FiniteIntervals.of_fin 833600 200 complete_chunk4168

lemma complete_chunk4169 : ∀ i : Fin 200, Compatible (833800 + i.val) →
    (table.lookup (833800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4169 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 833800 834000 :=
  FiniteIntervals.of_fin 833800 200 complete_chunk4169

#print axioms interval_chunk4160
end Erdos184Work.PureFiveFilter4
