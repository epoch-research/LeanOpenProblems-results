import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1300 : ∀ i : Fin 200, Compatible (260000 + i.val) →
    (table.lookup (260000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1300 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 260000 260200 :=
  FiniteIntervals.of_fin 260000 200 complete_chunk1300

lemma complete_chunk1301 : ∀ i : Fin 200, Compatible (260200 + i.val) →
    (table.lookup (260200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1301 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 260200 260400 :=
  FiniteIntervals.of_fin 260200 200 complete_chunk1301

lemma complete_chunk1302 : ∀ i : Fin 200, Compatible (260400 + i.val) →
    (table.lookup (260400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1302 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 260400 260600 :=
  FiniteIntervals.of_fin 260400 200 complete_chunk1302

lemma complete_chunk1303 : ∀ i : Fin 200, Compatible (260600 + i.val) →
    (table.lookup (260600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1303 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 260600 260800 :=
  FiniteIntervals.of_fin 260600 200 complete_chunk1303

lemma complete_chunk1304 : ∀ i : Fin 200, Compatible (260800 + i.val) →
    (table.lookup (260800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1304 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 260800 261000 :=
  FiniteIntervals.of_fin 260800 200 complete_chunk1304

lemma complete_chunk1305 : ∀ i : Fin 200, Compatible (261000 + i.val) →
    (table.lookup (261000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1305 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 261000 261200 :=
  FiniteIntervals.of_fin 261000 200 complete_chunk1305

lemma complete_chunk1306 : ∀ i : Fin 200, Compatible (261200 + i.val) →
    (table.lookup (261200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1306 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 261200 261400 :=
  FiniteIntervals.of_fin 261200 200 complete_chunk1306

lemma complete_chunk1307 : ∀ i : Fin 200, Compatible (261400 + i.val) →
    (table.lookup (261400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1307 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 261400 261600 :=
  FiniteIntervals.of_fin 261400 200 complete_chunk1307

lemma complete_chunk1308 : ∀ i : Fin 200, Compatible (261600 + i.val) →
    (table.lookup (261600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1308 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 261600 261800 :=
  FiniteIntervals.of_fin 261600 200 complete_chunk1308

lemma complete_chunk1309 : ∀ i : Fin 200, Compatible (261800 + i.val) →
    (table.lookup (261800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1309 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 261800 262000 :=
  FiniteIntervals.of_fin 261800 200 complete_chunk1309

#print axioms interval_chunk1300
end Erdos184Work.PureFiveFilter4
