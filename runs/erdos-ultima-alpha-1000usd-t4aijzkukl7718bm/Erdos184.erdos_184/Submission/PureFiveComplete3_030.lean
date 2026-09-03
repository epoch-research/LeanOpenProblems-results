import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk300 : ∀ i : Fin 200, Compatible (60000 + i.val) →
    (table.lookup (60000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk300 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60000 60200 :=
  FiniteIntervals.of_fin 60000 200 complete_chunk300

lemma complete_chunk301 : ∀ i : Fin 200, Compatible (60200 + i.val) →
    (table.lookup (60200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk301 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60200 60400 :=
  FiniteIntervals.of_fin 60200 200 complete_chunk301

lemma complete_chunk302 : ∀ i : Fin 200, Compatible (60400 + i.val) →
    (table.lookup (60400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk302 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60400 60600 :=
  FiniteIntervals.of_fin 60400 200 complete_chunk302

lemma complete_chunk303 : ∀ i : Fin 200, Compatible (60600 + i.val) →
    (table.lookup (60600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk303 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60600 60800 :=
  FiniteIntervals.of_fin 60600 200 complete_chunk303

lemma complete_chunk304 : ∀ i : Fin 200, Compatible (60800 + i.val) →
    (table.lookup (60800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk304 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 60800 61000 :=
  FiniteIntervals.of_fin 60800 200 complete_chunk304

lemma complete_chunk305 : ∀ i : Fin 200, Compatible (61000 + i.val) →
    (table.lookup (61000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk305 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61000 61200 :=
  FiniteIntervals.of_fin 61000 200 complete_chunk305

lemma complete_chunk306 : ∀ i : Fin 200, Compatible (61200 + i.val) →
    (table.lookup (61200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk306 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61200 61400 :=
  FiniteIntervals.of_fin 61200 200 complete_chunk306

lemma complete_chunk307 : ∀ i : Fin 200, Compatible (61400 + i.val) →
    (table.lookup (61400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk307 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61400 61600 :=
  FiniteIntervals.of_fin 61400 200 complete_chunk307

lemma complete_chunk308 : ∀ i : Fin 200, Compatible (61600 + i.val) →
    (table.lookup (61600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk308 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61600 61800 :=
  FiniteIntervals.of_fin 61600 200 complete_chunk308

lemma complete_chunk309 : ∀ i : Fin 200, Compatible (61800 + i.val) →
    (table.lookup (61800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk309 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 61800 62000 :=
  FiniteIntervals.of_fin 61800 200 complete_chunk309

#print axioms interval_chunk300
end Erdos184Work.PureFiveFilter3
