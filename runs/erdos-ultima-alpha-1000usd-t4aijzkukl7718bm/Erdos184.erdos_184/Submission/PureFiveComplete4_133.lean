import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1330 : ∀ i : Fin 200, Compatible (266000 + i.val) →
    (table.lookup (266000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1330 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 266000 266200 :=
  FiniteIntervals.of_fin 266000 200 complete_chunk1330

lemma complete_chunk1331 : ∀ i : Fin 200, Compatible (266200 + i.val) →
    (table.lookup (266200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1331 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 266200 266400 :=
  FiniteIntervals.of_fin 266200 200 complete_chunk1331

lemma complete_chunk1332 : ∀ i : Fin 200, Compatible (266400 + i.val) →
    (table.lookup (266400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1332 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 266400 266600 :=
  FiniteIntervals.of_fin 266400 200 complete_chunk1332

lemma complete_chunk1333 : ∀ i : Fin 200, Compatible (266600 + i.val) →
    (table.lookup (266600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1333 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 266600 266800 :=
  FiniteIntervals.of_fin 266600 200 complete_chunk1333

lemma complete_chunk1334 : ∀ i : Fin 200, Compatible (266800 + i.val) →
    (table.lookup (266800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1334 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 266800 267000 :=
  FiniteIntervals.of_fin 266800 200 complete_chunk1334

lemma complete_chunk1335 : ∀ i : Fin 200, Compatible (267000 + i.val) →
    (table.lookup (267000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1335 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 267000 267200 :=
  FiniteIntervals.of_fin 267000 200 complete_chunk1335

lemma complete_chunk1336 : ∀ i : Fin 200, Compatible (267200 + i.val) →
    (table.lookup (267200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1336 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 267200 267400 :=
  FiniteIntervals.of_fin 267200 200 complete_chunk1336

lemma complete_chunk1337 : ∀ i : Fin 200, Compatible (267400 + i.val) →
    (table.lookup (267400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1337 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 267400 267600 :=
  FiniteIntervals.of_fin 267400 200 complete_chunk1337

lemma complete_chunk1338 : ∀ i : Fin 200, Compatible (267600 + i.val) →
    (table.lookup (267600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1338 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 267600 267800 :=
  FiniteIntervals.of_fin 267600 200 complete_chunk1338

lemma complete_chunk1339 : ∀ i : Fin 200, Compatible (267800 + i.val) →
    (table.lookup (267800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1339 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 267800 268000 :=
  FiniteIntervals.of_fin 267800 200 complete_chunk1339

#print axioms interval_chunk1330
end Erdos184Work.PureFiveFilter4
