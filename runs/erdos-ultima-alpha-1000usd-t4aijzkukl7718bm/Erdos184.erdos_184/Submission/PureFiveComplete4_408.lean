import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4080 : ∀ i : Fin 200, Compatible (816000 + i.val) →
    (table.lookup (816000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4080 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 816000 816200 :=
  FiniteIntervals.of_fin 816000 200 complete_chunk4080

lemma complete_chunk4081 : ∀ i : Fin 200, Compatible (816200 + i.val) →
    (table.lookup (816200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4081 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 816200 816400 :=
  FiniteIntervals.of_fin 816200 200 complete_chunk4081

lemma complete_chunk4082 : ∀ i : Fin 200, Compatible (816400 + i.val) →
    (table.lookup (816400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4082 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 816400 816600 :=
  FiniteIntervals.of_fin 816400 200 complete_chunk4082

lemma complete_chunk4083 : ∀ i : Fin 200, Compatible (816600 + i.val) →
    (table.lookup (816600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4083 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 816600 816800 :=
  FiniteIntervals.of_fin 816600 200 complete_chunk4083

lemma complete_chunk4084 : ∀ i : Fin 200, Compatible (816800 + i.val) →
    (table.lookup (816800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4084 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 816800 817000 :=
  FiniteIntervals.of_fin 816800 200 complete_chunk4084

lemma complete_chunk4085 : ∀ i : Fin 200, Compatible (817000 + i.val) →
    (table.lookup (817000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4085 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 817000 817200 :=
  FiniteIntervals.of_fin 817000 200 complete_chunk4085

lemma complete_chunk4086 : ∀ i : Fin 200, Compatible (817200 + i.val) →
    (table.lookup (817200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4086 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 817200 817400 :=
  FiniteIntervals.of_fin 817200 200 complete_chunk4086

lemma complete_chunk4087 : ∀ i : Fin 200, Compatible (817400 + i.val) →
    (table.lookup (817400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4087 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 817400 817600 :=
  FiniteIntervals.of_fin 817400 200 complete_chunk4087

lemma complete_chunk4088 : ∀ i : Fin 200, Compatible (817600 + i.val) →
    (table.lookup (817600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4088 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 817600 817800 :=
  FiniteIntervals.of_fin 817600 200 complete_chunk4088

lemma complete_chunk4089 : ∀ i : Fin 200, Compatible (817800 + i.val) →
    (table.lookup (817800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4089 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 817800 818000 :=
  FiniteIntervals.of_fin 817800 200 complete_chunk4089

#print axioms interval_chunk4080
end Erdos184Work.PureFiveFilter4
