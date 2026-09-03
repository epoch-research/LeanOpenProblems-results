import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5980 : ∀ i : Fin 200, Compatible (1196000 + i.val) →
    (table.lookup (1196000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5980 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1196000 1196200 :=
  FiniteIntervals.of_fin 1196000 200 complete_chunk5980

lemma complete_chunk5981 : ∀ i : Fin 200, Compatible (1196200 + i.val) →
    (table.lookup (1196200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5981 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1196200 1196400 :=
  FiniteIntervals.of_fin 1196200 200 complete_chunk5981

lemma complete_chunk5982 : ∀ i : Fin 200, Compatible (1196400 + i.val) →
    (table.lookup (1196400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5982 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1196400 1196600 :=
  FiniteIntervals.of_fin 1196400 200 complete_chunk5982

lemma complete_chunk5983 : ∀ i : Fin 200, Compatible (1196600 + i.val) →
    (table.lookup (1196600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5983 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1196600 1196800 :=
  FiniteIntervals.of_fin 1196600 200 complete_chunk5983

lemma complete_chunk5984 : ∀ i : Fin 200, Compatible (1196800 + i.val) →
    (table.lookup (1196800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5984 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1196800 1197000 :=
  FiniteIntervals.of_fin 1196800 200 complete_chunk5984

lemma complete_chunk5985 : ∀ i : Fin 200, Compatible (1197000 + i.val) →
    (table.lookup (1197000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5985 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1197000 1197200 :=
  FiniteIntervals.of_fin 1197000 200 complete_chunk5985

lemma complete_chunk5986 : ∀ i : Fin 200, Compatible (1197200 + i.val) →
    (table.lookup (1197200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5986 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1197200 1197400 :=
  FiniteIntervals.of_fin 1197200 200 complete_chunk5986

lemma complete_chunk5987 : ∀ i : Fin 200, Compatible (1197400 + i.val) →
    (table.lookup (1197400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5987 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1197400 1197600 :=
  FiniteIntervals.of_fin 1197400 200 complete_chunk5987

lemma complete_chunk5988 : ∀ i : Fin 200, Compatible (1197600 + i.val) →
    (table.lookup (1197600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5988 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1197600 1197800 :=
  FiniteIntervals.of_fin 1197600 200 complete_chunk5988

lemma complete_chunk5989 : ∀ i : Fin 200, Compatible (1197800 + i.val) →
    (table.lookup (1197800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5989 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1197800 1198000 :=
  FiniteIntervals.of_fin 1197800 200 complete_chunk5989

#print axioms interval_chunk5980
end Erdos184Work.PureFiveFilter4
