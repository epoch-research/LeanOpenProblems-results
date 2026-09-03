import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk980 : ∀ i : Fin 200, Compatible (196000 + i.val) →
    (table.lookup (196000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk980 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 196000 196200 :=
  FiniteIntervals.of_fin 196000 200 complete_chunk980

lemma complete_chunk981 : ∀ i : Fin 200, Compatible (196200 + i.val) →
    (table.lookup (196200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk981 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 196200 196400 :=
  FiniteIntervals.of_fin 196200 200 complete_chunk981

lemma complete_chunk982 : ∀ i : Fin 200, Compatible (196400 + i.val) →
    (table.lookup (196400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk982 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 196400 196600 :=
  FiniteIntervals.of_fin 196400 200 complete_chunk982

lemma complete_chunk983 : ∀ i : Fin 200, Compatible (196600 + i.val) →
    (table.lookup (196600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk983 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 196600 196800 :=
  FiniteIntervals.of_fin 196600 200 complete_chunk983

lemma complete_chunk984 : ∀ i : Fin 200, Compatible (196800 + i.val) →
    (table.lookup (196800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk984 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 196800 197000 :=
  FiniteIntervals.of_fin 196800 200 complete_chunk984

lemma complete_chunk985 : ∀ i : Fin 200, Compatible (197000 + i.val) →
    (table.lookup (197000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk985 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 197000 197200 :=
  FiniteIntervals.of_fin 197000 200 complete_chunk985

lemma complete_chunk986 : ∀ i : Fin 200, Compatible (197200 + i.val) →
    (table.lookup (197200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk986 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 197200 197400 :=
  FiniteIntervals.of_fin 197200 200 complete_chunk986

lemma complete_chunk987 : ∀ i : Fin 200, Compatible (197400 + i.val) →
    (table.lookup (197400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk987 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 197400 197600 :=
  FiniteIntervals.of_fin 197400 200 complete_chunk987

lemma complete_chunk988 : ∀ i : Fin 200, Compatible (197600 + i.val) →
    (table.lookup (197600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk988 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 197600 197800 :=
  FiniteIntervals.of_fin 197600 200 complete_chunk988

lemma complete_chunk989 : ∀ i : Fin 200, Compatible (197800 + i.val) →
    (table.lookup (197800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk989 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 197800 198000 :=
  FiniteIntervals.of_fin 197800 200 complete_chunk989

#print axioms interval_chunk980
end Erdos184Work.PureFiveFilter4
