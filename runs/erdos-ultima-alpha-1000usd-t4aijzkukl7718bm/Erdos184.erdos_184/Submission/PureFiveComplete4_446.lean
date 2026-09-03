import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4460 : ∀ i : Fin 200, Compatible (892000 + i.val) →
    (table.lookup (892000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4460 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 892000 892200 :=
  FiniteIntervals.of_fin 892000 200 complete_chunk4460

lemma complete_chunk4461 : ∀ i : Fin 200, Compatible (892200 + i.val) →
    (table.lookup (892200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4461 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 892200 892400 :=
  FiniteIntervals.of_fin 892200 200 complete_chunk4461

lemma complete_chunk4462 : ∀ i : Fin 200, Compatible (892400 + i.val) →
    (table.lookup (892400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4462 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 892400 892600 :=
  FiniteIntervals.of_fin 892400 200 complete_chunk4462

lemma complete_chunk4463 : ∀ i : Fin 200, Compatible (892600 + i.val) →
    (table.lookup (892600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4463 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 892600 892800 :=
  FiniteIntervals.of_fin 892600 200 complete_chunk4463

lemma complete_chunk4464 : ∀ i : Fin 200, Compatible (892800 + i.val) →
    (table.lookup (892800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4464 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 892800 893000 :=
  FiniteIntervals.of_fin 892800 200 complete_chunk4464

lemma complete_chunk4465 : ∀ i : Fin 200, Compatible (893000 + i.val) →
    (table.lookup (893000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4465 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 893000 893200 :=
  FiniteIntervals.of_fin 893000 200 complete_chunk4465

lemma complete_chunk4466 : ∀ i : Fin 200, Compatible (893200 + i.val) →
    (table.lookup (893200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4466 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 893200 893400 :=
  FiniteIntervals.of_fin 893200 200 complete_chunk4466

lemma complete_chunk4467 : ∀ i : Fin 200, Compatible (893400 + i.val) →
    (table.lookup (893400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4467 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 893400 893600 :=
  FiniteIntervals.of_fin 893400 200 complete_chunk4467

lemma complete_chunk4468 : ∀ i : Fin 200, Compatible (893600 + i.val) →
    (table.lookup (893600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4468 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 893600 893800 :=
  FiniteIntervals.of_fin 893600 200 complete_chunk4468

lemma complete_chunk4469 : ∀ i : Fin 200, Compatible (893800 + i.val) →
    (table.lookup (893800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4469 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 893800 894000 :=
  FiniteIntervals.of_fin 893800 200 complete_chunk4469

#print axioms interval_chunk4460
end Erdos184Work.PureFiveFilter4
