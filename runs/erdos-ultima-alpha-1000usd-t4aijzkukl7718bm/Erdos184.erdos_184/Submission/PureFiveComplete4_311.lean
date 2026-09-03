import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3110 : ∀ i : Fin 200, Compatible (622000 + i.val) →
    (table.lookup (622000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3110 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 622000 622200 :=
  FiniteIntervals.of_fin 622000 200 complete_chunk3110

lemma complete_chunk3111 : ∀ i : Fin 200, Compatible (622200 + i.val) →
    (table.lookup (622200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3111 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 622200 622400 :=
  FiniteIntervals.of_fin 622200 200 complete_chunk3111

lemma complete_chunk3112 : ∀ i : Fin 200, Compatible (622400 + i.val) →
    (table.lookup (622400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3112 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 622400 622600 :=
  FiniteIntervals.of_fin 622400 200 complete_chunk3112

lemma complete_chunk3113 : ∀ i : Fin 200, Compatible (622600 + i.val) →
    (table.lookup (622600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3113 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 622600 622800 :=
  FiniteIntervals.of_fin 622600 200 complete_chunk3113

lemma complete_chunk3114 : ∀ i : Fin 200, Compatible (622800 + i.val) →
    (table.lookup (622800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3114 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 622800 623000 :=
  FiniteIntervals.of_fin 622800 200 complete_chunk3114

lemma complete_chunk3115 : ∀ i : Fin 200, Compatible (623000 + i.val) →
    (table.lookup (623000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3115 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 623000 623200 :=
  FiniteIntervals.of_fin 623000 200 complete_chunk3115

lemma complete_chunk3116 : ∀ i : Fin 200, Compatible (623200 + i.val) →
    (table.lookup (623200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3116 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 623200 623400 :=
  FiniteIntervals.of_fin 623200 200 complete_chunk3116

lemma complete_chunk3117 : ∀ i : Fin 200, Compatible (623400 + i.val) →
    (table.lookup (623400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3117 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 623400 623600 :=
  FiniteIntervals.of_fin 623400 200 complete_chunk3117

lemma complete_chunk3118 : ∀ i : Fin 200, Compatible (623600 + i.val) →
    (table.lookup (623600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3118 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 623600 623800 :=
  FiniteIntervals.of_fin 623600 200 complete_chunk3118

lemma complete_chunk3119 : ∀ i : Fin 200, Compatible (623800 + i.val) →
    (table.lookup (623800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3119 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 623800 624000 :=
  FiniteIntervals.of_fin 623800 200 complete_chunk3119

#print axioms interval_chunk3110
end Erdos184Work.PureFiveFilter4
