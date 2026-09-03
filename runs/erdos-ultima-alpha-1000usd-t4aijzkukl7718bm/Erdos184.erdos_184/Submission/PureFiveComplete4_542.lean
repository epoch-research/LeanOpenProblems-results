import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5420 : ∀ i : Fin 200, Compatible (1084000 + i.val) →
    (table.lookup (1084000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5420 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1084000 1084200 :=
  FiniteIntervals.of_fin 1084000 200 complete_chunk5420

lemma complete_chunk5421 : ∀ i : Fin 200, Compatible (1084200 + i.val) →
    (table.lookup (1084200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5421 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1084200 1084400 :=
  FiniteIntervals.of_fin 1084200 200 complete_chunk5421

lemma complete_chunk5422 : ∀ i : Fin 200, Compatible (1084400 + i.val) →
    (table.lookup (1084400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5422 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1084400 1084600 :=
  FiniteIntervals.of_fin 1084400 200 complete_chunk5422

lemma complete_chunk5423 : ∀ i : Fin 200, Compatible (1084600 + i.val) →
    (table.lookup (1084600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5423 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1084600 1084800 :=
  FiniteIntervals.of_fin 1084600 200 complete_chunk5423

lemma complete_chunk5424 : ∀ i : Fin 200, Compatible (1084800 + i.val) →
    (table.lookup (1084800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5424 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1084800 1085000 :=
  FiniteIntervals.of_fin 1084800 200 complete_chunk5424

lemma complete_chunk5425 : ∀ i : Fin 200, Compatible (1085000 + i.val) →
    (table.lookup (1085000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5425 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1085000 1085200 :=
  FiniteIntervals.of_fin 1085000 200 complete_chunk5425

lemma complete_chunk5426 : ∀ i : Fin 200, Compatible (1085200 + i.val) →
    (table.lookup (1085200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5426 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1085200 1085400 :=
  FiniteIntervals.of_fin 1085200 200 complete_chunk5426

lemma complete_chunk5427 : ∀ i : Fin 200, Compatible (1085400 + i.val) →
    (table.lookup (1085400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5427 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1085400 1085600 :=
  FiniteIntervals.of_fin 1085400 200 complete_chunk5427

lemma complete_chunk5428 : ∀ i : Fin 200, Compatible (1085600 + i.val) →
    (table.lookup (1085600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5428 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1085600 1085800 :=
  FiniteIntervals.of_fin 1085600 200 complete_chunk5428

lemma complete_chunk5429 : ∀ i : Fin 200, Compatible (1085800 + i.val) →
    (table.lookup (1085800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5429 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1085800 1086000 :=
  FiniteIntervals.of_fin 1085800 200 complete_chunk5429

#print axioms interval_chunk5420
end Erdos184Work.PureFiveFilter4
