import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4920 : ∀ i : Fin 200, Compatible (984000 + i.val) →
    (table.lookup (984000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4920 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 984000 984200 :=
  FiniteIntervals.of_fin 984000 200 complete_chunk4920

lemma complete_chunk4921 : ∀ i : Fin 200, Compatible (984200 + i.val) →
    (table.lookup (984200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4921 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 984200 984400 :=
  FiniteIntervals.of_fin 984200 200 complete_chunk4921

lemma complete_chunk4922 : ∀ i : Fin 200, Compatible (984400 + i.val) →
    (table.lookup (984400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4922 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 984400 984600 :=
  FiniteIntervals.of_fin 984400 200 complete_chunk4922

lemma complete_chunk4923 : ∀ i : Fin 200, Compatible (984600 + i.val) →
    (table.lookup (984600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4923 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 984600 984800 :=
  FiniteIntervals.of_fin 984600 200 complete_chunk4923

lemma complete_chunk4924 : ∀ i : Fin 200, Compatible (984800 + i.val) →
    (table.lookup (984800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4924 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 984800 985000 :=
  FiniteIntervals.of_fin 984800 200 complete_chunk4924

lemma complete_chunk4925 : ∀ i : Fin 200, Compatible (985000 + i.val) →
    (table.lookup (985000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4925 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 985000 985200 :=
  FiniteIntervals.of_fin 985000 200 complete_chunk4925

lemma complete_chunk4926 : ∀ i : Fin 200, Compatible (985200 + i.val) →
    (table.lookup (985200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4926 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 985200 985400 :=
  FiniteIntervals.of_fin 985200 200 complete_chunk4926

lemma complete_chunk4927 : ∀ i : Fin 200, Compatible (985400 + i.val) →
    (table.lookup (985400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4927 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 985400 985600 :=
  FiniteIntervals.of_fin 985400 200 complete_chunk4927

lemma complete_chunk4928 : ∀ i : Fin 200, Compatible (985600 + i.val) →
    (table.lookup (985600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4928 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 985600 985800 :=
  FiniteIntervals.of_fin 985600 200 complete_chunk4928

lemma complete_chunk4929 : ∀ i : Fin 200, Compatible (985800 + i.val) →
    (table.lookup (985800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4929 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 985800 986000 :=
  FiniteIntervals.of_fin 985800 200 complete_chunk4929

#print axioms interval_chunk4920
end Erdos184Work.PureFiveFilter4
