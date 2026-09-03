import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4180 : ∀ i : Fin 200, Compatible (836000 + i.val) →
    (table.lookup (836000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4180 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 836000 836200 :=
  FiniteIntervals.of_fin 836000 200 complete_chunk4180

lemma complete_chunk4181 : ∀ i : Fin 200, Compatible (836200 + i.val) →
    (table.lookup (836200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4181 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 836200 836400 :=
  FiniteIntervals.of_fin 836200 200 complete_chunk4181

lemma complete_chunk4182 : ∀ i : Fin 200, Compatible (836400 + i.val) →
    (table.lookup (836400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4182 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 836400 836600 :=
  FiniteIntervals.of_fin 836400 200 complete_chunk4182

lemma complete_chunk4183 : ∀ i : Fin 200, Compatible (836600 + i.val) →
    (table.lookup (836600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4183 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 836600 836800 :=
  FiniteIntervals.of_fin 836600 200 complete_chunk4183

lemma complete_chunk4184 : ∀ i : Fin 200, Compatible (836800 + i.val) →
    (table.lookup (836800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4184 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 836800 837000 :=
  FiniteIntervals.of_fin 836800 200 complete_chunk4184

lemma complete_chunk4185 : ∀ i : Fin 200, Compatible (837000 + i.val) →
    (table.lookup (837000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4185 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 837000 837200 :=
  FiniteIntervals.of_fin 837000 200 complete_chunk4185

lemma complete_chunk4186 : ∀ i : Fin 200, Compatible (837200 + i.val) →
    (table.lookup (837200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4186 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 837200 837400 :=
  FiniteIntervals.of_fin 837200 200 complete_chunk4186

lemma complete_chunk4187 : ∀ i : Fin 200, Compatible (837400 + i.val) →
    (table.lookup (837400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4187 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 837400 837600 :=
  FiniteIntervals.of_fin 837400 200 complete_chunk4187

lemma complete_chunk4188 : ∀ i : Fin 200, Compatible (837600 + i.val) →
    (table.lookup (837600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4188 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 837600 837800 :=
  FiniteIntervals.of_fin 837600 200 complete_chunk4188

lemma complete_chunk4189 : ∀ i : Fin 200, Compatible (837800 + i.val) →
    (table.lookup (837800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4189 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 837800 838000 :=
  FiniteIntervals.of_fin 837800 200 complete_chunk4189

#print axioms interval_chunk4180
end Erdos184Work.PureFiveFilter4
