import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5220 : ∀ i : Fin 200, Compatible (1044000 + i.val) →
    (table.lookup (1044000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5220 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1044000 1044200 :=
  FiniteIntervals.of_fin 1044000 200 complete_chunk5220

lemma complete_chunk5221 : ∀ i : Fin 200, Compatible (1044200 + i.val) →
    (table.lookup (1044200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5221 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1044200 1044400 :=
  FiniteIntervals.of_fin 1044200 200 complete_chunk5221

lemma complete_chunk5222 : ∀ i : Fin 200, Compatible (1044400 + i.val) →
    (table.lookup (1044400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5222 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1044400 1044600 :=
  FiniteIntervals.of_fin 1044400 200 complete_chunk5222

lemma complete_chunk5223 : ∀ i : Fin 200, Compatible (1044600 + i.val) →
    (table.lookup (1044600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5223 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1044600 1044800 :=
  FiniteIntervals.of_fin 1044600 200 complete_chunk5223

lemma complete_chunk5224 : ∀ i : Fin 200, Compatible (1044800 + i.val) →
    (table.lookup (1044800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5224 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1044800 1045000 :=
  FiniteIntervals.of_fin 1044800 200 complete_chunk5224

lemma complete_chunk5225 : ∀ i : Fin 200, Compatible (1045000 + i.val) →
    (table.lookup (1045000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5225 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1045000 1045200 :=
  FiniteIntervals.of_fin 1045000 200 complete_chunk5225

lemma complete_chunk5226 : ∀ i : Fin 200, Compatible (1045200 + i.val) →
    (table.lookup (1045200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5226 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1045200 1045400 :=
  FiniteIntervals.of_fin 1045200 200 complete_chunk5226

lemma complete_chunk5227 : ∀ i : Fin 200, Compatible (1045400 + i.val) →
    (table.lookup (1045400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5227 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1045400 1045600 :=
  FiniteIntervals.of_fin 1045400 200 complete_chunk5227

lemma complete_chunk5228 : ∀ i : Fin 200, Compatible (1045600 + i.val) →
    (table.lookup (1045600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5228 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1045600 1045800 :=
  FiniteIntervals.of_fin 1045600 200 complete_chunk5228

lemma complete_chunk5229 : ∀ i : Fin 200, Compatible (1045800 + i.val) →
    (table.lookup (1045800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5229 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1045800 1046000 :=
  FiniteIntervals.of_fin 1045800 200 complete_chunk5229

#print axioms interval_chunk5220
end Erdos184Work.PureFiveFilter4
