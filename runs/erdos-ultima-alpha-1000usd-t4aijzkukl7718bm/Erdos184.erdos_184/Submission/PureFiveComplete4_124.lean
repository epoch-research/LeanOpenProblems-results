import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1240 : ∀ i : Fin 200, Compatible (248000 + i.val) →
    (table.lookup (248000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1240 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 248000 248200 :=
  FiniteIntervals.of_fin 248000 200 complete_chunk1240

lemma complete_chunk1241 : ∀ i : Fin 200, Compatible (248200 + i.val) →
    (table.lookup (248200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1241 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 248200 248400 :=
  FiniteIntervals.of_fin 248200 200 complete_chunk1241

lemma complete_chunk1242 : ∀ i : Fin 200, Compatible (248400 + i.val) →
    (table.lookup (248400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1242 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 248400 248600 :=
  FiniteIntervals.of_fin 248400 200 complete_chunk1242

lemma complete_chunk1243 : ∀ i : Fin 200, Compatible (248600 + i.val) →
    (table.lookup (248600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1243 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 248600 248800 :=
  FiniteIntervals.of_fin 248600 200 complete_chunk1243

lemma complete_chunk1244 : ∀ i : Fin 200, Compatible (248800 + i.val) →
    (table.lookup (248800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1244 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 248800 249000 :=
  FiniteIntervals.of_fin 248800 200 complete_chunk1244

lemma complete_chunk1245 : ∀ i : Fin 200, Compatible (249000 + i.val) →
    (table.lookup (249000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1245 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 249000 249200 :=
  FiniteIntervals.of_fin 249000 200 complete_chunk1245

lemma complete_chunk1246 : ∀ i : Fin 200, Compatible (249200 + i.val) →
    (table.lookup (249200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1246 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 249200 249400 :=
  FiniteIntervals.of_fin 249200 200 complete_chunk1246

lemma complete_chunk1247 : ∀ i : Fin 200, Compatible (249400 + i.val) →
    (table.lookup (249400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1247 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 249400 249600 :=
  FiniteIntervals.of_fin 249400 200 complete_chunk1247

lemma complete_chunk1248 : ∀ i : Fin 200, Compatible (249600 + i.val) →
    (table.lookup (249600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1248 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 249600 249800 :=
  FiniteIntervals.of_fin 249600 200 complete_chunk1248

lemma complete_chunk1249 : ∀ i : Fin 200, Compatible (249800 + i.val) →
    (table.lookup (249800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1249 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 249800 250000 :=
  FiniteIntervals.of_fin 249800 200 complete_chunk1249

#print axioms interval_chunk1240
end Erdos184Work.PureFiveFilter4
