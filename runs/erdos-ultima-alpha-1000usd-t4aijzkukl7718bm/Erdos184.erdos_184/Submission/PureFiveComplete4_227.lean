import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2270 : ∀ i : Fin 200, Compatible (454000 + i.val) →
    (table.lookup (454000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2270 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 454000 454200 :=
  FiniteIntervals.of_fin 454000 200 complete_chunk2270

lemma complete_chunk2271 : ∀ i : Fin 200, Compatible (454200 + i.val) →
    (table.lookup (454200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2271 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 454200 454400 :=
  FiniteIntervals.of_fin 454200 200 complete_chunk2271

lemma complete_chunk2272 : ∀ i : Fin 200, Compatible (454400 + i.val) →
    (table.lookup (454400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2272 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 454400 454600 :=
  FiniteIntervals.of_fin 454400 200 complete_chunk2272

lemma complete_chunk2273 : ∀ i : Fin 200, Compatible (454600 + i.val) →
    (table.lookup (454600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2273 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 454600 454800 :=
  FiniteIntervals.of_fin 454600 200 complete_chunk2273

lemma complete_chunk2274 : ∀ i : Fin 200, Compatible (454800 + i.val) →
    (table.lookup (454800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2274 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 454800 455000 :=
  FiniteIntervals.of_fin 454800 200 complete_chunk2274

lemma complete_chunk2275 : ∀ i : Fin 200, Compatible (455000 + i.val) →
    (table.lookup (455000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2275 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 455000 455200 :=
  FiniteIntervals.of_fin 455000 200 complete_chunk2275

lemma complete_chunk2276 : ∀ i : Fin 200, Compatible (455200 + i.val) →
    (table.lookup (455200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2276 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 455200 455400 :=
  FiniteIntervals.of_fin 455200 200 complete_chunk2276

lemma complete_chunk2277 : ∀ i : Fin 200, Compatible (455400 + i.val) →
    (table.lookup (455400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2277 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 455400 455600 :=
  FiniteIntervals.of_fin 455400 200 complete_chunk2277

lemma complete_chunk2278 : ∀ i : Fin 200, Compatible (455600 + i.val) →
    (table.lookup (455600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2278 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 455600 455800 :=
  FiniteIntervals.of_fin 455600 200 complete_chunk2278

lemma complete_chunk2279 : ∀ i : Fin 200, Compatible (455800 + i.val) →
    (table.lookup (455800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2279 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 455800 456000 :=
  FiniteIntervals.of_fin 455800 200 complete_chunk2279

#print axioms interval_chunk2270
end Erdos184Work.PureFiveFilter4
