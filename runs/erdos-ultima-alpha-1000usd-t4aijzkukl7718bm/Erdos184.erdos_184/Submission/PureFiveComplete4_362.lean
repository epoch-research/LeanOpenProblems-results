import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3620 : ∀ i : Fin 200, Compatible (724000 + i.val) →
    (table.lookup (724000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3620 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 724000 724200 :=
  FiniteIntervals.of_fin 724000 200 complete_chunk3620

lemma complete_chunk3621 : ∀ i : Fin 200, Compatible (724200 + i.val) →
    (table.lookup (724200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3621 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 724200 724400 :=
  FiniteIntervals.of_fin 724200 200 complete_chunk3621

lemma complete_chunk3622 : ∀ i : Fin 200, Compatible (724400 + i.val) →
    (table.lookup (724400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3622 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 724400 724600 :=
  FiniteIntervals.of_fin 724400 200 complete_chunk3622

lemma complete_chunk3623 : ∀ i : Fin 200, Compatible (724600 + i.val) →
    (table.lookup (724600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3623 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 724600 724800 :=
  FiniteIntervals.of_fin 724600 200 complete_chunk3623

lemma complete_chunk3624 : ∀ i : Fin 200, Compatible (724800 + i.val) →
    (table.lookup (724800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3624 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 724800 725000 :=
  FiniteIntervals.of_fin 724800 200 complete_chunk3624

lemma complete_chunk3625 : ∀ i : Fin 200, Compatible (725000 + i.val) →
    (table.lookup (725000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3625 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 725000 725200 :=
  FiniteIntervals.of_fin 725000 200 complete_chunk3625

lemma complete_chunk3626 : ∀ i : Fin 200, Compatible (725200 + i.val) →
    (table.lookup (725200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3626 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 725200 725400 :=
  FiniteIntervals.of_fin 725200 200 complete_chunk3626

lemma complete_chunk3627 : ∀ i : Fin 200, Compatible (725400 + i.val) →
    (table.lookup (725400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3627 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 725400 725600 :=
  FiniteIntervals.of_fin 725400 200 complete_chunk3627

lemma complete_chunk3628 : ∀ i : Fin 200, Compatible (725600 + i.val) →
    (table.lookup (725600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3628 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 725600 725800 :=
  FiniteIntervals.of_fin 725600 200 complete_chunk3628

lemma complete_chunk3629 : ∀ i : Fin 200, Compatible (725800 + i.val) →
    (table.lookup (725800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3629 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 725800 726000 :=
  FiniteIntervals.of_fin 725800 200 complete_chunk3629

#print axioms interval_chunk3620
end Erdos184Work.PureFiveFilter4
