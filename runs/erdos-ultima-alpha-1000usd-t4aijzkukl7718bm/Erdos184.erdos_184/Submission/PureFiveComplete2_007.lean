import Submission.PureFiveFilter2
import Submission.FiniteIntervals

/-! Small-subinterval kernel checks, grouped into the original certificate intervals. -/
namespace Erdos184Work.PureFiveFilter2
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_sub70_0 : ∀ i : Fin 200, Compatible (70000 + i.val) →
    (table.lookup (70000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub70_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 70000 70200 :=
  FiniteIntervals.of_fin 70000 200 complete_sub70_0

lemma complete_sub70_1 : ∀ i : Fin 200, Compatible (70200 + i.val) →
    (table.lookup (70200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub70_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 70200 70400 :=
  FiniteIntervals.of_fin 70200 200 complete_sub70_1

lemma complete_sub70_2 : ∀ i : Fin 200, Compatible (70400 + i.val) →
    (table.lookup (70400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub70_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 70400 70600 :=
  FiniteIntervals.of_fin 70400 200 complete_sub70_2

lemma complete_sub70_3 : ∀ i : Fin 200, Compatible (70600 + i.val) →
    (table.lookup (70600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub70_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 70600 70800 :=
  FiniteIntervals.of_fin 70600 200 complete_sub70_3

lemma complete_sub70_4 : ∀ i : Fin 200, Compatible (70800 + i.val) →
    (table.lookup (70800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub70_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 70800 71000 :=
  FiniteIntervals.of_fin 70800 200 complete_sub70_4

lemma interval_chunk70 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 70000 71000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub70_0 interval_sub70_1) (FiniteIntervals.merge interval_sub70_2 (FiniteIntervals.merge interval_sub70_3 interval_sub70_4)))

lemma complete_sub71_0 : ∀ i : Fin 200, Compatible (71000 + i.val) →
    (table.lookup (71000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub71_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 71000 71200 :=
  FiniteIntervals.of_fin 71000 200 complete_sub71_0

lemma complete_sub71_1 : ∀ i : Fin 200, Compatible (71200 + i.val) →
    (table.lookup (71200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub71_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 71200 71400 :=
  FiniteIntervals.of_fin 71200 200 complete_sub71_1

lemma complete_sub71_2 : ∀ i : Fin 200, Compatible (71400 + i.val) →
    (table.lookup (71400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub71_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 71400 71600 :=
  FiniteIntervals.of_fin 71400 200 complete_sub71_2

lemma complete_sub71_3 : ∀ i : Fin 200, Compatible (71600 + i.val) →
    (table.lookup (71600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub71_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 71600 71800 :=
  FiniteIntervals.of_fin 71600 200 complete_sub71_3

lemma complete_sub71_4 : ∀ i : Fin 200, Compatible (71800 + i.val) →
    (table.lookup (71800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub71_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 71800 72000 :=
  FiniteIntervals.of_fin 71800 200 complete_sub71_4

lemma interval_chunk71 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 71000 72000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub71_0 interval_sub71_1) (FiniteIntervals.merge interval_sub71_2 (FiniteIntervals.merge interval_sub71_3 interval_sub71_4)))

lemma complete_sub72_0 : ∀ i : Fin 200, Compatible (72000 + i.val) →
    (table.lookup (72000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub72_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 72000 72200 :=
  FiniteIntervals.of_fin 72000 200 complete_sub72_0

lemma complete_sub72_1 : ∀ i : Fin 200, Compatible (72200 + i.val) →
    (table.lookup (72200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub72_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 72200 72400 :=
  FiniteIntervals.of_fin 72200 200 complete_sub72_1

lemma complete_sub72_2 : ∀ i : Fin 200, Compatible (72400 + i.val) →
    (table.lookup (72400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub72_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 72400 72600 :=
  FiniteIntervals.of_fin 72400 200 complete_sub72_2

lemma complete_sub72_3 : ∀ i : Fin 200, Compatible (72600 + i.val) →
    (table.lookup (72600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub72_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 72600 72800 :=
  FiniteIntervals.of_fin 72600 200 complete_sub72_3

lemma complete_sub72_4 : ∀ i : Fin 200, Compatible (72800 + i.val) →
    (table.lookup (72800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub72_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 72800 73000 :=
  FiniteIntervals.of_fin 72800 200 complete_sub72_4

lemma interval_chunk72 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 72000 73000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub72_0 interval_sub72_1) (FiniteIntervals.merge interval_sub72_2 (FiniteIntervals.merge interval_sub72_3 interval_sub72_4)))

lemma complete_sub73_0 : ∀ i : Fin 200, Compatible (73000 + i.val) →
    (table.lookup (73000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub73_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 73000 73200 :=
  FiniteIntervals.of_fin 73000 200 complete_sub73_0

lemma complete_sub73_1 : ∀ i : Fin 200, Compatible (73200 + i.val) →
    (table.lookup (73200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub73_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 73200 73400 :=
  FiniteIntervals.of_fin 73200 200 complete_sub73_1

lemma complete_sub73_2 : ∀ i : Fin 200, Compatible (73400 + i.val) →
    (table.lookup (73400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub73_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 73400 73600 :=
  FiniteIntervals.of_fin 73400 200 complete_sub73_2

lemma complete_sub73_3 : ∀ i : Fin 200, Compatible (73600 + i.val) →
    (table.lookup (73600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub73_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 73600 73800 :=
  FiniteIntervals.of_fin 73600 200 complete_sub73_3

lemma complete_sub73_4 : ∀ i : Fin 200, Compatible (73800 + i.val) →
    (table.lookup (73800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub73_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 73800 74000 :=
  FiniteIntervals.of_fin 73800 200 complete_sub73_4

lemma interval_chunk73 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 73000 74000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub73_0 interval_sub73_1) (FiniteIntervals.merge interval_sub73_2 (FiniteIntervals.merge interval_sub73_3 interval_sub73_4)))

lemma complete_sub74_0 : ∀ i : Fin 200, Compatible (74000 + i.val) →
    (table.lookup (74000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub74_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 74000 74200 :=
  FiniteIntervals.of_fin 74000 200 complete_sub74_0

lemma complete_sub74_1 : ∀ i : Fin 200, Compatible (74200 + i.val) →
    (table.lookup (74200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub74_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 74200 74400 :=
  FiniteIntervals.of_fin 74200 200 complete_sub74_1

lemma complete_sub74_2 : ∀ i : Fin 200, Compatible (74400 + i.val) →
    (table.lookup (74400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub74_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 74400 74600 :=
  FiniteIntervals.of_fin 74400 200 complete_sub74_2

lemma complete_sub74_3 : ∀ i : Fin 200, Compatible (74600 + i.val) →
    (table.lookup (74600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub74_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 74600 74800 :=
  FiniteIntervals.of_fin 74600 200 complete_sub74_3

lemma complete_sub74_4 : ∀ i : Fin 200, Compatible (74800 + i.val) →
    (table.lookup (74800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub74_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 74800 75000 :=
  FiniteIntervals.of_fin 74800 200 complete_sub74_4

lemma interval_chunk74 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 74000 75000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub74_0 interval_sub74_1) (FiniteIntervals.merge interval_sub74_2 (FiniteIntervals.merge interval_sub74_3 interval_sub74_4)))

lemma complete_sub75_0 : ∀ i : Fin 200, Compatible (75000 + i.val) →
    (table.lookup (75000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub75_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 75000 75200 :=
  FiniteIntervals.of_fin 75000 200 complete_sub75_0

lemma complete_sub75_1 : ∀ i : Fin 200, Compatible (75200 + i.val) →
    (table.lookup (75200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub75_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 75200 75400 :=
  FiniteIntervals.of_fin 75200 200 complete_sub75_1

lemma complete_sub75_2 : ∀ i : Fin 200, Compatible (75400 + i.val) →
    (table.lookup (75400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub75_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 75400 75600 :=
  FiniteIntervals.of_fin 75400 200 complete_sub75_2

lemma complete_sub75_3 : ∀ i : Fin 200, Compatible (75600 + i.val) →
    (table.lookup (75600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub75_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 75600 75800 :=
  FiniteIntervals.of_fin 75600 200 complete_sub75_3

lemma complete_sub75_4 : ∀ i : Fin 200, Compatible (75800 + i.val) →
    (table.lookup (75800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub75_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 75800 76000 :=
  FiniteIntervals.of_fin 75800 200 complete_sub75_4

lemma interval_chunk75 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 75000 76000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub75_0 interval_sub75_1) (FiniteIntervals.merge interval_sub75_2 (FiniteIntervals.merge interval_sub75_3 interval_sub75_4)))

lemma complete_sub76_0 : ∀ i : Fin 200, Compatible (76000 + i.val) →
    (table.lookup (76000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub76_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 76000 76200 :=
  FiniteIntervals.of_fin 76000 200 complete_sub76_0

lemma complete_sub76_1 : ∀ i : Fin 200, Compatible (76200 + i.val) →
    (table.lookup (76200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub76_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 76200 76400 :=
  FiniteIntervals.of_fin 76200 200 complete_sub76_1

lemma complete_sub76_2 : ∀ i : Fin 200, Compatible (76400 + i.val) →
    (table.lookup (76400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub76_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 76400 76600 :=
  FiniteIntervals.of_fin 76400 200 complete_sub76_2

lemma complete_sub76_3 : ∀ i : Fin 200, Compatible (76600 + i.val) →
    (table.lookup (76600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub76_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 76600 76800 :=
  FiniteIntervals.of_fin 76600 200 complete_sub76_3

lemma complete_sub76_4 : ∀ i : Fin 200, Compatible (76800 + i.val) →
    (table.lookup (76800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub76_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 76800 77000 :=
  FiniteIntervals.of_fin 76800 200 complete_sub76_4

lemma interval_chunk76 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 76000 77000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub76_0 interval_sub76_1) (FiniteIntervals.merge interval_sub76_2 (FiniteIntervals.merge interval_sub76_3 interval_sub76_4)))

lemma complete_sub77_0 : ∀ i : Fin 200, Compatible (77000 + i.val) →
    (table.lookup (77000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub77_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 77000 77200 :=
  FiniteIntervals.of_fin 77000 200 complete_sub77_0

lemma complete_sub77_1 : ∀ i : Fin 200, Compatible (77200 + i.val) →
    (table.lookup (77200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub77_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 77200 77400 :=
  FiniteIntervals.of_fin 77200 200 complete_sub77_1

lemma complete_sub77_2 : ∀ i : Fin 200, Compatible (77400 + i.val) →
    (table.lookup (77400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub77_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 77400 77600 :=
  FiniteIntervals.of_fin 77400 200 complete_sub77_2

lemma complete_sub77_3 : ∀ i : Fin 160, Compatible (77600 + i.val) →
    (table.lookup (77600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub77_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 77600 77760 :=
  FiniteIntervals.of_fin 77600 160 complete_sub77_3

lemma interval_chunk77 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 77000 77760 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub77_0 interval_sub77_1) (FiniteIntervals.merge interval_sub77_2 interval_sub77_3))

#print axioms interval_chunk70
end Erdos184Work.PureFiveFilter2
