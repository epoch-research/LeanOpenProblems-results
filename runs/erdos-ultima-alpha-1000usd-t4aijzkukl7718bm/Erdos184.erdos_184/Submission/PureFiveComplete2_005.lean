import Submission.PureFiveFilter2
import Submission.FiniteIntervals

/-! Small-subinterval kernel checks, grouped into the original certificate intervals. -/
namespace Erdos184Work.PureFiveFilter2
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_sub50_0 : ∀ i : Fin 200, Compatible (50000 + i.val) →
    (table.lookup (50000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub50_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50000 50200 :=
  FiniteIntervals.of_fin 50000 200 complete_sub50_0

lemma complete_sub50_1 : ∀ i : Fin 200, Compatible (50200 + i.val) →
    (table.lookup (50200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub50_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50200 50400 :=
  FiniteIntervals.of_fin 50200 200 complete_sub50_1

lemma complete_sub50_2 : ∀ i : Fin 200, Compatible (50400 + i.val) →
    (table.lookup (50400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub50_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50400 50600 :=
  FiniteIntervals.of_fin 50400 200 complete_sub50_2

lemma complete_sub50_3 : ∀ i : Fin 200, Compatible (50600 + i.val) →
    (table.lookup (50600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub50_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50600 50800 :=
  FiniteIntervals.of_fin 50600 200 complete_sub50_3

lemma complete_sub50_4 : ∀ i : Fin 200, Compatible (50800 + i.val) →
    (table.lookup (50800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub50_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50800 51000 :=
  FiniteIntervals.of_fin 50800 200 complete_sub50_4

lemma interval_chunk50 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 50000 51000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub50_0 interval_sub50_1) (FiniteIntervals.merge interval_sub50_2 (FiniteIntervals.merge interval_sub50_3 interval_sub50_4)))

lemma complete_sub51_0 : ∀ i : Fin 200, Compatible (51000 + i.val) →
    (table.lookup (51000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub51_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51000 51200 :=
  FiniteIntervals.of_fin 51000 200 complete_sub51_0

lemma complete_sub51_1 : ∀ i : Fin 200, Compatible (51200 + i.val) →
    (table.lookup (51200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub51_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51200 51400 :=
  FiniteIntervals.of_fin 51200 200 complete_sub51_1

lemma complete_sub51_2 : ∀ i : Fin 200, Compatible (51400 + i.val) →
    (table.lookup (51400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub51_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51400 51600 :=
  FiniteIntervals.of_fin 51400 200 complete_sub51_2

lemma complete_sub51_3 : ∀ i : Fin 200, Compatible (51600 + i.val) →
    (table.lookup (51600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub51_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51600 51800 :=
  FiniteIntervals.of_fin 51600 200 complete_sub51_3

lemma complete_sub51_4 : ∀ i : Fin 200, Compatible (51800 + i.val) →
    (table.lookup (51800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub51_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51800 52000 :=
  FiniteIntervals.of_fin 51800 200 complete_sub51_4

lemma interval_chunk51 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 51000 52000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub51_0 interval_sub51_1) (FiniteIntervals.merge interval_sub51_2 (FiniteIntervals.merge interval_sub51_3 interval_sub51_4)))

lemma complete_sub52_0 : ∀ i : Fin 200, Compatible (52000 + i.val) →
    (table.lookup (52000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub52_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52000 52200 :=
  FiniteIntervals.of_fin 52000 200 complete_sub52_0

lemma complete_sub52_1 : ∀ i : Fin 200, Compatible (52200 + i.val) →
    (table.lookup (52200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub52_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52200 52400 :=
  FiniteIntervals.of_fin 52200 200 complete_sub52_1

lemma complete_sub52_2 : ∀ i : Fin 200, Compatible (52400 + i.val) →
    (table.lookup (52400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub52_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52400 52600 :=
  FiniteIntervals.of_fin 52400 200 complete_sub52_2

lemma complete_sub52_3 : ∀ i : Fin 200, Compatible (52600 + i.val) →
    (table.lookup (52600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub52_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52600 52800 :=
  FiniteIntervals.of_fin 52600 200 complete_sub52_3

lemma complete_sub52_4 : ∀ i : Fin 200, Compatible (52800 + i.val) →
    (table.lookup (52800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub52_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52800 53000 :=
  FiniteIntervals.of_fin 52800 200 complete_sub52_4

lemma interval_chunk52 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 52000 53000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub52_0 interval_sub52_1) (FiniteIntervals.merge interval_sub52_2 (FiniteIntervals.merge interval_sub52_3 interval_sub52_4)))

lemma complete_sub53_0 : ∀ i : Fin 200, Compatible (53000 + i.val) →
    (table.lookup (53000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub53_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53000 53200 :=
  FiniteIntervals.of_fin 53000 200 complete_sub53_0

lemma complete_sub53_1 : ∀ i : Fin 200, Compatible (53200 + i.val) →
    (table.lookup (53200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub53_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53200 53400 :=
  FiniteIntervals.of_fin 53200 200 complete_sub53_1

lemma complete_sub53_2 : ∀ i : Fin 200, Compatible (53400 + i.val) →
    (table.lookup (53400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub53_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53400 53600 :=
  FiniteIntervals.of_fin 53400 200 complete_sub53_2

lemma complete_sub53_3 : ∀ i : Fin 200, Compatible (53600 + i.val) →
    (table.lookup (53600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub53_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53600 53800 :=
  FiniteIntervals.of_fin 53600 200 complete_sub53_3

lemma complete_sub53_4 : ∀ i : Fin 200, Compatible (53800 + i.val) →
    (table.lookup (53800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub53_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53800 54000 :=
  FiniteIntervals.of_fin 53800 200 complete_sub53_4

lemma interval_chunk53 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 53000 54000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub53_0 interval_sub53_1) (FiniteIntervals.merge interval_sub53_2 (FiniteIntervals.merge interval_sub53_3 interval_sub53_4)))

lemma complete_sub54_0 : ∀ i : Fin 200, Compatible (54000 + i.val) →
    (table.lookup (54000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub54_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54000 54200 :=
  FiniteIntervals.of_fin 54000 200 complete_sub54_0

lemma complete_sub54_1 : ∀ i : Fin 200, Compatible (54200 + i.val) →
    (table.lookup (54200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub54_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54200 54400 :=
  FiniteIntervals.of_fin 54200 200 complete_sub54_1

lemma complete_sub54_2 : ∀ i : Fin 200, Compatible (54400 + i.val) →
    (table.lookup (54400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub54_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54400 54600 :=
  FiniteIntervals.of_fin 54400 200 complete_sub54_2

lemma complete_sub54_3 : ∀ i : Fin 200, Compatible (54600 + i.val) →
    (table.lookup (54600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub54_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54600 54800 :=
  FiniteIntervals.of_fin 54600 200 complete_sub54_3

lemma complete_sub54_4 : ∀ i : Fin 200, Compatible (54800 + i.val) →
    (table.lookup (54800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub54_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54800 55000 :=
  FiniteIntervals.of_fin 54800 200 complete_sub54_4

lemma interval_chunk54 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54000 55000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub54_0 interval_sub54_1) (FiniteIntervals.merge interval_sub54_2 (FiniteIntervals.merge interval_sub54_3 interval_sub54_4)))

lemma complete_sub55_0 : ∀ i : Fin 200, Compatible (55000 + i.val) →
    (table.lookup (55000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub55_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55000 55200 :=
  FiniteIntervals.of_fin 55000 200 complete_sub55_0

lemma complete_sub55_1 : ∀ i : Fin 200, Compatible (55200 + i.val) →
    (table.lookup (55200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub55_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55200 55400 :=
  FiniteIntervals.of_fin 55200 200 complete_sub55_1

lemma complete_sub55_2 : ∀ i : Fin 200, Compatible (55400 + i.val) →
    (table.lookup (55400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub55_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55400 55600 :=
  FiniteIntervals.of_fin 55400 200 complete_sub55_2

lemma complete_sub55_3 : ∀ i : Fin 200, Compatible (55600 + i.val) →
    (table.lookup (55600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub55_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55600 55800 :=
  FiniteIntervals.of_fin 55600 200 complete_sub55_3

lemma complete_sub55_4 : ∀ i : Fin 200, Compatible (55800 + i.val) →
    (table.lookup (55800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub55_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55800 56000 :=
  FiniteIntervals.of_fin 55800 200 complete_sub55_4

lemma interval_chunk55 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55000 56000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub55_0 interval_sub55_1) (FiniteIntervals.merge interval_sub55_2 (FiniteIntervals.merge interval_sub55_3 interval_sub55_4)))

lemma complete_sub56_0 : ∀ i : Fin 200, Compatible (56000 + i.val) →
    (table.lookup (56000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub56_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56000 56200 :=
  FiniteIntervals.of_fin 56000 200 complete_sub56_0

lemma complete_sub56_1 : ∀ i : Fin 200, Compatible (56200 + i.val) →
    (table.lookup (56200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub56_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56200 56400 :=
  FiniteIntervals.of_fin 56200 200 complete_sub56_1

lemma complete_sub56_2 : ∀ i : Fin 200, Compatible (56400 + i.val) →
    (table.lookup (56400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub56_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56400 56600 :=
  FiniteIntervals.of_fin 56400 200 complete_sub56_2

lemma complete_sub56_3 : ∀ i : Fin 200, Compatible (56600 + i.val) →
    (table.lookup (56600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub56_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56600 56800 :=
  FiniteIntervals.of_fin 56600 200 complete_sub56_3

lemma complete_sub56_4 : ∀ i : Fin 200, Compatible (56800 + i.val) →
    (table.lookup (56800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub56_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56800 57000 :=
  FiniteIntervals.of_fin 56800 200 complete_sub56_4

lemma interval_chunk56 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 56000 57000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub56_0 interval_sub56_1) (FiniteIntervals.merge interval_sub56_2 (FiniteIntervals.merge interval_sub56_3 interval_sub56_4)))

lemma complete_sub57_0 : ∀ i : Fin 200, Compatible (57000 + i.val) →
    (table.lookup (57000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub57_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57000 57200 :=
  FiniteIntervals.of_fin 57000 200 complete_sub57_0

lemma complete_sub57_1 : ∀ i : Fin 200, Compatible (57200 + i.val) →
    (table.lookup (57200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub57_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57200 57400 :=
  FiniteIntervals.of_fin 57200 200 complete_sub57_1

lemma complete_sub57_2 : ∀ i : Fin 200, Compatible (57400 + i.val) →
    (table.lookup (57400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub57_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57400 57600 :=
  FiniteIntervals.of_fin 57400 200 complete_sub57_2

lemma complete_sub57_3 : ∀ i : Fin 200, Compatible (57600 + i.val) →
    (table.lookup (57600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub57_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57600 57800 :=
  FiniteIntervals.of_fin 57600 200 complete_sub57_3

lemma complete_sub57_4 : ∀ i : Fin 200, Compatible (57800 + i.val) →
    (table.lookup (57800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub57_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57800 58000 :=
  FiniteIntervals.of_fin 57800 200 complete_sub57_4

lemma interval_chunk57 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 57000 58000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub57_0 interval_sub57_1) (FiniteIntervals.merge interval_sub57_2 (FiniteIntervals.merge interval_sub57_3 interval_sub57_4)))

lemma complete_sub58_0 : ∀ i : Fin 200, Compatible (58000 + i.val) →
    (table.lookup (58000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub58_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58000 58200 :=
  FiniteIntervals.of_fin 58000 200 complete_sub58_0

lemma complete_sub58_1 : ∀ i : Fin 200, Compatible (58200 + i.val) →
    (table.lookup (58200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub58_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58200 58400 :=
  FiniteIntervals.of_fin 58200 200 complete_sub58_1

lemma complete_sub58_2 : ∀ i : Fin 200, Compatible (58400 + i.val) →
    (table.lookup (58400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub58_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58400 58600 :=
  FiniteIntervals.of_fin 58400 200 complete_sub58_2

lemma complete_sub58_3 : ∀ i : Fin 200, Compatible (58600 + i.val) →
    (table.lookup (58600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub58_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58600 58800 :=
  FiniteIntervals.of_fin 58600 200 complete_sub58_3

lemma complete_sub58_4 : ∀ i : Fin 200, Compatible (58800 + i.val) →
    (table.lookup (58800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub58_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58800 59000 :=
  FiniteIntervals.of_fin 58800 200 complete_sub58_4

lemma interval_chunk58 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 58000 59000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub58_0 interval_sub58_1) (FiniteIntervals.merge interval_sub58_2 (FiniteIntervals.merge interval_sub58_3 interval_sub58_4)))

lemma complete_sub59_0 : ∀ i : Fin 200, Compatible (59000 + i.val) →
    (table.lookup (59000 + i.val)).isSome = true := by decide +kernel
lemma interval_sub59_0 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59000 59200 :=
  FiniteIntervals.of_fin 59000 200 complete_sub59_0

lemma complete_sub59_1 : ∀ i : Fin 200, Compatible (59200 + i.val) →
    (table.lookup (59200 + i.val)).isSome = true := by decide +kernel
lemma interval_sub59_1 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59200 59400 :=
  FiniteIntervals.of_fin 59200 200 complete_sub59_1

lemma complete_sub59_2 : ∀ i : Fin 200, Compatible (59400 + i.val) →
    (table.lookup (59400 + i.val)).isSome = true := by decide +kernel
lemma interval_sub59_2 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59400 59600 :=
  FiniteIntervals.of_fin 59400 200 complete_sub59_2

lemma complete_sub59_3 : ∀ i : Fin 200, Compatible (59600 + i.val) →
    (table.lookup (59600 + i.val)).isSome = true := by decide +kernel
lemma interval_sub59_3 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59600 59800 :=
  FiniteIntervals.of_fin 59600 200 complete_sub59_3

lemma complete_sub59_4 : ∀ i : Fin 200, Compatible (59800 + i.val) →
    (table.lookup (59800 + i.val)).isSome = true := by decide +kernel
lemma interval_sub59_4 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59800 60000 :=
  FiniteIntervals.of_fin 59800 200 complete_sub59_4

lemma interval_chunk59 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 59000 60000 := (FiniteIntervals.merge (FiniteIntervals.merge interval_sub59_0 interval_sub59_1) (FiniteIntervals.merge interval_sub59_2 (FiniteIntervals.merge interval_sub59_3 interval_sub59_4)))

#print axioms interval_chunk50
end Erdos184Work.PureFiveFilter2
