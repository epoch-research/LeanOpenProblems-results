import Submission.PureSixActions2Base
namespace Erdos184Work.PureSixActions2
open PureSixRowModel2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base48 : BaseValid 48 := by decide +kernel
lemma row48_0 : ∀ q : Fin (choices 0), RowValid 48 0 q := by decide +kernel
lemma row48_1 : ∀ q : Fin (choices 1), RowValid 48 1 q := by decide +kernel
lemma row48_2 : ∀ q : Fin (choices 2), RowValid 48 2 q := by decide +kernel
lemma row48_3 : ∀ q : Fin (choices 3), RowValid 48 3 q := by decide +kernel
lemma row48_4 : ∀ q : Fin (choices 4), RowValid 48 4 q := by decide +kernel
lemma row48_5 : ∀ q : Fin (choices 5), RowValid 48 5 q := by decide +kernel
lemma valid_group48 : Valid 48 := by
  refine ⟨base48.1,base48.2.1,base48.2.2,?_⟩
  intro i
  fin_cases i
  · exact row48_0
  · exact row48_1
  · exact row48_2
  · exact row48_3
  · exact row48_4
  · exact row48_5
lemma valid_sub6_0 : ∀ i : Fin 1, ValidAt (48 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group48
lemma valid_part6_0 : FiniteIntervals.Covers ValidAt 48 49 :=
  FiniteIntervals.of_fin 48 1 valid_sub6_0
lemma base49 : BaseValid 49 := by decide +kernel
lemma row49_0 : ∀ q : Fin (choices 0), RowValid 49 0 q := by decide +kernel
lemma row49_1 : ∀ q : Fin (choices 1), RowValid 49 1 q := by decide +kernel
lemma row49_2 : ∀ q : Fin (choices 2), RowValid 49 2 q := by decide +kernel
lemma row49_3 : ∀ q : Fin (choices 3), RowValid 49 3 q := by decide +kernel
lemma row49_4 : ∀ q : Fin (choices 4), RowValid 49 4 q := by decide +kernel
lemma row49_5 : ∀ q : Fin (choices 5), RowValid 49 5 q := by decide +kernel
lemma valid_group49 : Valid 49 := by
  refine ⟨base49.1,base49.2.1,base49.2.2,?_⟩
  intro i
  fin_cases i
  · exact row49_0
  · exact row49_1
  · exact row49_2
  · exact row49_3
  · exact row49_4
  · exact row49_5
lemma valid_sub6_1 : ∀ i : Fin 1, ValidAt (49 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group49
lemma valid_part6_1 : FiniteIntervals.Covers ValidAt 49 50 :=
  FiniteIntervals.of_fin 49 1 valid_sub6_1
lemma base50 : BaseValid 50 := by decide +kernel
lemma row50_0 : ∀ q : Fin (choices 0), RowValid 50 0 q := by decide +kernel
lemma row50_1 : ∀ q : Fin (choices 1), RowValid 50 1 q := by decide +kernel
lemma row50_2 : ∀ q : Fin (choices 2), RowValid 50 2 q := by decide +kernel
lemma row50_3 : ∀ q : Fin (choices 3), RowValid 50 3 q := by decide +kernel
lemma row50_4 : ∀ q : Fin (choices 4), RowValid 50 4 q := by decide +kernel
lemma row50_5 : ∀ q : Fin (choices 5), RowValid 50 5 q := by decide +kernel
lemma valid_group50 : Valid 50 := by
  refine ⟨base50.1,base50.2.1,base50.2.2,?_⟩
  intro i
  fin_cases i
  · exact row50_0
  · exact row50_1
  · exact row50_2
  · exact row50_3
  · exact row50_4
  · exact row50_5
lemma valid_sub6_2 : ∀ i : Fin 1, ValidAt (50 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group50
lemma valid_part6_2 : FiniteIntervals.Covers ValidAt 50 51 :=
  FiniteIntervals.of_fin 50 1 valid_sub6_2
lemma base51 : BaseValid 51 := by decide +kernel
lemma row51_0 : ∀ q : Fin (choices 0), RowValid 51 0 q := by decide +kernel
lemma row51_1 : ∀ q : Fin (choices 1), RowValid 51 1 q := by decide +kernel
lemma row51_2 : ∀ q : Fin (choices 2), RowValid 51 2 q := by decide +kernel
lemma row51_3 : ∀ q : Fin (choices 3), RowValid 51 3 q := by decide +kernel
lemma row51_4 : ∀ q : Fin (choices 4), RowValid 51 4 q := by decide +kernel
lemma row51_5 : ∀ q : Fin (choices 5), RowValid 51 5 q := by decide +kernel
lemma valid_group51 : Valid 51 := by
  refine ⟨base51.1,base51.2.1,base51.2.2,?_⟩
  intro i
  fin_cases i
  · exact row51_0
  · exact row51_1
  · exact row51_2
  · exact row51_3
  · exact row51_4
  · exact row51_5
lemma valid_sub6_3 : ∀ i : Fin 1, ValidAt (51 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group51
lemma valid_part6_3 : FiniteIntervals.Covers ValidAt 51 52 :=
  FiniteIntervals.of_fin 51 1 valid_sub6_3
lemma base52 : BaseValid 52 := by decide +kernel
lemma row52_0 : ∀ q : Fin (choices 0), RowValid 52 0 q := by decide +kernel
lemma row52_1 : ∀ q : Fin (choices 1), RowValid 52 1 q := by decide +kernel
lemma row52_2 : ∀ q : Fin (choices 2), RowValid 52 2 q := by decide +kernel
lemma row52_3 : ∀ q : Fin (choices 3), RowValid 52 3 q := by decide +kernel
lemma row52_4 : ∀ q : Fin (choices 4), RowValid 52 4 q := by decide +kernel
lemma row52_5 : ∀ q : Fin (choices 5), RowValid 52 5 q := by decide +kernel
lemma valid_group52 : Valid 52 := by
  refine ⟨base52.1,base52.2.1,base52.2.2,?_⟩
  intro i
  fin_cases i
  · exact row52_0
  · exact row52_1
  · exact row52_2
  · exact row52_3
  · exact row52_4
  · exact row52_5
lemma valid_sub6_4 : ∀ i : Fin 1, ValidAt (52 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group52
lemma valid_part6_4 : FiniteIntervals.Covers ValidAt 52 53 :=
  FiniteIntervals.of_fin 52 1 valid_sub6_4
lemma base53 : BaseValid 53 := by decide +kernel
lemma row53_0 : ∀ q : Fin (choices 0), RowValid 53 0 q := by decide +kernel
lemma row53_1 : ∀ q : Fin (choices 1), RowValid 53 1 q := by decide +kernel
lemma row53_2 : ∀ q : Fin (choices 2), RowValid 53 2 q := by decide +kernel
lemma row53_3 : ∀ q : Fin (choices 3), RowValid 53 3 q := by decide +kernel
lemma row53_4 : ∀ q : Fin (choices 4), RowValid 53 4 q := by decide +kernel
lemma row53_5 : ∀ q : Fin (choices 5), RowValid 53 5 q := by decide +kernel
lemma valid_group53 : Valid 53 := by
  refine ⟨base53.1,base53.2.1,base53.2.2,?_⟩
  intro i
  fin_cases i
  · exact row53_0
  · exact row53_1
  · exact row53_2
  · exact row53_3
  · exact row53_4
  · exact row53_5
lemma valid_sub6_5 : ∀ i : Fin 1, ValidAt (53 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group53
lemma valid_part6_5 : FiniteIntervals.Covers ValidAt 53 54 :=
  FiniteIntervals.of_fin 53 1 valid_sub6_5
lemma base54 : BaseValid 54 := by decide +kernel
lemma row54_0 : ∀ q : Fin (choices 0), RowValid 54 0 q := by decide +kernel
lemma row54_1 : ∀ q : Fin (choices 1), RowValid 54 1 q := by decide +kernel
lemma row54_2 : ∀ q : Fin (choices 2), RowValid 54 2 q := by decide +kernel
lemma row54_3 : ∀ q : Fin (choices 3), RowValid 54 3 q := by decide +kernel
lemma row54_4 : ∀ q : Fin (choices 4), RowValid 54 4 q := by decide +kernel
lemma row54_5 : ∀ q : Fin (choices 5), RowValid 54 5 q := by decide +kernel
lemma valid_group54 : Valid 54 := by
  refine ⟨base54.1,base54.2.1,base54.2.2,?_⟩
  intro i
  fin_cases i
  · exact row54_0
  · exact row54_1
  · exact row54_2
  · exact row54_3
  · exact row54_4
  · exact row54_5
lemma valid_sub6_6 : ∀ i : Fin 1, ValidAt (54 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group54
lemma valid_part6_6 : FiniteIntervals.Covers ValidAt 54 55 :=
  FiniteIntervals.of_fin 54 1 valid_sub6_6
lemma base55 : BaseValid 55 := by decide +kernel
lemma row55_0 : ∀ q : Fin (choices 0), RowValid 55 0 q := by decide +kernel
lemma row55_1 : ∀ q : Fin (choices 1), RowValid 55 1 q := by decide +kernel
lemma row55_2 : ∀ q : Fin (choices 2), RowValid 55 2 q := by decide +kernel
lemma row55_3 : ∀ q : Fin (choices 3), RowValid 55 3 q := by decide +kernel
lemma row55_4 : ∀ q : Fin (choices 4), RowValid 55 4 q := by decide +kernel
lemma row55_5 : ∀ q : Fin (choices 5), RowValid 55 5 q := by decide +kernel
lemma valid_group55 : Valid 55 := by
  refine ⟨base55.1,base55.2.1,base55.2.2,?_⟩
  intro i
  fin_cases i
  · exact row55_0
  · exact row55_1
  · exact row55_2
  · exact row55_3
  · exact row55_4
  · exact row55_5
lemma valid_sub6_7 : ∀ i : Fin 1, ValidAt (55 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group55
lemma valid_part6_7 : FiniteIntervals.Covers ValidAt 55 56 :=
  FiniteIntervals.of_fin 55 1 valid_sub6_7
lemma valid_interval6 : FiniteIntervals.Covers ValidAt 48 56 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part6_0 valid_part6_1) (FiniteIntervals.merge valid_part6_2 valid_part6_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part6_4 valid_part6_5) (FiniteIntervals.merge valid_part6_6 valid_part6_7)))
#print axioms valid_interval6
end Erdos184Work.PureSixActions2
