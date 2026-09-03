import Submission.PureSixActions2Base
namespace Erdos184Work.PureSixActions2
open PureSixRowModel2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base56 : BaseValid 56 := by decide +kernel
lemma row56_0 : ∀ q : Fin (choices 0), RowValid 56 0 q := by decide +kernel
lemma row56_1 : ∀ q : Fin (choices 1), RowValid 56 1 q := by decide +kernel
lemma row56_2 : ∀ q : Fin (choices 2), RowValid 56 2 q := by decide +kernel
lemma row56_3 : ∀ q : Fin (choices 3), RowValid 56 3 q := by decide +kernel
lemma row56_4 : ∀ q : Fin (choices 4), RowValid 56 4 q := by decide +kernel
lemma row56_5 : ∀ q : Fin (choices 5), RowValid 56 5 q := by decide +kernel
lemma valid_group56 : Valid 56 := by
  refine ⟨base56.1,base56.2.1,base56.2.2,?_⟩
  intro i
  fin_cases i
  · exact row56_0
  · exact row56_1
  · exact row56_2
  · exact row56_3
  · exact row56_4
  · exact row56_5
lemma valid_sub7_0 : ∀ i : Fin 1, ValidAt (56 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group56
lemma valid_part7_0 : FiniteIntervals.Covers ValidAt 56 57 :=
  FiniteIntervals.of_fin 56 1 valid_sub7_0
lemma base57 : BaseValid 57 := by decide +kernel
lemma row57_0 : ∀ q : Fin (choices 0), RowValid 57 0 q := by decide +kernel
lemma row57_1 : ∀ q : Fin (choices 1), RowValid 57 1 q := by decide +kernel
lemma row57_2 : ∀ q : Fin (choices 2), RowValid 57 2 q := by decide +kernel
lemma row57_3 : ∀ q : Fin (choices 3), RowValid 57 3 q := by decide +kernel
lemma row57_4 : ∀ q : Fin (choices 4), RowValid 57 4 q := by decide +kernel
lemma row57_5 : ∀ q : Fin (choices 5), RowValid 57 5 q := by decide +kernel
lemma valid_group57 : Valid 57 := by
  refine ⟨base57.1,base57.2.1,base57.2.2,?_⟩
  intro i
  fin_cases i
  · exact row57_0
  · exact row57_1
  · exact row57_2
  · exact row57_3
  · exact row57_4
  · exact row57_5
lemma valid_sub7_1 : ∀ i : Fin 1, ValidAt (57 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group57
lemma valid_part7_1 : FiniteIntervals.Covers ValidAt 57 58 :=
  FiniteIntervals.of_fin 57 1 valid_sub7_1
lemma base58 : BaseValid 58 := by decide +kernel
lemma row58_0 : ∀ q : Fin (choices 0), RowValid 58 0 q := by decide +kernel
lemma row58_1 : ∀ q : Fin (choices 1), RowValid 58 1 q := by decide +kernel
lemma row58_2 : ∀ q : Fin (choices 2), RowValid 58 2 q := by decide +kernel
lemma row58_3 : ∀ q : Fin (choices 3), RowValid 58 3 q := by decide +kernel
lemma row58_4 : ∀ q : Fin (choices 4), RowValid 58 4 q := by decide +kernel
lemma row58_5 : ∀ q : Fin (choices 5), RowValid 58 5 q := by decide +kernel
lemma valid_group58 : Valid 58 := by
  refine ⟨base58.1,base58.2.1,base58.2.2,?_⟩
  intro i
  fin_cases i
  · exact row58_0
  · exact row58_1
  · exact row58_2
  · exact row58_3
  · exact row58_4
  · exact row58_5
lemma valid_sub7_2 : ∀ i : Fin 1, ValidAt (58 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group58
lemma valid_part7_2 : FiniteIntervals.Covers ValidAt 58 59 :=
  FiniteIntervals.of_fin 58 1 valid_sub7_2
lemma base59 : BaseValid 59 := by decide +kernel
lemma row59_0 : ∀ q : Fin (choices 0), RowValid 59 0 q := by decide +kernel
lemma row59_1 : ∀ q : Fin (choices 1), RowValid 59 1 q := by decide +kernel
lemma row59_2 : ∀ q : Fin (choices 2), RowValid 59 2 q := by decide +kernel
lemma row59_3 : ∀ q : Fin (choices 3), RowValid 59 3 q := by decide +kernel
lemma row59_4 : ∀ q : Fin (choices 4), RowValid 59 4 q := by decide +kernel
lemma row59_5 : ∀ q : Fin (choices 5), RowValid 59 5 q := by decide +kernel
lemma valid_group59 : Valid 59 := by
  refine ⟨base59.1,base59.2.1,base59.2.2,?_⟩
  intro i
  fin_cases i
  · exact row59_0
  · exact row59_1
  · exact row59_2
  · exact row59_3
  · exact row59_4
  · exact row59_5
lemma valid_sub7_3 : ∀ i : Fin 1, ValidAt (59 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group59
lemma valid_part7_3 : FiniteIntervals.Covers ValidAt 59 60 :=
  FiniteIntervals.of_fin 59 1 valid_sub7_3
lemma base60 : BaseValid 60 := by decide +kernel
lemma row60_0 : ∀ q : Fin (choices 0), RowValid 60 0 q := by decide +kernel
lemma row60_1 : ∀ q : Fin (choices 1), RowValid 60 1 q := by decide +kernel
lemma row60_2 : ∀ q : Fin (choices 2), RowValid 60 2 q := by decide +kernel
lemma row60_3 : ∀ q : Fin (choices 3), RowValid 60 3 q := by decide +kernel
lemma row60_4 : ∀ q : Fin (choices 4), RowValid 60 4 q := by decide +kernel
lemma row60_5 : ∀ q : Fin (choices 5), RowValid 60 5 q := by decide +kernel
lemma valid_group60 : Valid 60 := by
  refine ⟨base60.1,base60.2.1,base60.2.2,?_⟩
  intro i
  fin_cases i
  · exact row60_0
  · exact row60_1
  · exact row60_2
  · exact row60_3
  · exact row60_4
  · exact row60_5
lemma valid_sub7_4 : ∀ i : Fin 1, ValidAt (60 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group60
lemma valid_part7_4 : FiniteIntervals.Covers ValidAt 60 61 :=
  FiniteIntervals.of_fin 60 1 valid_sub7_4
lemma base61 : BaseValid 61 := by decide +kernel
lemma row61_0 : ∀ q : Fin (choices 0), RowValid 61 0 q := by decide +kernel
lemma row61_1 : ∀ q : Fin (choices 1), RowValid 61 1 q := by decide +kernel
lemma row61_2 : ∀ q : Fin (choices 2), RowValid 61 2 q := by decide +kernel
lemma row61_3 : ∀ q : Fin (choices 3), RowValid 61 3 q := by decide +kernel
lemma row61_4 : ∀ q : Fin (choices 4), RowValid 61 4 q := by decide +kernel
lemma row61_5 : ∀ q : Fin (choices 5), RowValid 61 5 q := by decide +kernel
lemma valid_group61 : Valid 61 := by
  refine ⟨base61.1,base61.2.1,base61.2.2,?_⟩
  intro i
  fin_cases i
  · exact row61_0
  · exact row61_1
  · exact row61_2
  · exact row61_3
  · exact row61_4
  · exact row61_5
lemma valid_sub7_5 : ∀ i : Fin 1, ValidAt (61 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group61
lemma valid_part7_5 : FiniteIntervals.Covers ValidAt 61 62 :=
  FiniteIntervals.of_fin 61 1 valid_sub7_5
lemma base62 : BaseValid 62 := by decide +kernel
lemma row62_0 : ∀ q : Fin (choices 0), RowValid 62 0 q := by decide +kernel
lemma row62_1 : ∀ q : Fin (choices 1), RowValid 62 1 q := by decide +kernel
lemma row62_2 : ∀ q : Fin (choices 2), RowValid 62 2 q := by decide +kernel
lemma row62_3 : ∀ q : Fin (choices 3), RowValid 62 3 q := by decide +kernel
lemma row62_4 : ∀ q : Fin (choices 4), RowValid 62 4 q := by decide +kernel
lemma row62_5 : ∀ q : Fin (choices 5), RowValid 62 5 q := by decide +kernel
lemma valid_group62 : Valid 62 := by
  refine ⟨base62.1,base62.2.1,base62.2.2,?_⟩
  intro i
  fin_cases i
  · exact row62_0
  · exact row62_1
  · exact row62_2
  · exact row62_3
  · exact row62_4
  · exact row62_5
lemma valid_sub7_6 : ∀ i : Fin 1, ValidAt (62 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group62
lemma valid_part7_6 : FiniteIntervals.Covers ValidAt 62 63 :=
  FiniteIntervals.of_fin 62 1 valid_sub7_6
lemma base63 : BaseValid 63 := by decide +kernel
lemma row63_0 : ∀ q : Fin (choices 0), RowValid 63 0 q := by decide +kernel
lemma row63_1 : ∀ q : Fin (choices 1), RowValid 63 1 q := by decide +kernel
lemma row63_2 : ∀ q : Fin (choices 2), RowValid 63 2 q := by decide +kernel
lemma row63_3 : ∀ q : Fin (choices 3), RowValid 63 3 q := by decide +kernel
lemma row63_4 : ∀ q : Fin (choices 4), RowValid 63 4 q := by decide +kernel
lemma row63_5 : ∀ q : Fin (choices 5), RowValid 63 5 q := by decide +kernel
lemma valid_group63 : Valid 63 := by
  refine ⟨base63.1,base63.2.1,base63.2.2,?_⟩
  intro i
  fin_cases i
  · exact row63_0
  · exact row63_1
  · exact row63_2
  · exact row63_3
  · exact row63_4
  · exact row63_5
lemma valid_sub7_7 : ∀ i : Fin 1, ValidAt (63 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group63
lemma valid_part7_7 : FiniteIntervals.Covers ValidAt 63 64 :=
  FiniteIntervals.of_fin 63 1 valid_sub7_7
lemma valid_interval7 : FiniteIntervals.Covers ValidAt 56 64 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part7_0 valid_part7_1) (FiniteIntervals.merge valid_part7_2 valid_part7_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part7_4 valid_part7_5) (FiniteIntervals.merge valid_part7_6 valid_part7_7)))
#print axioms valid_interval7
end Erdos184Work.PureSixActions2
