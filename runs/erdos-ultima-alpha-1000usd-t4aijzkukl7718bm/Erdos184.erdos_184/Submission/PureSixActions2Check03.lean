import Submission.PureSixActions2Base
namespace Erdos184Work.PureSixActions2
open PureSixRowModel2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base24 : BaseValid 24 := by decide +kernel
lemma row24_0 : ∀ q : Fin (choices 0), RowValid 24 0 q := by decide +kernel
lemma row24_1 : ∀ q : Fin (choices 1), RowValid 24 1 q := by decide +kernel
lemma row24_2 : ∀ q : Fin (choices 2), RowValid 24 2 q := by decide +kernel
lemma row24_3 : ∀ q : Fin (choices 3), RowValid 24 3 q := by decide +kernel
lemma row24_4 : ∀ q : Fin (choices 4), RowValid 24 4 q := by decide +kernel
lemma row24_5 : ∀ q : Fin (choices 5), RowValid 24 5 q := by decide +kernel
lemma valid_group24 : Valid 24 := by
  refine ⟨base24.1,base24.2.1,base24.2.2,?_⟩
  intro i
  fin_cases i
  · exact row24_0
  · exact row24_1
  · exact row24_2
  · exact row24_3
  · exact row24_4
  · exact row24_5
lemma valid_sub3_0 : ∀ i : Fin 1, ValidAt (24 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group24
lemma valid_part3_0 : FiniteIntervals.Covers ValidAt 24 25 :=
  FiniteIntervals.of_fin 24 1 valid_sub3_0
lemma base25 : BaseValid 25 := by decide +kernel
lemma row25_0 : ∀ q : Fin (choices 0), RowValid 25 0 q := by decide +kernel
lemma row25_1 : ∀ q : Fin (choices 1), RowValid 25 1 q := by decide +kernel
lemma row25_2 : ∀ q : Fin (choices 2), RowValid 25 2 q := by decide +kernel
lemma row25_3 : ∀ q : Fin (choices 3), RowValid 25 3 q := by decide +kernel
lemma row25_4 : ∀ q : Fin (choices 4), RowValid 25 4 q := by decide +kernel
lemma row25_5 : ∀ q : Fin (choices 5), RowValid 25 5 q := by decide +kernel
lemma valid_group25 : Valid 25 := by
  refine ⟨base25.1,base25.2.1,base25.2.2,?_⟩
  intro i
  fin_cases i
  · exact row25_0
  · exact row25_1
  · exact row25_2
  · exact row25_3
  · exact row25_4
  · exact row25_5
lemma valid_sub3_1 : ∀ i : Fin 1, ValidAt (25 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group25
lemma valid_part3_1 : FiniteIntervals.Covers ValidAt 25 26 :=
  FiniteIntervals.of_fin 25 1 valid_sub3_1
lemma base26 : BaseValid 26 := by decide +kernel
lemma row26_0 : ∀ q : Fin (choices 0), RowValid 26 0 q := by decide +kernel
lemma row26_1 : ∀ q : Fin (choices 1), RowValid 26 1 q := by decide +kernel
lemma row26_2 : ∀ q : Fin (choices 2), RowValid 26 2 q := by decide +kernel
lemma row26_3 : ∀ q : Fin (choices 3), RowValid 26 3 q := by decide +kernel
lemma row26_4 : ∀ q : Fin (choices 4), RowValid 26 4 q := by decide +kernel
lemma row26_5 : ∀ q : Fin (choices 5), RowValid 26 5 q := by decide +kernel
lemma valid_group26 : Valid 26 := by
  refine ⟨base26.1,base26.2.1,base26.2.2,?_⟩
  intro i
  fin_cases i
  · exact row26_0
  · exact row26_1
  · exact row26_2
  · exact row26_3
  · exact row26_4
  · exact row26_5
lemma valid_sub3_2 : ∀ i : Fin 1, ValidAt (26 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group26
lemma valid_part3_2 : FiniteIntervals.Covers ValidAt 26 27 :=
  FiniteIntervals.of_fin 26 1 valid_sub3_2
lemma base27 : BaseValid 27 := by decide +kernel
lemma row27_0 : ∀ q : Fin (choices 0), RowValid 27 0 q := by decide +kernel
lemma row27_1 : ∀ q : Fin (choices 1), RowValid 27 1 q := by decide +kernel
lemma row27_2 : ∀ q : Fin (choices 2), RowValid 27 2 q := by decide +kernel
lemma row27_3 : ∀ q : Fin (choices 3), RowValid 27 3 q := by decide +kernel
lemma row27_4 : ∀ q : Fin (choices 4), RowValid 27 4 q := by decide +kernel
lemma row27_5 : ∀ q : Fin (choices 5), RowValid 27 5 q := by decide +kernel
lemma valid_group27 : Valid 27 := by
  refine ⟨base27.1,base27.2.1,base27.2.2,?_⟩
  intro i
  fin_cases i
  · exact row27_0
  · exact row27_1
  · exact row27_2
  · exact row27_3
  · exact row27_4
  · exact row27_5
lemma valid_sub3_3 : ∀ i : Fin 1, ValidAt (27 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group27
lemma valid_part3_3 : FiniteIntervals.Covers ValidAt 27 28 :=
  FiniteIntervals.of_fin 27 1 valid_sub3_3
lemma base28 : BaseValid 28 := by decide +kernel
lemma row28_0 : ∀ q : Fin (choices 0), RowValid 28 0 q := by decide +kernel
lemma row28_1 : ∀ q : Fin (choices 1), RowValid 28 1 q := by decide +kernel
lemma row28_2 : ∀ q : Fin (choices 2), RowValid 28 2 q := by decide +kernel
lemma row28_3 : ∀ q : Fin (choices 3), RowValid 28 3 q := by decide +kernel
lemma row28_4 : ∀ q : Fin (choices 4), RowValid 28 4 q := by decide +kernel
lemma row28_5 : ∀ q : Fin (choices 5), RowValid 28 5 q := by decide +kernel
lemma valid_group28 : Valid 28 := by
  refine ⟨base28.1,base28.2.1,base28.2.2,?_⟩
  intro i
  fin_cases i
  · exact row28_0
  · exact row28_1
  · exact row28_2
  · exact row28_3
  · exact row28_4
  · exact row28_5
lemma valid_sub3_4 : ∀ i : Fin 1, ValidAt (28 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group28
lemma valid_part3_4 : FiniteIntervals.Covers ValidAt 28 29 :=
  FiniteIntervals.of_fin 28 1 valid_sub3_4
lemma base29 : BaseValid 29 := by decide +kernel
lemma row29_0 : ∀ q : Fin (choices 0), RowValid 29 0 q := by decide +kernel
lemma row29_1 : ∀ q : Fin (choices 1), RowValid 29 1 q := by decide +kernel
lemma row29_2 : ∀ q : Fin (choices 2), RowValid 29 2 q := by decide +kernel
lemma row29_3 : ∀ q : Fin (choices 3), RowValid 29 3 q := by decide +kernel
lemma row29_4 : ∀ q : Fin (choices 4), RowValid 29 4 q := by decide +kernel
lemma row29_5 : ∀ q : Fin (choices 5), RowValid 29 5 q := by decide +kernel
lemma valid_group29 : Valid 29 := by
  refine ⟨base29.1,base29.2.1,base29.2.2,?_⟩
  intro i
  fin_cases i
  · exact row29_0
  · exact row29_1
  · exact row29_2
  · exact row29_3
  · exact row29_4
  · exact row29_5
lemma valid_sub3_5 : ∀ i : Fin 1, ValidAt (29 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group29
lemma valid_part3_5 : FiniteIntervals.Covers ValidAt 29 30 :=
  FiniteIntervals.of_fin 29 1 valid_sub3_5
lemma base30 : BaseValid 30 := by decide +kernel
lemma row30_0 : ∀ q : Fin (choices 0), RowValid 30 0 q := by decide +kernel
lemma row30_1 : ∀ q : Fin (choices 1), RowValid 30 1 q := by decide +kernel
lemma row30_2 : ∀ q : Fin (choices 2), RowValid 30 2 q := by decide +kernel
lemma row30_3 : ∀ q : Fin (choices 3), RowValid 30 3 q := by decide +kernel
lemma row30_4 : ∀ q : Fin (choices 4), RowValid 30 4 q := by decide +kernel
lemma row30_5 : ∀ q : Fin (choices 5), RowValid 30 5 q := by decide +kernel
lemma valid_group30 : Valid 30 := by
  refine ⟨base30.1,base30.2.1,base30.2.2,?_⟩
  intro i
  fin_cases i
  · exact row30_0
  · exact row30_1
  · exact row30_2
  · exact row30_3
  · exact row30_4
  · exact row30_5
lemma valid_sub3_6 : ∀ i : Fin 1, ValidAt (30 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group30
lemma valid_part3_6 : FiniteIntervals.Covers ValidAt 30 31 :=
  FiniteIntervals.of_fin 30 1 valid_sub3_6
lemma base31 : BaseValid 31 := by decide +kernel
lemma row31_0 : ∀ q : Fin (choices 0), RowValid 31 0 q := by decide +kernel
lemma row31_1 : ∀ q : Fin (choices 1), RowValid 31 1 q := by decide +kernel
lemma row31_2 : ∀ q : Fin (choices 2), RowValid 31 2 q := by decide +kernel
lemma row31_3 : ∀ q : Fin (choices 3), RowValid 31 3 q := by decide +kernel
lemma row31_4 : ∀ q : Fin (choices 4), RowValid 31 4 q := by decide +kernel
lemma row31_5 : ∀ q : Fin (choices 5), RowValid 31 5 q := by decide +kernel
lemma valid_group31 : Valid 31 := by
  refine ⟨base31.1,base31.2.1,base31.2.2,?_⟩
  intro i
  fin_cases i
  · exact row31_0
  · exact row31_1
  · exact row31_2
  · exact row31_3
  · exact row31_4
  · exact row31_5
lemma valid_sub3_7 : ∀ i : Fin 1, ValidAt (31 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group31
lemma valid_part3_7 : FiniteIntervals.Covers ValidAt 31 32 :=
  FiniteIntervals.of_fin 31 1 valid_sub3_7
lemma valid_interval3 : FiniteIntervals.Covers ValidAt 24 32 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part3_0 valid_part3_1) (FiniteIntervals.merge valid_part3_2 valid_part3_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part3_4 valid_part3_5) (FiniteIntervals.merge valid_part3_6 valid_part3_7)))
#print axioms valid_interval3
end Erdos184Work.PureSixActions2
