import Submission.PureSixActions2Base
namespace Erdos184Work.PureSixActions2
open PureSixRowModel2
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base40 : BaseValid 40 := by decide +kernel
lemma row40_0 : ∀ q : Fin (choices 0), RowValid 40 0 q := by decide +kernel
lemma row40_1 : ∀ q : Fin (choices 1), RowValid 40 1 q := by decide +kernel
lemma row40_2 : ∀ q : Fin (choices 2), RowValid 40 2 q := by decide +kernel
lemma row40_3 : ∀ q : Fin (choices 3), RowValid 40 3 q := by decide +kernel
lemma row40_4 : ∀ q : Fin (choices 4), RowValid 40 4 q := by decide +kernel
lemma row40_5 : ∀ q : Fin (choices 5), RowValid 40 5 q := by decide +kernel
lemma valid_group40 : Valid 40 := by
  refine ⟨base40.1,base40.2.1,base40.2.2,?_⟩
  intro i
  fin_cases i
  · exact row40_0
  · exact row40_1
  · exact row40_2
  · exact row40_3
  · exact row40_4
  · exact row40_5
lemma valid_sub5_0 : ∀ i : Fin 1, ValidAt (40 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group40
lemma valid_part5_0 : FiniteIntervals.Covers ValidAt 40 41 :=
  FiniteIntervals.of_fin 40 1 valid_sub5_0
lemma base41 : BaseValid 41 := by decide +kernel
lemma row41_0 : ∀ q : Fin (choices 0), RowValid 41 0 q := by decide +kernel
lemma row41_1 : ∀ q : Fin (choices 1), RowValid 41 1 q := by decide +kernel
lemma row41_2 : ∀ q : Fin (choices 2), RowValid 41 2 q := by decide +kernel
lemma row41_3 : ∀ q : Fin (choices 3), RowValid 41 3 q := by decide +kernel
lemma row41_4 : ∀ q : Fin (choices 4), RowValid 41 4 q := by decide +kernel
lemma row41_5 : ∀ q : Fin (choices 5), RowValid 41 5 q := by decide +kernel
lemma valid_group41 : Valid 41 := by
  refine ⟨base41.1,base41.2.1,base41.2.2,?_⟩
  intro i
  fin_cases i
  · exact row41_0
  · exact row41_1
  · exact row41_2
  · exact row41_3
  · exact row41_4
  · exact row41_5
lemma valid_sub5_1 : ∀ i : Fin 1, ValidAt (41 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group41
lemma valid_part5_1 : FiniteIntervals.Covers ValidAt 41 42 :=
  FiniteIntervals.of_fin 41 1 valid_sub5_1
lemma base42 : BaseValid 42 := by decide +kernel
lemma row42_0 : ∀ q : Fin (choices 0), RowValid 42 0 q := by decide +kernel
lemma row42_1 : ∀ q : Fin (choices 1), RowValid 42 1 q := by decide +kernel
lemma row42_2 : ∀ q : Fin (choices 2), RowValid 42 2 q := by decide +kernel
lemma row42_3 : ∀ q : Fin (choices 3), RowValid 42 3 q := by decide +kernel
lemma row42_4 : ∀ q : Fin (choices 4), RowValid 42 4 q := by decide +kernel
lemma row42_5 : ∀ q : Fin (choices 5), RowValid 42 5 q := by decide +kernel
lemma valid_group42 : Valid 42 := by
  refine ⟨base42.1,base42.2.1,base42.2.2,?_⟩
  intro i
  fin_cases i
  · exact row42_0
  · exact row42_1
  · exact row42_2
  · exact row42_3
  · exact row42_4
  · exact row42_5
lemma valid_sub5_2 : ∀ i : Fin 1, ValidAt (42 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group42
lemma valid_part5_2 : FiniteIntervals.Covers ValidAt 42 43 :=
  FiniteIntervals.of_fin 42 1 valid_sub5_2
lemma base43 : BaseValid 43 := by decide +kernel
lemma row43_0 : ∀ q : Fin (choices 0), RowValid 43 0 q := by decide +kernel
lemma row43_1 : ∀ q : Fin (choices 1), RowValid 43 1 q := by decide +kernel
lemma row43_2 : ∀ q : Fin (choices 2), RowValid 43 2 q := by decide +kernel
lemma row43_3 : ∀ q : Fin (choices 3), RowValid 43 3 q := by decide +kernel
lemma row43_4 : ∀ q : Fin (choices 4), RowValid 43 4 q := by decide +kernel
lemma row43_5 : ∀ q : Fin (choices 5), RowValid 43 5 q := by decide +kernel
lemma valid_group43 : Valid 43 := by
  refine ⟨base43.1,base43.2.1,base43.2.2,?_⟩
  intro i
  fin_cases i
  · exact row43_0
  · exact row43_1
  · exact row43_2
  · exact row43_3
  · exact row43_4
  · exact row43_5
lemma valid_sub5_3 : ∀ i : Fin 1, ValidAt (43 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group43
lemma valid_part5_3 : FiniteIntervals.Covers ValidAt 43 44 :=
  FiniteIntervals.of_fin 43 1 valid_sub5_3
lemma base44 : BaseValid 44 := by decide +kernel
lemma row44_0 : ∀ q : Fin (choices 0), RowValid 44 0 q := by decide +kernel
lemma row44_1 : ∀ q : Fin (choices 1), RowValid 44 1 q := by decide +kernel
lemma row44_2 : ∀ q : Fin (choices 2), RowValid 44 2 q := by decide +kernel
lemma row44_3 : ∀ q : Fin (choices 3), RowValid 44 3 q := by decide +kernel
lemma row44_4 : ∀ q : Fin (choices 4), RowValid 44 4 q := by decide +kernel
lemma row44_5 : ∀ q : Fin (choices 5), RowValid 44 5 q := by decide +kernel
lemma valid_group44 : Valid 44 := by
  refine ⟨base44.1,base44.2.1,base44.2.2,?_⟩
  intro i
  fin_cases i
  · exact row44_0
  · exact row44_1
  · exact row44_2
  · exact row44_3
  · exact row44_4
  · exact row44_5
lemma valid_sub5_4 : ∀ i : Fin 1, ValidAt (44 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group44
lemma valid_part5_4 : FiniteIntervals.Covers ValidAt 44 45 :=
  FiniteIntervals.of_fin 44 1 valid_sub5_4
lemma base45 : BaseValid 45 := by decide +kernel
lemma row45_0 : ∀ q : Fin (choices 0), RowValid 45 0 q := by decide +kernel
lemma row45_1 : ∀ q : Fin (choices 1), RowValid 45 1 q := by decide +kernel
lemma row45_2 : ∀ q : Fin (choices 2), RowValid 45 2 q := by decide +kernel
lemma row45_3 : ∀ q : Fin (choices 3), RowValid 45 3 q := by decide +kernel
lemma row45_4 : ∀ q : Fin (choices 4), RowValid 45 4 q := by decide +kernel
lemma row45_5 : ∀ q : Fin (choices 5), RowValid 45 5 q := by decide +kernel
lemma valid_group45 : Valid 45 := by
  refine ⟨base45.1,base45.2.1,base45.2.2,?_⟩
  intro i
  fin_cases i
  · exact row45_0
  · exact row45_1
  · exact row45_2
  · exact row45_3
  · exact row45_4
  · exact row45_5
lemma valid_sub5_5 : ∀ i : Fin 1, ValidAt (45 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group45
lemma valid_part5_5 : FiniteIntervals.Covers ValidAt 45 46 :=
  FiniteIntervals.of_fin 45 1 valid_sub5_5
lemma base46 : BaseValid 46 := by decide +kernel
lemma row46_0 : ∀ q : Fin (choices 0), RowValid 46 0 q := by decide +kernel
lemma row46_1 : ∀ q : Fin (choices 1), RowValid 46 1 q := by decide +kernel
lemma row46_2 : ∀ q : Fin (choices 2), RowValid 46 2 q := by decide +kernel
lemma row46_3 : ∀ q : Fin (choices 3), RowValid 46 3 q := by decide +kernel
lemma row46_4 : ∀ q : Fin (choices 4), RowValid 46 4 q := by decide +kernel
lemma row46_5 : ∀ q : Fin (choices 5), RowValid 46 5 q := by decide +kernel
lemma valid_group46 : Valid 46 := by
  refine ⟨base46.1,base46.2.1,base46.2.2,?_⟩
  intro i
  fin_cases i
  · exact row46_0
  · exact row46_1
  · exact row46_2
  · exact row46_3
  · exact row46_4
  · exact row46_5
lemma valid_sub5_6 : ∀ i : Fin 1, ValidAt (46 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group46
lemma valid_part5_6 : FiniteIntervals.Covers ValidAt 46 47 :=
  FiniteIntervals.of_fin 46 1 valid_sub5_6
lemma base47 : BaseValid 47 := by decide +kernel
lemma row47_0 : ∀ q : Fin (choices 0), RowValid 47 0 q := by decide +kernel
lemma row47_1 : ∀ q : Fin (choices 1), RowValid 47 1 q := by decide +kernel
lemma row47_2 : ∀ q : Fin (choices 2), RowValid 47 2 q := by decide +kernel
lemma row47_3 : ∀ q : Fin (choices 3), RowValid 47 3 q := by decide +kernel
lemma row47_4 : ∀ q : Fin (choices 4), RowValid 47 4 q := by decide +kernel
lemma row47_5 : ∀ q : Fin (choices 5), RowValid 47 5 q := by decide +kernel
lemma valid_group47 : Valid 47 := by
  refine ⟨base47.1,base47.2.1,base47.2.2,?_⟩
  intro i
  fin_cases i
  · exact row47_0
  · exact row47_1
  · exact row47_2
  · exact row47_3
  · exact row47_4
  · exact row47_5
lemma valid_sub5_7 : ∀ i : Fin 1, ValidAt (47 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group47
lemma valid_part5_7 : FiniteIntervals.Covers ValidAt 47 48 :=
  FiniteIntervals.of_fin 47 1 valid_sub5_7
lemma valid_interval5 : FiniteIntervals.Covers ValidAt 40 48 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_part5_0 valid_part5_1) (FiniteIntervals.merge valid_part5_2 valid_part5_3)) (FiniteIntervals.merge (FiniteIntervals.merge valid_part5_4 valid_part5_5) (FiniteIntervals.merge valid_part5_6 valid_part5_7)))
#print axioms valid_interval5
end Erdos184Work.PureSixActions2
