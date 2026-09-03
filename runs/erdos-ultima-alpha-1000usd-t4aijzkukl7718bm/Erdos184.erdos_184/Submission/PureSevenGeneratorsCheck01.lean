import Submission.PureSevenGeneratorsBase
namespace Erdos184Work.PureSevenGenerators
open PureSevenRowModel
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base1 : BaseValid 1 := by decide +kernel
lemma row1_0 : ∀ q : Fin (choices 0), RowValid 1 0 q := by decide +kernel
lemma row1_1 : ∀ q : Fin (choices 1), RowValid 1 1 q := by decide +kernel
lemma row1_2 : ∀ q : Fin (choices 2), RowValid 1 2 q := by decide +kernel
lemma row1_3 : ∀ q : Fin (choices 3), RowValid 1 3 q := by decide +kernel
lemma row1_4 : ∀ q : Fin (choices 4), RowValid 1 4 q := by decide +kernel
lemma row1_5 : ∀ q : Fin (choices 5), RowValid 1 5 q := by decide +kernel
lemma row1_6 : ∀ q : Fin (choices 6), RowValid 1 6 q := by decide +kernel
lemma valid_group1 : Valid 1 := by
  refine ⟨base1.1,base1.2.1,base1.2.2,?_⟩
  intro i
  fin_cases i
  · exact row1_0
  · exact row1_1
  · exact row1_2
  · exact row1_3
  · exact row1_4
  · exact row1_5
  · exact row1_6
lemma valid_sub1 : ∀ i : Fin 1, ValidAt (1 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group1
lemma valid_interval1 : FiniteIntervals.Covers ValidAt 1 2 :=
  FiniteIntervals.of_fin 1 1 valid_sub1
#print axioms valid_interval1
end Erdos184Work.PureSevenGenerators
