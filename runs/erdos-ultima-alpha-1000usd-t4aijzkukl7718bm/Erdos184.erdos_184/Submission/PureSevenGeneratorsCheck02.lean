import Submission.PureSevenGeneratorsBase
namespace Erdos184Work.PureSevenGenerators
open PureSevenRowModel
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base2 : BaseValid 2 := by decide +kernel
lemma row2_0 : ∀ q : Fin (choices 0), RowValid 2 0 q := by decide +kernel
lemma row2_1 : ∀ q : Fin (choices 1), RowValid 2 1 q := by decide +kernel
lemma row2_2 : ∀ q : Fin (choices 2), RowValid 2 2 q := by decide +kernel
lemma row2_3 : ∀ q : Fin (choices 3), RowValid 2 3 q := by decide +kernel
lemma row2_4 : ∀ q : Fin (choices 4), RowValid 2 4 q := by decide +kernel
lemma row2_5 : ∀ q : Fin (choices 5), RowValid 2 5 q := by decide +kernel
lemma row2_6 : ∀ q : Fin (choices 6), RowValid 2 6 q := by decide +kernel
lemma valid_group2 : Valid 2 := by
  refine ⟨base2.1,base2.2.1,base2.2.2,?_⟩
  intro i
  fin_cases i
  · exact row2_0
  · exact row2_1
  · exact row2_2
  · exact row2_3
  · exact row2_4
  · exact row2_5
  · exact row2_6
lemma valid_sub2 : ∀ i : Fin 1, ValidAt (2 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group2
lemma valid_interval2 : FiniteIntervals.Covers ValidAt 2 3 :=
  FiniteIntervals.of_fin 2 1 valid_sub2
#print axioms valid_interval2
end Erdos184Work.PureSevenGenerators
