import Submission.PureSevenGeneratorsBase
namespace Erdos184Work.PureSevenGenerators
open PureSevenRowModel
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base3 : BaseValid 3 := by decide +kernel
lemma row3_0 : ∀ q : Fin (choices 0), RowValid 3 0 q := by decide +kernel
lemma row3_1 : ∀ q : Fin (choices 1), RowValid 3 1 q := by decide +kernel
lemma row3_2 : ∀ q : Fin (choices 2), RowValid 3 2 q := by decide +kernel
lemma row3_3 : ∀ q : Fin (choices 3), RowValid 3 3 q := by decide +kernel
lemma row3_4 : ∀ q : Fin (choices 4), RowValid 3 4 q := by decide +kernel
lemma row3_5 : ∀ q : Fin (choices 5), RowValid 3 5 q := by decide +kernel
lemma row3_6 : ∀ q : Fin (choices 6), RowValid 3 6 q := by decide +kernel
lemma valid_group3 : Valid 3 := by
  refine ⟨base3.1,base3.2.1,base3.2.2,?_⟩
  intro i
  fin_cases i
  · exact row3_0
  · exact row3_1
  · exact row3_2
  · exact row3_3
  · exact row3_4
  · exact row3_5
  · exact row3_6
lemma valid_sub3 : ∀ i : Fin 1, ValidAt (3 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group3
lemma valid_interval3 : FiniteIntervals.Covers ValidAt 3 4 :=
  FiniteIntervals.of_fin 3 1 valid_sub3
#print axioms valid_interval3
end Erdos184Work.PureSevenGenerators
