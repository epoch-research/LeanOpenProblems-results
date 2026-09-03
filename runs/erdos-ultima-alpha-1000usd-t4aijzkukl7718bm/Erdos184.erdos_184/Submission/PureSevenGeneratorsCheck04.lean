import Submission.PureSevenGeneratorsBase
namespace Erdos184Work.PureSevenGenerators
open PureSevenRowModel
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base4 : BaseValid 4 := by decide +kernel
lemma row4_0 : ∀ q : Fin (choices 0), RowValid 4 0 q := by decide +kernel
lemma row4_1 : ∀ q : Fin (choices 1), RowValid 4 1 q := by decide +kernel
lemma row4_2 : ∀ q : Fin (choices 2), RowValid 4 2 q := by decide +kernel
lemma row4_3 : ∀ q : Fin (choices 3), RowValid 4 3 q := by decide +kernel
lemma row4_4 : ∀ q : Fin (choices 4), RowValid 4 4 q := by decide +kernel
lemma row4_5 : ∀ q : Fin (choices 5), RowValid 4 5 q := by decide +kernel
lemma row4_6 : ∀ q : Fin (choices 6), RowValid 4 6 q := by decide +kernel
lemma valid_group4 : Valid 4 := by
  refine ⟨base4.1,base4.2.1,base4.2.2,?_⟩
  intro i
  fin_cases i
  · exact row4_0
  · exact row4_1
  · exact row4_2
  · exact row4_3
  · exact row4_4
  · exact row4_5
  · exact row4_6
lemma valid_sub4 : ∀ i : Fin 1, ValidAt (4 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group4
lemma valid_interval4 : FiniteIntervals.Covers ValidAt 4 5 :=
  FiniteIntervals.of_fin 4 1 valid_sub4
#print axioms valid_interval4
end Erdos184Work.PureSevenGenerators
