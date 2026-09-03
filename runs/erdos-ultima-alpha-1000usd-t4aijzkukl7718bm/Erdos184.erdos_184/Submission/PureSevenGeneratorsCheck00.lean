import Submission.PureSevenGeneratorsBase
namespace Erdos184Work.PureSevenGenerators
open PureSevenRowModel
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma base0 : BaseValid 0 := by decide +kernel
lemma row0_0 : ∀ q : Fin (choices 0), RowValid 0 0 q := by decide +kernel
lemma row0_1 : ∀ q : Fin (choices 1), RowValid 0 1 q := by decide +kernel
lemma row0_2 : ∀ q : Fin (choices 2), RowValid 0 2 q := by decide +kernel
lemma row0_3 : ∀ q : Fin (choices 3), RowValid 0 3 q := by decide +kernel
lemma row0_4 : ∀ q : Fin (choices 4), RowValid 0 4 q := by decide +kernel
lemma row0_5 : ∀ q : Fin (choices 5), RowValid 0 5 q := by decide +kernel
lemma row0_6 : ∀ q : Fin (choices 6), RowValid 0 6 q := by decide +kernel
lemma valid_group0 : Valid 0 := by
  refine ⟨base0.1,base0.2.1,base0.2.2,?_⟩
  intro i
  fin_cases i
  · exact row0_0
  · exact row0_1
  · exact row0_2
  · exact row0_3
  · exact row0_4
  · exact row0_5
  · exact row0_6
lemma valid_sub0 : ∀ i : Fin 1, ValidAt (0 + i.val) := by
  intro i
  fin_cases i
  intro h
  exact valid_group0
lemma valid_interval0 : FiniteIntervals.Covers ValidAt 0 1 :=
  FiniteIntervals.of_fin 0 1 valid_sub0
#print axioms valid_interval0
end Erdos184Work.PureSevenGenerators
