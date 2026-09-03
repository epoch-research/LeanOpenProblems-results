import Submission.PureSevenFactor
namespace Erdos184Work.PureSevenFactor
open PureSevenMasks
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option Elab.async false
lemma complete_12_0_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 0 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_0_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 0 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_0_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 0 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_0_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 0 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_0_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 0 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_0 : CompleteAt 12 0 := by
  intro e1
  fin_cases e1
  · exact complete_12_0_0
  · exact complete_12_0_1
  · exact complete_12_0_2
  · exact complete_12_0_3
  · exact complete_12_0_4
lemma complete_12_1_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 1 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_1_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 1 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_1_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 1 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_1_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 1 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_1_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 1 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_1 : CompleteAt 12 1 := by
  intro e1
  fin_cases e1
  · exact complete_12_1_0
  · exact complete_12_1_1
  · exact complete_12_1_2
  · exact complete_12_1_3
  · exact complete_12_1_4
lemma complete_12_2_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 2 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_2_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 2 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_2_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 2 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_2_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 2 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_2_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 2 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_2 : CompleteAt 12 2 := by
  intro e1
  fin_cases e1
  · exact complete_12_2_0
  · exact complete_12_2_1
  · exact complete_12_2_2
  · exact complete_12_2_3
  · exact complete_12_2_4
lemma complete_12_3_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 3 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_3_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 3 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_3_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 3 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_3_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 3 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_3_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 3 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_3 : CompleteAt 12 3 := by
  intro e1
  fin_cases e1
  · exact complete_12_3_0
  · exact complete_12_3_1
  · exact complete_12_3_2
  · exact complete_12_3_3
  · exact complete_12_3_4
lemma complete_12_4_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 4 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_4_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 4 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_4_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 4 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_4_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 4 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_4_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 12 4 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_12_4 : CompleteAt 12 4 := by
  intro e1
  fin_cases e1
  · exact complete_12_4_0
  · exact complete_12_4_1
  · exact complete_12_4_2
  · exact complete_12_4_3
  · exact complete_12_4_4
lemma complete_case12 : ∀ e0, CompleteAt 12 e0 := by
  intro e0
  fin_cases e0
  · exact complete_12_0
  · exact complete_12_1
  · exact complete_12_2
  · exact complete_12_3
  · exact complete_12_4
#print axioms complete_case12
end Erdos184Work.PureSevenFactor
