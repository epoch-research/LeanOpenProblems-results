import Submission.PureSevenFactor
namespace Erdos184Work.PureSevenFactor
open PureSevenMasks
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option Elab.async false
lemma complete_0_0_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 0 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_0_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 0 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_0_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 0 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_0_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 0 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_0_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 0 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_0 : CompleteAt 0 0 := by
  intro e1
  fin_cases e1
  · exact complete_0_0_0
  · exact complete_0_0_1
  · exact complete_0_0_2
  · exact complete_0_0_3
  · exact complete_0_0_4
lemma complete_0_1_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 1 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_1_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 1 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_1_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 1 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_1_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 1 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_1_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 1 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_1 : CompleteAt 0 1 := by
  intro e1
  fin_cases e1
  · exact complete_0_1_0
  · exact complete_0_1_1
  · exact complete_0_1_2
  · exact complete_0_1_3
  · exact complete_0_1_4
lemma complete_0_2_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 2 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_2_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 2 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_2_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 2 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_2_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 2 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_2_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 2 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_2 : CompleteAt 0 2 := by
  intro e1
  fin_cases e1
  · exact complete_0_2_0
  · exact complete_0_2_1
  · exact complete_0_2_2
  · exact complete_0_2_3
  · exact complete_0_2_4
lemma complete_0_3_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 3 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_3_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 3 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_3_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 3 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_3_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 3 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_3_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 3 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_3 : CompleteAt 0 3 := by
  intro e1
  fin_cases e1
  · exact complete_0_3_0
  · exact complete_0_3_1
  · exact complete_0_3_2
  · exact complete_0_3_3
  · exact complete_0_3_4
lemma complete_0_4_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 4 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_4_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 4 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_4_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 4 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_4_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 4 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_4_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 0 4 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_0_4 : CompleteAt 0 4 := by
  intro e1
  fin_cases e1
  · exact complete_0_4_0
  · exact complete_0_4_1
  · exact complete_0_4_2
  · exact complete_0_4_3
  · exact complete_0_4_4
lemma complete_case0 : ∀ e0, CompleteAt 0 e0 := by
  intro e0
  fin_cases e0
  · exact complete_0_0
  · exact complete_0_1
  · exact complete_0_2
  · exact complete_0_3
  · exact complete_0_4
#print axioms complete_case0
end Erdos184Work.PureSevenFactor
