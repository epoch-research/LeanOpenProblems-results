import Submission.PureSevenFactor
namespace Erdos184Work.PureSevenFactor
open PureSevenMasks
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option Elab.async false
lemma complete_6_0_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 0 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_0_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 0 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_0_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 0 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_0_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 0 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_0_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 0 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_0 : CompleteAt 6 0 := by
  intro e1
  fin_cases e1
  · exact complete_6_0_0
  · exact complete_6_0_1
  · exact complete_6_0_2
  · exact complete_6_0_3
  · exact complete_6_0_4
lemma complete_6_1_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 1 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_1_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 1 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_1_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 1 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_1_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 1 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_1_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 1 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_1 : CompleteAt 6 1 := by
  intro e1
  fin_cases e1
  · exact complete_6_1_0
  · exact complete_6_1_1
  · exact complete_6_1_2
  · exact complete_6_1_3
  · exact complete_6_1_4
lemma complete_6_2_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 2 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_2_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 2 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_2_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 2 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_2_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 2 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_2_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 2 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_2 : CompleteAt 6 2 := by
  intro e1
  fin_cases e1
  · exact complete_6_2_0
  · exact complete_6_2_1
  · exact complete_6_2_2
  · exact complete_6_2_3
  · exact complete_6_2_4
lemma complete_6_3_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 3 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_3_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 3 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_3_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 3 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_3_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 3 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_3_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 3 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_3 : CompleteAt 6 3 := by
  intro e1
  fin_cases e1
  · exact complete_6_3_0
  · exact complete_6_3_1
  · exact complete_6_3_2
  · exact complete_6_3_3
  · exact complete_6_3_4
lemma complete_6_4_0 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 4 0 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_4_1 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 4 1 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_4_2 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 4 2 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_4_3 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 4 3 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_4_4 : ∀ e2 e3 e4 e5 : Fin 5,
    commonMask (expanded 6 4 4 e2 e3 e4 e5 0) = 0 := by decide +kernel
lemma complete_6_4 : CompleteAt 6 4 := by
  intro e1
  fin_cases e1
  · exact complete_6_4_0
  · exact complete_6_4_1
  · exact complete_6_4_2
  · exact complete_6_4_3
  · exact complete_6_4_4
lemma complete_case6 : ∀ e0, CompleteAt 6 e0 := by
  intro e0
  fin_cases e0
  · exact complete_6_0
  · exact complete_6_1
  · exact complete_6_2
  · exact complete_6_3
  · exact complete_6_4
#print axioms complete_case6
end Erdos184Work.PureSevenFactor
