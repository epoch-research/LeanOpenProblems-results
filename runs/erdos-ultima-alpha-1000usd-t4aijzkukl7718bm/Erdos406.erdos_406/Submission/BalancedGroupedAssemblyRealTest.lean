import Submission.BinaryGroupedDeadTripleTreeProbe

namespace Erdos406BalancedAssemblyRealTest
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedVariables false
def stepCheck (p : Fin 17) := Erdos406GroupedDeadTripleExported.stepCheck ⟨885+p.val, by have := p.isLt; omega⟩
def finishCheck (p : Fin 17) := stepCheck p
lemma step_check_chunk_0 (p : Fin 17) (hl : 0 ≤ p.val) (hh : p.val < 4) : stepCheck p = true := by
  have h : ∀ p : Fin 17, 0 ≤ p.val → p.val < 4 → stepCheck p = true := by decide +kernel
  exact h p hl hh
lemma step_check_chunk_1 (p : Fin 17) (hl : 4 ≤ p.val) (hh : p.val < 8) : stepCheck p = true := by
  have h : ∀ p : Fin 17, 4 ≤ p.val → p.val < 8 → stepCheck p = true := by decide +kernel
  exact h p hl hh
lemma step_check_chunk_2 (p : Fin 17) (hl : 8 ≤ p.val) (hh : p.val < 12) : stepCheck p = true := by
  have h : ∀ p : Fin 17, 8 ≤ p.val → p.val < 12 → stepCheck p = true := by decide +kernel
  exact h p hl hh
lemma step_check_chunk_3 (p : Fin 17) (hl : 12 ≤ p.val) (hh : p.val < 16) : stepCheck p = true := by
  have h : ∀ p : Fin 17, 12 ≤ p.val → p.val < 16 → stepCheck p = true := by decide +kernel
  exact h p hl hh
lemma step_check_chunk_4 (p : Fin 17) (hl : 16 ≤ p.val) (hh : p.val < 17) : stepCheck p = true := by
  have h : ∀ p : Fin 17, 16 ≤ p.val → p.val < 17 → stepCheck p = true := by decide +kernel
  exact h p hl hh
lemma step_check_all (p : Fin 17) : stepCheck p = true := by
  have hlo_root : 0 ≤ p.val := Nat.zero_le _
  have hhi_root : p.val < 17 := p.isLt
  by_cases hmid_0_5 : p.val < 8
  · by_cases hmid_0_2 : p.val < 4
    · exact step_check_chunk_0 p hlo_root hmid_0_2
    · have hlo_1_2 : 4 ≤ p.val := Nat.le_of_not_gt hmid_0_2
      exact step_check_chunk_1 p hlo_1_2 hmid_0_5
  · have hlo_2_5 : 8 ≤ p.val := Nat.le_of_not_gt hmid_0_5
    by_cases hmid_2_5 : p.val < 12
    · exact step_check_chunk_2 p hlo_2_5 hmid_2_5
    · have hlo_3_5 : 12 ≤ p.val := Nat.le_of_not_gt hmid_2_5
      by_cases hmid_3_5 : p.val < 16
      · exact step_check_chunk_3 p hlo_3_5 hmid_3_5
      · have hlo_4_5 : 16 ≤ p.val := Nat.le_of_not_gt hmid_3_5
        exact step_check_chunk_4 p hlo_4_5 hhi_root

lemma step_checks (p : Fin 17) : stepCheck p = true := step_check_all p
lemma finish_check_chunk_0 (p : Fin 17) (hl : 0 ≤ p.val) (hh : p.val < 16) : finishCheck p = true := by
  have h : ∀ p : Fin 17, 0 ≤ p.val → p.val < 16 → finishCheck p = true := by decide +kernel
  exact h p hl hh
lemma finish_check_chunk_1 (p : Fin 17) (hl : 16 ≤ p.val) (hh : p.val < 17) : finishCheck p = true := by
  have h : ∀ p : Fin 17, 16 ≤ p.val → p.val < 17 → finishCheck p = true := by decide +kernel
  exact h p hl hh
lemma finish_check_all (p : Fin 17) : finishCheck p = true := by
  have hlo_root : 0 ≤ p.val := Nat.zero_le _
  have hhi_root : p.val < 17 := p.isLt
  by_cases hmid_0_2 : p.val < 16
  · exact finish_check_chunk_0 p hlo_root hmid_0_2
  · have hlo_1_2 : 16 ≤ p.val := Nat.le_of_not_gt hmid_0_2
    exact finish_check_chunk_1 p hlo_1_2 hhi_root

lemma finish_checks (p : Fin 17) : finishCheck p = true := finish_check_all p
end
end Erdos406BalancedAssemblyRealTest
#print axioms Erdos406BalancedAssemblyRealTest.step_checks
#print axioms Erdos406BalancedAssemblyRealTest.finish_checks
