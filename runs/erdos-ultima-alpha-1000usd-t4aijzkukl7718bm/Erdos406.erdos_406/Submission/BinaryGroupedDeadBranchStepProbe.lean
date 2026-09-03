import Submission.BinaryGroupedDeadBranchPowerProbe
namespace Erdos406GroupedDeadBranchExported
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
def StepRow (p : Fin 821) : Prop := ∀ (d e : Fin 2) (cp : Fin 9),
    9*d.val+cp.val=2*carry p+e.val → ∀ sp ∈ D.next (source p) d.val,
    R sp (target p d.val cp.val sp) cp.val ∧
    ∀ tp ∈ ends (target p d.val cp.val sp),
      parent p d.val cp.val sp tp ∈ ends p ∧
      tp ∈ D.next (parent p d.val cp.val sp tp) e.val ∧
      H p (parent p d.val cp.val sp tp)+W (parent p d.val cp.val sp tp) e.val tp-
        W (source p) d.val sp ≤ H (target p d.val cp.val sp) tp

def stepCheck (p : Fin 821) : Bool :=
  ([0,1] : List ℕ).all fun d => ([0,1] : List ℕ).all fun e =>
    let cp := 2*carry p+e-9*d
    if 9*d ≤ 2*carry p+e ∧ cp < 9 then
      (nextList (source p) d).all fun sp =>
        decide (R sp (target p d cp sp) cp) &&
          (endsList (target p d cp sp)).all fun tp =>
            decide (parent p d cp sp tp ∈ ends p ∧
              tp ∈ D.next (parent p d cp sp tp) e ∧
              H p (parent p d cp sp tp)+W (parent p d cp sp tp) e tp-
                W (source p) d sp ≤ H (target p d cp sp) tp)
    else true


lemma general_degree_step_sample_0 : stepCheck 0 = true := by decide +kernel
lemma general_degree_step_sample_377 : stepCheck 377 = true := by decide +kernel
lemma general_degree_step_sample_379 : stepCheck 379 = true := by decide +kernel
lemma general_degree_step_sample_381 : stepCheck 381 = true := by decide +kernel
lemma general_degree_step_sample_790 : stepCheck 790 = true := by decide +kernel
lemma general_degree_step_sample_791 : stepCheck 791 = true := by decide +kernel
lemma general_degree_step_sample_802 : stepCheck 802 = true := by decide +kernel
lemma general_degree_step_sample_811 : stepCheck 811 = true := by decide +kernel
lemma general_degree_step_sample_812 : stepCheck 812 = true := by decide +kernel
lemma general_degree_step_sample_820 : stepCheck 820 = true := by decide +kernel
end
end Erdos406GroupedDeadBranchExported
#print axioms Erdos406GroupedDeadBranchExported.general_degree_step_sample_0
#print axioms Erdos406GroupedDeadBranchExported.general_degree_step_sample_377
#print axioms Erdos406GroupedDeadBranchExported.general_degree_step_sample_379
#print axioms Erdos406GroupedDeadBranchExported.general_degree_step_sample_381
#print axioms Erdos406GroupedDeadBranchExported.general_degree_step_sample_790
#print axioms Erdos406GroupedDeadBranchExported.general_degree_step_sample_791
#print axioms Erdos406GroupedDeadBranchExported.general_degree_step_sample_802
#print axioms Erdos406GroupedDeadBranchExported.general_degree_step_sample_811
#print axioms Erdos406GroupedDeadBranchExported.general_degree_step_sample_812
#print axioms Erdos406GroupedDeadBranchExported.general_degree_step_sample_820
