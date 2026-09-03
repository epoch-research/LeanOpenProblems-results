import Submission.BinaryGroupedDeadTriplePowerProbe
namespace Erdos406GroupedDeadTripleExported
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
def StepRow (p : Fin 929) : Prop := ∀ (d e : Fin 2) (cp : Fin 9),
    9*d.val+cp.val=2*carry p+e.val → ∀ sp ∈ D.next (source p) d.val,
    R sp (target p d.val cp.val sp) cp.val ∧
    ∀ tp ∈ ends (target p d.val cp.val sp),
      parent p d.val cp.val sp tp ∈ ends p ∧
      tp ∈ D.next (parent p d.val cp.val sp tp) e.val ∧
      H p (parent p d.val cp.val sp tp)+W (parent p d.val cp.val sp tp) e.val tp-
        W (source p) d.val sp ≤ H (target p d.val cp.val sp) tp

def stepCheck (p : Fin 929) : Bool :=
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


lemma triple_step_sample_164 : stepCheck 164 = true := by decide +kernel
lemma triple_step_sample_167 : stepCheck 167 = true := by decide +kernel
lemma triple_step_sample_168 : stepCheck 168 = true := by decide +kernel
lemma triple_step_sample_885 : stepCheck 885 = true := by decide +kernel
lemma triple_step_sample_886 : stepCheck 886 = true := by decide +kernel
lemma triple_step_sample_887 : stepCheck 887 = true := by decide +kernel
lemma triple_step_sample_926 : stepCheck 926 = true := by decide +kernel
lemma triple_step_sample_927 : stepCheck 927 = true := by decide +kernel
lemma triple_step_sample_928 : stepCheck 928 = true := by decide +kernel
end
end Erdos406GroupedDeadTripleExported
#print axioms Erdos406GroupedDeadTripleExported.triple_step_sample_164
#print axioms Erdos406GroupedDeadTripleExported.triple_step_sample_167
#print axioms Erdos406GroupedDeadTripleExported.triple_step_sample_168
#print axioms Erdos406GroupedDeadTripleExported.triple_step_sample_885
#print axioms Erdos406GroupedDeadTripleExported.triple_step_sample_886
#print axioms Erdos406GroupedDeadTripleExported.triple_step_sample_887
#print axioms Erdos406GroupedDeadTripleExported.triple_step_sample_926
#print axioms Erdos406GroupedDeadTripleExported.triple_step_sample_927
#print axioms Erdos406GroupedDeadTripleExported.triple_step_sample_928
