import Submission.AxisBasePolynomial

/-! One kernel-only block of the complete normalized base-signing enumeration.
This is an auxiliary finite certificate, not a proof of Erdős 213. -/
namespace Erdos213.AxisBaseCompleteness
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem block160 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (160*64+hi.val) lo.val=true := by
  decide +kernel

theorem block161 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (161*64+hi.val) lo.val=true := by
  decide +kernel

theorem block162 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (162*64+hi.val) lo.val=true := by
  decide +kernel

theorem block163 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (163*64+hi.val) lo.val=true := by
  decide +kernel

theorem block164 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (164*64+hi.val) lo.val=true := by
  decide +kernel

theorem block165 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (165*64+hi.val) lo.val=true := by
  decide +kernel

theorem block166 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (166*64+hi.val) lo.val=true := by
  decide +kernel

theorem block167 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (167*64+hi.val) lo.val=true := by
  decide +kernel

theorem block168 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (168*64+hi.val) lo.val=true := by
  decide +kernel

theorem block169 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (169*64+hi.val) lo.val=true := by
  decide +kernel

theorem block170 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (170*64+hi.val) lo.val=true := by
  decide +kernel

theorem block171 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (171*64+hi.val) lo.val=true := by
  decide +kernel

theorem block172 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (172*64+hi.val) lo.val=true := by
  decide +kernel

theorem block173 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (173*64+hi.val) lo.val=true := by
  decide +kernel

theorem block174 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (174*64+hi.val) lo.val=true := by
  decide +kernel

theorem block175 : ∀ hi : Fin 64, ∀ lo : Fin 64,
    checked (175*64+hi.val) lo.val=true := by
  decide +kernel

#print axioms block175
end Erdos213.AxisBaseCompleteness
