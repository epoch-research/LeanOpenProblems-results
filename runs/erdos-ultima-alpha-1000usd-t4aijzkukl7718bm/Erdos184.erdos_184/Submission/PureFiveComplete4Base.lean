import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Factored necessary conditions, permitting early rejection of row choices. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
def rowKey (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : ℕ := 20736 * q0.val + 1728 * q1.val + 144 * q2.val + 12 * q3.val + 1 * q4.val
def RowC0 (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : Prop := (enc00 q1,enc01 q2,enc02 q3,enc03 q4) ∈ good0
instance (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : Decidable (RowC0 q0 q1 q2 q3 q4) := inferInstanceAs (Decidable (_ ∈ good0))
def RowC1 (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : Prop := (enc10 q0,enc11 q3,enc12 q4,enc13 q2) ∈ good1
instance (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : Decidable (RowC1 q0 q1 q2 q3 q4) := inferInstanceAs (Decidable (_ ∈ good1))
def RowC2 (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : Prop := (enc20 q0,enc21 q3,enc22 q4,enc23 q1) ∈ good2
instance (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : Decidable (RowC2 q0 q1 q2 q3 q4) := inferInstanceAs (Decidable (_ ∈ good2))
def RowC3 (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : Prop := (enc30 q4,enc31 q1,enc32 q2,enc33 q0) ∈ good3
instance (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : Decidable (RowC3 q0 q1 q2 q3 q4) := inferInstanceAs (Decidable (_ ∈ good3))
def RowC4 (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : Prop := (enc40 q3,enc41 q1,enc42 q2,enc43 q0) ∈ good4
instance (q0 : Fin 60) (q1 : Fin 12) (q2 : Fin 12) (q3 : Fin 12) (q4 : Fin 12) : Decidable (RowC4 q0 q1 q2 q3 q4) := inferInstanceAs (Decidable (_ ∈ good4))

def OrderedComplete (q0 : Fin 60) : Prop :=
  ∀ q3 q4 q1 : Fin 12, RowC2 q0 q1 0 q3 q4 →
  ∀ q2 : Fin 12, RowC1 q0 0 q2 q3 q4 →
    RowC0 0 q1 q2 q3 q4 → RowC3 q0 q1 q2 0 q4 → RowC4 q0 q1 q2 q3 0 →
    (table.lookup (rowKey q0 q1 q2 q3 q4)).isSome = true
instance (q0 : Fin 60) : Decidable (OrderedComplete q0) := by unfold OrderedComplete; infer_instance

lemma rowKey_digits {j : ℕ} (hj : j < 1244160) :
    rowKey (digit0 j) (digit1 j) (digit2 j) (digit3 j) (digit4 j) = j := by
  dsimp only [rowKey,digit0,digit1,digit2,digit3,digit4]
  omega
#print axioms rowKey_digits
end Erdos184Work.PureFiveFilter4
