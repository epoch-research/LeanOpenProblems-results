import Submission.PureSixActionNumbers1
import Submission.PureSixActions1Check00
import Submission.PureSixActions1Check01
import Submission.PureSixActions1Check02
import Submission.PureSixActions1Check03
import Submission.PureSixActions1Check04
import Submission.PureSixActions1Check05
import Submission.PureSixActions1Check06
import Submission.PureSixActions1Check07
import Submission.PureSixActions1Check08
import Submission.PureSixActions1Check09
import Submission.PureSixActions1Check10
import Submission.PureSixActions1Check11

namespace Erdos184Work.PureSixActions1
open PureSixRowModel1
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_all : FiniteIntervals.Covers ValidAt 0 96 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_interval0 (FiniteIntervals.merge valid_interval1 valid_interval2)) (FiniteIntervals.merge valid_interval3 (FiniteIntervals.merge valid_interval4 valid_interval5))) (FiniteIntervals.merge (FiniteIntervals.merge valid_interval6 (FiniteIntervals.merge valid_interval7 valid_interval8)) (FiniteIntervals.merge valid_interval9 (FiniteIntervals.merge valid_interval10 valid_interval11))))
lemma valid (g : Groups) : Valid g := valid_all g.val (Nat.zero_le _) g.isLt g.isLt

def colorEquiv (g : Groups) : Equiv.Perm (Fin 6) where
  toFun := colorMap g
  invFun := colorInverse g
  left_inv := (valid g).1
  right_inv := (valid g).2.1

def rowEquiv (g : Groups) (i : Fin 6) (q : Fin (choices i)) :
    Fin (length i) ≃ Fin (length (colorMap g i)) where
  toFun := edgeForward g i q
  invFun := edgeBackward g i q
  left_inv := ((valid g).2.2.2 i q).1
  right_inv := ((valid g).2.2.2 i q).2.1

def action (g : Groups) : CyclicRowActions.Action length choices word where
  color := colorEquiv g
  vertex := ⟨vertexMap g,Function.LeftInverse.injective (valid g).2.2.1⟩
  row := rowImage g
  edge := rowEquiv g
  endpoints := fun i q j => ((valid g).2.2.2 i q).2.2 j

lemma action_apply_eq (g : Groups) (q : Rows) : (action g).apply q = applyRows g q := by
  funext j
  obtain ⟨i,rfl⟩ := (action g).color.surjective j
  rw [CyclicRowActions.Action.apply_color]
  apply Fin.ext
  change data g i (q i).val % choices (colorMap g i) =
    data g (colorInverse g (colorMap g i)) (q (colorInverse g (colorMap g i))).val % choices (colorMap g i)
  rw [(valid g).1 i]

#print axioms action
#print axioms action_apply_eq
end Erdos184Work.PureSixActions1
