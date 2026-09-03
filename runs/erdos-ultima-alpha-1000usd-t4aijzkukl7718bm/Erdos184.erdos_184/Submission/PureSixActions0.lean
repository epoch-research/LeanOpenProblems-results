import Submission.PureSixActionNumbers0
import Submission.PureSixActions0Check00
import Submission.PureSixActions0Check01
import Submission.PureSixActions0Check02
import Submission.PureSixActions0Check03
import Submission.PureSixActions0Check04
import Submission.PureSixActions0Check05
import Submission.PureSixActions0Check06
import Submission.PureSixActions0Check07
import Submission.PureSixActions0Check08
import Submission.PureSixActions0Check09
import Submission.PureSixActions0Check10
import Submission.PureSixActions0Check11
import Submission.PureSixActions0Check12
import Submission.PureSixActions0Check13
import Submission.PureSixActions0Check14
import Submission.PureSixActions0Check15
import Submission.PureSixActions0Check16
import Submission.PureSixActions0Check17
import Submission.PureSixActions0Check18
import Submission.PureSixActions0Check19
import Submission.PureSixActions0Check20
import Submission.PureSixActions0Check21
import Submission.PureSixActions0Check22
import Submission.PureSixActions0Check23
import Submission.PureSixActions0Check24
import Submission.PureSixActions0Check25
import Submission.PureSixActions0Check26
import Submission.PureSixActions0Check27
import Submission.PureSixActions0Check28
import Submission.PureSixActions0Check29
import Submission.PureSixActions0Check30
import Submission.PureSixActions0Check31
import Submission.PureSixActions0Check32
import Submission.PureSixActions0Check33
import Submission.PureSixActions0Check34
import Submission.PureSixActions0Check35
import Submission.PureSixActions0Check36
import Submission.PureSixActions0Check37
import Submission.PureSixActions0Check38
import Submission.PureSixActions0Check39
import Submission.PureSixActions0Check40
import Submission.PureSixActions0Check41
import Submission.PureSixActions0Check42
import Submission.PureSixActions0Check43
import Submission.PureSixActions0Check44
import Submission.PureSixActions0Check45
import Submission.PureSixActions0Check46
import Submission.PureSixActions0Check47
import Submission.PureSixActions0Check48
import Submission.PureSixActions0Check49
import Submission.PureSixActions0Check50
import Submission.PureSixActions0Check51
import Submission.PureSixActions0Check52
import Submission.PureSixActions0Check53
import Submission.PureSixActions0Check54
import Submission.PureSixActions0Check55
import Submission.PureSixActions0Check56
import Submission.PureSixActions0Check57
import Submission.PureSixActions0Check58
import Submission.PureSixActions0Check59

namespace Erdos184Work.PureSixActions0
open PureSixRowModel0
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_all : FiniteIntervals.Covers ValidAt 0 720 :=
  (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_interval0 (FiniteIntervals.merge valid_interval1 valid_interval2)) (FiniteIntervals.merge (FiniteIntervals.merge valid_interval3 valid_interval4) (FiniteIntervals.merge valid_interval5 valid_interval6))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_interval7 valid_interval8) (FiniteIntervals.merge valid_interval9 valid_interval10)) (FiniteIntervals.merge (FiniteIntervals.merge valid_interval11 valid_interval12) (FiniteIntervals.merge valid_interval13 valid_interval14)))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_interval15 (FiniteIntervals.merge valid_interval16 valid_interval17)) (FiniteIntervals.merge (FiniteIntervals.merge valid_interval18 valid_interval19) (FiniteIntervals.merge valid_interval20 valid_interval21))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_interval22 valid_interval23) (FiniteIntervals.merge valid_interval24 valid_interval25)) (FiniteIntervals.merge (FiniteIntervals.merge valid_interval26 valid_interval27) (FiniteIntervals.merge valid_interval28 valid_interval29))))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_interval30 (FiniteIntervals.merge valid_interval31 valid_interval32)) (FiniteIntervals.merge (FiniteIntervals.merge valid_interval33 valid_interval34) (FiniteIntervals.merge valid_interval35 valid_interval36))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_interval37 valid_interval38) (FiniteIntervals.merge valid_interval39 valid_interval40)) (FiniteIntervals.merge (FiniteIntervals.merge valid_interval41 valid_interval42) (FiniteIntervals.merge valid_interval43 valid_interval44)))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_interval45 (FiniteIntervals.merge valid_interval46 valid_interval47)) (FiniteIntervals.merge (FiniteIntervals.merge valid_interval48 valid_interval49) (FiniteIntervals.merge valid_interval50 valid_interval51))) (FiniteIntervals.merge (FiniteIntervals.merge (FiniteIntervals.merge valid_interval52 valid_interval53) (FiniteIntervals.merge valid_interval54 valid_interval55)) (FiniteIntervals.merge (FiniteIntervals.merge valid_interval56 valid_interval57) (FiniteIntervals.merge valid_interval58 valid_interval59))))))
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
end Erdos184Work.PureSixActions0
