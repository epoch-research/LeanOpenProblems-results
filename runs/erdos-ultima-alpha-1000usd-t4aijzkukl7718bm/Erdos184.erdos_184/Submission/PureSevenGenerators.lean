import Submission.PureSevenGeneratorsCheck00
import Submission.PureSevenGeneratorsCheck01
import Submission.PureSevenGeneratorsCheck02
import Submission.PureSevenGeneratorsCheck03
import Submission.PureSevenGeneratorsCheck04
namespace Erdos184Work.PureSevenGenerators
open PureSevenRowModel
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma valid_all : FiniteIntervals.Covers ValidAt 0 5 :=
  FiniteIntervals.merge (FiniteIntervals.merge valid_interval0 valid_interval1)
    (FiniteIntervals.merge valid_interval2 (FiniteIntervals.merge valid_interval3 valid_interval4))
lemma valid (g : Groups) : Valid g := valid_all g.val (Nat.zero_le _) g.isLt g.isLt

def colorEquiv (g : Groups) : Equiv.Perm (Fin 7) where
  toFun := colorMap g
  invFun := colorInverse g
  left_inv := (valid g).1
  right_inv := (valid g).2.1

def rowEquiv (g : Groups) (i : Fin 7) (q : Fin (choices i)) :
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

def applyRows (g : Groups) (q : Rows) (j : Fin 7) : Fin (choices j) :=
  ⟨data g (colorInverse g j) (q (colorInverse g j)).val % choices j,Nat.mod_lt _ (choices_pos _)⟩
lemma action_apply_eq (g : Groups) (q : Rows) : (action g).apply q = applyRows g q := by
  funext j
  obtain ⟨i,rfl⟩ := (action g).color.surjective j
  rw [CyclicRowActions.Action.apply_color]
  apply Fin.ext
  change data g i (q i).val % choices (colorMap g i) =
    data g (colorInverse g (colorMap g i)) (q (colorInverse g (colorMap g i))).val % choices (colorMap g i)
  rw [(valid g).1 i]

def actionKey (g : Groups) (j : ℕ) : ℕ := key (applyRows g (unkey j))
#print axioms action
#print axioms action_apply_eq
end Erdos184Work.PureSevenGenerators
