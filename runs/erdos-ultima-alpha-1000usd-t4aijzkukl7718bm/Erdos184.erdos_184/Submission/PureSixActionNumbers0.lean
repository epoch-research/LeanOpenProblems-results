import Submission.PureSixActions0Base
namespace Erdos184Work.PureSixActions0
open PureSixRowModel0
def applyRows (g : Groups) (q : Rows) (j : Fin 6) : Fin (choices j) :=
  ⟨data g (colorInverse g j) (q (colorInverse g j)).val % choices j,Nat.mod_lt _ (choices_pos _)⟩
def actionKey (g : Groups) (j : ℕ) : ℕ := key (applyRows g (unkey j))

end Erdos184Work.PureSixActions0
