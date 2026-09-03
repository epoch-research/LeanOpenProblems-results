import Submission.WallData

/-!
Final independent type/axiom checks for the finite supplied wall only.
The expected axiom set is the usual Lean/mathlib foundation:
`propext`, `Classical.choice`, `Quot.sound`, with no additional assumptions.
-/

open Erdos952.WallData

#check @LabelBlack
#check @Black
#check @BlackPath
#check @checkPacked
#check @checkPacked_sound
#check @wall_path_exact
#check @wall_path
#check @wall_displacement

#print axioms Erdos952.WallData.Part00.accepted0000
#print axioms Erdos952.WallData.Part27.accepted0442
#print axioms checkPacked_sound
#print axioms wall_path_exact
#print axioms wall_path
#print axioms start_black
#print axioms finish_black
#print axioms wall_displacement

example : BlackPath 1812223 (⟨146, -149⟩ : GaussianInt) ⟨576956, 95986⟩ :=
  wall_path_exact

example : Relation.ReflTransGen
    (fun p q : GaussianInt => Black p ∧ Black q ∧ (q - p).norm = 1)
    ⟨146, -149⟩ ⟨576956, 95986⟩ :=
  wall_path

example : Black (⟨146, -149⟩ : GaussianInt) ∧ Black (⟨576956, 95986⟩ : GaussianInt) :=
  ⟨start_black, finish_black⟩
