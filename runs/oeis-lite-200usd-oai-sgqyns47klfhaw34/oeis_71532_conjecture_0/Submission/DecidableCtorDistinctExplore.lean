import FormalConjectures.Util.ProblemImports

def decTag {P : Prop} (d : Decidable P) : Bool :=
  Decidable.casesOn d (fun _ => true) (fun _ => false)

example {P : Prop} (hp : P) (hn : ¬ P) : (Decidable.isTrue hp : Decidable P) ≠ Decidable.isFalse hn := by
  intro e
  have ht : decTag (Decidable.isTrue hp : Decidable P) = decTag (Decidable.isFalse hn) := congrArg decTag e
  simp [decTag] at ht

-- even simpler contradiction from hp hn
example {P : Prop} (hp : P) (hn : ¬ P) : False := hn hp
