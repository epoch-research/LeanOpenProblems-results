import FormalConjectures.Util.ProblemImports
-- Try quotients over Prop with arbitrary relation; should only yield classical choice/propext, no contradiction.
def Q := Quot (fun (a b : Prop) => a ↔ ¬ b)
#check Quot.sound (r := fun (a b : Prop) => a ↔ ¬ b)
example (P : Prop) : (Quot.mk (fun (a b : Prop) => a ↔ ¬ b) P = Quot.mk _ (¬ P)) := by
  apply Quot.sound
  constructor
  · intro h hp; exact hp h
  · intro hn; by_contra hp; exact hn hp
