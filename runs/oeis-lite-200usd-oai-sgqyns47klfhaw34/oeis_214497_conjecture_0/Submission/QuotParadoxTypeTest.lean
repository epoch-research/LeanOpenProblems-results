import FormalConjectures.Util.ProblemImports

inductive Two where | a | b | c

def r (P : Prop) : Two → Two → Prop
  | Two.a, Two.b => True
  | Two.b, Two.a => True
  | Two.b, Two.c => True
  | Two.c, Two.b => True
  | Two.a, Two.c => P
  | Two.c, Two.a => P
  | _, _ => True

-- Should fail because transitivity a~b and b~c requires a~c = P.
example (P : Prop) : Setoid Two := by
  refine ⟨r P, ?_, ?_, ?_⟩
  · intro x; cases x <;> simp [r]
  · intro x y h; cases x <;> cases y <;> simp [r] at h ⊢ <;> assumption
  · intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;> simp [r] at hxy hyz ⊢ <;> try assumption
