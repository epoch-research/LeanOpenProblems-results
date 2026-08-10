import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

-- Can classical or Decidable synthesize Inhabited P? no, but test exact terms.
example (P : Prop) : Inhabited (Decidable P) := inferInstance
example (P : Prop) : Nonempty (Decidable P) := ⟨loopDec P⟩

-- Decidable has Inhabited but P doesn't.
#synth (P : Prop) → Inhabited (Decidable P)

-- Try deriving an Inhabited P instance from an arbitrary Decidable P by recursion on the Decidable.
def inhOfDec? (P : Prop) (d : Decidable P) : Inhabited P := by
  cases d with
  | isTrue h => exact ⟨h⟩
  | isFalse hn =>
      -- impossible branch not fillable
      exact ⟨False.elim (hn (Classical.choice inferInstance))⟩
