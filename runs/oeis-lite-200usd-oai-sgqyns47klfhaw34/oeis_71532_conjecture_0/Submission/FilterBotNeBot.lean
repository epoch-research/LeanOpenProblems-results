import FormalConjectures.Util.ProblemImports
#print Filter.NeBot
#check Filter.eventually_bot
#check Filter.eventually_const
#check (by infer_instance : Filter.NeBot (⊥ : Filter Nat))
example (P : Prop) : P := by
  have hE : ∀ᶠ _ : Nat in (⊥ : Filter Nat), P := by simp
  exact (Filter.eventually_const (f := (⊥ : Filter Nat))).mp hE
#print axioms _example
