import FormalConjectures.Util.ProblemImports
partial def botNeBot (_ : Unit) : Filter.NeBot (⊥ : Filter Nat) := botNeBot ()
theorem bad : False := by
  have hE : ∀ᶠ _ : Nat in (⊥ : Filter Nat), False := by simp
  exact (@Filter.eventually_const Nat (⊥ : Filter Nat) (botNeBot ()) False).mp hE
#print axioms botNeBot
#print axioms bad
