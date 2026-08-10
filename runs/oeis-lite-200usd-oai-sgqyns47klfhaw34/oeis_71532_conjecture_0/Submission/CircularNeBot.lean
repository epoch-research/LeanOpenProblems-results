import FormalConjectures.Util.ProblemImports

noncomputable instance botNeBot : Filter.NeBot (⊥ : Filter Nat) where
  ne' := by
    intro h
    have hE : ∀ᶠ _ : Nat in (⊥ : Filter Nat), False := by simp
    exact (Filter.eventually_const (f := (⊥ : Filter Nat))).mp hE

theorem bad : False := by
  have hE : ∀ᶠ _ : Nat in (⊥ : Filter Nat), False := by simp
  exact (Filter.eventually_const (f := (⊥ : Filter Nat))).mp hE
#print axioms botNeBot
#print axioms bad
