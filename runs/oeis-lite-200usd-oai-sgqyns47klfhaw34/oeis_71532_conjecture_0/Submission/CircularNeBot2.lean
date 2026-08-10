import FormalConjectures.Util.ProblemImports

noncomputable def botNeBot : Filter.NeBot (⊥ : Filter Nat) :=
  ⟨by
    intro h
    have hE : ∀ᶠ _ : Nat in (⊥ : Filter Nat), False := by simp
    exact (@Filter.eventually_const Nat (⊥ : Filter Nat) botNeBot False).mp hE⟩

theorem bad : False := by
  have hE : ∀ᶠ _ : Nat in (⊥ : Filter Nat), False := by simp
  exact (@Filter.eventually_const Nat (⊥ : Filter Nat) botNeBot False).mp hE
#print axioms botNeBot
#print axioms bad
