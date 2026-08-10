import FormalConjectures.Util.ProblemImports

def R (x y : Nat) : Prop :=
  x = 1 ∧ y = 0

theorem wf_R : WellFounded R := by
  constructor
  intro x
  constructor
  intro y hy
  -- hy : R y x, i.e., y = 1 ∧ x = 0
  constructor
  intro z hz
  -- hz : R z y, i.e., z = 1 ∧ y = 0
  -- But from hy we have y = 1, and from hz we have y = 0, contradiction!
  rcases hy with ⟨rfl, rfl⟩
  rcases hz with ⟨_, h_false⟩
  contradiction
