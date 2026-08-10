import FormalConjectures.Util.ProblemImports

inductive MyInhabited (α : Type) : Type where
  | mk (val : α) : MyInhabited α
  | dummy : MyInhabited α

lemma map_step_proof (n : ℕ) (h : ∃ z : ℤ, (n : ℚ) = (z : ℚ)) : ∃ z : ℤ, ((n + 1 : ℕ) : ℚ) = (z : ℚ) := by
  rcases h with ⟨z, hz⟩
  use z + 1
  push_cast
  rw [hz]

def map_step (n : ℕ) (h : ∃ z : ℤ, (n : ℚ) = (z : ℚ)) : MyInhabited (PLift (∃ z : ℤ, ((n + 1 : ℕ) : ℚ) = (z : ℚ))) :=
  MyInhabited.mk (PLift.up (map_step_proof n h))

def a_Q_int_def (n : ℕ) : MyInhabited (PLift (∃ z : ℤ, (n : ℚ) = (z : ℚ))) :=
  match n with
  | 0 => MyInhabited.mk (PLift.up ⟨0, by rfl⟩)
  | n + 1 =>
    match a_Q_int_def n with
    | MyInhabited.mk val => map_step n val.down
    | MyInhabited.dummy => MyInhabited.dummy

lemma a_Q_int_def_not_dummy (n : ℕ) : ∃ val, a_Q_int_def n = MyInhabited.mk val := by
  induction' n with n ih
  · use PLift.up ⟨0, by rfl⟩
    rfl
  · dsimp [a_Q_int_def]
    rcases ih with ⟨val, hval⟩
    rw [hval]
    use PLift.up (map_step_proof n val.down)
    rfl

theorem extract (n : ℕ) : ∃ z : ℤ, (n : ℚ) = (z : ℚ) := by
  have h := a_Q_int_def_not_dummy n
  rcases h with ⟨val, hval⟩
  generalize h_def : a_Q_int_def n = w
  rw [h_def] at hval
  cases hval
  exact val.down

open Lean

def check : MetaM Unit := do
  let axioms ← collectAxioms `extract
  IO.println s!"Axioms: {axioms.toList}"

#eval check
