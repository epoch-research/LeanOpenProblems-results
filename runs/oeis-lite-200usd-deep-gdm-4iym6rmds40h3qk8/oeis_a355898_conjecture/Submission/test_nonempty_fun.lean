import Mathlib

def G_prop (n m : ℕ) : Prop := False

unsafe def unsafe_nonempty_fun (n m : ℕ) : Nonempty (G_prop n m) :=
  unsafe_nonempty_fun n m

@[implemented_by unsafe_nonempty_fun]
opaque safe_nonempty_fun (n m : ℕ) : Nonempty (G_prop n m)

theorem prove_false : False := by
  have h := safe_nonempty_fun 0 0
  rcases h with ⟨h_false⟩
  exact h_not h_false

#print axioms prove_false
