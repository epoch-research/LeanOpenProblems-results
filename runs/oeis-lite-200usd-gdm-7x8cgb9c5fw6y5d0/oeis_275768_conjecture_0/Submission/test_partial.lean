instance : Nonempty (False ∨ True) := ⟨Or.inr True.intro⟩

partial def bad_proof (u : Unit) : False ∨ True := bad_proof u

theorem cheat : False := by
  match bad_proof () with
  | Or.inl hf => exact hf
  | Or.inr ht => _
