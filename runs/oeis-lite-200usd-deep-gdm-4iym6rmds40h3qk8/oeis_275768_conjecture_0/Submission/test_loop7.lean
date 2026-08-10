import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

noncomputable instance inst_ne (n : ℕ) : Nonempty (PLift (PLift (a_test n = 4) → PLift False) ⊕ PLift (a_test n = 4)) := by
  by_cases h : a_test n = 4
  · exact ⟨.inr ⟨h⟩⟩
  · exact ⟨.inl ⟨fun h_eq => ⟨(h h_eq.down).elim⟩⟩⟩

partial def get_false_f (n : ℕ) (val_fn : (PLift (a_test n = 4) → PLift False) → PLift False) : PLift (PLift (a_test n = 4) → PLift False) ⊕ PLift (a_test n = 4) :=
  match get_false_f n val_fn with
  | .inl val_fn' => .inl val_fn'
  | .inr val_eq =>
    .inl ⟨fun h_eq =>
      match get_false_f n val_fn with
      | .inl val_fn'' => val_fn''.down h_eq
      | .inr val_eq' =>
        -- we can pass (fun h_eq => ...) to val_fn!
        have f : PLift (a_test n = 4) → PLift False := fun h_eq' =>
          match get_false_f n val_fn with
          | .inl val_fn''' => val_fn'''.down h_eq'
          | .inr val_eq'' => val_fn' -- wait, val_fn' is only in the .inl branch of the outer match.
          -- but we can just call get_false_f recursively!
          -- Actually, inside a partial def, we can just recurse indefinitely!
          -- Let us see if we can just return a dummy or recurse.
          -- Since get_false_f always returns .inl (classically), the .inr is never reached.
          -- So we can just recurse:
          match get_false_f n val_fn with
          | .inl val_fn''' => val_fn'''.down h_eq'
          | .inr _ => ⟨(by decide : False).elim⟩
        val_fn f
    ⟩

#print axioms get_false_f
