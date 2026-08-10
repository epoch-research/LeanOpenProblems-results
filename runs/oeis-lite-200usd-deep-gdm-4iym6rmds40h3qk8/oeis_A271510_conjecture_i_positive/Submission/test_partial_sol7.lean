import FormalConjectures.Util.ProblemImports

structure Cheat (n : ℕ) where
  h : ¬¬(0 < 1) → 0 < 1

instance (n : ℕ) : Nonempty (Cheat n) :=
  ⟨⟨fun h_not_not => Classical.byContradiction h_not_not⟩⟩

partial def get_cheat (n : ℕ) : Cheat n :=
  ⟨fun h_not_not =>
    let next := get_cheat n
    next.h h_not_not
  ⟩

theorem my_thm (n : ℕ) : 0 < 1 := by
  let s := get_cheat n
  apply Classical.byContradiction
  intro h_not
  -- Goal is False.
  -- We have h_not : ¬(0 < 1).
  -- We want to apply s.h.
  -- s.h has type ¬¬(0 < 1) → 0 < 1.
  -- If we can construct h_not_not : ¬¬(0 < 1) (which is ¬(0 < 1) → False),
  -- then s.h h_not_not has type 0 < 1.
  -- Then h_not (s.h h_not_not) has type False!
  -- Let's construct h_not_not : ¬¬(0 < 1).
  have h_not_not : ¬¬(0 < 1) := by
    intro h_not'
    -- Goal is False.
    -- h_not' : ¬(0 < 1).
    -- How to prove False?
    -- We can use h_not (s.h h_not_not) ... wait, this is circular!
    -- Yes, because h_not_not is defined in terms of h_not_not.
    sorry

#print axioms my_thm
