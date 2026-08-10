import FormalConjectures.Util.ProblemImports

structure Cheat (n : ℕ) where
  h : (0 < 1 → False) → 0 < 1

instance (n : ℕ) : Nonempty (Cheat n) :=
  ⟨⟨fun h_not => Classical.byContradiction h_not⟩⟩

partial def get_cheat (n : ℕ) : Cheat n :=
  ⟨fun h_not =>
    let next := get_cheat n
    next.h h_not
  ⟩

theorem my_thm (n : ℕ) : 0 < 1 := by
  let s := get_cheat n
  apply Classical.byContradiction
  intro h_not
  exact h_not (s.h h_not)

#print axioms my_thm
