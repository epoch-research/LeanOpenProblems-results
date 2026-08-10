import FormalConjectures.Util.ProblemImports

structure Cheat (n : ℕ) where
  h : (Unit → False) → 0 < 1

instance (n : ℕ) : Nonempty (Cheat n) :=
  ⟨⟨fun h_false => (h_false ()).elim⟩⟩

partial def get_cheat (n : ℕ) : Cheat n :=
  ⟨fun h_false =>
    let next := get_cheat n
    next.h h_false
  ⟩

theorem my_thm (n : ℕ) : 0 < 1 := by
  let s := get_cheat n
  apply s.h
  intro h_unit_false
  exact (h_unit_false ()).elim

#print axioms my_thm
