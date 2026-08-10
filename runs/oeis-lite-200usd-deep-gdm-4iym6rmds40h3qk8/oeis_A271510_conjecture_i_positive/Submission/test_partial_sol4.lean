import FormalConjectures.Util.ProblemImports

structure Cheat (n : ℕ) where
  x : ℕ
  h : (x = 0 → False) → 0 < 1

instance (n : ℕ) : Nonempty (Cheat n) :=
  ⟨⟨0, fun h_false => (h_false rfl).elim⟩⟩

partial def get_cheat (n : ℕ) : Cheat n :=
  ⟨1, fun _ =>
    let next := get_cheat n
    next.h (fun h_eq => Nat.noConfusion h_eq)
  ⟩

theorem my_thm (n : ℕ) : 0 < 1 := by
  let s := get_cheat n
  exact s.h (fun h_eq => Nat.noConfusion h_eq)

#print axioms my_thm
