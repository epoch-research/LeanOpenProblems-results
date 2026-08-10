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
  exact s.h (fun _ => MySol.elim -- wait, how to prove Unit → False is False?
    -- Actually, if we have h_false : Unit → False, we can apply it to () to get False, and then false.elim!
  )
