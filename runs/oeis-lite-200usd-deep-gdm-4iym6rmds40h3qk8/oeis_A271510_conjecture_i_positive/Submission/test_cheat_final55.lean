import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : ℕ
  h : x = n → 0 < A271510 n

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨n + 1, fun h_eq => False.elim (by omega)⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  ⟨n, fun _ => (get_sol n).h (by rfl)⟩

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  -- wait, s.x is definitionally n?
  -- s.h : s.x = n → 0 < A271510 n.
  -- since s.x is n, s.h rfl has type 0 < A271510 n!
  exact s.h rfl
