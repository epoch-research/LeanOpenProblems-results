import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : ℕ
  val : 0 < A271510 x
  h : ¬ (4 ∣ x) → x = n

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨0, by decide, fun h => False.elim (h (by use 0; rfl))⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) (hn : ¬ (4 ∣ n)) : 0 < A271510 n := by
  let s := get_sol n
  have h1 : s.x = n := s.h hn
  rw [← h1]
  exact s.val

#print axioms my_thm
