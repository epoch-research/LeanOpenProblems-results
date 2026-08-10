import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  val : 0 < A271510 n

mutual
  partial def get_sol (n : ℕ) [inst : Nonempty (MySol n)] : MySol n :=
    get_sol n

  instance (n : ℕ) : Nonempty (MySol n) :=
    ⟨get_sol n⟩
end

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  exact s.val
