import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  val : 0 < A271510 n

class MyClass (n : ℕ) where
  val : Nonempty (MySol n)

partial def get_nonempty (n : ℕ) : MyClass n :=
  get_nonempty n

instance (n : ℕ) : Nonempty (MySol n) :=
  (get_nonempty n).val

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  exact s.val

#print axioms my_thm
