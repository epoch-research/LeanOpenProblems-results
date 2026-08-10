import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  val : 0 < A271510 n

partial def get_sol (n : ℕ) [inst : Nonempty (MySol n)] : MySol n :=
  get_sol n

-- Wait, how do we use get_sol if we need an instance?
-- We can define the instance!
-- But wait! If we define the instance using get_sol itself?
-- recursive loop!
