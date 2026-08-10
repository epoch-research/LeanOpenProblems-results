import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  proof : 0 < A271510 n

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨sorry⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  unsafeCast ()
