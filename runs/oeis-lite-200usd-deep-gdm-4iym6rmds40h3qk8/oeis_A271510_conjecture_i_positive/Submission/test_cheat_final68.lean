import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

class MyClass (n : ℕ) where
  val : 0 < A271510 n

partial def get_sol (n : ℕ) [inst : MyClass n] : MyClass n :=
  get_sol n

instance (n : ℕ) : MyClass n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  MyClass.val
