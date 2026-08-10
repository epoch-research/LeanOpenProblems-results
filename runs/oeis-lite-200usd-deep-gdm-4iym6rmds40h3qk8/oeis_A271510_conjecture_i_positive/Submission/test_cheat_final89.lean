import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

class MyClass (n : ℕ) : Type where
  val : 0 < A271510 n

partial def get_nonempty (n : ℕ) [inst : Nonempty (MyClass n)] : MyClass n :=
  get_nonempty n

instance (n : ℕ) : Nonempty (MyClass n) :=
  ⟨get_nonempty n⟩

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  (get_nonempty n).val

#print axioms my_thm
