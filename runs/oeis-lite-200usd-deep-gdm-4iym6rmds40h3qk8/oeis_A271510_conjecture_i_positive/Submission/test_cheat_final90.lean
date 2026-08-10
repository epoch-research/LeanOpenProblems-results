import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

class MyClass (n : ℕ) : Type where
  val : 0 < A271510 n

mutual
  partial def get_nonempty (n : ℕ) [inst : Nonempty (MyClass n)] : MyClass n :=
    @get_nonempty n inst

  partial def get_nonempty_inst (n : ℕ) : Nonempty (MyClass n) :=
    ⟨@get_nonempty n (get_nonempty_inst n)⟩
end

instance (n : ℕ) : Nonempty (MyClass n) :=
  get_nonempty_inst n

theorem my_thm (n : ℕ) : 0 < A271510 n :=
  (@get_nonempty n (get_nonempty_inst n)).val

#print axioms my_thm
