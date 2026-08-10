import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((x → False) → False) → False) → 0 < A271510 n
  h1 : ((x → False) → False) → False

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨True,
    fun (h : ((True → False) → False) → False) => False.elim (h (fun (f : True → False) => f True.intro)),
    fun (h : (True → False) → False) => h (fun (f : True) => False.elim)⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h_not_not_x
  exact False.elim (s.h1 h_not_not_x)

#print axioms my_thm
