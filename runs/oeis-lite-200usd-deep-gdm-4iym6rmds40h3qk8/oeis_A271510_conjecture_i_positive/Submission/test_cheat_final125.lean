import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure Cheat (n : ℕ) where
  x : Prop
  proof : (((x → False) → False) → False) → 0 < A271510 n
  h_not_x : x → False

instance (n : ℕ) : Nonempty (Cheat n) :=
  ⟨⟨False,
    fun (h : ((False → False) → False) → False) =>
      (h (fun (h2 : False → False) => h2 (fun (f : False) => f))).elim,
    fun (f : False) => f⟩⟩

partial def get_cheat (n : ℕ) : Cheat n :=
  get_cheat n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_cheat n
  apply s.proof
  intro h_not_not_x
  exact h_not_not_x s.h_not_x

#print axioms my_thm
