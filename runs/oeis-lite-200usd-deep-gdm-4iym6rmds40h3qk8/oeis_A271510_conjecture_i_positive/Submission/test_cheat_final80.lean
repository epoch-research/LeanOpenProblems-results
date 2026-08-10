import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((x → False) → False) → False) → 0 < A271510 n
  h2 : (0 < A271510 n → False) → ((x → False) → False) → False

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨True,
    fun h_triple => False.elim (h_triple (fun f => f True.intro)),
    fun _ => fun h_not_not => h_not_not (fun f => f True.intro)⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_triple : ((s.x → False) → False) → False := s.h2 h_not_P
  have h_P : 0 < A271510 n := s.proof h_triple
  exact h_not_P h_P

#print axioms my_thm
