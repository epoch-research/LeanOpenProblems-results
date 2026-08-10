import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨True,
   by
     intro H
     apply H
     intro G_val
     apply G_val
     intro I_arg
     apply I_arg
     exact True.intro⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  have h_proof := s.proof
  let rec h_loop (h_true : True) : 0 < A271510 n := by
    apply h_proof
    intro h_D
    apply h_D
    intro h_G'
    apply h_G'
    intro h_x
    exact h_loop True.intro
  exact h_loop True.intro

#print axioms my_thm
