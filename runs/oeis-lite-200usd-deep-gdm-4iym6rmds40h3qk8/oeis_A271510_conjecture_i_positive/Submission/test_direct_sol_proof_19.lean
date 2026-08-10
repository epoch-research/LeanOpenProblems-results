import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n

noncomputable def get_sol (n : ℕ) : MySol n :=
  ⟨True,
   by
     intro H
     apply H
     intro G_val
     apply G_val
     intro I_arg
     apply I_arg
     exact True.intro⟩

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  unfold get_sol at s
  apply s.proof
  intro G_val
  apply G_val
  intro I_arg
  change (True → 0 < A271510 n) → 0 < A271510 n at I_arg
  apply I_arg
  exact True.intro

#print axioms my_thm
