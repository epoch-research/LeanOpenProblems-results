import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x

noncomputable def get_sol (n : ℕ) : MySol n :=
  ⟨True,
   by
     intro H
     apply H
     intro G_val
     apply G_val
     intro I_arg
     apply I_arg
     exact True.intro,
   fun _ => True.intro⟩

#print get_sol
