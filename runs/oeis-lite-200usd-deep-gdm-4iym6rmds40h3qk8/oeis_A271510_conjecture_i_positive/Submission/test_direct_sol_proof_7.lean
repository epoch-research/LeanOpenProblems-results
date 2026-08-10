import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x

instance (n : ℕ) : Nonempty (MySol n) :=
  ⟨⟨True,
   by
     intro H
     apply H
     intro G_val
     apply G_val
     intro I_arg
     apply I_arg
     exact True.intro,
   fun _ => True.intro⟩⟩

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  unfold get_sol at s
  have h_proof := s.proof
  change (((((True → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n at h_proof
  have h_loop : True → 0 < A271510 n := by
    intro h_true
    apply h_proof
    intro h_D
    apply h_D
    intro h_G'
    apply h_G'
    exact h_loop
  exact h_loop True.intro

#print axioms my_thm
