import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n
  h1 : ((((x → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → 0 < A271510 n) → x

instance my_inst (n : ℕ) : Nonempty (MySol n) := by
  let P := 0 < A271510 n
  refine ⟨⟨True, ?_, fun _ => True.intro⟩⟩
  · intro H
    apply H
    intro G_val
    apply G_val
    intro I_arg
    apply I_arg
    exact True.intro

#print axioms my_inst
