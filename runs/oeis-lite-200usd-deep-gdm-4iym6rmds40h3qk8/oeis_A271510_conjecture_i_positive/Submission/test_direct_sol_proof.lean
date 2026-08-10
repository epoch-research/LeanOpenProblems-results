import FormalConjectures.Util.ProblemImports

structure MySol where
  x : Prop
  proof : (((((x → False) → False) → False) → False) → False) → False

noncomputable def get_sol : MySol :=
  ⟨True,
   by
     intro H
     apply H
     intro G_val
     apply G_val
     intro I_arg
     apply I_arg
     exact True.intro⟩

theorem prove_false : False := by
  let s := get_sol
  have h_x : s.x := True.intro
  apply s.proof
  intro h_D
  apply h_D
  intro h_G
  exact h_G h_x
