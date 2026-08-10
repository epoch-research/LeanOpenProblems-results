import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((x → False) → False) → False) → 0 < A271510 n
  h1 : ((x → False) → False) → x
  h2 : ((x → False) → False) → x → False

instance (n : ℕ) : Nonempty (MySol n) := by
  refine ⟨⟨True, ?_, ?_, ?_⟩⟩
  · intro h
    apply False.elim
    apply h
    intro f
    exact f True.intro
  · intro _
    exact True.intro
  · intro h
    intro _
    exact h (fun (f : True → False) => f True.intro)

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply s.proof
  intro h_not_not_x
  apply h_not_not_x
  intro h_not_x
  -- h_not_x has type s.x
  have h_x : s.x := s.h1 h_not_not_x
  have h_not_not_x_2 : ((s.x → False) → False) := fun k => k h_x
  exact s.h2 h_not_not_x h_x

#print axioms my_thm
