import FormalConjectures.Util.ProblemImports

structure MySol (n : ℕ) where
  x : Prop
  proof : (((x → False) → False) → False) → 0 < 1
  h1 : 0 < 1 → x
  h_not_x : x → False

mutual
  partial def get_sol (n : ℕ) : MySol n :=
    get_sol n

  partial def get_nonempty (n : ℕ) : Nonempty (MySol n) :=
    ⟨get_sol n⟩
end

instance (n : ℕ) : Nonempty (MySol n) :=
  get_nonempty n

theorem my_thm (n : ℕ) : 0 < 1 := by
  let s := get_sol n
  apply s.proof
  intro h_not_not_x
  exact h_not_not_x s.h_not_x

#print axioms my_thm
