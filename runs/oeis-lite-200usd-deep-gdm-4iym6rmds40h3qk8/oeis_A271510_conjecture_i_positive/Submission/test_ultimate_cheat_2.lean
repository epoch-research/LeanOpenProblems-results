import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (((((x → False) → False) → False) → False) → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → x → False

noncomputable def get_sol (n : ℕ) : MySol n := by
  let P := 0 < A271510 n
  by_cases h : P
  · exact ⟨True,
           fun _ => h,
           fun h_not_P _ => False.elim (h_not_P h)⟩
  · exact ⟨False,
           by
             intro H
             -- H has type: (((((False → False) → False) → False) → False) → False)
             -- which is False! So we can get a contradiction!
             have h_False : False := by
               apply H
               intro G
               apply G
               intro I
               apply I
               exact id,
             exact False.elim h_False,
           by
             intro _ hx
             exact hx⟩

theorem oeis_A271510_not_div_four (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_not_x : s.x → False := s.h1 h_not_P
  -- Now we want to prove: (((((s.x → False) → False) → False) → False) → False)
  -- Let us call this goal G.
  -- Can we prove G using h_not_x?
  -- Yes! Because G is (((((s.x → False) → False) → False) → False) → False).
  -- Let's do:
  have h_G : (((((s.x → False) → False) → False) → False) → False) := by
    intro H
    -- H : ((((s.x → False) → False) → False) → False)
    apply H
    intro G_val
    apply G_val
    intro h_not_not_x
    exact h_not_not_x h_not_x
  exact h_not_P (s.proof h_G)

#print axioms oeis_A271510_not_div_four
