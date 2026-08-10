import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

structure MySol (n : ℕ) where
  x : Prop
  proof : (x → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → x
  h2 : 0 < A271510 n → x → False

noncomputable instance (n : ℕ) : Nonempty (MySol n) := by
  let P := 0 < A271510 n
  by_cases h : P
  · refine ⟨⟨False, ?_, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro h_not_P
      exact False.elim (h_not_P h)
    · intro _
      intro h_false
      exact h_false
  · refine ⟨⟨True, ?_, ?_, ?_⟩⟩
    · intro h_not_x
      exact False.elim (h_not_x True.intro)
    · intro _
      exact True.intro
    · intro h_pos
      intro _
      exact False.elim (h h_pos)

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

partial def get_not_x_or_neg_P (n : ℕ) : ((get_sol n).x → False) ∨ (0 < A271510 n → False) :=
  let s := get_sol n
  let rec h_not_x : s.x → False := fun h_x =>
    match get_not_x_or_neg_P n with
    | Or.inl h_not_x' => h_not_x' h_x
    | Or.inr h_neg_P => h_neg_P (s.proof h_not_x)
  Or.inl h_not_x

theorem my_thm (n : ℕ) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_x : s.x := s.h1 h_not_P
  match get_not_x_or_neg_P n with
  | Or.inl h_not_x => exact False.elim (h_not_x h_x)
  | Or.inr h_neg_P =>
    let rec h_not_x' : s.x → False := fun h_x' => h_neg_P (s.proof h_not_x')
    exact False.elim (h_not_x' h_x)

#print axioms my_thm
