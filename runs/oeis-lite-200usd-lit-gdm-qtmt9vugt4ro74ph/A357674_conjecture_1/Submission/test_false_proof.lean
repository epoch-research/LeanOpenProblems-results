import FormalConjectures.Util.ProblemImports

variable (P : Prop) (h_not : ¬ P)

def R (a b : Bool) : Prop :=
  (a = false ∧ b = false) ∨ (a = true ∧ b = true) ∨ P

lemma R_refl (a : Bool) : R P a a := by
  rcases a with rfl | rfl <;> simp [R]

lemma R_symm (a b : Bool) (h : R P a b) : R P b a := by
  rcases a with rfl | rfl <;> rcases b with rfl | rfl <;> simp [R] at * <;> tauto

lemma R_trans (a b c : Bool) (hab : R P a b) (hbc : R P b c) : R P a c := by
  rcases a with rfl | rfl <;> rcases b with rfl | rfl <;> rcases c with rfl | rfl <;> simp [R] at * <;> tauto

def Q : Type := Quot (R P)

open Classical

noncomputable def β (q : Q P) : Prop :=
  if q = Quot.mk (R P) false then True else P

noncomputable def f (a : Bool) : β P (Quot.mk (R P) a) := by
  rcases a with rfl | rfl
  · -- a = false
    have h_false : β P (Quot.mk (R P) false) = True := by
      dsimp [β]
      rw [if_pos rfl]
    exact cast h_false.symm True.intro
  · -- a = true
    -- here q = Quot.mk (R P) true.
    -- If P is false, then we can show Quot.mk (R P) true ≠ Quot.mk (R P) false.
    -- Wait, we need to return something of type β P (Quot.mk (R P) true).
    -- But since β is defined using `if`, we can do by_cases on `Quot.mk (R P) true = Quot.mk (R P) false`.
    by_cases h_eq : Quot.mk (R P) true = Quot.mk (R P) false
    · have h_type : β P (Quot.mk (R P) true) = True := by
        dsimp [β]
        rw [if_pos h_eq]
      exact cast h_type.symm True.intro
    · have h_type : β P (Quot.mk (R P) true) = P := by
        dsimp [β]
        rw [if_neg h_eq]
      -- Now we need a term of type P. But wait, we have ¬ P, not P!
      -- So we can't construct P here unless we can show h_eq is impossible.
      -- But wait! If we have ¬ P, can we show h_eq is impossible?
      -- Yes! Let's see: if we can prove ¬ (Quot.mk (R P) true = Quot.mk (R P) false).
      -- Then the `by_cases` is not needed, we can just prove the negation and use `if_neg`.
      -- But even if we prove the negation, we STILL need a term of type P!
      -- Since we don't have a term of type P, we can't construct it!
      sorry
