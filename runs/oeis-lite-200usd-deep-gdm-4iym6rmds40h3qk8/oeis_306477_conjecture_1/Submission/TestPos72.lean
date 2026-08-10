inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def R (X Y : Type) : Prop := X = Empty ∧ Y ≠ Empty

theorem acc_R (X : Type) : Acc R X := by
  by_cases h : X = Empty
  · subst h
    apply Acc.intro
    intro y hy
    exact False.elim (hy.2 rfl)
  · apply Acc.intro
    intro y hy
    have hyX : y = Empty := hy.1
    subst hyX
    apply Acc.intro
    intro z hz
    exact False.elim (hz.2 rfl)

theorem wf_R : WellFounded R := WellFounded.intro acc_R

-- Now let's try to define f : Type → T using wf_R!
noncomputable def f (X : Type) : T :=
  if h : X = Empty then
    T.base
  else
    T.mk (fun Y =>
      -- We want to call f Y.
      -- To do so, we need Y to be smaller than X according to R.
      -- R Y X means Y = Empty ∧ X ≠ Empty.
      -- We know X ≠ Empty (from the else branch h).
      -- But Y is any Type! It might not be Empty!
      -- So we can't show Y < X for any Y.
      -- Thus well-founded recursion cannot be directly used for all Y.
      sorry
    )
