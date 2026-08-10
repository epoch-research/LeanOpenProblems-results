open Classical

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

noncomputable def f (X : Type) : T :=
  if X = Empty then
    T.base
  else
    T.mk (fun Y =>
      sorry
    )
