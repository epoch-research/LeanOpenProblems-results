import FormalConjectures.Util.ProblemImports

-- Attempted quotient/proof-irrelevance paradox diagnostic.

def alpha : Prop := True ∨ True

def rel (P : Prop) (x y : alpha) : Prop :=
  Or.elim x
    (fun _ => Or.elim y (fun _ => True) (fun _ => P))
    (fun _ => Or.elim y (fun _ => P) (fun _ => True))

instance setoidRel (P : Prop) : Setoid alpha where
  r := rel P
  iseqv := by
    constructor
    · intro x
      cases x <;> simp [rel]
    · intro x y h
      cases x <;> cases y <;> simp [rel] at h ⊢
      exact h
    · intro x y z hxy hyz
      cases x <;> cases y <;> cases z <;> simp [rel] at hxy hyz ⊢
      all_goals assumption

theorem arbitrary (P : Prop) : P := by
  let a : alpha := Or.inl True.intro
  let b : alpha := Or.inr True.intro
  have hq : (Quotient.mk' a : Quotient (setoidRel P)) = Quotient.mk' b := by
    -- if quotient over Prop is Prop, proof irrelevance may prove this
    apply Subsingleton.elim
  have hr := Quotient.exact hq
  change rel P a b at hr
  simpa [a,b,rel] using hr

#print axioms arbitrary
example : False := arbitrary False
