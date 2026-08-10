import FormalConjectures.Util.ProblemImports
#check Quot.ind
#check Quot.rec
#check Quot.recOn
#check Quotient.ind
#check Quotient.rec
#check Quotient.recOn
#check Quot.lift
#check Quotient.lift

-- Try to define a non-respecting predicate/function out of Quot to get False.
def qFalse : Quot (fun _ _ : Unit => True) → Prop := by
  intro q
  refine Quot.liftOn q (fun _ => False) ?_
  intro a b h; rfl

-- qFalse is constantly False, not helpful.
example : ¬ ∀ q, qFalse q := by
  intro h
  exact h (Quot.mk _ ())

-- Try relation indexed by a Prop.
def qP (P : Prop) : Quot (fun _ _ : Unit => P) → Prop := by
  intro q
  refine Quot.liftOn q (fun _ => P) ?_
  intro a b h; rfl

example (P : Prop) : (∀ q, qP P q) → P := by
  intro h; exact h (Quot.mk _ ())
