import FormalConjectures.Util.ProblemImports

inductive TwoProofs : Prop where
| left : TwoProofs
| right : TwoProofs

-- All proof constructors are equal.
example : TwoProofs.left = TwoProofs.right := proof_irrel _ _

-- Any equality-based relation cannot distinguish them.
def relEqOr (P : Prop) (a b : TwoProofs) : Prop := a = b ∨ P

example (P : Prop) : relEqOr P TwoProofs.left TwoProofs.right := by
  left; exact proof_irrel _ _

-- Pattern matching on a proposition can only eliminate to Prop, but still cannot produce contradictory
-- cases without already proving the desired proposition. Try defining a discriminator Prop.
def discr (a : TwoProofs) : Prop := TwoProofs.casesOn (motive := fun _ => Prop) a True False

#check discr
#reduce discr TwoProofs.left
#reduce discr TwoProofs.right

example : discr TwoProofs.left := by native_decide
example : ¬ discr TwoProofs.right := by native_decide

example : False := by
  have h : TwoProofs.left = TwoProofs.right := proof_irrel _ _
  have hd : discr TwoProofs.left = discr TwoProofs.right := congrArg discr h
  -- If discr reduced to True/False this would be contradiction. Does it?
  native_decide
