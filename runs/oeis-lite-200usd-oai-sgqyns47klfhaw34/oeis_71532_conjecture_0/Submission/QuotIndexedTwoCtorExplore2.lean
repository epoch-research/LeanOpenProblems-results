import FormalConjectures.Util.ProblemImports

namespace QuotIndexedTwoCtorExplore2

def Q := Quot (fun (_ _ : Bool) => True)

inductive I : Q → Prop where
| left : I (Quot.mk _ false)
| right : I (Quot.mk _ true)

def leftAtTrue : I (Quot.mk _ true) := by
  have h : Quot.mk (fun (_ _ : Bool) => True) false = Quot.mk _ true := Quot.sound trivial
  exact h ▸ I.left

theorem eqProof : leftAtTrue = I.right := Subsingleton.elim _ _

#check I.rec
#check I.casesOn
#check I.noConfusionType
#check I.noConfusion
#check I.left.injEq

-- Try cases on equality after reverting? 
theorem bad1 : False := by
  have e : leftAtTrue = I.right := eqProof
  -- cases e just rewrites right to leftAtTrue, should not see constructors.
  cases e
  -- goal false remains? maybe no.

#print axioms eqProof
#print axioms bad1
end QuotIndexedTwoCtorExplore2
