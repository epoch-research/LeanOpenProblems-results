import FormalConjectures.Util.ProblemImports

namespace QuotIndexedPropMotiveExplore

def Q := Quot (fun (_ _ : Bool) => True)

inductive I : Q → Prop where
| left : I (Quot.mk _ false)
| right : I (Quot.mk _ true)

def leftAtTrue : I (Quot.mk _ true) := by
  have h : Quot.mk (fun (_ _ : Bool) => True) false = Quot.mk _ true := Quot.sound trivial
  exact h ▸ I.left

-- Various motives to see if recursor can prove contradictory properties for transported left.
example : (leftAtTrue = I.right → False) → False := by
  intro h
  exact h (Subsingleton.elim _ _)

-- Can recursor prove leftAtTrue ≠ right? Need cases.
example : leftAtTrue ≠ I.right := by
  intro e
  -- Try induction on leftAtTrue with motive being inequality to right.
  induction leftAtTrue with
  | left =>
      -- goal? likely impossible equation of quotient indices blocks
      simp
  | right => exact e rfl

end QuotIndexedPropMotiveExplore
