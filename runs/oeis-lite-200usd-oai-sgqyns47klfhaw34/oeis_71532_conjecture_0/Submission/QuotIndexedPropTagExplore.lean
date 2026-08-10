import FormalConjectures.Util.ProblemImports

namespace QuotIndexedPropTagExplore

def Q := Quot (fun (_ _ : Bool) => True)

inductive I : Q → Prop where
| left : I (Quot.mk _ false)
| right : I (Quot.mk _ true)

def leftAtTrue : I (Quot.mk _ true) := by
  have h : Quot.mk (fun (_ _ : Bool) => True) false = Quot.mk _ true := Quot.sound trivial
  exact h ▸ I.left

-- Prop-valued recursor distinguishing constructors.
def tag {q : Q} (i : I q) : Prop :=
  I.rec (motive := fun q i => Prop) False True i

#reduce tag I.left
#reduce tag I.right
#reduce tag leftAtTrue

example : tag I.left = False := rfl
example : tag I.right = True := rfl
-- Is transported left's tag reducible to False?
example : tag leftAtTrue = False := by
  unfold leftAtTrue tag
  -- try simp/reduce
  rfl

-- If yes, proof irrelevance yields contradiction.
theorem bad : False := by
  have e : leftAtTrue = I.right := Subsingleton.elim _ _
  have ht : tag leftAtTrue = tag I.right := congrArg tag e
  have hl : tag leftAtTrue = False := by
    unfold leftAtTrue tag
    rfl
  have hr : tag I.right = True := rfl
  rw [hl, hr] at ht
  exact false_of_true_eq_false ht.symm

#print axioms leftAtTrue
#print axioms tag
#print axioms bad
end QuotIndexedPropTagExplore
