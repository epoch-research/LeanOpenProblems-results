import FormalConjectures.Util.ProblemImports

namespace QuotIndexedTwoCtorExplore

def Q := Quot (fun (_ _ : Bool) => True)

inductive I : Q → Prop where
| left : I (Quot.mk _ false)
| right : I (Quot.mk _ true)

-- transport left to true index
def leftAtTrue : I (Quot.mk _ true) := by
  have h : Quot.mk (fun (_ _ : Bool) => True) false = Quot.mk _ true := Quot.sound trivial
  exact h ▸ I.left

-- Since I true is Prop, leftAtTrue = right by proof irrelevance.
theorem eqProof : leftAtTrue = I.right := proof_irrel_heq _ _ |> heq_eq_eq.mp

-- Try noConfusion / cases on equality to derive False.
theorem bad1 : False := by
  unfold leftAtTrue at eqProof
  -- direct cases?
  have e := eqProof
  cases e

-- Try noConfusion explicitly.
#check I.noConfusion

theorem bad2 : False := by
  have hidx : (Quot.mk (fun (_ _ : Bool) => True) true) = Quot.mk _ true := rfl
  have heq : (I.right : I (Quot.mk _ true)) ≍ leftAtTrue := by exact HEq.symm (heq_of_eq eqProof)
  -- noConfusionType may be False for different constructors?
  exact I.noConfusion hidx heq

#print axioms leftAtTrue
#print axioms eqProof
#print axioms bad1
#print axioms bad2
end QuotIndexedTwoCtorExplore
