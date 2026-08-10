import FormalConjectures.Util.ProblemImports

-- A local structure in Type with a proof field: equality is by proof irrelevance if data fields match,
-- but noConfusion should not extract impossible data.
structure SProof where
  p : True

#check SProof.noConfusion
#print SProof.noConfusion

example : False := by
  let a : SProof := ⟨True.intro⟩
  let b : SProof := ⟨True.intro⟩
  have h : a = b := by cases a; cases b; rfl
  -- no contradiction expected
  exact?

-- A structure in Prop with apparent multiple constructors/fields has restricted noConfusion.
structure PStruct : Prop where
  p : True

#check PStruct.noConfusion
#print PStruct.noConfusion

inductive PTwo : Prop where
| a : PTwo
| b : PTwo

#check PTwo.rec
#check PTwo.casesOn
-- no noConfusion expected for Prop inductives
#check PTwo.noConfusion
