import FormalConjectures.Util.ProblemImports

def Rb (_ _ : Bool) : Prop := True
def QB : Type := Quot Rb
def qb (b : Bool) : QB := Quot.mk Rb b

inductive I : QB → Type where
| mk : (b : Bool) → I (qb b)

-- Try prove subsingleton of fibers
example (x : QB) : Subsingleton (I x) := by
  constructor
  intro a b
  cases a with
  | mk ba =>
    cases b with
    | mk bb =>
      -- goal mk ba = mk bb? with index equations maybe not
      cases ba <;> cases bb <;> rfl

-- If succeeds, contradiction
example : False := by
  have ss : Subsingleton (I (qb true)) := by
    constructor
    intro a b
    cases a with
    | mk ba =>
      cases b with
      | mk bb =>
        cases ba <;> cases bb <;> rfl
  have h : I.mk true = (show I (qb true) from (Quot.sound (show Rb false true from trivial)) ▸ I.mk false) := Subsingleton.elim _ _
  -- not directly noConfusion maybe transport hides
  cases h
