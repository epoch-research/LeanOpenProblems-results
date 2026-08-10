import FormalConjectures.Util.ProblemImports

def alwaysTrue (p : Prop) [Decidable p] : Bool := true

def realDecide (p : Prop) [Decidable p] : Bool := decide p
@[implemented_by alwaysTrue]
def evilDecideImpl (p : Prop) [Decidable p] : Bool := realDecide p

#eval evilDecideImpl False
example : evilDecideImpl False = true := by native_decide
-- Can this yield False?
example : False := by
  have h : evilDecideImpl False = true := by native_decide
  change decide False = true at h
  simp at h
