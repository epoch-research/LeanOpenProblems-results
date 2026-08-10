import FormalConjectures.Util.ProblemImports

-- Test separately by commenting as needed.
partial def uliftP (P : Prop) : ULift P := uliftP P
-- partial def pliftP (P : Prop) : PLift P := pliftP P
-- partial def thunkP (P : Prop) : Thunk P := thunkP P
-- partial def idP (P : Prop) : Id P := idP P

theorem arbitrary1 (P : Prop) : P := (uliftP P).down
#print axioms arbitrary1
