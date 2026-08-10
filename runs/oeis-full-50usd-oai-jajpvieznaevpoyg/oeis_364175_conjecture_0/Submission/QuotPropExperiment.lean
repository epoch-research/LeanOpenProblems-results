import FormalConjectures.Util.ProblemImports

-- Try to collapse propositions through a quotient by the total relation.
def QProp := Quot (fun _ _ : Prop => True)
example : (Quot.mk (fun _ _ : Prop => True) True : QProp) = Quot.mk _ False := Quot.sound trivial

-- Check if there is any built-in injectivity principle (there should not be).
#check Quot.exact
#check Quot.sound
#check Quot.ind
#check Quot.lift
