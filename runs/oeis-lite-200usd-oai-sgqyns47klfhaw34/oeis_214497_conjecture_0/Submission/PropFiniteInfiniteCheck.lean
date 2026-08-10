import FormalConjectures.Util.ProblemImports
#synth Fintype Prop
#synth Finite Prop
#synth Infinite Prop
#check Fintype.card Prop
#eval Fintype.card Prop
example : Fintype.card Prop = 2 := by native_decide
-- don't use native_decide in final; just exploring
