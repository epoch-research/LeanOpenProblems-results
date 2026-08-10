import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check Padic.normedField
#check Padic.instNontriviallyNormedField
#check NormedField.toNormedCommRing
#check NormedField.toField
#check NontriviallyNormedField.toNormedField
