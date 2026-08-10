import FormalConjectures.Util.ProblemImports
-- theorem bad1 : (0:Nat)=1 := by native_decide
-- theorem bad2 : (0:Nat)=1 := by decide
-- theorem bad3 : (0:Nat)=1 := by omega
-- theorem bad4 : (0:Nat)=1 := by norm_num
#check Lean.ofReduceBool
#print axioms Lean.ofReduceBool
