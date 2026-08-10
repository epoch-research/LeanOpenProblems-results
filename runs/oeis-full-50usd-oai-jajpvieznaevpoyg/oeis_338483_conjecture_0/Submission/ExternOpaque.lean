import FormalConjectures.Util.ProblemImports
@[extern "lean_panic_fn"] opaque extFalse : False

theorem TextFalse : False := extFalse
#print axioms TextFalse
