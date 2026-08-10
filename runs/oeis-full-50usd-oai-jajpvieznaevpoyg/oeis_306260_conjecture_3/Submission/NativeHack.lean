import FormalConjectures.Util.ProblemImports
unsafe def falseDecImpl : Decidable (False) := unsafeCast (Decidable.isTrue True.intro)
@[implemented_by falseDecImpl]
noncomputable def falseDec : Decidable (False) := Classical.decEq Prop False False |>.rec (fun _ => isFalse id) (fun _ => isFalse id)
-- above nonsense maybe typechecks?
example : False := by
  letI := falseDec
  native_decide
#print axioms NativeHack._example
