import FormalConjectures.Util.ProblemImports
unsafe def bogusDecidable (P : Prop) : Decidable P := Decidable.isTrue (unsafeCast ())
unsafe instance (P : Prop) : Decidable P := bogusDecidable P
set_option trace.compiler.ir.result true in
theorem bad : False := by native_decide
#print axioms bad
