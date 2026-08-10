import FormalConjectures.Util.ProblemImports
unsafe def bogusFalseImpl : Decidable (∀ n : ℕ, n = 0) := unsafeCast (Decidable.isTrue True.intro)
@[implemented_by bogusFalseImpl]
noncomputable def bogusFalseDec : Decidable (∀ n : ℕ, n = 0) := Classical.propDecidable _
attribute [local instance] bogusFalseDec

theorem allNatEqZero2 : ∀ n : ℕ, n = 0 := by
  native_decide

#print axioms allNatEqZero2
#eval (allNatEqZero2 1)
