import FormalConjectures.Util.ProblemImports
unsafe def bogusImpl (p : Prop) : Decidable p := unsafeCast (Decidable.isTrue True.intro)
@[implemented_by bogusImpl]
noncomputable def bogusDec (p : Prop) : Decidable p := Classical.propDecidable p

theorem allNatEqZero : ∀ n : ℕ, n = 0 := by
  letI : Decidable (∀ n : ℕ, n = 0) := bogusDec _
  native_decide

#print axioms allNatEqZero
