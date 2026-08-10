import FormalConjectures.Util.ProblemImports

open Matrix Nat

noncomputable def fakeIntToRat (z : ℤ) : ℚ :=
  (Denumerable.eqv ℚ).symm (Int.natAbs z)

noncomputable local instance fakeIntCastRat : IntCast ℚ where
  intCast := fakeIntToRat

theorem fake_surj (q : ℚ) : q ∈ Set.range (Int.cast : ℤ → ℚ) := by
  refine ⟨((Denumerable.eqv ℚ) q : ℕ), ?_⟩
  simp [Int.cast, fakeIntCastRat, fakeIntToRat]

#print axioms fake_surj
