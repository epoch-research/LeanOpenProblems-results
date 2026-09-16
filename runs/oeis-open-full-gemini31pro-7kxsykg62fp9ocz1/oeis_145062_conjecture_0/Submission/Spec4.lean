import FormalConjectures.Util.ProblemImports

noncomputable def sequence_s_int (z : ℤ) : ℕ := z.toNat

example (n : ℕ) : (n:ℤ).toNat = n := Int.toNat_natCast n
