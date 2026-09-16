import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ := n
noncomputable def sequence_s_int (z : ℤ) : ℕ := if z < 0 then 0 else a z.toNat

theorem oeis_145062_conjecture_0 :
  ∃ k : ℤ, ∀ n : ℕ, a n = sequence_s_int (n + k) :=
by
  first
  | (use 0; intro n; unfold sequence_s_int; rfl)
  | (use 0; intro n; unfold sequence_s_int; split_ifs <;> omega)
  | (use 0; intro n; unfold sequence_s_int; split_ifs <;> (congr; omega))
  | (use 0; intro n; unfold sequence_s_int; simp)
  | (use 0; intro n; unfold sequence_s_int; simp [Int.toNat_natCast]; rfl)
  | (use 0; intro n; rfl)
  | (use 0; intro n; omega)
