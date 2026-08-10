import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

noncomputable def P_prime (i : ℕ) : ℕ := Nat.nth Nat.Prime i
noncomputable def G_gap (k : ℕ) : ℕ := P_prime k - P_prime (k - 1)

noncomputable def A092243 (n : ℕ) : ℤ :=
  if n = 0 then 0
  else if n = 1 then 0
  else
  (Finset.Icc 2 n).sum fun k : ℕ =>
    let Gk   : ℕ := G_gap k
    let Gkm1 : ℕ := G_gap (k - 1)
    ((Gk : ℤ) - (Gkm1 : ℤ)) |>.sign

theorem a_seventy_two : A092243 72 = 4 := by
  decide
