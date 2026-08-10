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

lemma A092243_succ (n : ℕ) (hn : n ≥ 1) :
    A092243 (n + 1) = A092243 n + ((G_gap (n + 1) : ℤ) - (G_gap n : ℤ)).sign := by
  unfold A092243
  rcases n with _ | n
  · contradiction
  rcases n with _ | n
  · simp [G_gap, P_prime]
  · simp
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp [G_gap, P_prime]

theorem G_gap_two : G_gap 2 = 2 := by
  simp [G_gap, P_prime]

