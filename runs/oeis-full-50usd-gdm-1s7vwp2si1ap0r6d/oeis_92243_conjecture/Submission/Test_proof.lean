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
    A092243 (n + 1) = A092243 n +
      ((G_gap (n + 1) : ℤ) - (G_gap n : ℤ)).sign := by
  unfold A092243
  rcases n with _ | n
  · contradiction
  rcases n with _ | n
  · simp [G_gap, P_prime]
  · simp
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp [G_gap, P_prime]

theorem nth_prime_five_eq_thirteen : Nat.nth Nat.Prime 5 = 13 := by
  have : Nat.count Nat.Prime 13 = 5 := by decide
  rw [← this]
  apply Nat.nth_count
  decide

theorem a_five : A092243 5 = 1 := by
  rw [A092243_succ 4 (by omega)]
  rw [A092243_succ 3 (by omega)]
  rw [A092243_succ 2 (by omega)]
  rw [A092243_succ 1 (by omega)]
  unfold A092243
  simp [nth_prime_five_eq_thirteen, G_gap, P_prime]

theorem nth_prime_six_eq_seventeen : Nat.nth Nat.Prime 6 = 17 := by
  have : Nat.count Nat.Prime 17 = 6 := by decide
  rw [← this]
  apply Nat.nth_count
  decide

theorem a_six : A092243 6 = 2 := by
  rw [A092243_succ 5 (by omega)]
  rw [a_five]
  simp [nth_prime_five_eq_thirteen, nth_prime_six_eq_seventeen, G_gap, P_prime]
  decide

lemma gap_bound_of_score_bound (B : ℤ) (h_score : ∀ n, A092243 n ≤ B) (n : ℕ) (hn : n ≥ 2) : (G_gap n : ℤ) ≤ 2 * B + 8 :=
  sorryAx _ false

