import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

noncomputable def A092243 (n : ℕ) : ℤ :=
  let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i
  let G_gap (k : ℕ) : ℕ := P k - P (k - 1)
  if n = 0 then 0
  else if n = 1 then 0
  else
  (Finset.Icc 2 n).sum fun k : ℕ =>
    let Gk   : ℕ := G_gap k
    let Gkm1 : ℕ := G_gap (k - 1)
    ((Gk : ℤ) - (Gkm1 : ℤ)) |>.sign

structure OEIS_A092243_Conjectures where
  positive_after_large_n : ∃ n : ℕ, n > 250000 ∧ A092243 n > 0
  bounded_below : ∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n
  bounded_above : ∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B
  infinitely_positive : Set.Infinite {n : ℕ | A092243 n > 0}
  infinitely_negative : Set.Infinite {n : ℕ | A092243 n < 0}

lemma A092243_succ (n : ℕ) (hn : n ≥ 1) :
    A092243 (n + 1) = A092243 n +
      let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i
      let G_gap (k : ℕ) : ℕ := P k - P (k - 1)
      ((G_gap (n + 1) : ℤ) - (G_gap n : ℤ)).sign := by
  unfold A092243
  rcases n with _ | n
  · contradiction
  rcases n with _ | n
  · simp
  · simp
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp

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
  simp [nth_prime_five_eq_thirteen]


theorem test_sign_pos : (5 : ℤ).sign = 1 := by rfl
theorem test_sign_neg : (-5 : ℤ).sign = -1 := by rfl
theorem test_sign_zero : (0 : ℤ).sign = 0 := by rfl

theorem nth_prime_six_eq_seventeen : Nat.nth Nat.Prime 6 = 17 := by
  have : Nat.count Nat.Prime 17 = 6 := by decide
  rw [← this]
  apply Nat.nth_count
  decide

theorem a_six : A092243 6 = 2 := by
  rw [A092243_succ 5 (by omega)]
  rw [a_five]
  simp [nth_prime_five_eq_thirteen, nth_prime_six_eq_seventeen]
  decide

noncomputable def P_prime (i : ℕ) : ℕ := Nat.nth Nat.Prime i
noncomputable def G_gap (k : ℕ) : ℕ := P_prime k - P_prime (k - 1)

lemma G_gap_eq (k : ℕ) : G_gap k = Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1) := rfl

theorem G_gap_zero : G_gap 0 = 0 := by
  simp [G_gap, P_prime]

theorem G_gap_one : G_gap 1 = 1 := by
  simp [G_gap, P_prime]

lemma G_gap_unbounded_int (B : ℤ) : ∃ n, (G_gap n : ℤ) > B := by sorry

lemma gap_bound_of_score_bound (B : ℤ) (h_score : ∀ n, A092243 n ≤ B) (n : ℕ) (hn : n ≥ 2) : (G_gap n : ℤ) ≤ 2 * B + 8 := by sorry

theorem oeis_92243_conjecture.disproof : ¬ OEIS_A092243_Conjectures := by
  intro h
  rcases h.bounded_above with ⟨B, h_score⟩
  obtain ⟨n, hn_unbdd⟩ := G_gap_unbounded_int (max (2 * B + 8) 1)
  have hn_ge_2 : n ≥ 2 := by
    by_contra! hn_lt_2
    interval_cases n
    · have : G_gap 0 = 0 := G_gap_zero
      omega
    · have : G_gap 1 = 1 := G_gap_one
      omega
  have hg := gap_bound_of_score_bound B h_score n hn_ge_2
  omega
#print axioms oeis_92243_conjecture.disproof
