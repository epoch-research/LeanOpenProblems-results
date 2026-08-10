import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 =>
  let an_1 := a (n + 1)
  let an_2 := a n
  if Nat.Prime an_1 ∧ an_1 > 2 then
    an_1 - an_2
  else
    an_1 + an_2

def helper_statement (k : ℕ) : Prop :=
  (∀ m ≤ k + 1, m ≥ 1 → a m ≥ 1) ∧ a k % 2 = (if k % 3 = 0 then 0 else 1) ∧ ¬ (Nat.Prime (a (k + 1)) ∧ a (k + 1) > 2 ∧ Nat.Prime (a (k + 2)) ∧ a (k + 2) > 2)

theorem gcd_sub_helper (m n : ℕ) (h : m ≤ n) : Nat.gcd (n - m) n = Nat.gcd m n := by
  nth_rw 2 [← Nat.sub_add_cancel h]
  rw [add_comm]
  rw [Nat.gcd_add_self_right]
  rw [Nat.gcd_comm]
  rw [Nat.gcd_sub_self_right h]

theorem gcd_consecutive_helper (n : ℕ) (ih : ∀ k < n + 2, helper_statement k)
  (h_cond : Nat.Prime (a (n + 3)) ∧ a (n + 3) > 2 ∧ Nat.Prime (a (n + 4)) ∧ a (n + 4) > 2)
  (ha_n3 : a (n + 3) = a (n + 2) + a (n + 1)) :
  ∀ m ≤ n + 3, Nat.gcd (a (m + 1)) (a m) = 1 := by
  intro m hm
  induction' m using Nat.strong_induction_on with m ih_m
  rcases m with _ | _ | m
  · change Nat.gcd (a 1) (a 0) = 1
    rfl
  · change Nat.gcd (a 2) (a 1) = 1
    rfl
  · -- we are proving Nat.gcd (a (m + 3)) (a (m + 2)) = 1
    -- where m + 2 <= n + 3, so m <= n + 1
    have h_m_le : m ≤ n + 1 := by omega
    have h_ge : (Nat.Prime (a (m + 2)) ∧ a (m + 2) > 2) → a (m + 2) ≥ a (m + 1) := by
      intro hcond
      by_cases hm_eq : m = n + 1
      · subst hm_eq
        rw [ha_n3]
        exact Nat.le_add_right _ _
      · -- m < n + 1, so m <= n
        -- we can use helper (m) which is ih m
        have h_ih_m := ih m (by omega)
        -- since m <= n, we want to show a (m + 2) >= a (m + 1) under hcond
        by_contra h_lt
        have h_prime_n : Nat.Prime (a (m + 1)) ∧ a (m + 1) > 2 := by
          by_contra h_not_pn
          have ha_n1_eq : a (m + 2) = a (m + 1) + a m := by
            have h_eq4 : m + 1 = m + 1 := rfl
            have h_eq3 : m + 2 = m + 2 := rfl
            change (if Nat.Prime (a (m + 1)) ∧ a (m + 1) > 2 then a (m + 1) - a m else a (m + 1) + a m) = a (m + 1) + a m
            split
            · rename_i h_cond_true
              exact False.elim (h_not_pn h_cond_true)
            · rfl
          rw [ha_n1_eq] at h_lt
          omega
        have h_not_p_prev : ¬ (Nat.Prime (a (m + 1)) ∧ a (m + 1) > 2 ∧ Nat.Prime (a (m + 2)) ∧ a (m + 2) > 2) := by
          exact h_ih_m.2.2
        exact h_not_p_prev ⟨h_prime_n.1, h_prime_n.2, hcond.1, hcond.2⟩
    -- now we can prove Nat.gcd (a (m + 3)) (a (m + 2)) = 1
    change Nat.gcd (if Nat.Prime (a (m + 2)) ∧ a (m + 2) > 2 then a (m + 2) - a (m + 1) else a (m + 2) + a (m + 1)) (a (m + 2)) = 1
    split
    · rename_i h_cond_true
      have h_ge_true := h_ge h_cond_true
      rw [gcd_sub_helper (a (m + 1)) (a (m + 2)) h_ge_true]
      rw [Nat.gcd_comm]
      exact ih_m (m + 1) (by omega) (by omega)
    · rw [add_comm]
      rw [Nat.gcd_add_self_left]
      rw [Nat.gcd_comm]
      exact ih_m (m + 1) (by omega) (by omega)

