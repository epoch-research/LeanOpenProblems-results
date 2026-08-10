import FormalConjectures.Util.ProblemImports

lemma carry_index_ge_of_ge_a_two (n : ℕ) (hn : n ≠ 0) (t : ℕ) (ht : t ≥ a n)
  (h_le : a (n + 1) ≤ a n + 2)
  (m : ℕ) (hm : S t (n + 2) = add_at (S t (n + 1)) m) :
  m + 2 ≥ n := by
  have h_diff : t = a n + (t - a n) := by omega
  generalize hk : t - a n = k
  rw [h_diff] at hm
  induction k generalizing t m with
  | zero =>
    have h_eq_t : t = a n := by omega
    subst h_eq_t
    simp at hm
    rcases S_add_at_index_le (n + 1) (a n) (by omega) with ⟨m_0, hm_0_le, hm_0⟩
    have hm_eq : m = m_0 := by
      apply add_at_injective (S (a n) (n + 1)) m m_0
      rw [hm, hm_0]
    subst hm_eq
    have h_stable : S (a n) n = replicate n 1 := by
      have h_a_eq : a n = sInf {k | S k n = replicate n 1} := a_eq_sInf n hn
      rw [h_a_eq]
      exact Nat.sInf_mem (S_set_nonempty n hn)
    rcases S_add_at_index_le n (a n) hn with ⟨i_prev, hi_prev_le, hi_prev⟩
    have h_i_prev_ge : i_prev + 2 ≥ n := by
      have h_nonempty : {k | S k n = replicate n 1}.Nonempty := S_set_nonempty n hn
      have h_nonempty2 : {k | S k (n + 1) = replicate (n + 1) 1}.Nonempty := S_set_nonempty (n + 1) (by omega)
      apply index_ge_of_a_le n (a n) hn rfl h_nonempty h_nonempty2 h_le i_prev
      rw [hi_prev, h_stable]
    -- Wait, if m_0 < n - 2:
    have h_cases : m_0 + 2 ≥ n ∨ m_0 + 2 < n := by omega
    rcases h_cases with h_ge | h_lt
    · exact h_ge
    · -- We want to get a contradiction from h_lt : m_0 + 2 < n
      sorry
  | succ k ih =>
    rcases S_add_at_index_le (n + 1) (a n + k) (by omega) with ⟨m_k, hm_k_le, hm_k⟩
    have h_stable : S (a n + k) (n + 1) = replicate (n + 1) 1 := by
      -- Wait, S (a n + k) (n + 1) is not stable at a n + k
      sorry

