import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000


open scoped Nat.Prime

theorem primeCounting_succ_le (x : ℕ) : π (x + 1) ≤ π x + 1 := by
  change Nat.primeCounting' (x + 2) ≤ Nat.primeCounting' (x + 1) + 1
  unfold Nat.primeCounting'
  rw [Nat.count_succ]
  split_ifs <;> omega

theorem primeCounting_double_succ_le (x : ℕ) : π (π (x + 1)) ≤ π (π x) + 1 := by
  have h1 : π (x + 1) ≤ π x + 1 := primeCounting_succ_le x
  have h2 : π (π (x + 1)) ≤ π (π x + 1) := Nat.monotone_primeCounting h1
  have h3 : π (π x + 1) ≤ π (π x) + 1 := primeCounting_succ_le (π x)
  exact h2.trans h3

theorem primeCounting_double_add_le (x : ℕ) : ∀ n, π (π (x + n)) ≤ π (π x) + n := by
  intro n
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have h1 : π (π (x + n + 1)) ≤ π (π (x + n)) + 1 := by
      have h_eq : x + n + 1 = (x + n) + 1 := by omega
      rw [h_eq]
      exact primeCounting_double_succ_le (x + n)
    have h2 : π (π (x + n)) + 1 ≤ π (π x) + n + 1 := by omega
    have h_eq2 : x + (n + 1) = x + n + 1 := by omega
    rw [h_eq2]
    omega


theorem primeCounting_double_step_le (k n : ℕ) : π (π ((k + 1) * n)) ≤ π (π (k * n)) + n := by
  have h_eq : (k + 1) * n = k * n + n := by ring
  rw [h_eq]
  exact primeCounting_double_add_le (k * n) n


theorem primeCounting_double_mono : Monotone (fun x => π (π x)) := by
  intro x y hxy
  exact Nat.monotone_primeCounting (Nat.monotone_primeCounting hxy)

def a_test (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

theorem a_pos_1 : a_test 1 > 0 := by decide
theorem a_pos_2 : a_test 2 > 0 := by decide
theorem a_pos_3 : a_test 3 > 0 := by decide
theorem a_pos_4 : a_test 4 > 0 := by decide



theorem discrete_ivt (f : ℕ → ℕ) (h_step : ∀ x, f (x + 1) ≤ f x + 1)
    (a : ℕ) (v : ℕ) : ∀ d, f a ≤ v → v ≤ f (a + d) → ∃ x ∈ Finset.Icc a (a + d), f x = v := by
  intro d
  induction d with
  | zero =>
    intro h1 h2
    simp only [add_zero] at h2
    have h_eq : f a = v := by omega
    use a
    simp [h_eq]
  | succ d ih =>
    intro h1 h2
    by_cases h_le : v ≤ f (a + d)
    · have ih_res := ih h1 h_le
      rcases ih_res with ⟨x, hx, hx_eq⟩
      use x
      simp only [Finset.mem_Icc] at hx ⊢
      refine ⟨⟨hx.1, hx.2.trans (Nat.le_succ _)⟩, hx_eq⟩
    · push_neg at h_le
      have h_step_val := h_step (a + d)
      have h2_simped : v ≤ f (a + d + 1) := by
        have h_eq_assoc : a + (d + 1) = a + d + 1 := by omega
        exact h_eq_assoc ▸ h2
      have h_eq : f (a + d + 1) = v := by omega
      use a + d + 1
      simp only [Finset.mem_Icc]
      refine ⟨by omega, h_eq⟩



set_option maxHeartbeats 10000000

theorem test_f_1440 : π (π 1440) = 49 := by decide

