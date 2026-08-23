import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- g(c, d) = c^4 + 4d^4 + c^2 d^2 -/
def g (c d : ℕ) : ℕ := c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2

theorem g_eq (c d : ℕ) : g c d = c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 := rfl

/-- The form we study. -/
def F (x y c d : ℕ) : ℕ := x ^ 2 + 2 * y ^ 2 + g c d

lemma F_eq (x y c d : ℕ) :
    F x y c d = x ^ 2 + 2 * y ^ 2 + c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 := by
  simp [F, g]; ring

/-- Nonnegativity of each term implies variables are at most `sqrt n`. -/
lemma le_sqrt_of_sq_le {a n : ℕ} (h : a ^ 2 ≤ n) : a ≤ sqrt n :=
  le_sqrt_of_le_sq h

lemma exists_of_pos_a {n : ℕ} (h : 0 < a n) :
    ∃ x y c d : ℕ, x ^ 2 + 2 * y ^ 2 + c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 = n := by
  simp only [a] at h
  set R := range (sqrt n + 1)
  set S := R.product (R.product (R.product R))
  have : (S.filter (fun p =>
      p.1 ^ 2 + 2 * p.2.1 ^ 2 + p.2.2.1 ^ 4 + 4 * p.2.2.2 ^ 4 +
        p.2.2.1 ^ 2 * p.2.2.2 ^ 2 = n)).card > 0 := h
  obtain ⟨p, hp⟩ := card_pos.mp this
  simp only [mem_filter] at hp
  exact ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, hp.2⟩

lemma pos_a_of_exists {n : ℕ} {x y c d : ℕ}
    (h : x ^ 2 + 2 * y ^ 2 + c ^ 4 + 4 * d ^ 4 + c ^ 2 * d ^ 2 = n) :
    0 < a n := by
  have hx : x ≤ sqrt n := le_sqrt_of_sq_le (by omega)
  have hy : y ≤ sqrt n := by
    have : 2 * y ^ 2 ≤ n := by omega
    have : y ^ 2 ≤ n := le_trans (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2)) this
    exact le_sqrt_of_sq_le this
  have hc : c ≤ sqrt n := by
    have : c ^ 4 ≤ n := by omega
    have : c ^ 2 ≤ c ^ 4 ∨ c ≤ 1 := by
      cases c with
      | zero => simp
      | succ c =>
        cases c with
        | zero => simp
        | succ c =>
          left
          rw [pow_succ, pow_succ, pow_two]
          exact Nat.mul_le_mul_left _ (by nlinarith)
    sorry
  sorry
