import FormalConjectures.Util.ProblemImports

lemma add_pow_le_custom (a b L : ℕ) (hL : 1 ≤ L) : a^L + b^L ≤ (a + b)^L := by
  induction L with
  | zero => omega
  | succ L ih =>
    cases L with
    | zero => simp
    | succ L =>
      have h1 : a^(L+2) = a^(L+1) * a := by ring
      have h2 : b^(L+2) = b^(L+1) * b := by ring
      rw [h1, h2]
      have ha : a ≤ a + b := by omega
      have hb : b ≤ a + b := by omega
      have h3 : a^(L+1) * a ≤ a^(L+1) * (a + b) := Nat.mul_le_mul_left (a^(L+1)) ha
      have h4 : b^(L+1) * b ≤ b^(L+1) * (a + b) := Nat.mul_le_mul_left (b^(L+1)) hb
      have h5 : a^(L+2) + b^(L+2) ≤ a^(L+1) * (a + b) + b^(L+1) * (a + b) := by
        -- a^(L+2) = a^(L+1) * a and b^(L+2) = b^(L+1) * b
        rw [h1, h2]
        omega
      have h6 : a^(L+1) * (a + b) + b^(L+1) * (a + b) = (a^(L+1) + b^(L+1)) * (a + b) := by ring
      have ih_spec := ih (by omega)
      have h7 : (a^(L+1) + b^(L+1)) * (a + b) ≤ (a + b)^(L+1) * (a + b) := Nat.mul_le_mul_right (a + b) ih_spec
      have h8 : (a + b)^(L+1) * (a + b) = (a + b)^(L+2) := by ring
      calc
        a^(L+2) + b^(L+2) ≤ a^(L+1) * (a + b) + b^(L+1) * (a + b) := h5
        _ = (a^(L+1) + b^(L+1)) * (a + b) := h6
        _ ≤ (a + b)^(L+1) * (a + b) := h7
        _ = (a + b)^(L+2) := h8

lemma sum_pow_le_sum_pow {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) (L : ℕ) (hL : 1 ≤ L) :
    (∑ k ∈ s, f k ^ L) ≤ (∑ k ∈ s, f k) ^ L := by
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    have : 0^L = 0 := Nat.zero_pow (by omega)
    rw [this]
  · intro x s hx ih
    simp only [Finset.sum_insert hx]
    have h_ih : f x ^ L + (∑ k ∈ s, f k ^ L) ≤ f x ^ L + (∑ k ∈ s, f k) ^ L := by omega
    have h_add := add_pow_le_custom (f x) (∑ k ∈ s, f k) L hL
    omega

