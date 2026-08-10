import FormalConjectures.Util.ProblemImports

open Finset

lemma sum_range_sq_subtraction_free (m : ℕ) :
    6 * (∑ i ∈ range (m + 1), i ^ 2) = m * (m + 1) * (2 * m + 1) := by
  induction' m with m ih
  · simp
  · rw [sum_range_succ, mul_add, ih]
    ring

lemma div_mul_cancel_H (H X : ℕ) (hH : 0 < H) :
    4 * (X / (4 * H)) = X / H - (X % (4 * H)) / H := by
  have h_id : X = (X / (4 * H) * 4) * H + X % (4 * H) := by
    have h1 := (Nat.div_add_mod X (4 * H)).symm
    have h2 : 4 * H * (X / (4 * H)) = (X / (4 * H) * 4) * H := by ring
    rw [h2] at h1
    exact h1
  have h_div_H : X / H = X / (4 * H) * 4 + (X % (4 * H)) / H := by
    conv_lhs => rw [h_id]
    have h_comm : (X / (4 * H) * 4) * H + X % (4 * H) = X % (4 * H) + (X / (4 * H) * 4) * H := by ring
    rw [h_comm]
    have h_comm2 : (X / (4 * H) * 4) * H = H * (X / (4 * H) * 4) := by ring
    rw [h_comm2]
    rw [Nat.add_mul_div_left (X % (4 * H)) (X / (4 * H) * 4) hH]
    omega
  omega

lemma div_ge_quadratic_even (H d : ℕ) (hH : 4 ≤ H) :
    4 * ((H + d) ^ 2 / (4 * H)) ≥ d ^ 2 / H + 2 * d + H - 3 := by
  have hH_pos : 0 < H := by omega
  rw [div_mul_cancel_H H ((H + d) ^ 2) hH_pos]
  have h_div_H : (H + d) ^ 2 / H = H + 2 * d + d ^ 2 / H := by
    have h1 : (H + d) ^ 2 = d ^ 2 + H * (H + 2 * d) := by ring
    conv_lhs => rw [h1]
    have h2 := Nat.add_mul_div_left (d ^ 2) (H + 2 * d) hH_pos
    rw [h2]
    omega
  rw [h_div_H]
  have h_mod_div : ((H + d) ^ 2) % (4 * H) / H ≤ 3 := by
    have h_equiv : ((H + d) ^ 2) % (4 * H) / H ≤ 3 ↔ ((H + d) ^ 2) % (4 * H) / H < 4 := by omega
    rw [h_equiv]
    rw [Nat.div_lt_iff_lt_mul hH_pos]
    have h1 : ((H + d) ^ 2) % (4 * H) < 4 * H := Nat.mod_lt _ (by omega)
    exact h1
  omega

lemma div_ge_universal (H X : ℕ) (hH : 0 < H) :
    4 * (X / (4 * H)) ≥ X / H - 3 := by
  rw [div_mul_cancel_H H X hH]
  have h_mod : (X % (4 * H)) / H ≤ 3 := by
    have h_equiv : (X % (4 * H)) / H ≤ 3 ↔ (X % (4 * H)) / H < 4 := by omega
    rw [h_equiv]
    rw [Nat.div_lt_iff_lt_mul hH]
    exact Nat.mod_lt _ (by omega)
  omega

lemma first_half_sum_bound (H : ℕ) (hH : 1 ≤ H) :
    6 * (∑ k ∈ range H, k ^ 2 / H) + 9 * H ≥ 2 * H ^ 2 + 7 := by
  have hH_pos : 0 < H := by omega
  have h_term : ∀ k ∈ range H, k ^ 2 ≤ H * (k ^ 2 / H) + (H - 1) := by
    intro k hk
    have h_mod := Nat.div_add_mod (k ^ 2) H
    have h_lt := Nat.mod_lt (k ^ 2) hH_pos
    omega
  have h_sum := sum_le_sum h_term
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at h_sum
  rw [← mul_sum] at h_sum
  have h_sum_sq : 6 * (∑ k ∈ range H, k ^ 2) = (H - 1) * H * (2 * H - 1) := by
    have h_eq : range H = range (H - 1 + 1) := by
      congr
      omega
    rw [h_eq]
    rw [sum_range_sq_subtraction_free (H - 1)]
    have h_sub : 1 ≤ H := hH
    have h_sub2 : 1 ≤ 2 * H := by omega
    zify [h_sub, h_sub2]
    ring
  have h_sum6 : 6 * (∑ k ∈ range H, k ^ 2) ≤ 6 * (H * (∑ k ∈ range H, k ^ 2 / H) + H * (H - 1)) := Nat.mul_le_mul_left 6 h_sum
  rw [h_sum_sq] at h_sum6
  have h_sub1 : 1 ≤ H := hH
  have h_sub2 : 1 ≤ 2 * H := by omega
  zify [h_sub1, h_sub2] at h_sum6 ⊢
  nlinarith

lemma sum_split_half (H : ℕ) (f : ℕ → ℕ) :
    ∑ k ∈ range (2 * H), f k = (∑ k ∈ range H, f k) + (∑ d ∈ range H, f (H + d)) := by
  have h_eq : 2 * H = H + H := by ring
  nth_rw 1 [h_eq]
  exact sum_range_add f H H


lemma S_even_bound_new_improved (H : ℕ) (hH : 25 ≤ H) :
    8 * H ^ 2 - 18 * H + 4 ≤ 12 * (∑ k ∈ range (2 * H), k ^ 2 / (4 * H)) := by
  have hH_pos : 0 < H := by omega
  rw [sum_split_half H (fun k => k ^ 2 / (4 * H))]
  rw [add_comm, mul_add]
  have h_term1 : ∀ d ∈ range H, 12 * ((H + d) ^ 2 / (4 * H)) + 9 ≥ 3 * (d ^ 2 / H) + 6 * d + 3 * H := by
    intro d hd
    have h_quad := div_ge_quadratic_even H d (by omega)
    omega
  have h_term2 : ∀ k ∈ range H, 12 * (k ^ 2 / (4 * H)) + 9 ≥ 3 * (k ^ 2 / H) := by
    intro k hk
    have h_univ := div_ge_universal H (k ^ 2) hH_pos
    omega
  have h_sum1 := sum_le_sum h_term1
  have h_sum2 := sum_le_sum h_term2
  simp_rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum] at h_sum1 h_sum2
  have h_pull : ∑ x ∈ range H, 6 * x = 6 * (∑ x ∈ range H, x) := by rw [← mul_sum]
  rw [h_pull] at h_sum1
  have h_id_sum : 2 * (∑ d ∈ range H, d) = H * (H - 1) := by
    have h := sum_range_id_mul_two H
    omega
  have h_half := first_half_sum_bound H (by omega)
  have h_sub1 : 1 ≤ H := by omega
  have h_sub2 : 1 ≤ H - 1 := by omega
  have hH_sub : 18 * H ≤ 8 * H ^ 2 := by nlinarith
  have h_cast3 : ((8 * H ^ 2 - 18 * H : ℕ) : ℤ) = 8 * (H : ℤ) ^ 2 - 18 * (H : ℤ) := by
    rw [Nat.cast_sub hH_sub]
    push_cast
    rfl
  zify [h_sub1, h_sub2] at hH h_sum1 h_sum2 h_id_sum h_half ⊢
  rw [h_cast3]
  nlinarith
