import Submission.Check4

open BigOperators Real Filter Topology

def L_seq (n : ℕ) : ℝ := 5 / (6 * (n : ℝ)^2 + 6 * (n : ℝ))

lemma L_diff_eq (n : ℕ) (hn : 2 ≤ n) : L_seq n - L_seq (n + 1) =
    5 / (3 * (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  unfold L_seq
  have : (n : ℝ) > 0 := by
    have : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    linarith
  field_simp; ring

lemma refined_bound_gt_L_diff (n : ℕ) (hn : 2 ≤ n) :
    (4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
    (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1) >
    L_seq n - L_seq (n + 1) := by
  rw [L_diff_eq n hn]
  have : (n : ℝ) ≥ 2 := by exact_mod_cast hn
  have h_num_pos : 66*(n:ℝ)^4 + 264*(n:ℝ)^3 + 433*(n:ℝ)^2 + 338*(n:ℝ) + 99 > 0 := by positivity
  have h_den_pos : 3 * (18 * (n : ℝ)^9 + 162 * (n : ℝ)^8 + 645 * (n : ℝ)^7 + 1491 * (n : ℝ)^6 + 2210 * (n : ℝ)^5 + 2188 * (n : ℝ)^4 + 1453 * (n : ℝ)^3 + 623 * (n : ℝ)^2 + 154 * (n : ℝ) + 16) > 0 := by positivity
  have h_eq : ((4 * (n : ℝ) + 4) / (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1) +
              (((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) / (3 * ((n : ℝ) + 1)^4 * (2 * (n : ℝ)^2 + 4 * (n : ℝ) + 1)) - 2 / ((n : ℝ) + 1)) -
              5 / (3 * (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
              (66*(n:ℝ)^4 + 264*(n:ℝ)^3 + 433*(n:ℝ)^2 + 338*(n:ℝ) + 99) /
              (3 * (18 * (n : ℝ)^9 + 162 * (n : ℝ)^8 + 645 * (n : ℝ)^7 + 1491 * (n : ℝ)^6 + 2210 * (n : ℝ)^5 + 2188 * (n : ℝ)^4 + 1453 * (n : ℝ)^3 + 623 * (n : ℝ)^2 + 154 * (n : ℝ) + 16)) := by
    field_simp; ring
  rw [← sub_pos, h_eq]
  exact div_pos h_num_pos h_den_pos

def pairing_sum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2

lemma pairing_sum_eq (n : ℕ) : pairing_sum n = ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) / 3 := by
  induction n with
  | zero =>
    unfold pairing_sum
    simp
    ring
  | succ n ih =>
    unfold pairing_sum at ih ⊢
    rw [Finset.sum_range_succ']
    push_cast
    have h_shift : (fun i : ℕ ↦ (2 * ((n : ℝ) + 1) + 1 - 2 * ((i : ℝ) + 1))^2) =
                   (fun i : ℕ ↦ (2 * (n : ℝ) + 1 - 2 * (i : ℝ))^2) := by
      ext i
      ring
    rw [h_shift]
    rw [ih]
    ring
