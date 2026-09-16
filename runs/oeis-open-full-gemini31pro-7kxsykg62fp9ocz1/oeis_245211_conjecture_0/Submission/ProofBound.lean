import Mathlib

open Nat Finset

lemma sum_reflect {p k : ℕ} :
  (∑ j ∈ range (k + 1), (1 : ℚ) / (p ^ (k - j) : ℚ)) =
  (∑ i ∈ range (k + 1), (1 : ℚ) / (p ^ i : ℚ)) := by
  have := sum_range_reflect (fun i => (1 : ℚ) / (p ^ i : ℚ)) (k + 1)
  have h_eq : (fun j => (1 : ℚ) / (p ^ (k + 1 - 1 - j) : ℚ)) = (fun j => (1 : ℚ) / (p ^ (k - j) : ℚ)) := by
    ext j
    have : k + 1 - 1 - j = k - j := by omega
    rw [this]
  rw [h_eq] at this
  exact this

lemma my_geom_sum_eq {p k : ℕ} (hp : 2 ≤ p) :
  (∑ i ∈ range (k + 1), (1 : ℚ) / (p ^ i : ℚ)) =
  (1 - (1 / (p : ℚ)) ^ (k + 1)) / (1 - 1 / (p : ℚ)) := by
  have h_eq : (fun i => (1 : ℚ) / (p ^ i : ℚ)) = (fun i => (1 / (p : ℚ)) ^ i) := by
    ext i
    rw [div_pow, one_pow]
  rw [sum_congr rfl (fun i _ => congr_fun h_eq i)]
  have hp_ne : (1 / (p : ℚ)) ≠ 1 := by
    intro h
    have : (1 : ℚ) = (p : ℚ) := (div_eq_one_iff_eq (by positivity)).mp h
    have hp_le : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  have h_geom := geom_sum_eq hp_ne (k + 1)
  rw [h_geom]
  have h_sub1 : ((1 / (p : ℚ)) ^ (k + 1) - 1) = - (1 - (1 / (p : ℚ)) ^ (k + 1)) := by ring
  have h_sub2 : ((1 / (p : ℚ)) - 1) = - (1 - 1 / (p : ℚ)) := by ring
  rw [h_sub1, h_sub2, neg_div_neg_eq]

lemma geom_sum_bound {p k : ℕ} (hp : 2 ≤ p) :
  (∑ j ∈ range (k + 1), (1 : ℚ) / (p ^ (k - j) : ℚ)) < (p : ℚ) / ((p : ℚ) - 1) := by
  rw [sum_reflect, my_geom_sum_eq hp]
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast (by omega)
  have hp_gt1 : (1 : ℚ) < p := by exact_mod_cast (by omega)
  have h_den_pos : (0 : ℚ) < 1 - 1 / (p : ℚ) := by
    have : 1 / (p : ℚ) < 1 := by
      rw [div_lt_iff₀ hp_pos]
      linarith
    linarith
  have h_num_lt : 1 - (1 / (p : ℚ)) ^ (k + 1) < 1 := by
    have : (0 : ℚ) < (1 / (p : ℚ)) ^ (k + 1) := by positivity
    linarith
  have h_lt : (1 - (1 / (p : ℚ)) ^ (k + 1)) / (1 - 1 / (p : ℚ)) < 1 / (1 - 1 / (p : ℚ)) := by
    rw [div_lt_div_iff_of_pos_right h_den_pos]
    exact h_num_lt
  have h_eq : 1 / (1 - 1 / (p : ℚ)) = (p : ℚ) / ((p : ℚ) - 1) := by
    rw [one_div]
    have h_sub : 1 - 1 / (p : ℚ) = ((p : ℚ) - 1) / (p : ℚ) := by
      calc 1 - 1 / (p : ℚ) = (p : ℚ) / (p : ℚ) - 1 / (p : ℚ) := by rw [div_self (by positivity)]
        _ = ((p : ℚ) - 1) / (p : ℚ) := by rw [sub_div]
    rw [h_sub, inv_div]
  rwa [h_eq] at h_lt

lemma S_prime_pow_lt {p k : ℕ} (hp : 2 ≤ p) :
  (∑ j ∈ range (k + 1), ((j + 1 : ℕ) : ℚ) / (p ^ (k - j) : ℚ)) <
  ((k + 1 : ℕ) : ℚ) * ((p : ℚ) / ((p : ℚ) - 1)) := by
  have h1 : (∑ j ∈ range (k + 1), ((j + 1 : ℕ) : ℚ) / (p ^ (k - j) : ℚ)) ≤
    ((k + 1 : ℕ) : ℚ) * ∑ j ∈ range (k + 1), (1 : ℚ) / (p ^ (k - j) : ℚ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    rw [mem_range] at hj
    have h_le : ((j + 1 : ℕ) : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega)
    have h_pos : (0 : ℚ) ≤ (1 : ℚ) / (p ^ (k - j) : ℚ) := by positivity
    calc ((j + 1 : ℕ) : ℚ) / (p ^ (k - j) : ℚ) = ((j + 1 : ℕ) : ℚ) * (1 / (p ^ (k - j) : ℚ)) := by ring
      _ ≤ ((k + 1 : ℕ) : ℚ) * (1 / (p ^ (k - j) : ℚ)) := mul_le_mul_of_nonneg_right h_le h_pos
  have h2 := geom_sum_bound hp (k := k)
  have hk_pos : (0 : ℚ) < ((k + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega)
  have h3 : ((k + 1 : ℕ) : ℚ) * ∑ j ∈ range (k + 1), (1 : ℚ) / (p ^ (k - j) : ℚ) <
    ((k + 1 : ℕ) : ℚ) * ((p : ℚ) / ((p : ℚ) - 1)) := by
    exact mul_lt_mul_of_pos_left h2 hk_pos
  exact h1.trans_lt h3
