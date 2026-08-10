import Mathlib

lemma test_gs_prime_contradiction
    (q r s g_s_prime c A B C Y' Y a_s : ℕ)
    (hq_prime : Nat.Prime q)
    (hp_lt_q : 2 < q)
    (hq_lt_r : q < r)
    (hA : A = 3)
    (hB : B = 2 * q - 1)
    (hC : C = 2 * r - 1)
    (hY : Y = (2 * s - 1) * Y')
    (hY'_pos : 1 ≤ Y')
    (h_prod : q * (r * (2 * g_s_prime)) = 2 * C * A * B * Y' - a_s)
    (ha_s_pos : 1 ≤ a_s) :
    False := by
  have hq_ge : 5 ≤ q := by
    have : q ≠ 3 := by
      rintro rfl
      -- since q is prime and 2 < q < r, etc.
      sorry
    omega
  have hr_ge : 7 ≤ r := by omega
  have h_prod_int : (q : ℤ) * r * 2 * g_s_prime = 2 * C * A * B * Y' - a_s := by
    zify at h_prod ⊢
    linarith [h_prod]
  sorry
