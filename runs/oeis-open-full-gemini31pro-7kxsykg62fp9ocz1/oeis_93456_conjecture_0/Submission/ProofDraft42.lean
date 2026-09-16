import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma p_pow_dvd_an_minus_1 (p M n : ℕ) (hp5 : 5 ≤ p) (hM : p ≤ M) (hp_dvd : p ∣ M - 1)
  (h_dvd1 : (∏ x ∈ Icc (M - p + 3) M, (p * x)) ∣ a (n - 1)) :
  p ^ (p - 1) ∣ a (n - 1) := by
  have h_prod : (∏ x ∈ Icc (M - p + 3) M, (p * x)) = p^(p - 2) * ∏ x ∈ Icc (M - p + 3) M, x := by
    rw [prod_mul_distrib, prod_const]
    congr 1
    have : (Icc (M - p + 3) M).card = p - 2 := by
      rw [Nat.card_Icc]
      zify [show p ≤ M by omega]
      omega
    rw [this]
  rw [h_prod] at h_dvd1
  have h_p : p ∣ ∏ x ∈ Icc (M - p + 3) M, x := by
    have H : M - 1 ∈ Icc (M - p + 3) M := by
      rw [mem_Icc]; constructor <;> omega
    exact dvd_trans hp_dvd (dvd_prod_of_mem (fun x => x) H)
  obtain ⟨k, hk⟩ := h_p
  rw [hk] at h_dvd1
  have h_pow : p ^ (p - 2) * (p * k) = p ^ (p - 1) * k := by
    have : p ^ (p - 1) = p ^ (p - 2) * p := by
      have : p - 1 = p - 2 + 1 := by omega
      rw [this, pow_add, pow_one]
    rw [this]
    ring
  rw [h_pow] at h_dvd1
  exact dvd_of_mul_right_dvd h_dvd1
