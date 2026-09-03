import FormalConjecturesUtil

/-! A greedy construction of finite sign patterns with small additive
self-convolution energy. This is an auxiliary finite result only. -/
namespace Erdos66SignEnergy
open Polynomial
noncomputable section

/-- The coefficients at and beyond `n` vanish. -/
def SupportedBelow (P : ℤ[X]) (n : ℕ) : Prop := ∀ i, n ≤ i → P.coeff i = 0

/-- The ordered additive self-convolution energy of a length-`n` sequence. -/
def energy (P : ℤ[X]) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * n), ((P ^ 2).coeff i) ^ 2

def append (P : ℤ[X]) (n : ℕ) (s : ℤ) : ℤ[X] := P + C s * X ^ n

lemma supported_square {P : ℤ[X]} {n : ℕ} (hP : SupportedBelow P n) :
    SupportedBelow (P ^ 2) (2 * n) := by
  intro i hi
  rw [pow_two, coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have hab' := Finset.mem_antidiagonal.mp hab
  by_cases ha : n ≤ ab.1
  · rw [hP _ ha, zero_mul]
  · rw [hP ab.2 (by omega), mul_zero]

lemma append_supported {P : ℤ[X]} {n : ℕ} (hP : SupportedBelow P n) (s : ℤ) :
    SupportedBelow (append P n s) (n + 1) := by
  intro i hi
  simp only [append, coeff_add, coeff_C_mul, coeff_X_pow,
    hP i (by omega), if_neg (by omega : i ≠ n), mul_zero, add_zero]

lemma append_coeff_old (P : ℤ[X]) (n : ℕ) (s : ℤ) (i : ℕ) (hi : i < n) :
    (append P n s).coeff i = P.coeff i := by
  simp [append, coeff_C_mul, coeff_X_pow, ne_of_lt hi]

lemma append_coeff_last {P : ℤ[X]} {n : ℕ} (hP : SupportedBelow P n) (s : ℤ) :
    (append P n s).coeff n = s := by simp [append, hP n le_rfl]

lemma append_square (P : ℤ[X]) (n : ℕ) (s : ℤ) :
    (append P n s) ^ 2 = P ^ 2 + C (2 * s) * (P * X ^ n) + C (s ^ 2) * X ^ (2 * n) := by
  simp only [append, map_mul, map_ofNat, map_pow, mul_comm 2 n, pow_mul]
  ring

lemma append_square_low (P : ℤ[X]) (n : ℕ) (s : ℤ) (i : ℕ) (hi : i < n) :
    ((append P n s) ^ 2).coeff i = (P ^ 2).coeff i := by
  rw [append_square]
  simp only [coeff_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow,
    if_neg (by omega : ¬n ≤ i), if_neg (by omega : i ≠ 2 * n), mul_zero, add_zero]

lemma append_square_middle (P : ℤ[X]) (n : ℕ) (s : ℤ) (i : ℕ) (hi : i < n) :
    ((append P n s) ^ 2).coeff (n + i) = (P ^ 2).coeff (n + i) + 2 * s * P.coeff i := by
  rw [append_square]
  simp only [coeff_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow,
    if_pos (Nat.le_add_right n i), Nat.add_sub_cancel_left,
    if_neg (by omega : n + i ≠ 2 * n), mul_zero, add_zero]

lemma append_square_top {P : ℤ[X]} {n : ℕ} (hP : SupportedBelow P n)
    (s : ℤ) (hs : s ^ 2 = 1) :
    ((append P n s) ^ 2).coeff (2 * n) = 1 := by
  rw [append_square]
  simp only [coeff_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow,
    if_pos (by omega : n ≤ 2 * n), if_pos rfl, hs, mul_one,
    supported_square hP (2 * n) le_rfl]
  rw [hP (2 * n - n) (by omega)]
  simp

lemma append_square_top_succ {P : ℤ[X]} {n : ℕ} (hP : SupportedBelow P n) (s : ℤ) :
    ((append P n s) ^ 2).coeff (2 * n + 1) = 0 := by
  rw [append_square]
  simp only [coeff_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow,
    if_pos (by omega : n ≤ 2 * n + 1), if_neg (by omega : 2 * n + 1 ≠ 2 * n),
    mul_zero, add_zero, supported_square hP (2 * n + 1) (by omega)]
  rw [hP (2 * n + 1 - n) (by omega)]
  ring

lemma energy_split (P : ℤ[X]) (n : ℕ) :
    energy P n = (∑ i ∈ Finset.range n, ((P ^ 2).coeff i) ^ 2) +
      ∑ i ∈ Finset.range n, ((P ^ 2).coeff (n + i)) ^ 2 := by
  unfold energy
  rw [two_mul, Finset.sum_range_add]

lemma append_energy {P : ℤ[X]} {n : ℕ} (hP : SupportedBelow P n)
    (s : ℤ) (hs : s ^ 2 = 1) :
    energy (append P n s) (n + 1) =
      (∑ i ∈ Finset.range n, ((P ^ 2).coeff i) ^ 2) +
      (∑ i ∈ Finset.range n, ((P ^ 2).coeff (n + i) + 2 * s * P.coeff i) ^ 2) + 1 := by
  unfold energy
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ,
    append_square_top hP s hs, append_square_top_succ hP s]
  norm_num only [zero_pow, one_pow, add_zero]
  rw [show 2 * n = n + n by omega, Finset.sum_range_add]
  congr 2
  · apply Finset.sum_congr rfl
    intro i hi
    rw [append_square_low P n s i (Finset.mem_range.mp hi)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [append_square_middle P n s i (Finset.mem_range.mp hi)]

/-- The sum of the two possible new energies has no cubic cross term. -/
lemma append_energy_average {P : ℤ[X]} {n : ℕ} (hP : SupportedBelow P n)
    (hsign : ∀ i < n, P.coeff i = 1 ∨ P.coeff i = -1) :
    energy (append P n 1) (n + 1) + energy (append P n (-1)) (n + 1) =
      2 * energy P n + 8 * n + 2 := by
  rw [append_energy hP 1 (by norm_num), append_energy hP (-1) (by norm_num),
    energy_split]
  have hsum :
      (∑ i ∈ Finset.range n, ((P ^ 2).coeff (n + i) + 2 * (1 : ℤ) * P.coeff i) ^ 2) +
      (∑ i ∈ Finset.range n, ((P ^ 2).coeff (n + i) + 2 * (-1 : ℤ) * P.coeff i) ^ 2) =
      2 * (∑ i ∈ Finset.range n, ((P ^ 2).coeff (n + i)) ^ 2) + 8 * n := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i ∈ Finset.range n, (2 * ((P ^ 2).coeff (n + i)) ^ 2 + 8) := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases hsign i (Finset.mem_range.mp hi) with h | h <;> rw [h] <;> ring
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
  linarith

/-- Greedy sign choice gives the same energy bound as averaging independent signs. -/
theorem exists_sign_polynomial (n : ℕ) :
    ∃ P : ℤ[X], SupportedBelow P n ∧
      (∀ i < n, P.coeff i = 1 ∨ P.coeff i = -1) ∧
      energy P n ≤ 2 * (n : ℤ) ^ 2 - n := by
  induction n with
  | zero =>
      exact ⟨0, by simp [SupportedBelow], by simp, by simp [energy]⟩
  | succ n ih =>
      obtain ⟨P, hP, hsign, hE⟩ := ih
      have hsign' (s : ℤ) (hs : s = 1 ∨ s = -1) :
          ∀ i < n + 1, (append P n s).coeff i = 1 ∨ (append P n s).coeff i = -1 := by
        intro i hi
        by_cases hin : i < n
        · rw [append_coeff_old P n s i hin]
          exact hsign i hin
        · have hei : i = n := by omega
          subst i
          rw [append_coeff_last hP s]
          exact hs
      have hav := append_energy_average hP hsign
      by_cases h : energy (append P n 1) (n + 1) ≤ 2 * ((n + 1 : ℕ) : ℤ) ^ 2 - (n + 1)
      · exact ⟨append P n 1, append_supported hP _, hsign' _ (Or.inl rfl), h⟩
      · refine ⟨append P n (-1), append_supported hP _, hsign' _ (Or.inr rfl), ?_⟩
        push_cast at h ⊢
        nlinarith

/-- The resulting sign self-convolution has an `O(n^(3/2))` absolute fiber sum. -/
theorem exists_sign_polynomial_l1 (n : ℕ) :
    ∃ P : ℤ[X], SupportedBelow P n ∧
      (∀ i < n, P.coeff i = 1 ∨ P.coeff i = -1) ∧
      (∑ i ∈ Finset.range (2 * n), |(P ^ 2).coeff i|) ^ 2 ≤ 4 * (n : ℤ) ^ 3 := by
  obtain ⟨P, hP, hsign, hE⟩ := exists_sign_polynomial n
  refine ⟨P, hP, hsign, ?_⟩
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (2 * n))
    (f := fun i ↦ |(P ^ 2).coeff i|)
  simp only [Finset.card_range, sq_abs, Nat.cast_mul, Nat.cast_ofNat] at hcs
  change _ ≤ 2 * (n : ℤ) * energy P n at hcs
  have hn : 0 ≤ (n : ℤ) := Nat.cast_nonneg n
  have hm := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * (n : ℤ))
  nlinarith [sq_nonneg (n : ℤ)]

end
end Erdos66SignEnergy
