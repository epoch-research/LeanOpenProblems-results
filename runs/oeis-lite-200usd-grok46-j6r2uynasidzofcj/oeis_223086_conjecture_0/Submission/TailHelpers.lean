import FormalConjectures.Util.ProblemImports

-- Scratch file: only used during development. Final proof lives in Spec.lean.

open Nat Function

def A006368_inv (m : ℕ) : ℕ :=
  if m % 3 = 0 then (2 * m) / 3
  else if m % 3 = 1 then (4 * m - 1) / 3
  else (4 * m + 1) / 3

lemma exists_form_mod3_zero {n : ℕ} (h : n % 3 = 0) : ∃ t, n = 3 * t :=
  ⟨n / 3, (Nat.div_add_mod n 3).symm.trans (by rw [h]; ring)⟩
lemma exists_form_mod3_one {n : ℕ} (h : n % 3 = 1) : ∃ t, n = 3 * t + 1 :=
  ⟨n / 3, (Nat.div_add_mod n 3).symm.trans (by rw [h])⟩
lemma exists_form_mod3_two {n : ℕ} (h : n % 3 = 2) : ∃ t, n = 3 * t + 2 :=
  ⟨n / 3, (Nat.div_add_mod n 3).symm.trans (by rw [h])⟩
lemma mod3_cases (n : ℕ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega

lemma inv_mod3_zero (t : ℕ) : A006368_inv (3 * t) = 2 * t := by
  simp [A006368_inv]
  convert Nat.mul_div_cancel_left (2 * t) (by decide : 0 < 3) using 2
  ring
lemma inv_mod3_one (t : ℕ) : A006368_inv (3 * t + 1) = 4 * t + 1 := by
  have h : (3 * t + 1) % 3 = 1 := by omega
  simp [A006368_inv, h]
  convert Nat.mul_div_cancel_left (4 * t + 1) (by decide : 0 < 3) using 2
  have : 4 * (3 * t + 1) = 12 * t + 4 := by ring
  rw [this]
  have : 1 ≤ 12 * t + 4 := by omega
  rw [Nat.sub_eq_of_eq_add]; ring
lemma inv_mod3_two (t : ℕ) : A006368_inv (3 * t + 2) = 4 * t + 3 := by
  have h0 : ¬ (3 * t + 2) % 3 = 0 := by omega
  have h1 : ¬ (3 * t + 2) % 3 = 1 := by omega
  simp [A006368_inv, h0, h1]
  convert Nat.mul_div_cancel_left (4 * t + 3) (by decide : 0 < 3) using 2
  ring

instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
lemma odd_three : Odd (3 : ℕ) := ⟨1, by decide⟩
lemma padicValNat_three_three : padicValNat 3 3 = 1 := padicValNat.self (by decide : 1 < 3)
lemma padicValNat_two_three : padicValNat 3 2 = 0 :=
  padicValNat.eq_zero_of_not_dvd (by decide)

def ker3 (n : ℕ) : ℕ := n / 3 ^ padicValNat 3 n
lemma ker3_mul (n : ℕ) : n = 3 ^ padicValNat 3 n * ker3 n := by
  unfold ker3
  exact (Nat.div_mul_cancel (pow_padicValNat_dvd)).symm |>.trans (mul_comm _ _)
    |> fun h => by
      have := Nat.mul_div_cancel' (pow_padicValNat_dvd (p := 3) (n := n))
      rw [← this]; unfold ker3; ring_nf

#check ker3_mul
