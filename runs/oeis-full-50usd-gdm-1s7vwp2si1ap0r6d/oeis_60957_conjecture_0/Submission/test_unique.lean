import FormalConjectures.Util.ProblemImports

open Finset Nat

lemma val_lt_h (n p x h : ℕ) (hp : Nat.Prime p) (hx : x ∈ Icc 1 n) (h_h : p^h > n) :
    padicValNat p x < h := by
  have hp_fact : Fact (Nat.Prime p) := ⟨hp⟩
  by_contra h_ge
  push_neg at h_ge
  have h_pow_dvd : p^h ∣ p^(padicValNat p x) := pow_dvd_pow p h_ge
  have h_div : p^h ∣ x := dvd_trans h_pow_dvd pow_padicValNat_dvd
  have h_x_pos : x ≥ 1 := mem_Icc.1 hx |>.1
  have h_le : p^h ≤ x := Nat.le_of_dvd h_x_pos h_div
  have h_x_le : x ≤ n := mem_Icc.1 hx |>.2
  omega
