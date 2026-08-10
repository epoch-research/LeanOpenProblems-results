import FormalConjectures.Util.ProblemImports

open Nat

lemma div_odd_mod_two_universal (A B : ℕ) (hB : B % 2 = 1) :
    (A / B) % 2 = (A % 2 + (A % B) % 2) % 2 := by
  have h_div := Nat.div_add_mod A B
  have h1 : A % 2 = (B * (A / B) + A % B) % 2 := by rw [h_div]
  rw [Nat.add_mod, Nat.mul_mod, hB] at h1
  simp only [one_mul, Nat.mod_mod] at h1
  omega

lemma mod_two_mul_eq (A D : ℕ) (hD : D > 0) :
    A % (2 * D) = ((A / D) % 2) * D + A % D := by
  have h_div := Nat.div_add_mod A D
  have h_div2 := Nat.div_add_mod (A / D) 2
  have h_mul : A = (2 * ((A / D) / 2) + (A / D) % 2) * D + A % D := by
    calc A = D * (A / D) + A % D := h_div.symm
         _ = D * (2 * ((A / D) / 2) + (A / D) % 2) + A % D := by rw [h_div2]
         _ = (2 * ((A / D) / 2) + (A / D) % 2) * D + A % D := by ring
  have h_ring : (2 * ((A / D) / 2) + (A / D) % 2) * D + A % D =
                ((A / D) / 2) * (2 * D) + (((A / D) % 2) * D + A % D) := by ring
  rw [h_ring] at h_mul
  have h_mod : A % (2 * D) = (((A / D) / 2) * (2 * D) + (((A / D) % 2) * D + A % D)) % (2 * D) := by
    congr 1
  rw [Nat.add_comm, Nat.add_mul_mod_self_right] at h_mod
  rw [h_mod]
  have h_lt : ((A / D) % 2) * D + A % D < 2 * D := by
    have h_modD : A % D < D := Nat.mod_lt _ hD
    rcases Nat.mod_two_eq_zero_or_one (A / D) with h0 | h1
    · rw [h0]
      omega
    · rw [h1]
      omega
  exact Nat.mod_eq_of_lt h_lt

lemma mod_eq_mul_of_coprime (A B D : ℕ) (hD_pos : D > 0) (hD : D % 2 = 1)
    (h2 : A % 2 = B % 2) (hD_eq : A % D = B % D) :
    A % (2 * D) = B % (2 * D) := by
  rw [mod_two_mul_eq A D hD_pos]
  rw [mod_two_mul_eq B D hD_pos]
  rw [hD_eq]
  have hA_div := div_odd_mod_two_universal A D hD
  have hB_div := div_odd_mod_two_universal B D hD
  rw [hA_div, hB_div, h2, hD_eq]


