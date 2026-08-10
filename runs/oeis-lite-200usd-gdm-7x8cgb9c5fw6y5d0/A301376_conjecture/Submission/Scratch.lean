import FormalConjectures.Util.ProblemImports

open Nat

lemma not_sq_add_sq (m : ℕ) (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 4 = 3) (h1 : p ∣ m) (h2 : ¬ p^2 ∣ m) :
    ¬ ∃ z w : ℕ, z^2 + w^2 = m := by
  intro ⟨z, w, hzw⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply h2
    exact dvd_zero (p^2)
  have h_padic : padicValNat p m = 1 := by
    have h_le : 1 ≤ padicValNat p m := one_le_padicValNat_of_dvd hm0 h1
    have h_lt : padicValNat p m < 2 := by
      by_contra h_ge
      push_neg at h_ge
      have h_pow_dvd : p^2 ∣ m := (padicValNat_dvd_iff_le hm0).mpr h_ge
      contradiction
    omega
  have h_eq : (∃ x y, m = x ^ 2 + y ^ 2) := ⟨z, w, hzw.symm⟩
  rw [Nat.eq_sq_add_sq_iff] at h_eq
  have hp_mem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp.out, h1, hm0⟩
  have h_even : Even (padicValNat p m) := h_eq p hp_mem hp3
  rw [h_padic] at h_even
  contradiction
