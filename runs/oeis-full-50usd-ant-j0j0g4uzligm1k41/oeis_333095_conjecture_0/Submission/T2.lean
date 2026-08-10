import FormalConjectures.Util.ProblemImports
open Nat Finset

def bz (n k : ℕ) : ℤ :=
  ((3*n+2*k-1).choose k : ℤ) - (if k = 0 then 0 else ((3*n+2*k-1).choose (k-1) : ℤ))

theorem term_eq_bz (n k : ℕ) (hn : 1 ≤ n) :
    (3*n : ℚ) / (3*n + 2*k) * ((3*n+2*k).choose k : ℚ) = (bz n k : ℚ) := by
  have hr1 : 3 ≤ 3*n := by omega
  unfold bz
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.mul_zero, Nat.add_zero, if_pos rfl, Nat.choose_zero_right]
    have hrr : (3*(n:ℚ)) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · rw [if_neg (by omega)]
    have hN : 3*n + 2*k - 1 + 1 = 3*n + 2*k := by omega
    have ei : (3*n+2*k-1).choose k * (3*n+2*k) = (3*n+2*k).choose k * (3*n+k) := by
      have := Nat.choose_mul_succ_eq (3*n+2*k-1) k
      rw [hN] at this
      have hsub : 3*n + 2*k - k = 3*n + k := by omega
      rw [hsub] at this; exact this
    have hk1 : k - 1 + 1 = k := by omega
    have eii : (3*n+2*k-1).choose k * k = (3*n+2*k-1).choose (k-1) * (3*n+k) := by
      have := Nat.choose_succ_right_eq (3*n+2*k-1) (k-1)
      rw [hk1] at this
      have hsub : 3*n + 2*k - 1 - (k-1) = 3*n + k := by omega
      rw [hsub] at this; exact this
    have eiQ : ((3*n+2*k-1).choose k : ℚ) * (3*n+2*k) = ((3*n+2*k).choose k : ℚ) * (3*n+k) := by
      exact_mod_cast ei
    have eiiQ : ((3*n+2*k-1).choose k : ℚ) * k = ((3*n+2*k-1).choose (k-1) : ℚ) * (3*n+k) := by
      exact_mod_cast eii
    have h1 : (3*(n:ℚ) + 2*k) ≠ 0 := by positivity
    have h2 : (3*(n:ℚ) + k) ≠ 0 := by positivity
    push_cast at eiQ eiiQ ⊢
    set A : ℚ := ((3*n+2*k-1).choose k : ℚ)
    set B : ℚ := ((3*n+2*k).choose k : ℚ)
    set D : ℚ := ((3*n+2*k-1).choose (k-1) : ℚ)
    have goalEq : (3*(n:ℚ)) * B = (A - D)*(3*n+2*k) := by
      have hkey : (3*(n:ℚ)+k)*((3*(n:ℚ)) * B) = (3*(n:ℚ)+k)*((A - D)*(3*n+2*k)) := by
        linear_combination (-(3*(n:ℚ)))*eiQ + (-(3*(n:ℚ)+2*(k:ℚ)))*eiiQ
      exact mul_left_cancel₀ h2 hkey
    rw [div_mul_eq_mul_div, div_eq_iff h1]
    linear_combination goalEq
