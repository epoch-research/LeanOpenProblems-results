import FormalConjectures.Util.ProblemImports

open Nat

def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (x, y) := P n
    (x - (n + 1) * y, (n + 1) * x + y)

theorem P_succ_succ_succ_succ (n : ℕ) :
    (P (n + 4)).1 = ((n : ℤ)^4 + 10 * (n : ℤ)^3 + 29 * (n : ℤ)^2 + 20 * (n : ℤ) - 10) * (P n).1 - (- (4 * (n : ℤ)^3 + 30 * (n : ℤ)^2 + 66 * (n : ℤ) + 40)) * (P n).2 ∧
    (P (n + 4)).2 = (- (4 * (n : ℤ)^3 + 30 * (n : ℤ)^2 + 66 * (n : ℤ) + 40)) * (P n).1 + ((n : ℤ)^4 + 10 * (n : ℤ)^3 + 29 * (n : ℤ)^2 + 20 * (n : ℤ) - 10) * (P n).2 := by
  have h1 : (P (n + 1)).1 = (P n).1 - (n + 1 : ℤ) * (P n).2 ∧ (P (n + 1)).2 = (n + 1 : ℤ) * (P n).1 + (P n).2 := by
    simp [P]
  have h2 : (P (n + 2)).1 = (P (n + 1)).1 - (n + 2 : ℤ) * (P (n + 1)).2 ∧ (P (n + 2)).2 = (n + 2 : ℤ) * (P (n + 1)).1 + (P (n + 1)).2 := by
    simp [P]
  have h3 : (P (n + 3)).1 = (P (n + 2)).1 - (n + 3 : ℤ) * (P (n + 2)).2 ∧ (P (n + 3)).2 = (n + 3 : ℤ) * (P (n + 2)).1 + (P (n + 2)).2 := by
    simp [P]
  have h4 : (P (n + 4)).1 = (P (n + 3)).1 - (n + 4 : ℤ) * (P (n + 3)).2 ∧ (P (n + 4)).2 = (n + 4 : ℤ) * (P (n + 3)).1 + (P (n + 3)).2 := by
    simp [P]
  rcases h1 with ⟨x1, y1⟩
  rcases h2 with ⟨x2, y2⟩
  rcases h3 with ⟨x3, y3⟩
  rcases h4 with ⟨x4, y4⟩
  rw [x4, y4, x3, y3, x2, y2, x1, y1]
  constructor <;> ring

lemma coeff_C_eq (k : ℕ) :
    ((4 * k : ℕ) : ℤ)^4 + 10 * ((4 * k : ℕ) : ℤ)^3 + 29 * ((4 * k : ℕ) : ℤ)^2 + 20 * ((4 * k : ℕ) : ℤ) - 10 =
    4 * (64 * (k : ℤ)^4 + 160 * (k : ℤ)^3 + 116 * (k : ℤ)^2 + 20 * (k : ℤ) - 3) + 2 := by
  push_cast
  ring

lemma coeff_D_eq (k : ℕ) :
    4 * ((4 * k : ℕ) : ℤ)^3 + 30 * ((4 * k : ℕ) : ℤ)^2 + 66 * ((4 * k : ℕ) : ℤ) + 40 =
    8 * (32 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 33 * (k : ℤ) + 5) := by
  push_cast
  ring


lemma val_mul_power_odd (k : ℕ) (x : ℤ) (hx : x % 2 = 1 ∨ x % 2 = -1) :
    padicValInt 2 ((2 : ℤ)^(k + 1) * x) = k + 1 := by
  rw [padicValInt.mul]
  · have h2 : padicValInt 2 ((2:ℤ)^(k+1)) = k + 1 := by
      unfold padicValInt
      rw [Int.natAbs_pow]
      have : (2 : ℤ).natAbs = 2 := rfl
      rw [this]
      exact padicValNat.padicValNat_self_prime_pow
    have h_odd : padicValInt 2 x = 0 := by
      unfold padicValInt
      apply padicValNat.eq_zero_of_not_dvd
      intro hc
      have h_dvd : (2:ℤ) ∣ x := by
        have h_eq : (2:ℤ) = ((2 : ℕ) : ℤ) := rfl
        rw [h_eq]
        rwa [Int.ofNat_dvd_left] at hc
      have h_mod : x % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h_dvd
      omega
    rw [h2, h_odd, add_zero]
  · positivity
  · intro hc
    subst hc
    omega
