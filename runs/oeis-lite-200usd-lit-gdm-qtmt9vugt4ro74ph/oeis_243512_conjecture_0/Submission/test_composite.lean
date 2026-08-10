import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000

open Nat ArithmeticFunction Rat

theorem sigma_one_mul_coprime (a b : ℕ) (h : Coprime a b) :
    sigma 1 (a * b) = sigma 1 a * sigma 1 b := by
  exact isMultiplicative_sigma.map_mul_of_coprime h

theorem nat_div_eq_divInt (a b : ℕ) : ((a : ℚ) / (b : ℚ)) = (a : ℤ) /. (b : ℤ) := by
  rw [Rat.divInt_eq_div]
  push_cast
  rfl

theorem coprime_num_den (a b : ℕ) (hb : 0 < b) (h_cop : Coprime a b) :
    (((a : ℤ) /. (b : ℤ)).num = a) ∧ (((a : ℤ) /. (b : ℤ)).den = b) := by
  have h_gcd : Int.gcd b a = 1 := by
    have h1 : (b : ℤ).natAbs = b := rfl
    have h2 : (a : ℤ).natAbs = a := rfl
    simp [Int.gcd, h1, h2]
    exact h_cop.symm
  have h_sign : Int.sign b = 1 := by
    rw [Int.sign_eq_one_of_pos]
    omega
  constructor
  · rw [Rat.num_divInt]
    rw [h_gcd, h_sign]
    simp
  · rw [Rat.den_divInt]
    have hb_ne : (b : ℤ) ≠ 0 := by omega
    rw [if_neg hb_ne]
    rw [h_gcd]
    simp

def A243473_val (i : ℕ) : ℕ :=
  if i = 0 then 0
  else
    let r : Rat := (sigma 1 i : Rat) / (i : Rat)
    (r.num - (r.den : ℤ)).toNat

theorem composite_g_case (n : ℕ) (g : ℕ) (hg_pos : 0 < g) (hn : 2 < n) :
    let d := Nat.gcd (sigma 1 g) g
    let val := (sigma 1 g - g) / d
    let b := g / d
    let a := sigma 1 g / d
    let k := (n - 1) / val
    let P := k * b - 1
    (h_val_dvd : val ∣ n - 1) →
    (h_P_prime : P.Prime) →
    (h_P_not_dvd_g : ¬ P ∣ g) →
    (h_cop : Coprime (k * a) P) →
    A243473_val (g * P) = n := by
  intro d val b a k P h_val_dvd h_P_prime h_P_not_dvd_g h_cop
  unfold A243473_val
  have hP_pos : 0 < P := h_P_prime.pos
  have hP_ge_two : 2 ≤ P := h_P_prime.two_le
  have hg_ne_zero : g ≠ 0 := hg_pos.ne'
  have hP_ne_zero : P ≠ 0 := hP_pos.ne'
  have hgP_ne_zero : g * P ≠ 0 := mul_ne_zero hg_ne_zero hP_ne_zero
  rw [if_neg hgP_ne_zero]
  have h_cop_gP : Coprime g P := Nat.Coprime.symm (h_P_prime.coprime_iff_not_dvd.mpr h_P_not_dvd_g)
  have h_sigma_gP : sigma 1 (g * P) = sigma 1 g * (P + 1) := by
    rw [sigma_one_mul_coprime g P h_cop_gP]
    have h_sigma_P : sigma 1 P = P + 1 := by
      rw [sigma_apply, Nat.Prime.divisors h_P_prime]
      have h_ne : 1 ≠ P := h_P_prime.ne_one.symm
      have h_not_mem : 1 ∉ ({P} : Finset ℕ) := by
        simp; exact h_ne
      rw [Finset.sum_insert h_not_mem]
      simp; omega
    rw [h_sigma_P]
  have hd_dvd_g : d ∣ g := Nat.gcd_dvd_right (sigma 1 g) g
  have hd_dvd_sig : d ∣ sigma 1 g := Nat.gcd_dvd_left (sigma 1 g) g
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_right (sigma 1 g) hg_pos
  have h_g_eq : g = d * b := (Nat.mul_div_cancel' hd_dvd_g).symm
  have h_sig_eq : sigma 1 g = d * a := (Nat.mul_div_cancel' hd_dvd_sig).symm
  have h_kb_pos : 0 < k * b := by
    have : 2 ≤ k * b - 1 := hP_ge_two
    omega
  have h_P_add_one : P + 1 = k * b := by
    have : P = k * b - 1 := rfl
    omega
  have h_sig_gP_val : sigma 1 (g * P) = d * a * (k * b) := by
    rw [h_sigma_gP, h_sig_eq, h_P_add_one]
  have h_gP_val : g * P = d * b * P := by
    rw [h_g_eq, mul_assoc]
  have h_rat_eq : ((sigma 1 (g * P) : Rat) / (g * P : Rat)) = ((k * a : Rat) / (P : Rat)) := by
    have h1 : (sigma 1 (g * P) : Rat) = (a * k * g : Rat) := by
      have : sigma 1 (g * P) = a * k * g := by
        rw [h_sig_gP_val, h_g_eq]
        ring
      rw [this]
      push_cast
      rfl
    have h2 : (g * P : Rat) = (P * g : Rat) := by
      push_cast
      ring
    rw [h1, h2]
    have h_g_ne : (g : Rat) ≠ 0 := cast_ne_zero.mpr hg_ne_zero
    rw [mul_div_mul_right _ _ h_g_ne]
    ring
  have h_gP_cast : ((g * P : ℕ) : Rat) = (g : Rat) * (P : Rat) := by push_cast; rfl
  rw [h_gP_cast]
  rw [h_rat_eq]
  have h_fold : (k * a : Rat) / (P : Rat) = ((k * a : ℕ) : Rat) / ((P : ℕ) : Rat) := by
    push_cast
    rfl
  rw [h_fold]
  rw [nat_div_eq_divInt]
  dsimp only
  have h_num_den := coprime_num_den (k * a) P hP_pos h_cop
  rw [h_num_den.1, h_num_den.2]
  push_cast
  have h_a_sub_b : (a : ℤ) - (b : ℤ) = (val : ℤ) := by
    have h_sig_sub_g : sigma 1 g - g = d * val := by
      have : (sigma 1 g - g) / d = val := rfl
      have hd_dvd_sub : d ∣ sigma 1 g - g := by
        apply Nat.dvd_sub
        · exact hd_dvd_sig
        · exact hd_dvd_g
      exact (Nat.mul_div_cancel' hd_dvd_sub).symm
    have h_ring : (sigma 1 g : ℤ) - (g : ℤ) = ((sigma 1 g - g) : ℕ) := by
      have h_mem : g ∈ divisors g := by
        rw [mem_divisors]
        refine ⟨dvd_rfl, hg_pos.ne'⟩
      have h_le : g ≤ sigma 1 g := by
        rw [sigma_one_apply]
        apply Finset.single_le_sum (fun a _ => zero_le a) h_mem
      omega
    have h_ring2 : (sigma 1 g : ℤ) - (g : ℤ) = (d * a : ℤ) - (d * b : ℤ) := by
      rw [h_sig_eq, h_g_eq]
      push_cast
      rfl
    rw [h_ring2, ← mul_sub_left_distrib] at h_ring
    rw [h_sig_sub_g] at h_ring
    push_cast at h_ring
    have hd_ne_zero : (d : ℤ) ≠ 0 := by
      exact cast_ne_zero.mpr hd_pos.ne'
    exact mul_left_cancel₀ hd_ne_zero h_ring
  have h_final : (k * a : ℤ) - (P : ℤ) = (n : ℤ) := by
    have hP_def : (P : ℤ) = (k * b : ℤ) - 1 := by
      have : P = k * b - 1 := rfl
      omega
    rw [hP_def]
    have h_ring3 : (k * a : ℤ) - ((k * b : ℤ) - 1) = (k : ℤ) * ((a : ℤ) - (b : ℤ)) + 1 := by ring
    rw [h_ring3, h_a_sub_b]
    have h_kv_eq : (k * val : ℕ) = n - 1 := Nat.div_mul_cancel h_val_dvd
    have h_kv_eq_z : (k : ℤ) * (val : ℤ) = (n : ℤ) - 1 := by
      push_cast
      omega
    rw [h_kv_eq_z]
    omega
  rw [h_final]
  rfl
