import FormalConjectures.Util.ProblemImports

open Complex Filter Asymptotics Topology

noncomputable def a (n : ℕ) : ℤ :=
  let product_term (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod product_term).im)

open Nat

def P : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let (x, y) := P n
    (x - (n + 1) * y, (n + 1) * x + y)

private theorem P_complex (n : ℕ) :
    ((Finset.range (n + 1)).prod (fun k ↦ 1 + (k : ℂ) * I)) = ((P n).1 : ℂ) + ((P n).2 : ℂ) * I := by
  induction n with
  | zero =>
    apply Complex.ext <;> simp [P]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    apply Complex.ext <;> simp [P] <;> ring

theorem a_eq_P_im (n : ℕ) : a n = (P n).2 := by
  unfold a
  dsimp
  rw [P_complex]
  simp

def InductionHyp (n : ℕ) : Prop :=
  let k := n / 4
  match n % 4 with
  | 0 => 2^k ∣ (P n).1 ∧ 2^k ∣ (P n).2
  | 1 => 2^k ∣ (P n).1 ∧ 2^k ∣ (P n).2 ∧ 2^(k+1) ∣ ((P n).1 - (P n).2)
  | 2 => 2^k ∣ (P n).1 ∧ 2^k ∣ (P n).2 ∧ 2^(k+1) ∣ ((P n).1 - (P n).2)
  | _ => 2^(k+1) ∣ (P n).1 ∧ 2^(k+1) ∣ (P n).2

theorem induction_hyp_step (n : ℕ) : InductionHyp n := by
  induction n with
  | zero =>
    unfold InductionHyp
    simp [P]
  | succ n ih =>
    unfold InductionHyp at *
    have h_mod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h_mod with h0 | h1 | h2 | h3
    · -- Case n % 4 = 0
      have h_mod_succ : (n + 1) % 4 = 1 := by omega
      have h_div_succ : (n + 1) / 4 = n / 4 := by omega
      rw [h0] at ih
      dsimp at ih
      rw [h_mod_succ, h_div_succ]
      simp [P]
      set k := n / 4
      rcases ih with ⟨hx, hy⟩
      rcases hx with ⟨X, hX⟩
      rcases hy with ⟨Y, hY⟩
      rw [hX, hY]
      have h_pow1 : (2:ℤ)^(k+1) = (2:ℤ)^k * 2 := by
        have : k + 1 = k + 1 := by omega
        rw [pow_succ]
      refine ⟨?_, ?_, ?_⟩
      · use X - (4 * k + 1) * Y
        have h_n : n = 4 * k := by omega
        rw [h_n]
        push_cast; ring
      · use (4 * k + 1) * X + Y
        have h_n : n = 4 * k := by omega
        rw [h_n]
        push_cast; ring
      · use - 2 * (k : ℤ) * X - (2 * (k : ℤ) + 1) * Y
        have h_n : n = 4 * k := by omega
        rw [h_n]
        rw [h_pow1]
        push_cast; ring
    · -- Case n % 4 = 1
      have h_mod_succ : (n + 1) % 4 = 2 := by omega
      have h_div_succ : (n + 1) / 4 = n / 4 := by omega
      rw [h1] at ih
      dsimp at ih
      rw [h_mod_succ, h_div_succ]
      simp [P]
      set k := n / 4
      rcases ih with ⟨hx, hy, hd⟩
      rcases hy with ⟨Y, hY⟩
      rcases hd with ⟨D, hD⟩
      have hx_eq : (P n).1 = (2 : ℤ)^k * Y + (2 : ℤ)^(k+1) * D := by omega
      rw [hx_eq, hY]
      have h_pow1 : (2:ℤ)^(k+1) = (2:ℤ)^k * 2 := by
        have : k + 1 = k + 1 := by omega
        rw [pow_succ]
      refine ⟨?_, ?_, ?_⟩
      · use Y + 2 * D - (4 * k + 2) * Y
        have h_n : n = 4 * k + 1 := by omega
        rw [h_n]
        rw [h_pow1]
        push_cast; ring
      · use (4 * k + 2) * (Y + 2 * D) + Y
        have h_n : n = 4 * k + 1 := by omega
        rw [h_n]
        rw [h_pow1]
        push_cast; ring
      · use -(4 * k + 2) * Y - (4 * k + 1) * D
        have h_n : n = 4 * k + 1 := by omega
        rw [h_n]
        rw [h_pow1]
        push_cast; ring
    · -- Case n % 4 = 2
      have h_mod_succ : (n + 1) % 4 = 3 := by omega
      have h_div_succ : (n + 1) / 4 = n / 4 := by omega
      rw [h2] at ih
      dsimp at ih
      rw [h_mod_succ, h_div_succ]
      simp [P]
      set k := n / 4
      rcases ih with ⟨hx, hy, hd⟩
      rcases hy with ⟨Y, hY⟩
      rcases hd with ⟨D, hD⟩
      have hx_eq : (P n).1 = (2 : ℤ)^k * Y + (2 : ℤ)^(k+1) * D := by omega
      rw [hx_eq, hY]
      have h_pow1 : (2:ℤ)^(k+1) = (2:ℤ)^k * 2 := by
        have : k + 1 = k + 1 := by omega
        rw [pow_succ]
      constructor
      · use D - (2 * (k:ℤ) + 1) * Y
        have h_n : n = 4 * k + 2 := by omega
        rw [h_n]
        rw [h_pow1]
        push_cast; ring
      · use 2 * ((k:ℤ) + 1) * Y + (4 * (k:ℤ) + 3) * D
        have h_n : n = 4 * k + 2 := by omega
        rw [h_n]
        rw [h_pow1]
        push_cast; ring
    · -- Case n % 4 = 3
      have h_mod_succ : (n + 1) % 4 = 0 := by omega
      have h_div_succ : (n + 1) / 4 = n / 4 + 1 := by omega
      rw [h3] at ih
      dsimp at ih
      rw [h_mod_succ, h_div_succ]
      simp [P]
      set k := n / 4
      rcases ih with ⟨hx, hy⟩
      rcases hx with ⟨X, hX⟩
      rcases hy with ⟨Y, hY⟩
      rw [hX, hY]
      have h_pow1 : (2:ℤ)^(k+1) = (2:ℤ)^k * 2 := by
        have : k + 1 = k + 1 := by omega
        rw [pow_succ]
      constructor
      · use X - (4 * k + 4) * Y
        have h_n : n = 4 * k + 3 := by omega
        rw [h_n]
        rw [h_pow1]
        push_cast; ring
      · use (4 * k + 4) * X + Y
        have h_n : n = 4 * k + 3 := by omega
        rw [h_n]
        rw [h_pow1]
        push_cast; ring


theorem P_norm_pos (n : ℕ) : (P n).1^2 + (P n).2^2 > 0 := by
  induction n with
  | zero =>
    simp [P]
  | succ n ih =>
    have h_eq : (P (n + 1)).1^2 + (P (n + 1)).2^2 = (1 + ((n + 1 : ℕ) : ℤ)^2) * ((P n).1^2 + (P n).2^2) := by
      simp [P]
      ring
    rw [h_eq]
    have h_sq_pos : 1 + ((n + 1 : ℕ) : ℤ)^2 > 0 := by
      have : ((n + 1 : ℕ) : ℤ)^2 ≥ 0 := sq_nonneg _
      omega
    exact mul_pos h_sq_pos ih

theorem valuation_one_add_sq_even (m : ℤ) (h : m % 2 = 0) : padicValInt 2 (1 + m^2) = 0 := by
  unfold padicValInt
  apply padicValNat.eq_zero_of_not_dvd
  intro hc
  have h_dvd : (2 : ℤ) ∣ (1 + m^2) := by
    rwa [← Int.ofNat_dvd_left] at hc
  have h_mod : (1 + m^2) % 2 = 1 := by
    have hm : m = 2 * (m / 2) := by omega
    set k := m / 2
    rw [hm]
    have : 1 + (2 * k)^2 = 2 * (2 * k^2) + 1 := by ring
    rw [this]
    omega
  have h_hc : (1 + m^2) % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h_dvd
  omega

theorem valuation_one_add_sq_odd (m : ℤ) (h : m % 2 = 1) : padicValInt 2 (1 + m^2) = 1 := by
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_eq : 1 + m^2 = 2 * (2 * (m / 2)^2 + 2 * (m / 2) + 1) := by
    have : m = 2 * (m / 2) + 1 := by omega
    nth_rw 1 [this]
    ring
  have h_odd : ¬ (2 : ℤ) ∣ (2 * (m / 2)^2 + 2 * (m / 2) + 1) := by
    intro hc
    rcases hc with ⟨d, hd⟩
    omega
  have h_eq_zero : padicValInt 2 (2 * (m / 2)^2 + 2 * (m / 2) + 1) = 0 := by
    unfold padicValInt
    apply padicValNat.eq_zero_of_not_dvd
    intro hc
    apply h_odd
    rwa [← Int.ofNat_dvd_left] at hc
  rw [h_eq]
  rw [padicValInt.mul]
  · have h2 : padicValInt 2 2 = 1 := by
      unfold padicValInt
      norm_num
    rw [h2, h_eq_zero, add_zero]
  · norm_num
  · intro hc
    have h_mod : (2 * (m / 2)^2 + 2 * (m / 2) + 1) % 2 = 1 := by
      set k := m / 2
      have : 2 * k^2 + 2 * k + 1 = 2 * (k^2 + k) + 1 := by ring
      rw [this]
      omega
    rw [hc] at h_mod
    norm_num at h_mod

theorem valuation_one_add_sq (m : ℤ) : padicValInt 2 (1 + m^2) = if m % 2 = 0 then 0 else 1 := by
  by_cases h : m % 2 = 0
  · rw [if_pos h]
    exact valuation_one_add_sq_even m h
  · have h_odd : m % 2 = 1 := by omega
    rw [if_neg h]
    exact valuation_one_add_sq_odd m h_odd

theorem valuation_P_norm (n : ℕ) : padicValInt 2 ((P n).1^2 + (P n).2^2) = (n + 1) / 2 := by
  induction n with
  | zero =>
    simp [P, valuation_one_add_sq]
  | succ n ih =>
    have h_eq : (P (n + 1)).1^2 + (P (n + 1)).2^2 = (1 + ((n + 1 : ℕ) : ℤ)^2) * ((P n).1^2 + (P n).2^2) := by
      simp [P]
      ring
    rw [h_eq]
    rw [padicValInt.mul]
    · have h_val : padicValInt 2 (1 + ((n + 1 : ℕ) : ℤ)^2) = if (n + 1) % 2 = 0 then 0 else 1 := by
        have h_eq2 : (1 + ((n + 1 : ℕ) : ℤ)^2) = 1 + (n + 1 : ℤ)^2 := by push_cast; rfl
        rw [h_eq2, valuation_one_add_sq (n + 1 : ℤ)]
        have h_mod : (n + 1 : ℤ) % 2 = ↑((n + 1) % 2) := by simp
        rw [h_mod]
        split_ifs with h1 h2 h2
        · rfl
        · exfalso; omega
        · exfalso; omega
        · rfl
      rw [h_val, ih]
      split_ifs with h
      · have : (n + 1) % 2 = 0 := h
        omega
      · have : (n + 1) % 2 = 1 := by omega
        omega
    · have : 1 + ((n + 1 : ℕ) : ℤ)^2 ≥ 1 := by
        have : ((n + 1 : ℕ) : ℤ)^2 ≥ 0 := sq_nonneg _
        omega
      omega
    · exact ne_of_gt (P_norm_pos n)

theorem val_eq_of_dvd_not_dvd {y : ℤ} {k : ℕ} (hy0 : y ≠ 0) (h1 : (2:ℤ)^k ∣ y) (h2 : ¬ (2:ℤ)^(k+1) ∣ y) : padicValInt 2 y = k := by
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy0' : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy0
  have hd1 : 2^k ∣ y.natAbs := by
    have h_eq : (2:ℤ)^k = ((2^k : ℕ) : ℤ) := by simp
    rw [h_eq] at h1
    rwa [Int.ofNat_dvd_left] at h1
  have hd2 : ¬ 2^(k+1) ∣ y.natAbs := by
    intro hc
    apply h2
    have h_eq : (2:ℤ)^(k+1) = ((2^(k+1) : ℕ) : ℤ) := by simp
    rw [h_eq]
    rwa [Int.ofNat_dvd_left]
  unfold padicValInt
  rw [padicValNat_dvd_iff_le hy0'] at hd1 hd2
  omega

theorem valuation_a_eq_k (n : ℕ) (h_ih : InductionHyp n) (h_mod : n % 4 = 1 ∨ n % 4 = 2) :
    padicValInt 2 (P n).2 = n / 4 := by
  have h_prime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set k := n / 4
  have h_cases : n % 4 = 1 ∨ n % 4 = 2 := h_mod
  have h_ih_cases : 2^k ∣ (P n).1 ∧ 2^k ∣ (P n).2 ∧ 2^(k+1) ∣ ((P n).1 - (P n).2) := by
    unfold InductionHyp at h_ih
    rcases h_cases with h1 | h2
    · rw [h1] at h_ih; exact h_ih
    · rw [h2] at h_ih; exact h_ih
  rcases h_ih_cases with ⟨h_x, h_y, h_xy⟩
  have h_not_div_y : ¬ (2:ℤ)^(k+1) ∣ (P n).2 := by
    intro h_div_y
    have h_div_x : (2:ℤ)^(k+1) ∣ (P n).1 := by
      have h_eq : (P n).1 = ((P n).1 - (P n).2) + (P n).2 := by ring
      rw [h_eq]
      exact dvd_add h_xy h_div_y
    have h_div_norm : (2:ℤ)^(2*k + 2) ∣ ((P n).1^2 + (P n).2^2) := by
      rcases h_div_x with ⟨A, hA⟩
      rcases h_div_y with ⟨B, hB⟩
      use A^2 + B^2
      rw [hA, hB]
      ring
    have hd_nat : 2^(2*k + 2) ∣ ((P n).1^2 + (P n).2^2).natAbs := by
      have h_eq : (2:ℤ)^(2*k + 2) = ((2^(2*k + 2) : ℕ) : ℤ) := by simp
      rw [h_eq] at h_div_norm
      rwa [Int.ofNat_dvd_left] at h_div_norm
    have h_pos : ((P n).1^2 + (P n).2^2).natAbs ≠ 0 := by
      have : ((P n).1^2 + (P n).2^2) > 0 := P_norm_pos n
      omega
    rw [padicValNat_dvd_iff_le h_pos] at hd_nat
    have h_val : padicValInt 2 ((P n).1^2 + (P n).2^2) = (n + 1) / 2 := valuation_P_norm n
    unfold padicValInt at h_val
    rw [h_val] at hd_nat
    rcases h_cases with h1 | h2
    · have : (n + 1) / 2 = 2 * k + 1 := by omega
      omega
    · have : (n + 1) / 2 = 2 * k + 1 := by omega
      omega
  have hy_ne_zero : (P n).2 ≠ 0 := by
    intro hc
    apply h_not_div_y
    rw [hc]
    exact dvd_zero _
  exact val_eq_of_dvd_not_dvd hy_ne_zero h_y h_not_div_y


lemma le_pow_two_add_two (S : ℕ) : S * S + 2 * S ≤ 2 ^ (2 * S) := by
  induction S with
  | zero => simp
  | succ S ih =>
    by_cases hS : S = 0
    · subst hS; decide
    · have h1 : (S + 1) * (S + 1) + 2 * (S + 1) = S * S + 4 * S + 3 := by ring
      have h2 : 2 ^ (2 * (S + 1)) = 4 * 2 ^ (2 * S) := by
        have : 2 * (S + 1) = 2 * S + 2 := by ring
        rw [this, pow_add]
        ring
      rw [h1, h2]
      have h_ih' : S * S + 4 * S + 3 ≤ 4 * (S * S + 2 * S) := by omega
      exact le_trans h_ih' (Nat.mul_le_mul_left 4 ih)

lemma pow_two_mul_sqrt_ge (x : ℕ) : x ≤ 2 ^ (2 * Nat.sqrt x) := by
  have h1 : x < (Nat.sqrt x + 1) * (Nat.sqrt x + 1) := Nat.lt_succ_sqrt x
  have h_eq : (Nat.sqrt x + 1) * (Nat.sqrt x + 1) = Nat.sqrt x * Nat.sqrt x + 2 * Nat.sqrt x + 1 := by ring
  rw [h_eq] at h1
  have h2 : x ≤ Nat.sqrt x * Nat.sqrt x + 2 * Nat.sqrt x := by omega
  exact le_trans h2 (le_pow_two_add_two (Nat.sqrt x))

lemma log_two_le_two_mul_sqrt (x : ℕ) : Nat.log 2 x ≤ 2 * Nat.sqrt x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have hx_pos : x ≠ 0 := hx
    have h1 : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 hx_pos
    have h2 : x ≤ 2 ^ (2 * Nat.sqrt x) := pow_two_mul_sqrt_ge x
    have h3 : 2 ^ Nat.log 2 x ≤ 2 ^ (2 * Nat.sqrt x) := le_trans h1 h2
    exact (Nat.pow_le_pow_iff_right (by decide)).1 h3

lemma padicValNat_le_two_mul_sqrt (x : ℕ) : padicValNat 2 x ≤ 2 * Nat.sqrt x :=
  le_trans (padicValNat_le_nat_log x) (log_two_le_two_mul_sqrt x)

lemma sqrt_div_self_le (n : ℕ) (hn : n ≥ 1) :
    (Nat.sqrt n : ℚ) / (n : ℚ) ≤ 1 / (Nat.sqrt n : ℚ) := by
  have hS_pos : (Nat.sqrt n : ℚ) > 0 := by
    have : Nat.sqrt n ≥ 1 := Nat.le_sqrt.mpr (by omega)
    exact_mod_cast this
  have h_sq : (Nat.sqrt n : ℚ) * (Nat.sqrt n : ℚ) ≤ n := by
    have := Nat.sqrt_le n
    exact_mod_cast this
  have h_mul : (Nat.sqrt n : ℚ) * (Nat.sqrt n : ℚ) / (n : ℚ) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    simpa using h_sq
  have : (Nat.sqrt n : ℚ) / (n : ℚ) = ((Nat.sqrt n : ℚ) * (Nat.sqrt n : ℚ) / (n : ℚ)) * (1 / (Nat.sqrt n : ℚ)) := by
    have h_ne : (Nat.sqrt n : ℚ) ≠ 0 := by positivity
    field_simp
  rw [this]
  have h_inv_pos : 1 / (Nat.sqrt n : ℚ) ≥ 0 := by positivity
  nlinarith


lemma tendsto_sqrt_atTop_coe : Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℚ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨q, hq⟩ := exists_nat_ge b
  use q ^ 2
  intro n hn
  have h_sqrt : q ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt, ← pow_two]
    exact hn
  have h_cast : (q : ℚ) ≤ (Nat.sqrt n : ℚ) := by exact_mod_cast h_sqrt
  linarith


lemma tendsto_sqrt_div_self_atTop : Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℚ) / (n : ℚ)) atTop (nhds 0) := by
  have h_inv : Tendsto (fun n : ℕ ↦ 1 / (Nat.sqrt n : ℚ)) atTop (nhds 0) := by
    have h_comp := Tendsto.comp tendsto_inv_atTop_zero tendsto_sqrt_atTop_coe
    have h_eq : (fun n : ℕ ↦ 1 / (Nat.sqrt n : ℚ)) = (fun n ↦ (Nat.sqrt n : ℚ)⁻¹) := by
      ext n; simp [one_div]
    rw [h_eq]
    exact h_comp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ ↦ 0) (h := fun n ↦ 1 / (Nat.sqrt n : ℚ))
  · exact tendsto_const_nhds
  · exact h_inv
  · intro n
    by_cases hn : n ≥ 1
    · have : (Nat.sqrt n : ℚ) ≥ 0 := by positivity
      have : (n : ℚ) ≥ 0 := by positivity
      exact div_nonneg (by positivity) (by positivity)
    · have : n = 0 := by omega
      subst this; simp
  · intro n
    by_cases hn : n ≥ 1
    · exact sqrt_div_self_le n hn
    · have : n = 0 := by omega
      subst this; simp


lemma valuation_le_norm (n : ℕ) :
    2 ^ (2 * padicValInt 2 (P n).2) ≤ (P n).1^2 + (P n).2^2 := by
  by_cases hy : (P n).2 = 0
  · have h_pos := P_norm_pos n
    rw [hy] at h_pos ⊢
    have h_v0 : padicValInt 2 0 = 0 := by
      unfold padicValInt
      rfl
    rw [h_v0]
    simp only [mul_zero, pow_zero, zero_pow, add_zero, Int.cast_zero] at h_pos ⊢
    omega
  · have h_le : 2 ^ padicValInt 2 (P n).2 ≤ ((P n).2).natAbs := by
      unfold padicValInt
      have h_dvd := pow_padicValNat_dvd (p := 2) (n := ((P n).2).natAbs)
      have h_pos : ((P n).2).natAbs > 0 := by
        have : (P n).2 ≠ 0 := hy
        omega
      exact Nat.le_of_dvd h_pos h_dvd
    have h_le2 : (2 ^ padicValInt 2 (P n).2) ^ 2 ≤ ((P n).2).natAbs ^ 2 := Nat.pow_le_pow_left h_le 2
    have h_le2_cast : ((2 ^ padicValInt 2 (P n).2) ^ 2 : ℤ) ≤ ((P n).2.natAbs : ℤ) ^ 2 := by exact_mod_cast h_le2
    rw [Int.natAbs_sq] at h_le2_cast
    have h_pow_eq : ((2 ^ padicValInt 2 (P n).2) ^ 2 : ℤ) = (2 : ℤ) ^ (2 * padicValInt 2 (P n).2) := by
      push_cast
      ring
    rw [h_pow_eq] at h_le2_cast
    have h_norm : (P n).2^2 ≤ (P n).1^2 + (P n).2^2 := by
      have : (P n).1^2 ≥ 0 := sq_nonneg _
      omega
    exact le_trans h_le2_cast h_norm

lemma P_succ_succ_succ_succ (n : ℕ) :
    (P (n + 4)).1 = ((n : ℤ)^4 + 10 * (n : ℤ)^3 + 29 * (n : ℤ)^2 + 20 * (n : ℤ) - 10) * (P n).1 - (- (4 * (n : ℤ)^3 + 30 * (n : ℤ)^2 + 66 * (n : ℤ) + 40)) * (P n).2 ∧
    (P (n + 4)).2 = (- (4 * (n : ℤ)^3 + 30 * (n : ℤ)^2 + 66 * (n : ℤ) + 40)) * (P n).1 + ((n : ℤ)^4 + 10 * (n : ℤ)^3 + 29 * (n : ℤ)^2 + 20 * (n : ℤ) - 10) * (P n).2 := by
  have h1 : (P (n + 1)).1 = (P n).1 - (n + 1 : ℤ) * (P n).2 ∧ (P (n + 1)).2 = (n + 1 : ℤ) * (P n).1 + (P n).2 := by
    exact ⟨rfl, rfl⟩
  have h2 : (P (n + 2)).1 = (P (n + 1)).1 - (n + 2 : ℤ) * (P (n + 1)).2 ∧ (P (n + 2)).2 = (n + 2 : ℤ) * (P (n + 1)).1 + (P (n + 1)).2 := by
    exact ⟨rfl, rfl⟩
  have h3 : (P (n + 3)).1 = (P (n + 2)).1 - (n + 3 : ℤ) * (P (n + 2)).2 ∧ (P (n + 3)).2 = (n + 3 : ℤ) * (P (n + 2)).1 + (P (n + 2)).2 := by
    exact ⟨rfl, rfl⟩
  have h4 : (P (n + 4)).1 = (P (n + 3)).1 - (n + 4 : ℤ) * (P (n + 3)).2 ∧ (P (n + 4)).2 = (n + 4 : ℤ) * (P (n + 3)).1 + (P (n + 3)).2 := by
    exact ⟨rfl, rfl⟩
  rcases h1 with ⟨x1, y1⟩
  rcases h2 with ⟨x2, y2⟩
  rcases h3 with ⟨x3, y3⟩
  rcases h4 with ⟨x4, y4⟩
  rw [x4, y4, x3, y3, x2, y2, x1, y1]
  constructor <;> ring


theorem dvd_a (n : ℕ) : (2 : ℤ)^(n / 4) ∣ a n := by
  rw [a_eq_P_im]
  have h_ih := induction_hyp_step n
  unfold InductionHyp at h_ih
  rcases h_mod : n % 4 with _ | _ | _ | _
  · rw [h_mod] at h_ih; exact h_ih.2
  · rw [h_mod] at h_ih; exact h_ih.2.1
  · rw [h_mod] at h_ih; exact h_ih.2.1
  · rw [h_mod] at h_ih
    have h_div : (2 : ℤ)^(n / 4 + 1) ∣ (P n).2 := h_ih.2
    have h_le : n / 4 ≤ n / 4 + 1 := by omega
    have h_pow : (2 : ℤ)^(n / 4) ∣ (2 : ℤ)^(n / 4 + 1) := pow_dvd_pow _ h_le
    exact dvd_trans h_pow h_div


lemma valuation_a_ge_k (n : ℕ) (hn : a n ≠ 0) : padicValInt 2 (a n) ≥ n / 4 := by
  have h_dvd := dvd_a n
  have h_pos : (a n).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  unfold padicValInt
  change n / 4 ≤ padicValNat 2 (a n).natAbs
  rw [← padicValNat_dvd_iff_le h_pos]
  have h_pow_eq : (2 : ℤ)^(n / 4) = (((2^(n / 4) : ℕ) : ℤ)) := by simp
  rw [h_pow_eq] at h_dvd
  rwa [Int.ofNat_dvd_left] at h_dvd






lemma bound_linear (n : ℕ) : 2 * n + 3 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_eq : 2 * (n + 1) + 3 = (2 * n + 3) + 2 := by omega
    rw [h_eq]
    have h_pow : 2 ^ (n + 1 + 2) = 2 ^ (n + 2) + 2 ^ (n + 2) := by
      have : n + 1 + 2 = n + 2 + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [h_pow]
    have h_two : 2 ≤ 2 ^ (n + 2) := by
      have h_pow_eq : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := by
        have : n + 2 = n + 1 + 1 := by omega
        rw [this, pow_succ]
      rw [h_pow_eq]
      have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow (n + 1) 2 (by decide)
      omega
    omega

lemma bound_quadratic (n : ℕ) : 1 + (n + 1)^2 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h_eq : 1 + (n + 1 + 1)^2 = 1 + (n + 1)^2 + 2 * n + 3 := by ring
    rw [h_eq]
    have h_pow : 2 ^ (n + 1 + 2) = 2 ^ (n + 2) + 2 ^ (n + 2) := by
      have : n + 1 + 2 = n + 2 + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [h_pow]
    have h_lin := bound_linear n
    omega

lemma norm_le_power (n : ℕ) : (P n).1^2 + (P n).2^2 ≤ (2 : ℤ)^(n^2 + 3 * n + 1) := by
  induction n with
  | zero =>
    simp [P]
  | succ n ih =>
    have h_eq : (P (n + 1)).1^2 + (P (n + 1)).2^2 = (1 + (n + 1 : ℤ)^2) * ((P n).1^2 + (P n).2^2) := by
      simp [P]
      ring
    rw [h_eq]
    have h_bound : 1 + (n + 1 : ℤ)^2 ≤ (2 : ℤ)^(n + 2) := by
      have hq := bound_quadratic n
      exact_mod_cast hq
    have h_pos_norm : (P n).1^2 + (P n).2^2 ≥ 0 := by positivity
    have h_pos_bound : (2 : ℤ)^(n + 2) ≥ 0 := by positivity
    have h_mul : (1 + (n + 1 : ℤ)^2) * ((P n).1^2 + (P n).2^2) ≤ (2 : ℤ)^(n + 2) * (2 : ℤ)^(n^2 + 3 * n + 1) := by
      apply mul_le_mul h_bound ih h_pos_norm h_pos_bound
    have h_pow : (2 : ℤ)^(n + 2) * (2 : ℤ)^(n^2 + 3 * n + 1) = (2 : ℤ)^(n^2 + 4 * n + 3) := by
      rw [← pow_add]
      congr 1
      ring
    have h_le : (2 : ℤ)^(n^2 + 4 * n + 3) ≤ (2 : ℤ)^((n + 1)^2 + 3 * (n + 1) + 1) := by
      have h_exp : n^2 + 4 * n + 3 ≤ (n + 1)^2 + 3 * (n + 1) + 1 := by ring_nf; omega
      have h_nat : 2^(n^2 + 4 * n + 3) ≤ 2^((n + 1)^2 + 3 * (n + 1) + 1) := Nat.pow_le_pow_right (by decide) h_exp
      exact_mod_cast h_nat
    rw [h_pow] at h_mul
    exact le_trans h_mul h_le


lemma P_identity (n : ℕ) :
    ((n + 1 : ℤ)^2 + 1) * (P n).2 = (P (n + 1)).2 - (n + 1 : ℤ) * (P (n + 1)).1 := by
  simp [P]
  ring


lemma P_identity_3 (n : ℕ) (hn : n ≥ 1) :
    (P n).2 = (n : ℤ) * (P (n - 1)).1 + (P (n - 1)).2 := by
  rcases n with _ | n
  · omega
  · simp [P]


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
      exact padicValNat.prime_pow (k + 1)
    have h_odd : padicValInt 2 x = 0 := by
      unfold padicValInt
      apply padicValNat.eq_zero_of_not_dvd
      intro hc
      have h_dvd : (2:ℤ) ∣ x := Int.natAbs_dvd_natAbs.mp hc
      have h_mod : x % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h_dvd
      omega
    rw [h2, h_odd, add_zero]
  · positivity
  · intro hc
    subst hc
    omega


def Property (k : ℕ) : Prop :=
  2^k ∣ (P (4 * k)).1 ∧ ¬ (2^(k+1) ∣ (P (4 * k)).1) ∧ 2^(k+2) ∣ (P (4 * k)).2

lemma Property_one : Property 1 := by
  unfold Property
  decide

lemma dvd_of_pow_succ_dvd_mul (k : ℕ) (A : ℤ) (h : (2 : ℤ)^(k + 2) ∣ (2 : ℤ)^(k + 1) * A) : 2 ∣ A := by
  have h_pow : (2 : ℤ)^(k + 2) = (2 : ℤ)^(k + 1) * 2 := by ring
  rw [h_pow] at h
  have h_two : (2 : ℤ)^(k + 1) ≠ 0 := by positivity
  rwa [mul_dvd_mul_iff_left h_two] at h

lemma Property_step (k : ℕ) (hk : k ≥ 1) (ih : Property k) : Property (k + 1) := by
  unfold Property at *
  rcases ih with ⟨h1, h2, h3⟩
  rcases h1 with ⟨X, hX⟩
  rcases h3 with ⟨Y, hY⟩
  have hX_odd : X % 2 = 1 ∨ X % 2 = -1 := by
    by_contra hc
    push_neg at hc
    have : X = 2 * (X / 2) := by omega
    have h_div : (2 : ℤ)^(k + 1) ∣ (P (4 * k)).1 := by
      rw [hX, this]
      use X / 2
      ring
    exact h2 h_div
  have h_succ := P_succ_succ_succ_succ (4 * k)
  have h_eq1 : 4 * k + 4 = 4 * (k + 1) := by omega
  rw [h_eq1] at h_succ
  rcases h_succ with ⟨h_succ1, h_succ2⟩
  rw [coeff_C_eq, coeff_D_eq] at h_succ1 h_succ2
  rw [hX, hY] at h_succ1 h_succ2
  have h_pow1 : (2 : ℤ)^(k + 1) = (2 : ℤ)^k * 2 := by rw [pow_add, pow_one]
  have h_pow2 : (2 : ℤ)^(k + 2) = (2 : ℤ)^k * 4 := by rw [pow_add]; rfl
  have h_pow3 : (2 : ℤ)^(k + 3) = (2 : ℤ)^k * 8 := by rw [pow_add]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [h_succ1]
    rw [h_pow1, h_pow2]
    use (128 * (k : ℤ)^4 + 320 * (k : ℤ)^3 + 232 * (k : ℤ)^2 + 40 * (k : ℤ) - 5) * X + 16 * (32 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 33 * (k : ℤ) + 5) * Y
    ring
  · intro hc
    have h_eq : (P (4 * (k + 1))).1 = (2 : ℤ)^(k + 1) * ( (128 * (k : ℤ)^4 + 320 * (k : ℤ)^3 + 232 * (k : ℤ)^2 + 40 * (k : ℤ) - 5) * X + 16 * (32 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 33 * (k : ℤ) + 5) * Y ) := by
      rw [h_succ1]
      rw [h_pow1, h_pow2]
      ring
    rw [h_eq] at hc
    have h_div := dvd_of_pow_succ_dvd_mul k _ hc
    have h_odd : ¬ 2 ∣ (128 * (k : ℤ)^4 + 320 * (k : ℤ)^3 + 232 * (k : ℤ)^2 + 40 * (k : ℤ) - 5) * X + 16 * (32 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 33 * (k : ℤ) + 5) * Y := by
      intro h_dvd
      have h_dvd2 : 2 ∣ 16 * (32 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 33 * (k : ℤ) + 5) * Y := by
        use 8 * (32 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 33 * (k : ℤ) + 5) * Y
        ring
      have h_sub := dvd_sub h_dvd h_dvd2
      have h_sub_simplified : 2 ∣ (128 * (k : ℤ)^4 + 320 * (k : ℤ)^3 + 232 * (k : ℤ)^2 + 40 * (k : ℤ) - 5) * X := by
        have h_eq_sub : (128 * (k : ℤ)^4 + 320 * (k : ℤ)^3 + 232 * (k : ℤ)^2 + 40 * (k : ℤ) - 5) * X + 16 * (32 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 33 * (k : ℤ) + 5) * Y - 16 * (32 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 33 * (k : ℤ) + 5) * Y = (128 * (k : ℤ)^4 + 320 * (k : ℤ)^3 + 232 * (k : ℤ)^2 + 40 * (k : ℤ) - 5) * X := by ring
        rw [← h_eq_sub]
        exact h_sub
      have h_mod : ((128 * (k : ℤ)^4 + 320 * (k : ℤ)^3 + 232 * (k : ℤ)^2 + 40 * (k : ℤ) - 5) * X) % 2 ≠ 0 := by
        rw [Int.mul_emod]
        rcases hX_odd with hX_odd' | hX_odd'
        · rw [hX_odd']
          have : (128 * (k : ℤ)^4 + 320 * (k : ℤ)^3 + 232 * (k : ℤ)^2 + 40 * (k : ℤ) - 5) % 2 = 1 := by omega
          rw [this]
          decide
        · rw [hX_odd']
          have : (128 * (k : ℤ)^4 + 320 * (k : ℤ)^3 + 232 * (k : ℤ)^2 + 40 * (k : ℤ) - 5) % 2 = 1 := by omega
          rw [this]
          decide
      have h_mod2 : ((128 * (k : ℤ)^4 + 320 * (k : ℤ)^3 + 232 * (k : ℤ)^2 + 40 * (k : ℤ) - 5) * X) % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h_sub_simplified
      exact h_mod h_mod2
    exact h_odd h_div
  · rw [h_succ2]
    rw [h_pow2, h_pow3]
    use - (32 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 33 * (k : ℤ) + 5) * X + (2 * (64 * (k : ℤ)^4 + 160 * (k : ℤ)^3 + 116 * (k : ℤ)^2 + 20 * (k : ℤ) - 3) + 1) * Y
    ring

lemma Property_all (k : ℕ) (hk : k ≥ 1) : Property k := by
  induction k, hk using Nat.le_induction with
  | base => exact Property_one
  | succ k hk' ih => exact Property_step k hk' ih

lemma P_succ_succ_succ (n : ℕ) :
    (P (n + 3)).2 = (- ((n : ℤ)^3 + 6 * (n : ℤ)^2 + 8 * (n : ℤ))) * (P n).1 + (- (3 * (n : ℤ)^2 + 12 * (n : ℤ) + 10)) * (P n).2 := by
  have h1 : (P (n + 1)).1 = (P n).1 - (n + 1 : ℤ) * (P n).2 ∧ (P (n + 1)).2 = (n + 1 : ℤ) * (P n).1 + (P n).2 := ⟨rfl, rfl⟩
  have h2 : (P (n + 2)).1 = (P (n + 1)).1 - (n + 2 : ℤ) * (P (n + 1)).2 ∧ (P (n + 2)).2 = (n + 2 : ℤ) * (P (n + 1)).1 + (P (n + 1)).2 := ⟨rfl, rfl⟩
  have h3 : (P (n + 3)).1 = (P (n + 2)).1 - (n + 3 : ℤ) * (P (n + 2)).2 ∧ (P (n + 3)).2 = (n + 3 : ℤ) * (P (n + 2)).1 + (P (n + 2)).2 := ⟨rfl, rfl⟩
  rcases h1 with ⟨x1, y1⟩
  rcases h2 with ⟨x2, y2⟩
  rcases h3 with ⟨x3, y3⟩
  rw [y3, x2, y2, x1, y1]
  ring

lemma coeff_odd_case_0 (n : ℕ) (h0 : n % 4 = 0) :
    ((n : ℤ)^3 + 6 * (n : ℤ)^2 + 8 * (n : ℤ) - 3) % 2 = 1 ∨
    ((n : ℤ)^3 + 6 * (n : ℤ)^2 + 8 * (n : ℤ) - 3) % 2 = -1 := by
  have : (n : ℤ) = 4 * (n / 4 : ℕ) := by
    have : n = 4 * (n / 4) := by omega
    exact_mod_cast this
  set k := (n / 4 : ℕ)
  rw [this]
  have h_eq : (4 * (k : ℤ))^3 + 6 * (4 * (k : ℤ))^2 + 8 * (4 * (k : ℤ)) - 3 = 2 * (32 * (k : ℤ)^3 + 48 * (k : ℤ)^2 + 16 * (k : ℤ) - 2) + 1 := by ring
  rw [h_eq]
  omega

lemma coeff_val_case_3 (n : ℕ) (h3 : n % 4 = 3) :
    padicValInt 2 ((n : ℤ)^3 + 6 * (n : ℤ)^2 + 8 * (n : ℤ) - 3) = 1 := by
  have : (n : ℤ) = 4 * (n / 4 : ℕ) + 3 := by
    have : n = 4 * (n / 4) + 3 := by omega
    exact_mod_cast this
  set k := (n / 4 : ℕ)
  rw [this]
  have h_eq : (4 * (k : ℤ) + 3)^3 + 6 * (4 * (k : ℤ) + 3)^2 + 8 * (4 * (k : ℤ) + 3) - 3 = 2 * (2 * (16 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 71 * (k : ℤ) + 25) + 1) := by ring
  rw [h_eq]
  rw [padicValInt.mul]
  · have h2 : padicValInt 2 2 = 1 := by unfold padicValInt; norm_num
    have h_odd : padicValInt 2 (2 * (16 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 71 * (k : ℤ) + 25) + 1) = 0 := by
      unfold padicValInt
      apply padicValNat.eq_zero_of_not_dvd
      intro hc
      have h_dvd : (2 : ℤ) ∣ (2 * (16 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 71 * (k : ℤ) + 25) + 1) := Int.natAbs_dvd_natAbs.mp hc
      have h_mod : (2 * (16 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 71 * (k : ℤ) + 25) + 1) % 2 = 0 := Int.dvd_iff_emod_eq_zero.mp h_dvd
      omega
    rw [h2, h_odd, add_zero]
  · norm_num
  · intro hc
    have h_mod : (2 * (16 * (k : ℤ)^3 + 60 * (k : ℤ)^2 + 71 * (k : ℤ) + 25) + 1) % 2 = 1 := by omega
    rw [hc] at h_mod
    norm_num at h_mod




lemma valuation_P_im_le_half_norm (n : ℕ) (h_mod : n % 4 = 1 ∨ n % 4 = 2) (hy : (P n).2 ≠ 0) :
    2 * padicValInt 2 (P n).2 ≤ (n + 1) / 2 := by
  have h_val := valuation_a_eq_k n (induction_hyp_step n) h_mod
  rw [h_val]
  omega

lemma valuation_a_le (n : ℕ) : (padicValInt 2 (a n) : ℚ) ≤ (n : ℚ) / 4 + 2 * (Nat.sqrt n : ℚ) + 3 := by
  have h_mod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h_mod with h0 | h1 | h2 | h3
  · sorry
  · rw [a_eq_P_im]
    have h_val := valuation_a_eq_k n (induction_hyp_step n) (Or.inl h1)
    rw [h_val]
    have h_div : (n / 4 : ℕ) * 4 ≤ n := Nat.div_mul_le_self n 4
    have h_div_q : ((n / 4 : ℕ) : ℚ) * 4 ≤ (n : ℚ) := by exact_mod_cast h_div
    have : ((n / 4 : ℕ) : ℚ) ≤ (n : ℚ) / 4 := by linarith
    have h_sqrt : (Nat.sqrt n : ℚ) ≥ 0 := by positivity
    linarith
  · rw [a_eq_P_im]
    have h_val := valuation_a_eq_k n (induction_hyp_step n) (Or.inr h2)
    rw [h_val]
    have h_div : (n / 4 : ℕ) * 4 ≤ n := Nat.div_mul_le_self n 4
    have h_div_q : ((n / 4 : ℕ) : ℚ) * 4 ≤ (n : ℚ) := by exact_mod_cast h_div
    have : ((n / 4 : ℕ) : ℚ) ≤ (n : ℚ) / 4 := by linarith
    have h_sqrt : (Nat.sqrt n : ℚ) ≥ 0 := by positivity
    linarith
  · sorry

lemma a_ne_zero_mod12 (n : ℕ) (hn : n ≥ 4) (h_mod : n % 4 = 1 ∨ n % 4 = 2) : a n ≠ 0 := by
  have h_val := valuation_a_eq_k n (induction_hyp_step n) h_mod
  rw [a_eq_P_im]
  intro hc
  rw [hc] at h_val
  have h_v0 : padicValInt 2 0 = 0 := by
    unfold padicValInt
    rfl
  rw [h_v0] at h_val
  have h_div : n / 4 ≥ 1 := by omega
  omega

lemma a_ne_zero (n : ℕ) (hn : n ≥ 4) : a n ≠ 0 := by
  have h_mod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h_mod with h0 | h1 | h2 | h3
  · sorry
  · exact a_ne_zero_mod12 n hn (Or.inl h1)
  · exact a_ne_zero_mod12 n hn (Or.inr h2)
  · sorry

def g_seq (n : ℕ) : ℚ :=
  if n < 4 then -1 else 1 - 4 / (n : ℚ)

def h_seq (n : ℕ) : ℚ :=
  if n < 4 then 100 else 1 + 8 * (Nat.sqrt n : ℚ) / (n : ℚ) + 12 / (n : ℚ)

lemma tendsto_g : Tendsto g_seq atTop (nhds 1) := by
  have h_eq : ∀ᶠ (n : ℕ) in atTop, g_seq n = 1 - 4 * (n : ℚ)⁻¹ := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    unfold g_seq
    split_ifs with h'
    · omega
    · have : (n : ℚ) ≠ 0 := by positivity
      rw [div_eq_mul_inv, mul_comm]
  rw [tendsto_congr' h_eq]
  have h_inv : Tendsto (fun n : ℕ ↦ (n : ℚ)⁻¹) atTop (nhds 0) :=
    Tendsto.comp tendsto_inv_atTop_zero tendsto_natCast_atTop_atTop
  have h_mul : Tendsto (fun n : ℕ ↦ 4 * (n : ℚ)⁻¹) atTop (nhds (4 * 0)) :=
    Tendsto.const_mul 4 h_inv
  rw [mul_zero] at h_mul
  have h_sub : Tendsto (fun n : ℕ ↦ 1 - 4 * (n : ℚ)⁻¹) atTop (nhds (1 - 0)) :=
    Tendsto.const_sub 1 h_mul
  rw [sub_zero] at h_sub
  exact h_sub

lemma tendsto_h : Tendsto h_seq atTop (nhds 1) := by
  have h_eq : ∀ᶠ (n : ℕ) in atTop, h_seq n = 1 + 8 * ((Nat.sqrt n : ℚ) / (n : ℚ)) + 12 * (n : ℚ)⁻¹ := by
    filter_upwards [eventually_ge_atTop 4] with n hn
    unfold h_seq
    split_ifs with h'
    · omega
    · have : (n : ℚ) ≠ 0 := by positivity
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
  rw [tendsto_congr' h_eq]
  have h_sqrt : Tendsto (fun n : ℕ ↦ (Nat.sqrt n : ℚ) / (n : ℚ)) atTop (nhds 0) := tendsto_sqrt_div_self_atTop
  have h_mul1 : Tendsto (fun n : ℕ ↦ 8 * ((Nat.sqrt n : ℚ) / (n : ℚ))) atTop (nhds (8 * 0)) :=
    Tendsto.const_mul 8 h_sqrt
  rw [mul_zero] at h_mul1
  have h_inv : Tendsto (fun n : ℕ ↦ (n : ℚ)⁻¹) atTop (nhds 0) :=
    Tendsto.comp tendsto_inv_atTop_zero tendsto_natCast_atTop_atTop
  have h_mul2 : Tendsto (fun n : ℕ ↦ 12 * (n : ℚ)⁻¹) atTop (nhds (12 * 0)) :=
    Tendsto.const_mul 12 h_inv
  rw [mul_zero] at h_mul2
  have h_add1 : Tendsto (fun n : ℕ ↦ 1 + 8 * ((Nat.sqrt n : ℚ) / (n : ℚ))) atTop (nhds (1 + 0)) :=
    Tendsto.const_add 1 h_mul1
  rw [add_zero] at h_add1
  have h_add2 : Tendsto (fun n : ℕ ↦ 1 + 8 * ((Nat.sqrt n : ℚ) / (n : ℚ)) + 12 * (n : ℚ)⁻¹) atTop (nhds (1 + 0)) :=
    Tendsto.add h_add1 h_mul2
  rw [add_zero] at h_add2
  exact h_add2

section AsymptoticConjectures

/--
Conjecture (Moll's Conjecture 5.5 analogue for A105751, Type 2 prime p=2):
The 2-adic valuation $v_2(a(n))$ has asymptotic linear behavior,
specifically, $v_2(a(n)) \sim n/4$ as $n \to \infty$.
-/
theorem oeis_A105751_conjecture_Moll_2 :
    Tendsto (fun n ↦ (4 : ℚ) * (padicValInt 2 (a n) : ℚ) / (n : ℚ)) atTop (nhds 1) := by
  have h_g : Tendsto g_seq atTop (nhds 1) := tendsto_g
  have h_h : Tendsto h_seq atTop (nhds 1) := tendsto_h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h_g h_h
  · intro n
    unfold g_seq
    split_ifs with h
    · -- n < 4
      have h_pos : (4 : ℚ) * (padicValInt 2 (a n) : ℚ) / (n : ℚ) ≥ 0 := by positivity
      linarith
    · -- n ≥ 4
      push_neg at h
      have h_pos : (n : ℚ) > 0 := by positivity
      have h_ne : (n : ℚ) ≠ 0 := ne_of_gt h_pos
      have h_v_ge := valuation_a_ge_k n (a_ne_zero n h)
      have h_v_ge_q : (padicValInt 2 (a n) : ℚ) ≥ ((n / 4 : ℕ) : ℚ) := by exact_mod_cast h_v_ge
      have h_div := (Nat.div_add_mod n 4).symm
      have h_div_q : (n : ℚ) = 4 * ((n / 4 : ℕ) : ℚ) + ((n % 4 : ℕ) : ℚ) := by exact_mod_cast h_div
      have h_mod_lt : ((n % 4 : ℕ) : ℚ) < 4 := by
        have : n % 4 < 4 := Nat.mod_lt n (by decide)
        exact_mod_cast this
      have h_mod_ge : ((n % 4 : ℕ) : ℚ) ≥ 0 := by positivity
      have h_div_ge : ((n / 4 : ℕ) : ℚ) ≥ (n : ℚ)/4 - 1 := by linarith
      have h_ge : (padicValInt 2 (a n) : ℚ) ≥ (n : ℚ)/4 - 1 := le_trans h_div_ge h_v_ge_q
      field_simp at *
      linarith
  · intro n
    unfold h_seq
    split_ifs with h
    · -- n < 4
      rcases n with _ | _ | _ | _ | hn
      · -- n = 0
        have h_a0 : a 0 = 0 := by
          rw [a_eq_P_im]
          rfl
        have h_v0 : padicValInt 2 0 = 0 := by
          unfold padicValInt
          rfl
        simp [h_a0, h_v0]
      · -- n = 1
        have h_a1 : a 1 = 1 := by
          rw [a_eq_P_im]
          rfl
        have h_v1 : padicValInt 2 1 = 0 := by
          unfold padicValInt
          apply padicValNat.eq_zero_of_not_dvd
          intro hc
          omega
        simp [h_a1, h_v1]
      · -- n = 2
        have h_a2 : a 2 = 3 := by
          rw [a_eq_P_im]
          rfl
        have h_v2 : padicValInt 2 3 = 0 := by
          unfold padicValInt
          apply padicValNat.eq_zero_of_not_dvd
          intro hc
          omega
        simp [h_a2, h_v2]
      · -- n = 3
        have h_a3 : a 3 = 0 := by
          rw [a_eq_P_im]
          rfl
        have h_v3 : padicValInt 2 0 = 0 := by
          unfold padicValInt
          rfl
        simp [h_a3, h_v3]
      · -- n ≥ 4
        omega
    · -- n ≥ 4
      push_neg at h
      have h_pos : (n : ℚ) > 0 := by positivity
      have h_ne : (n : ℚ) ≠ 0 := ne_of_gt h_pos
      have h_le := valuation_a_le n
      field_simp at *
      linarith

end AsymptoticConjectures
