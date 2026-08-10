/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.Util.ProblemImports

set_option linter.style.namespace false

open Nat Int Real

/--
The auxiliary sequence $b(k)$, where $b(1)=2$ and $b(k) = b(k-1) + \mathrm{lcm}(\lfloor \sqrt{2} \cdot k \rfloor, b(k-1))$ for $k \ge 2$.
-/
noncomputable def b : ℕ → ℕ
| 0 => 0 -- Placeholder for a 1-indexed sequence
| 1 => 2
| k + 1 => -- This computes b(k+1) based on b(k). The index is k+1 >= 2.
  let b_prev := b k
  let k_val : ℕ := k + 1
  -- Calculation of $\lfloor \sqrt{2} \cdot k_{val} \rfloor$, where k_val is the current index.
  let m_real := (Real.sqrt 2) * k_val.cast
  let m_int : ℤ := Int.floor m_real
  let m_nat : ℕ := m_int.toNat
  b_prev + b_prev.lcm m_nat

lemma b_succ (k : ℕ) (hk : k ≠ 0) : b (k + 1) = b k + (b k).lcm (Int.toNat (Int.floor (Real.sqrt 2 * (k + 1).cast))) := by
  rw [b]
  exact hk

lemma M_pos (n : ℕ) (hn : 1 ≤ n) : 0 < (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) := by
  have h1 : (2 : ℝ) ≤ (n + 1).cast := by
    have : (2 : ℕ) ≤ n + 1 := by omega
    exact_mod_cast this
  have h2 : 1 < Real.sqrt 2 := one_lt_sqrt_two
  have h3 : (2 : ℝ) < Real.sqrt 2 * (n + 1).cast := by
    calc
      (2 : ℝ) < Real.sqrt 2 * 2 := by linarith
      _ ≤ Real.sqrt 2 * (n + 1).cast := by
        apply mul_le_mul_of_nonneg_left h1
        exact Real.sqrt_nonneg 2
  have h4 : 2 ≤ Int.floor (Real.sqrt 2 * (n + 1).cast) := by
    exact Int.le_floor.mpr (le_of_lt h3)
  have h5 : 0 < Int.floor (Real.sqrt 2 * (n + 1).cast) := by omega
  omega

/--
A323386: $a(n) = b(n+1)/b(n) - 1$ where $b(k)$ is defined recursively.
-/
noncomputable def A323386 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0 -- Sequence is 1-indexed.
  | n_idx =>
    let bn_plus_1 := b (n_idx + 1)
    let bn := b n_idx
    (bn_plus_1 / bn) - 1


lemma b_ge_two_pow (n : ℕ) (hn : 1 ≤ n) : 2^n ≤ b n := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      rw [b]
      decide
    | succ n =>
      have : 1 ≤ n + 1 := by omega
      have ih_ge := ih this
      rw [b_succ (n + 1) (by omega)]
      have h_double : 2 * b (n + 1) = b (n + 1) + b (n + 1) := by ring
      have h_lcm_ge : b (n + 1) + b (n + 1) ≤ b (n + 1) + Nat.lcm (b (n + 1)) (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := by
        apply Nat.add_le_add_left
        exact Nat.le_lcm_left (b (n + 1)) (M_pos (n + 1) (by omega))
      have h_pow : 2^(n + 2) = 2 * 2^(n + 1) := by ring
      rw [h_pow]
      calc
        2 * 2^(n + 1) ≤ 2 * b (n + 1) := Nat.mul_le_mul_left 2 ih_ge
        _ = b (n + 1) + b (n + 1) := h_double
        _ ≤ b (n + 1) + Nat.lcm (b (n + 1)) (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := h_lcm_ge

-- Let us prove that b n is positive for all n >= 1
lemma b_pos (n : ℕ) (hn : 1 ≤ n) : 0 < b n := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      rw [b]
      decide
    | succ n =>
      have : 1 ≤ n + 1 := by omega
      have ih_pos := ih this
      rw [b]
      · exact Nat.lt_of_lt_of_le ih_pos (Nat.le_add_right _ _)
      · exact Nat.succ_ne_zero n

lemma floor_sqrt_two_mul_two : Int.floor (Real.sqrt 2 * 2) = 2 := by
  have h1 : (2 : ℝ) ≤ Real.sqrt 2 * 2 := by
    -- 1 < Real.sqrt 2, so 2 < Real.sqrt 2 * 2
    have : 1 < Real.sqrt 2 := one_lt_sqrt_two
    linarith
  have h2 : Real.sqrt 2 * 2 < (2 : ℝ) + 1 := by
    -- Real.sqrt 2 < 3/2, so Real.sqrt 2 * 2 < 3
    have : Real.sqrt 2 < 3 / 2 := sqrt_two_lt_three_halves
    linarith
  rw [Int.floor_eq_iff]
  constructor
  · exact h1
  · exact h2

lemma floor_sqrt_two_mul_three : Int.floor (Real.sqrt 2 * 3) = 4 := by
  have h1 : (4 : ℝ) ≤ Real.sqrt 2 * 3 := by
    have h_low : (4 / 3 : ℝ) < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
    linarith
  have h2 : Real.sqrt 2 * 3 < (4 : ℝ) + 1 := by
    have : Real.sqrt 2 < 3 / 2 := sqrt_two_lt_three_halves
    linarith
  rw [Int.floor_eq_iff]
  constructor
  · exact h1
  · exact h2

theorem a1 : A323386 1 = 1 := by
  dsimp [A323386]
  have hb1 : b 1 = 2 := by rfl
  have h_succ : b 2 = b 1 + (b 1).lcm (Int.toNat (Int.floor (Real.sqrt 2 * (1 + 1 : ℕ).cast))) := by
    exact b_succ 1 (by decide)
  have h_cast : (1 + 1 : ℕ).cast = (2 : ℝ) := by norm_num
  rw [h_cast] at h_succ
  rw [floor_sqrt_two_mul_two] at h_succ
  rw [hb1] at h_succ
  have hb2 : b 2 = 4 := by
    rw [h_succ]
    rfl
  rw [hb1, hb2]

theorem a2 : A323386 2 = 1 := by
  dsimp [A323386]
  have hb1 : b 1 = 2 := by rfl
  have h_succ1 : b 2 = b 1 + (b 1).lcm (Int.toNat (Int.floor (Real.sqrt 2 * (1 + 1 : ℕ).cast))) := by
    exact b_succ 1 (by decide)
  have h_cast1 : (1 + 1 : ℕ).cast = (2 : ℝ) := by norm_num
  rw [h_cast1] at h_succ1
  rw [floor_sqrt_two_mul_two] at h_succ1
  rw [hb1] at h_succ1
  have hb2 : b 2 = 4 := by
    rw [h_succ1]
    rfl
  have h_succ2 : b 3 = b 2 + (b 2).lcm (Int.toNat (Int.floor (Real.sqrt 2 * (2 + 1 : ℕ).cast))) := by
    exact b_succ 2 (by decide)
  have h_cast2 : (2 + 1 : ℕ).cast = (3 : ℝ) := by norm_num
  rw [h_cast2] at h_succ2
  rw [floor_sqrt_two_mul_three] at h_succ2
  rw [hb2] at h_succ2
  have hb3 : b 3 = 8 := by
    rw [h_succ2]
    rfl
  rw [hb2, hb3]

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : A323386 n = b (n + 1) / b n - 1 := by
  dsimp [A323386]
  cases n with
  | zero => contradiction
  | succ n => rfl

lemma b_div_simp (A B : ℕ) (hA : 0 < A) (hB : A ∣ B) : (A + B) / A - 1 = B / A := by
  rw [Nat.add_div_of_dvd_left hB]
  rw [Nat.div_self hA]
  exact Nat.add_sub_cancel_left 1 (B / A)

lemma lcm_div_self (A B : ℕ) (hA : 0 < A) : A.lcm B / A = B / A.gcd B := by
  have h_gcd_pos : 0 < A.gcd B := Nat.gcd_pos_of_pos_left B hA
  have hdvd1 : A.gcd B ∣ B := Nat.gcd_dvd_right A B
  have hB_eq : B = B / A.gcd B * A.gcd B := (Nat.div_mul_cancel hdvd1).symm
  have h_mul : A.gcd B * A.lcm B = A * B := Nat.gcd_mul_lcm A B
  have h_mul2 : A * B = A * (B / A.gcd B * A.gcd B) := congr_arg (fun x => A * x) hB_eq
  have h_mul3 : A * (B / A.gcd B * A.gcd B) = A.gcd B * (A * (B / A.gcd B)) := by ac_rfl
  have h_mul4 : A * B = A.gcd B * (A * (B / A.gcd B)) := h_mul2.trans h_mul3
  rw [h_mul4] at h_mul
  have h_lcm : A.lcm B = A * (B / A.gcd B) := Nat.eq_of_mul_eq_mul_left h_gcd_pos h_mul
  rw [h_lcm]
  exact Nat.mul_div_cancel_left _ hA

lemma a_simp (n : ℕ) (hn : 1 ≤ n) : A323386 n = (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) / (b n).gcd (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) := by
  rw [a_eq n hn]
  have h_succ := b_succ n (by omega)
  rw [h_succ]
  rw [b_div_simp (b n) ((b n).lcm (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast)))) (b_pos n hn) (Nat.dvd_lcm_left _ _)]
  rw [lcm_div_self (b n) (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) (b_pos n hn)]


lemma b_div_self (n : ℕ) (hn : 1 ≤ n) : (b n) ∣ b (n + 1) := by
  have h_succ := b_succ n (by omega)
  rw [h_succ]
  apply Nat.dvd_add
  · exact Nat.dvd_refl (b n)
  · exact Nat.dvd_lcm_left (b n) _


lemma dvd_b_of_dvd_b (q : ℕ) (n : ℕ) (hn : 1 ≤ n) (h_dvd : q ∣ b n) (k : ℕ) (hk : n ≤ k) : q ∣ b k := by
  induction k with
  | zero =>
    have : n = 0 := by omega
    subst this
    contradiction
  | succ k ih =>
    by_cases h_cases : n ≤ k
    · have hk_pos : 1 ≤ k := by omega
      have h_div := b_div_self k hk_pos
      exact Nat.dvd_trans (ih h_cases) h_div
    · have : k + 1 = n := by omega
      subst this
      exact h_dvd


lemma b_mod (n : ℕ) (hn : 1 ≤ n) : (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) ∣ (b (n + 1) - b n) := by
  have h_succ := b_succ n (by omega)
  rw [h_succ]
  rw [Nat.add_sub_cancel_left]
  exact Nat.dvd_lcm_right (b n) _

lemma b_step_eq (j : ℕ) (hj : 1 ≤ j) : b (j + 1) = b j * (A323386 j + 1) := by
  have h_div := b_div_self j hj
  have h_pos := b_pos j hj
  have h_eq : A323386 j = b (j + 1) / b j - 1 := a_eq j hj
  have h_cancel : b (j + 1) = b j * (b (j + 1) / b j) := by
    rw [Nat.mul_comm]
    exact (Nat.div_mul_cancel h_div).symm
  have h_div_ne : b (j + 1) / b j ≠ 0 := by
    intro h_zero
    have h_mul := Nat.div_mul_cancel h_div
    rw [h_zero, Nat.zero_mul] at h_mul
    have h_pos2 := b_pos (j + 1) (by omega)
    omega
  have h_div_ge : 1 ≤ b (j + 1) / b j := Nat.one_le_iff_ne_zero.mpr h_div_ne
  have h_sub_eq : b (j + 1) / b j = A323386 j + 1 := by
    omega
  rw [h_sub_eq] at h_cancel
  exact h_cancel



lemma padicValNat_le_of_dvd {q A B : ℕ} [hq : Fact q.Prime] (hB : B ≠ 0) (h_dvd : A ∣ B) :
    padicValNat q A ≤ padicValNat q B := by
  by_cases hA : A = 0
  · subst hA
    simp
  · have h_pow : q ^ padicValNat q A ∣ A := pow_padicValNat_dvd
    have h_pow_dvd : q ^ padicValNat q A ∣ B := Nat.dvd_trans h_pow h_dvd
    rwa [padicValNat_dvd_iff_le hB] at h_pow_dvd





lemma sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  have h1 : (2 : ℝ) < 4 := by norm_num
  have h2 := Real.sqrt_lt_sqrt (by norm_num) h1
  have h3 : Real.sqrt 4 = 2 := by
    have h_sq : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h_sq]
    exact Real.sqrt_sq (by norm_num)
  rw [h3] at h2
  exact h2


lemma floor_lt_two_mul (n : ℕ) : Int.floor (Real.sqrt 2 * (n + 2).cast) < 2 * (n + 2) := by
  have h_sqrt : Real.sqrt 2 < 2 := sqrt_two_lt_two
  have h_pos : (0 : ℝ) < (n + 2).cast := by positivity
  have h_mul : Real.sqrt 2 * (n + 2).cast < 2 * (n + 2).cast := mul_lt_mul_of_pos_right h_sqrt h_pos
  rw [Int.floor_lt]
  exact_mod_cast h_mul

lemma two_mul_le_two_pow (n : ℕ) : 2 * (n + 2) ≤ 2^(n + 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : 2^(n + 3) = 2 * 2^(n + 2) := by ring
    have h2 : 2 * (n + 3) = 2 * (n + 2) + 2 := by ring
    rw [h1, h2]
    have h3 : 2 ≤ 2^(n + 2) := by
      have : 2^1 ≤ 2^(n + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      exact this
    omega

lemma M_lt_two_pow (n : ℕ) : (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) < 2^(n + 2) := by
  have h_floor := floor_lt_two_mul n
  have h_pow := two_mul_le_two_pow n
  have h_floor_pos : 0 ≤ Int.floor (Real.sqrt 2 * (n + 2).cast) := by
    apply Int.floor_nonneg.mpr
    positivity
  have h_lt : Int.floor (Real.sqrt 2 * (n + 2).cast) < (2^(n + 2) : ℤ) := by
    have : (2 * (n + 2) : ℤ) ≤ (2^(n + 2) : ℤ) := by
      exact_mod_cast h_pow
    omega
  rw [Int.toNat_lt h_floor_pos]
  exact h_lt



lemma gcd_v2_eq (k c M : ℕ) [Fact (Nat.Prime 2)] (hM : M ≠ 0) (hc : c ≠ 0) (h_le : padicValNat 2 M ≤ k) :
    padicValNat 2 ((2^k * c).gcd M) = padicValNat 2 M := by
  let g := (2^k * c).gcd M
  have h_dvd_M : g ∣ M := Nat.gcd_dvd_right _ _
  have h_le1 : padicValNat 2 g ≤ padicValNat 2 M := padicValNat_le_of_dvd hM h_dvd_M
  have h_pow_dvd_M : 2 ^ padicValNat 2 M ∣ M := pow_padicValNat_dvd
  have h_pow_dvd_pow : 2 ^ padicValNat 2 M ∣ 2 ^ k := pow_dvd_pow 2 h_le
  have h_pow_dvd_X : 2 ^ padicValNat 2 M ∣ 2^k * c := Nat.dvd_trans h_pow_dvd_pow (Nat.dvd_mul_right _ _)
  have h_dvd_g : 2 ^ padicValNat 2 M ∣ g := Nat.dvd_gcd h_pow_dvd_X h_pow_dvd_M
  have hg_ne : g ≠ 0 := by
    intro h_g0
    have h_gcd_ne : (2^k * c).gcd M ≠ 0 := by
      apply Nat.gcd_ne_zero_left
      have : 2^k * c ≠ 0 := by positivity
      exact this
    omega
  have h_le2 : padicValNat 2 M ≤ padicValNat 2 g := (padicValNat_dvd_iff_le hg_ne).mp h_dvd_g
  have h_eq : padicValNat 2 g = padicValNat 2 M := le_antisymm h_le1 h_le2
  exact h_eq



lemma lcm_eq_mul_div_gcd (x y : ℕ) (hx : 0 < x) : x.lcm y = (x * y) / x.gcd y := by
  have h_gcd_pos : 0 < x.gcd y := Nat.gcd_pos_of_pos_left y hx
  have h_mul : x * y = x.gcd y * x.lcm y := (Nat.gcd_mul_lcm x y).symm
  rw [h_mul]
  rw [Nat.mul_comm, Nat.mul_div_cancel _ h_gcd_pos]

lemma b_div_by_two_pow (n : ℕ) (hn : 1 ≤ n) : 2^n ∣ b n := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      rw [b]
      decide
    · have hn_pos : 1 ≤ n := by omega
      have ih_val := ih hn_pos
      obtain ⟨c, hc_eq⟩ := ih_val
      have hc_ne : c ≠ 0 := by
        intro hc0
        subst hc0
        have h_pos := b_pos n hn_pos
        omega
      have h_succ := b_succ n (by omega)
      let M := Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))
      have h_M_pos := M_pos n hn_pos
      have h_M_ne : M ≠ 0 := by omega
      have h_lcm_eq : (b n).lcm M = b n * M / (b n).gcd M := lcm_eq_mul_div_gcd _ _ (b_pos n hn_pos)
      have h_gcd_dvd : (b n).gcd M ∣ M := Nat.gcd_dvd_right _ _
      obtain ⟨D, hD_eq⟩ := h_gcd_dvd
      have h_div_cancel : (b n * M) / (b n).gcd M = b n * D := by
        nth_rw 1 [hD_eq]
        have h_gcd_pos : 0 < (b n).gcd M := Nat.gcd_pos_of_pos_right _ h_M_pos
        rw [← Nat.mul_assoc, Nat.mul_comm (b n), Nat.mul_assoc]
        rw [Nat.mul_div_cancel_left _ h_gcd_pos]
      rw [h_succ, h_lcm_eq, h_div_cancel, hc_eq]
      have h_factor : 2^n * c + 2^n * c * D = 2^n * (c * (1 + D)) := by ring
      rw [h_factor]
      by_cases hc_even : 2 ∣ c
      · obtain ⟨d, hd_eq⟩ := hc_even
        rw [hd_eq]
        have h_ring : 2^n * (2 * d * (1 + D)) = 2^(n + 1) * (d * (1 + D)) := by
          have : 2^(n + 1) = 2^n * 2 := by ring
          rw [this]
          ring
        rw [h_ring]
        exact Nat.dvd_mul_right _ _
      · have h_fact_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have h_lt : M < 2^(n + 1) := by
          have h_M_lt := M_lt_two_pow (n - 1)
          have h_eq : n - 1 + 2 = n + 1 := by omega
          rw [h_eq] at h_M_lt
          exact h_M_lt
        have h_not_dvd : ¬ 2^(n + 1) ∣ M := by
          intro h_dvd
          have h_le := Nat.le_of_dvd h_M_pos h_dvd
          omega
        have h_v2_M_le : padicValNat 2 M ≤ n := by
          by_contra h_contr
          have : n + 1 ≤ padicValNat 2 M := by omega
          have h_dvd : 2^(n + 1) ∣ M := (padicValNat_dvd_iff_le h_M_ne).mpr this
          exact h_not_dvd h_dvd
        have h_v2_eq := gcd_v2_eq n c M h_M_ne hc_ne h_v2_M_le
        have h_v2_D : padicValNat 2 D = 0 := by
          have hD_gcd : D = M / (b n).gcd M := by
            nth_rw 1 [hD_eq]
            exact (Nat.mul_div_cancel_left _ (Nat.gcd_pos_of_pos_right _ h_M_pos)).symm
          have h_v2_eq' := h_v2_eq
          rw [← hc_eq] at h_v2_eq'
          rw [hD_gcd]
          have h_gcd_dvd_M : (b n).gcd M ∣ M := Nat.gcd_dvd_right _ _
          rw [padicValNat.div_of_dvd h_gcd_dvd_M]
          rw [h_v2_eq']
          omega
        have hD_ne : D ≠ 0 := by
          intro hD0
          subst hD0
          rw [Nat.mul_zero] at hD_eq
          exact h_M_ne hD_eq
        have h_not_dvd_D : ¬ 2 ∣ D := by
          intro h_dvd_D
          have h_v2_D_ge : 1 ≤ padicValNat 2 D := by
            rwa [← padicValNat_dvd_iff_le hD_ne]
          omega
        have h_odd_D : D % 2 = 1 := by
          have h_mod_lt : D % 2 < 2 := Nat.mod_lt _ (by decide)
          have h_mod_ne : D % 2 ≠ 0 := by
            intro h0
            have : 2 ∣ D := Nat.dvd_of_mod_eq_zero h0
            exact h_not_dvd_D this
          omega
        have h_even_1_add_D : (1 + D) % 2 = 0 := by
          rw [Nat.add_mod, h_odd_D]
        have h_dvd_1_add_D : 2 ∣ 1 + D := Nat.dvd_of_mod_eq_zero h_even_1_add_D
        obtain ⟨d, hd_eq⟩ := h_dvd_1_add_D
        rw [hd_eq]
        have h_ring : 2^n * (c * (2 * d)) = 2^(n + 1) * (c * d) := by
          have : 2^(n + 1) = 2^n * 2 := by ring
          rw [this]
          ring
        rw [h_ring]
        exact Nat.dvd_mul_right _ _



lemma padicValNat_two_b_ge (n : ℕ) (hn : 1 ≤ n) : n ≤ padicValNat 2 (b n) := by
  have h_fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_dvd := b_div_by_two_pow n hn
  have h_ne : b n ≠ 0 := by
    have := b_pos n hn
    omega
  exact (padicValNat_dvd_iff_le h_ne).mp h_dvd






lemma padicValNat_add_eq_of_lt {q A B : ℕ} [hq : Fact q.Prime] (hA : A ≠ 0) (hB : B ≠ 0)
    (hval : padicValNat q A < padicValNat q B) :
    padicValNat q (A + B) = padicValNat q A := by
  generalize h_v : padicValNat q A = v
  have h_v_succ : v + 1 ≤ padicValNat q B := by omega
  have h_dvd_A : q ^ v ∣ A := by
    rw [← h_v]
    exact pow_padicValNat_dvd
  have h_dvd_B : q ^ (v + 1) ∣ B := (padicValNat_dvd_iff_le hB).mpr h_v_succ
  have h_dvd_B_weak : q ^ v ∣ B := by
    have h_pow : q ^ v ∣ q ^ (v + 1) := pow_dvd_pow q (Nat.le_succ _)
    exact Nat.dvd_trans h_pow h_dvd_B
  have h_dvd_sum : q ^ v ∣ A + B := Nat.dvd_add h_dvd_A h_dvd_B_weak
  have h_not_dvd_sum : ¬ q ^ (v + 1) ∣ A + B := by
    intro h_dvd_AB
    have h_dvd_sub : q ^ (v + 1) ∣ (A + B) - B := Nat.dvd_sub h_dvd_AB h_dvd_B
    rw [Nat.add_sub_cancel] at h_dvd_sub
    have h_not_dvd_A : ¬ q ^ (v + 1) ∣ A := by
      have h_not := pow_succ_padicValNat_not_dvd (p := q) hA
      rw [h_v] at h_not
      exact h_not
    exact h_not_dvd_A h_dvd_sub
  have h_sum_ne_zero : A + B ≠ 0 := by omega
  have h_le_v : padicValNat q (A + B) ≤ v := by
    by_contra h_contr
    have h_lt : v < padicValNat q (A + B) := by omega
    have h_dvd : q ^ (v + 1) ∣ A + B := (padicValNat_dvd_iff_le h_sum_ne_zero).mpr h_lt
    exact h_not_dvd_sum h_dvd
  have h_ge_v : v ≤ padicValNat q (A + B) := by
    have := (padicValNat_dvd_iff_le h_sum_ne_zero).mp h_dvd_sum
    omega
  omega


lemma M_diff_bounds (n : ℕ) :
    (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) - (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) = 1 ∨
    (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) - (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) = 2 := by
  let x := Real.sqrt 2 * (n + 1).cast
  let y := Real.sqrt 2 * (n + 2).cast
  have h_diff : y - x = Real.sqrt 2 := by
    change Real.sqrt 2 * (n + 2).cast - Real.sqrt 2 * (n + 1).cast = Real.sqrt 2
    have : (n + 2).cast = (n + 1).cast + (1 : ℝ) := by
      push_cast
      ring
    rw [this]
    ring
  have h_floor_y_le : (Int.floor y : ℝ) ≤ y := Int.floor_le y
  have h_floor_x_gt : x - 1 < (Int.floor x : ℝ) := by
    have := Int.lt_floor_add_one x
    linarith
  have h_floor_y_gt : y - 1 < (Int.floor y : ℝ) := by
    have := Int.lt_floor_add_one y
    linarith
  have h_floor_x_le : (Int.floor x : ℝ) ≤ x := Int.floor_le x

  have h_diff_lt : (Int.floor y : ℝ) - (Int.floor x : ℝ) < Real.sqrt 2 + 1 := by
    linarith
  have h_diff_gt : (Int.floor y : ℝ) - (Int.floor x : ℝ) > Real.sqrt 2 - 1 := by
    linarith

  have h_sqrt2_lt : Real.sqrt 2 < 1.5 := by
    have h1 : (2 : ℝ) < 1.5^2 := by norm_num
    have h2 := Real.sqrt_lt_sqrt (by norm_num) h1
    have h3 : Real.sqrt (1.5^2) = 1.5 := by
      exact Real.sqrt_sq (by norm_num)
    rwa [h3] at h2
  have h_sqrt2_gt : 1.4 < Real.sqrt 2 := by
    have h1 : 1.4^2 < (2 : ℝ) := by norm_num
    have h2 := Real.sqrt_lt_sqrt (by norm_num) h1
    have h3 : Real.sqrt (1.4^2) = 1.4 := by
      exact Real.sqrt_sq (by norm_num)
    rwa [h3] at h2

  have h_diff_lt_val : (Int.floor y : ℝ) - (Int.floor x : ℝ) < 2.5 := by linarith
  have h_diff_gt_val : (Int.floor y : ℝ) - (Int.floor x : ℝ) > 0.4 := by linarith

  have h_diff_int : (Int.floor y - Int.floor x : ℤ) = Int.floor y - Int.floor x := by rfl
  have h_diff_lt_int : Int.floor y - Int.floor x < 3 := by
    have h_cast : ((Int.floor y - Int.floor x : ℤ) : ℝ) < 3 := by
      push_cast
      linarith [h_diff_lt_val]
    exact_mod_cast h_cast
  have h_diff_gt_int : Int.floor y - Int.floor x > 0 := by
    have h_cast : ((Int.floor y - Int.floor x : ℤ) : ℝ) > 0 := by
      push_cast
      linarith [h_diff_gt_val]
    exact_mod_cast h_cast

  have h_diff_cases : Int.floor y - Int.floor x = 1 ∨ Int.floor y - Int.floor x = 2 := by omega

  have h_x_pos : 0 ≤ Int.floor x := by
    apply Int.floor_nonneg.mpr
    positivity
  have h_y_pos : 0 ≤ Int.floor y := by
    apply Int.floor_nonneg.mpr
    positivity

  have h_nat_x : (Int.floor x).toNat = Int.toNat (Int.floor x) := rfl
  have h_nat_y : (Int.floor y).toNat = Int.toNat (Int.floor y) := rfl

  have h_toNat_sub : (Int.floor y).toNat - (Int.floor x).toNat = (Int.floor y - Int.floor x).toNat := by
    rw [← Int.toNat_sub]
    · omega
  rw [← h_nat_x, ← h_nat_y, h_toNat_sub]

  rcases h_diff_cases with h1 | h2
  · left
    rw [h1]
    rfl
  · right
    rw [h2]
    rfl


lemma valuation_M_curr_M_next (n : ℕ) (hn : 1 ≤ n) (q : ℕ) [hq : Fact q.Prime] (hq2 : q ≠ 2) :
    padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) = 0 ∨
    padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) = 0 := by
  by_contra h_contr
  push_neg at h_contr
  obtain ⟨h_next, h_curr⟩ := h_contr
  have h_q_ne_one : q ≠ 1 := hq.out.ne_one
  have h_M_pos1 : (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) ≠ 0 := (M_pos n hn).ne'
  have h_M_pos2 : (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≠ 0 := (M_pos (n + 1) (by omega)).ne'
  have h_dvd_curr : q ∣ (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) := by
    have h_eq_zero := padicValNat.eq_zero_iff (p := q) (n := Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast)))
    tauto
  have h_dvd_next : q ∣ (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := by
    have h_eq_zero := padicValNat.eq_zero_iff (p := q) (n := Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast)))
    tauto
  let M1 := Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))
  let M2 := Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))
  have h_diff_bounds := M_diff_bounds n
  change M2 - M1 = 1 ∨ M2 - M1 = 2 at h_diff_bounds
  have h_le_M : M1 ≤ M2 := by
    rcases h_diff_bounds with h | h
    · omega
    · omega
  have h_dvd_diff : q ∣ M2 - M1 := Nat.dvd_sub h_dvd_next h_dvd_curr
  rcases h_diff_bounds with h1 | h2
  · rw [h1] at h_dvd_diff
    have : ¬ q ∣ 1 := Nat.Prime.not_dvd_one hq.out
    exact this h_dvd_diff
  · rw [h2] at h_dvd_diff
    have h_le_2 : q ≤ 2 := Nat.le_of_dvd (by decide) h_dvd_diff
    have h_ge_2 : 2 ≤ q := hq.out.two_le
    have : q = 2 := by omega
    exact hq2 this



lemma valuation_b_succ (n : ℕ) (hn : 1 ≤ n) (q : ℕ) [hq : Fact q.Prime]
    (h_curr : padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) = 0) :
    padicValNat q (b (n + 1)) = padicValNat q (b n) + padicValNat q ((Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) + (b n).gcd (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast)))) := by
  let M1 := Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))
  have hb_step : b (n + 1) = b n * (A323386 n + 1) := b_step_eq n hn
  have h_bn_ne : b n ≠ 0 := (b_pos n hn).ne'
  have h_a_ne : A323386 n + 1 ≠ 0 := by omega
  have h_val_mul : padicValNat q (b (n + 1)) = padicValNat q (b n) + padicValNat q (A323386 n + 1) := by
    rw [hb_step]
    exact padicValNat.mul h_bn_ne h_a_ne
  rw [h_val_mul]
  have h_M1_ne : M1 ≠ 0 := (M_pos n hn).ne'
  have hg_dvd : (b n).gcd M1 ∣ M1 := Nat.gcd_dvd_right _ _
  have h_mul_eq : (b n).gcd M1 * (A323386 n + 1) = M1 + (b n).gcd M1 := by
    rw [Nat.mul_add, Nat.mul_one]
    rw [a_simp n hn]
    rw [Nat.mul_div_cancel' hg_dvd]
  have h_g_ne : (b n).gcd M1 ≠ 0 := by
    have : 0 < M1 := M_pos n hn
    exact (Nat.gcd_pos_of_pos_right (b n) this).ne'
  have h_v_g : padicValNat q ((b n).gcd M1) = 0 := by
    have h_le := padicValNat_le_of_dvd (q := q) h_M1_ne hg_dvd
    rw [h_curr] at h_le
    omega
  have h_mul_val := padicValNat.mul (p := q) h_g_ne h_a_ne
  rw [h_mul_eq] at h_mul_val
  rw [h_v_g, Nat.zero_add] at h_mul_val
  dsimp [M1] at *
  rw [← h_mul_val]

lemma key_lemma (n : ℕ) (hn : 1 ≤ n) (q : ℕ) [hq : Fact q.Prime] (hq_le : q^2 ≤ (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast)))) :
    padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) ≤ padicValNat q (b n) + 1 := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      -- Base case: n + 1 = 1, so the index is b 1.
      -- Int.toNat (Int.floor (Real.sqrt 2 * (1 + 1 : ℕ).cast)) = 2.
      -- q^2 ≤ 2, which is impossible since q >= 2.
      have h_cast : (1 + 1 : ℕ).cast = (2 : ℝ) := by norm_num
      have h_floor : Int.floor (Real.sqrt 2 * (1 + 1 : ℕ).cast) = 2 := by
        rw [h_cast]
        exact floor_sqrt_two_mul_two
      have h_M : (Int.toNat (Int.floor (Real.sqrt 2 * (1 + 1 : ℕ).cast))) = 2 := by
        rw [h_floor]
        rfl
      rw [h_M] at hq_le
      have hq_ge : 2 ≤ q := hq.out.two_le
      have hq2_ge : 4 ≤ q^2 := by
        have : 2^2 ≤ q^2 := Nat.pow_le_pow_left hq_ge 2
        exact this
      omega
    · have hn_pos : 1 ≤ n := by omega
      by_cases hq2 : q = 2
      · subst hq2
        have h_v2_b_ge : n + 1 ≤ padicValNat 2 (b (n + 1)) := padicValNat_two_b_ge (n + 1) (by omega)
        have h_M_lt := M_lt_two_pow n
        have h_M_pos : 0 < (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := M_pos (n + 1) (by omega)
        have h_v_M_le : padicValNat 2 (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≤ n + 1 := by
          by_contra h_contr
          have h_lt : n + 1 < padicValNat 2 (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := by omega
          have h_dvd : 2^(n + 2) ∣ (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := by
            rwa [padicValNat_dvd_iff_le h_M_pos.ne']
          have h_le := Nat.le_of_dvd h_M_pos h_dvd
          omega
        change padicValNat 2 (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≤ padicValNat 2 (b (n + 1)) + 1
        omega
      · have h_or := valuation_M_curr_M_next n hn_pos q hq2
        rcases h_or with h_next | h_curr
        · change padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≤ padicValNat q (b (n + 1)) + 1
          rw [h_next]
          omega
        · change padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≤ padicValNat q (b (n + 1)) + 1
          by_cases h_le1 : padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≤ 1
          · have : 1 ≤ padicValNat q (b (n + 1)) + 1 := Nat.le_add_left 1 _
            omega
          · sorry


lemma key_lemma_strict (n : ℕ) (hn : 1 ≤ n) (q : ℕ) [hq : Fact q.Prime] (hq_lt : q^2 < (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast)))) :
    padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) ≤ padicValNat q (b n) := by
  by_cases hq2 : q = 2
  · subst hq2
    have h_v2_b_ge : n ≤ padicValNat 2 (b n) := padicValNat_two_b_ge n hn
    have h_M_lt := M_lt_two_pow (n - 1)
    have h_eq : n - 1 + 2 = n + 1 := by omega
    rw [h_eq] at h_M_lt
    have h_M_pos : 0 < (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) := M_pos n hn
    have h_v_M_le : padicValNat 2 (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) ≤ n := by
      by_contra h_contr
      have h_lt : n < padicValNat 2 (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) := by omega
      have h_dvd : 2^(n + 1) ∣ (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) := by
        rwa [padicValNat_dvd_iff_le h_M_pos.ne']
      have h_le := Nat.le_of_dvd h_M_pos h_dvd
      omega
    omega
  · by_cases h_val : padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) = 0
    · rw [h_val]
      omega
    · have h_le := key_lemma n hn q (by omega)
      by_cases h_lt : padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) ≤ padicValNat q (b n)
      · exact h_lt
      · have h_eq : padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) = padicValNat q (b n) + 1 := by omega
        sorry



lemma dvd_b_of_step (j n : ℕ) (hj : 1 ≤ j) (hjn : j < n) : (A323386 j + 1) ∣ b n := by
  have h1 : (A323386 j + 1) ∣ b (j + 1) := by
    rw [b_step_eq j hj]
    exact Nat.dvd_mul_left _ _
  exact dvd_b_of_dvd_b (A323386 j + 1) (j + 1) (by omega) h1 n (by omega)


/--
Conjecture 1: This sequence consists only of 1's and primes.
Conjecture 2: Every odd prime of the form $\lfloor \sqrt{2} \cdot m \rfloor$ is a term of this sequence.
Conjecture 3: At the first appearance of each prime of the form $\lfloor \sqrt{2} \cdot m \rfloor$, it is the next prime after the largest prime that has already appeared.
-/
theorem oeis_a323386_conjecture_1 : ∀ (n : ℕ), 1 ≤ n → (A323386 n = 1 ∨ Nat.Prime (A323386 n)) := by
  intro n hn
  by_cases h_one : A323386 n = 1
  · left; exact h_one
  · right
    have h_a_pos : 0 < A323386 n := by
      rw [a_simp n hn]
      have hM := M_pos n hn
      have h_gcd_dvd : (b n).gcd (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) ∣ (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) := Nat.gcd_dvd_right _ _
      have h_gcd_pos : 0 < (b n).gcd (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) := by
        apply Nat.gcd_pos_of_pos_right
        exact hM
      have h_div_ne_zero : (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) / (b n).gcd (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) ≠ 0 := by
        intro h_zero
        have h_mul := Nat.div_mul_cancel h_gcd_dvd
        rw [h_zero, Nat.zero_mul] at h_mul
        omega
      exact Nat.pos_of_ne_zero h_div_ne_zero
    have h_a_ge_2 : 2 ≤ A323386 n := by omega
    rw [Nat.prime_def_le_sqrt]
    refine ⟨h_a_ge_2, ?_⟩
    intro m hm m_le_sqrt_a
    intro h_m_dvd_a
    have h_m_pos : 0 < m := by omega
    have h_m_ne_one : m ≠ 1 := by omega
    let q := m.minFac
    have hq_prime : Nat.Prime q := Nat.minFac_prime h_m_ne_one
    have hq_fact : Fact q.Prime := ⟨hq_prime⟩
    have hq_dvd_m : q ∣ m := m.minFac_dvd
    have hq_dvd_a : q ∣ A323386 n := Nat.dvd_trans hq_dvd_m h_m_dvd_a
    have hq_le_m : q ≤ m := Nat.minFac_le h_m_pos
    have hq_le_sqrt_a : q ≤ (A323386 n).sqrt := le_trans hq_le_m m_le_sqrt_a
    have hq2_le_a : q^2 ≤ A323386 n := by
      rwa [← Nat.le_sqrt']
    let M := Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))
    have h_a_le_M : A323386 n ≤ M := by
      rw [a_simp n hn]
      exact Nat.div_le_self _ _
    have hq2_le_M : q^2 ≤ M := by omega
    have h_key := key_lemma n hn q hq2_le_M
    have h_a_ne : A323386 n ≠ 0 := by omega
    have hq_dvd_M : q ∣ M := by
      rw [a_simp n hn] at hq_dvd_a
      have h_gcd_dvd : (b n).gcd M ∣ M := Nat.gcd_dvd_right _ _
      have h_mul_eq := Nat.div_mul_cancel h_gcd_dvd
      rw [← h_mul_eq]
      exact dvd_mul_of_dvd_left hq_dvd_a _
    have h_mul : A323386 n * (b n).gcd M = M := by
      rw [a_simp n hn]
      have h_gcd_dvd : (b n).gcd M ∣ M := Nat.gcd_dvd_right _ _
      exact Nat.div_mul_cancel h_gcd_dvd
    have h_gcd_ne : (b n).gcd M ≠ 0 := by
      have : 0 < M := M_pos n hn
      have : 0 < (b n).gcd M := Nat.gcd_pos_of_pos_right _ this
      omega
    have hM_ne_zero : M ≠ 0 := by
      have : 0 < M := M_pos n hn
      omega
    have h_v_mul : padicValNat q (A323386 n) + padicValNat q ((b n).gcd M) = padicValNat q M := by
      rw [← padicValNat.mul h_a_ne h_gcd_ne, h_mul]
    have h_gcd_dvd_bn : (b n).gcd M ∣ b n := Nat.gcd_dvd_left _ _
    have h_gcd_dvd_M : (b n).gcd M ∣ M := Nat.gcd_dvd_right _ _
    have h_gcd_le_M : padicValNat q ((b n).gcd M) ≤ padicValNat q M := by
      have h_div_M : q ^ padicValNat q ((b n).gcd M) ∣ (b n).gcd M := pow_padicValNat_dvd
      have h_div_M2 : q ^ padicValNat q ((b n).gcd M) ∣ M := Nat.dvd_trans h_div_M h_gcd_dvd_M
      exact (padicValNat_dvd_iff_le hM_ne_zero).mp h_div_M2
    have h_gcd_ge : padicValNat q M - 1 ≤ padicValNat q ((b n).gcd M) := by
      by_cases h_vM_zero : padicValNat q M = 0
      · omega
      · have h_vM_pos : 1 ≤ padicValNat q M := by omega
        have h_pow_dvd : q ^ (padicValNat q M - 1) ∣ q ^ padicValNat q M := by
          apply pow_dvd_pow
          omega
        have h_pow_dvd_M : q ^ (padicValNat q M - 1) ∣ M := Nat.dvd_trans h_pow_dvd pow_padicValNat_dvd
        have h_pow_dvd_bn : q ^ (padicValNat q M - 1) ∣ b n := by
          have h_pow_dvd_bn_pow : q ^ (padicValNat q M - 1) ∣ q ^ padicValNat q (b n) := by
            apply pow_dvd_pow
            have h_key_M : padicValNat q M ≤ padicValNat q (b n) + 1 := key_lemma n hn q hq2_le_M
            omega
          exact Nat.dvd_trans h_pow_dvd_bn_pow pow_padicValNat_dvd
        have h_dvd_gcd : q ^ (padicValNat q M - 1) ∣ (b n).gcd M := Nat.dvd_gcd h_pow_dvd_bn h_pow_dvd_M
        exact (padicValNat_dvd_iff_le h_gcd_ne).mp h_dvd_gcd
    have h_v_a_le_1 : padicValNat q (A323386 n) ≤ 1 := by omega
    by_cases h_lt : q^2 < M
    · have h_key_strict := key_lemma_strict n hn q h_lt
      have h_v_a_pos : 1 ≤ padicValNat q (A323386 n) := by
        apply (padicValNat_dvd_iff_le h_a_ne).mp
        rwa [pow_one]
      have h_gcd_eq : padicValNat q ((b n).gcd M) = padicValNat q M := by
        have h1 : padicValNat q ((b n).gcd M) ≤ padicValNat q M := padicValNat_le_of_dvd hM_ne_zero (Nat.gcd_dvd_right _ _)
        have h2 : q ^ padicValNat q M ∣ (b n).gcd M := by
          apply Nat.dvd_gcd
          · have h_le_bn : padicValNat q M ≤ padicValNat q (b n) := h_key_strict
            have h_bn_ne : b n ≠ 0 := by
              have := b_pos n hn
              omega
            exact (padicValNat_dvd_iff_le h_bn_ne).mpr h_le_bn
          · exact pow_padicValNat_dvd
        have h3 : padicValNat q M ≤ padicValNat q ((b n).gcd M) := (padicValNat_dvd_iff_le h_gcd_ne).mp h2
        omega
      omega
    · have h_eq : q^2 = M := by omega
      have h_v2_M : padicValNat q M = 2 := by
        rw [← h_eq]
        exact padicValNat.prime_pow 2
      have h_v_bn_pos : 1 ≤ padicValNat q (b n) := by
        have h_key_weak : padicValNat q M ≤ padicValNat q (b n) + 1 := key_lemma n hn q hq2_le_M
        omega
      have h_q_dvd_bn : q ∣ b n := by
        have h_bn_ne : b n ≠ 0 := by
          have := b_pos n hn
          omega
        have := (padicValNat_dvd_iff_le h_bn_ne).mpr h_v_bn_pos
        rwa [pow_one] at this
      have h_q_dvd_M : q ∣ M := by
        rw [← h_eq]
        exact dvd_pow_self q (by decide)
      have h_q_dvd_gcd : q ∣ (b n).gcd M := Nat.dvd_gcd h_q_dvd_bn h_q_dvd_M
      have h_gcd_ge_q : q ≤ (b n).gcd M := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (by omega)) h_q_dvd_gcd
      have h_a_le_q : A323386 n ≤ q := by
        have h_mul_eq : A323386 n * (b n).gcd M = q^2 := by
          rw [h_mul, h_eq]
        have h_le_mul : A323386 n * q ≤ A323386 n * (b n).gcd M := Nat.mul_le_mul_left _ h_gcd_ge_q
        rw [h_mul_eq] at h_le_mul
        have h_ring : q^2 = q * q := by ring
        rw [h_ring] at h_le_mul
        exact Nat.le_of_mul_le_mul_right h_le_mul (by have : 2 ≤ q := hq_prime.two_le; omega)
      have hq_ge : 2 ≤ q := hq_prime.two_le
      have hq2_gt_q : q < q^2 := by
        have : q * 1 < q * q := by
          apply Nat.mul_lt_mul_of_pos_left
          · have : 2 ≤ q := hq_prime.two_le
            omega
          · have : 2 ≤ q := hq_prime.two_le
            omega
        rwa [Nat.mul_one, ← sq] at this
      omega

