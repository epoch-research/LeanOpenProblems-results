import FormalConjectures.Util.ProblemImports
open Nat
open Rat

noncomputable def A022030 (n : ℕ) : ℕ :=
  if n = 0 then 4
  else if n = 1 then 16
  else
    let a_n_1 := A022030 (n - 1)
    let a_n_2 := A022030 (n - 2)
    let num := a_n_1 ^ 2
    let den := a_n_2
    if n % 2 = 0 then
      (num + den - 1) / den - 1
    else
      (num / den) + 1
termination_by n

noncomputable def A022030_original (n : ℕ) : ℕ :=
  if h0 : n = 0 then 4
  else if h1 : n = 1 then 16
  else
    let b_n_1 := A022030_original (n - 1)
    let b_n_2 := A022030_original (n - 2)
    let num := b_n_1 ^ 2
    let den := b_n_2
    (num + den - 1) / den - 1
termination_by n

def C : ℕ → ℤ
| 0 => 4
| 1 => 16
| 2 => 63
| (n + 3) => 4 * C (n + 2) - C n

def d (n : ℕ) : ℤ := C (n + 1)^2 - C (n + 2) * C n

lemma C_add_3 (n : ℕ) : C (n + 3) = 4 * C (n + 2) - C n := by rfl

theorem d_rec (n : ℕ) : d (n + 3) = 4 * d (n + 1) + d n := by
  dsimp [d]
  have h1 : C (n + 3) = 4 * C (n + 2) - C n := C_add_3 n
  have h2 : C (n + 4) = 4 * C (n + 3) - C (n + 1) := C_add_3 (n + 1)
  have h3 : C (n + 5) = 4 * C (n + 4) - C (n + 2) := C_add_3 (n + 2)
  rw [h3, h2, h1]
  ring

theorem d_pos (n : ℕ) : 0 < d n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => norm_num [d, C]
  | 1 => norm_num [d, C]
  | 2 => norm_num [d, C]
  | m + 3 =>
    rw [d_rec m]
    have h1 : 0 < d (m + 1) := ih (m + 1) (by omega)
    have h2 : 0 < d m := ih m (by omega)
    linarith

theorem C_growth (n : ℕ) : 3 * C n ≤ C (n + 1) ∧ 0 < C n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => norm_num [C]
  | 1 => norm_num [C]
  | 2 => norm_num [C]
  | m + 3 =>
    constructor
    · rw [C_add_3 (m + 1)]
      have h1 : 3 * C (m + 2) ≤ C (m + 3) := (ih (m + 2) (by omega)).1
      have h2 : 3 * C (m + 1) ≤ C (m + 2) := (ih (m + 1) (by omega)).1
      have h3 : 0 < C (m + 1) := (ih (m + 1) (by omega)).2
      linarith
    · have h1 : 3 * C (m + 2) ≤ C (m + 3) := (ih (m + 2) (by omega)).1
      have h2 : 0 < C (m + 2) := (ih (m + 2) (by omega)).2
      linarith

theorem d_le_C (n : ℕ) : d n ≤ C n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 => norm_num [d, C]
  | 1 => norm_num [d, C]
  | 2 => norm_num [d, C]
  | m + 3 =>
    rw [d_rec m, C_add_3 m]
    have h1 : d (m + 1) ≤ C (m + 1) := ih (m + 1) (by omega)
    have h2 : d m ≤ C m := ih m (by omega)
    have h3 : 3 * C (m + 1) ≤ C (m + 2) := (C_growth (m + 1)).1
    have h4 : 3 * C m ≤ C (m + 1) := (C_growth m).1
    have h5 : 0 < C m := (C_growth m).2
    linarith

def C_nat (n : ℕ) : ℕ := (C n).toNat

lemma coe_C_nat (n : ℕ) : (C_nat n : ℤ) = C n := by
  dsimp [C_nat]
  exact Int.toNat_of_nonneg (by linarith [(C_growth n).2])

lemma C_nat_pos (n : ℕ) : 0 < C_nat n := by
  have := (C_growth n).2
  have h2 := coe_C_nat n
  zify at *
  linarith

lemma C_nat_div_eq (n : ℕ) : (C_nat (n + 1)^2 + C_nat n - 1) / C_nat n = C_nat (n + 2) + 1 := by
  apply Nat.div_eq_of_lt_le
  · have h1 : 0 < d n := d_pos n
    have h2 : d n = C (n + 1)^2 - C (n + 2) * C n := rfl
    have c0 : (C_nat n : ℤ) = C n := coe_C_nat n
    have c1 : (C_nat (n + 1) : ℤ) = C (n + 1) := coe_C_nat (n + 1)
    have c2 : (C_nat (n + 2) : ℤ) = C (n + 2) := coe_C_nat (n + 2)
    have cn_pos : 0 < C_nat n := C_nat_pos n
    have cn_pos_z : 0 < C n := (C_growth n).2
    have h_sub : ( (C_nat (n + 1)^2 + C_nat n - 1 : ℕ) : ℤ ) = C (n + 1)^2 + C n - 1 := by
      have sub_le : 1 ≤ C_nat (n + 1)^2 + C_nat n := by omega
      rw [Int.ofNat_sub sub_le]
      push_cast
      rw [c1, c0]
    zify at *
    nlinarith
  · have h1 : d n ≤ C n := d_le_C n
    have h2 : d n = C (n + 1)^2 - C (n + 2) * C n := rfl
    have c0 : (C_nat n : ℤ) = C n := coe_C_nat n
    have c1 : (C_nat (n + 1) : ℤ) = C (n + 1) := coe_C_nat (n + 1)
    have c2 : (C_nat (n + 2) : ℤ) = C (n + 2) := coe_C_nat (n + 2)
    have cn_pos : 0 < C_nat n := C_nat_pos n
    have h_sub : ( (C_nat (n + 1)^2 + C_nat n - 1 : ℕ) : ℤ ) = C (n + 1)^2 + C n - 1 := by
      have sub_le : 1 ≤ C_nat (n + 1)^2 + C_nat n := by omega
      rw [Int.ofNat_sub sub_le]
      push_cast
      rw [c1, c0]
    zify at *
    nlinarith

lemma C_nat_div_eq_sub_one (n : ℕ) : (C_nat (n + 1)^2 + C_nat n - 1) / C_nat n - 1 = C_nat (n + 2) := by
  have := C_nat_div_eq n
  omega

theorem A022030_original_eq_C_nat (n : ℕ) : A022030_original n = C_nat n := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 =>
    rw [A022030_original]
    dsimp
    rfl
  | 1 =>
    rw [A022030_original]
    dsimp
    rfl
  | m + 2 =>
    rw [A022030_original]
    have hm0 : ¬ (m + 2 = 0) := by omega
    have hm1 : ¬ (m + 2 = 1) := by omega
    rw [dif_neg hm0, dif_neg hm1]
    have h_sub1 : m + 2 - 1 = m + 1 := by omega
    have h_sub2 : m + 2 - 2 = m := by omega
    rw [h_sub1, h_sub2]
    have ih1 : A022030_original (m + 1) = C_nat (m + 1) := ih (m + 1) (by omega)
    have ih2 : A022030_original m = C_nat m := ih m (by omega)
    dsimp only
    rw [ih1, ih2]
    exact C_nat_div_eq_sub_one m

theorem oeis_22030_original_conjecture (n : ℕ) :
  A022030_original n = (
    if n = 0 then 4
    else if n = 1 then 16
    else if n = 2 then 63
    else
      4 * (A022030_original (n - 1)) - (A022030_original (n - 3))
  ) := by
  rw [A022030_original_eq_C_nat]
  split_ifs with h0 h1 h2
  · subst h0; rfl
  · subst h1; rfl
  · subst h2; rfl
  · rw [A022030_original_eq_C_nat, A022030_original_eq_C_nat]
    -- we need C_nat n = 4 * C_nat (n - 1) - C_nat (n - 3)
    obtain ⟨m, hm⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    subst hm
    have h_sub1 : m + 3 - 1 = m + 2 := by omega
    have h_sub3 : m + 3 - 3 = m := by omega
    rw [h_sub1, h_sub3]
    have h_add3 := C_add_3 m
    have c_m := coe_C_nat m
    have c_m2 := coe_C_nat (m + 2)
    have c_m3 := coe_C_nat (m + 3)
    have h_pos : 0 < C m := (C_growth m).2
    have h_pos2 : 0 < C (m + 2) := (C_growth (m + 2)).2
    have h_le : C m ≤ 4 * C (m + 2) := by linarith
    have h_le_nat : C_nat m ≤ 4 * C_nat (m + 2) := by
      zify at *
      linarith
    have h_sub : ((4 * C_nat (m + 2) - C_nat m : ℕ) : ℤ) = 4 * C (m + 2) - C m := by
      rw [Int.ofNat_sub h_le_nat]
      push_cast
      rw [c_m, c_m2]
    zify [c_m3, h_sub] at *
    linarith

theorem oeis_22030_original_conjecture.disproof : ¬ (type_of% @oeis_22030_original_conjecture) := sorry
