import FormalConjectures.Util.ProblemImports

open Nat Int Finset

lemma padicValNat_le_self (p x : ℕ) [hp : Fact p.Prime] (hx : x ≠ 0) : padicValNat p x ≤ x := by
  have h_pow := padicValNat.pow_padicValNat_dvd (p := p) (n := x)
  have h_le := Nat.le_of_dvd (Nat.pos_of_ne_zero hx) h_pow
  have h_p : p ≥ 2 := hp.out.two_le
  have h_pow_le : p ^ padicValNat p x ≥ padicValNat p x := Nat.le_self_pow (by omega) _
  omega

lemma padicValNat_eq_sum_dvd (p : ℕ) [hp : Fact p.Prime] (x : ℕ) (hx : x ≠ 0) :
    (padicValNat p x : ℤ) = ∑ j ∈ Ico 1 (x + 1), if p^j ∣ x then (1 : ℤ) else 0 := by
  let k := padicValNat p x
  have hk_le : k ≤ x := padicValNat_le_self p x hx
  have h_split : Ico 1 (x + 1) = Ico 1 (k + 1) ∪ Ico (k + 1) (x + 1) := by
    rw [union_Ico_eq_Ico]
    · omega
    · omega
  rw [h_split, sum_union]
  · have h_sum1 : ∑ j ∈ Ico 1 (k + 1), (if p^j ∣ x then (1 : ℤ) else 0) = ∑ j ∈ Ico 1 (k + 1), (1 : ℤ) := by
      apply sum_congr rfl
      intro j hj
      rw [mem_Ico] at hj
      have hj_le : j ≤ k := by omega
      have h_dvd : p^j ∣ x := by
        rw [padicValNat_dvd_iff_le hx]
        exact hj_le
      rw [if_pos h_dvd]
    have h_sum2 : ∑ j ∈ Ico (k + 1) (x + 1), (if p^j ∣ x then (1 : ℤ) else 0) = ∑ j ∈ Ico (k + 1) (x + 1), (0 : ℤ) := by
      apply sum_congr rfl
      intro j hj
      rw [mem_Ico] at hj
      have hj_gt : j > k := by omega
      have h_not_dvd : ¬ p^j ∣ x := by
        rw [padicValNat_dvd_iff_le hx]
        exact hj_gt
      rw [if_neg h_not_dvd]
    rw [h_sum1, h_sum2, sum_const, sum_const, nsmul_zero, add_zero]
    simp only [Ico_cards, card_Ico]
    have : k + 1 ≥ 1 := by omega
    omega
  · rw [disjoint_iff_ne]
    intro a ha b hb hab
    rw [mem_Ico] at ha hb
    omega


lemma padicValNat_eq_sum_dvd_of_lt (p : ℕ) [hp : Fact p.Prime] {B : ℕ} (x : ℕ) (hx : x ≠ 0) (h_lt : x < B) :
    (padicValNat p x : ℤ) = ∑ j ∈ Ico 1 B, if p^j ∣ x then (1 : ℤ) else 0 := by
  have h_split : Ico 1 B = Ico 1 (x + 1) ∪ Ico (x + 1) B := by
    rw [union_Ico_eq_Ico]
    · omega
    · omega
  rw [h_split, sum_union]
  · rw [← padicValNat_eq_sum_dvd p x hx]
    have h_zero : ∑ j ∈ Ico (x + 1) B, (if p^j ∣ x then (1 : ℤ) else 0) = 0 := by
      apply sum_eq_zero
      intro j hj
      rw [mem_Ico] at hj
      have hj_gt : j > padicValNat p x := by
        have : padicValNat p x ≤ x := padicValNat_le_self p x hx
        omega
      have h_not_dvd : ¬ p^j ∣ x := by
        rw [padicValNat_dvd_iff_le hx]
        exact hj_gt
      rw [if_neg h_not_dvd]
    rw [h_zero, add_zero]
  · rw [disjoint_iff_ne]
    intro a ha b hb hab
    rw [mem_Ico] at ha hb
    omega


lemma padicValNat_factorial_eq_sum (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (padicValNat p n.factorial : ℤ) = ∑ k ∈ range n, (padicValNat p (k + 1) : ℤ) := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    have h_fact : (k + 1).factorial = (k + 1) * k.factorial := rfl
    rw [h_fact]
    have fk : k.factorial ≠ 0 := factorial_ne_zero k
    rw [padicValNat.mul (succ_ne_zero k) fk]
    rw [sum_range_succ]
    push_cast
    omega


lemma r3_ge_min_of_eq (D y k : ℕ) (hD : D ≥ 2) (hy : y < D) (hk : k < 9) (h_eq : 9 * y + 1 = (9 - k) * D) :
    (3 * y) % D ≥ (2 * y) % D ∨ (3 * y) % D ≥ (4 * y) % D ∨ (3 * y) % D ≥ (7 * y) % D := by
  have h_not_3 : ¬ 3 ∣ (9 - k) := by
    intro h3
    have h_dvd : 3 ∣ 9 * y + 1 := by
      rw [h_eq]
      exact dvd_mul_of_dvd_left h3 D
    have h_dvd9 : 3 ∣ 9 * y := dvd_mul_of_dvd_left (by decide) y
    have : 3 ∣ 1 := (natCast_dvd_natCast).mp (by
      have : (3 : ℤ) ∣ (9 * y + 1 - 9 * y) := dvd_sub (by exact_mod_cast h_dvd) (by exact_mod_cast h_dvd9)
      exact_mod_cast this)
    omega
  interval_cases k
  · -- k = 0
    omega
  · -- k = 1
    right; left
    have h_mod3 : (3 * y) % D = (6 * D - 3) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    have h_mod4 : (4 * y) % D = (5 * D - 4) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    rw [h_mod3, h_mod4]
    omega
  · -- k = 2
    right; left
    have h_mod3 : (3 * y) % D = (3 * D - 3) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    have h_mod4 : (4 * y) % D = (1 * D - 4) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    rw [h_mod3, h_mod4]
    omega
  · -- k = 3
    omega
  · -- k = 4
    right; left
    have h_mod3 : (3 * y) % D = (6 * D - 3) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    have h_mod4 : (4 * y) % D = (2 * D - 4) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    rw [h_mod3, h_mod4]
    omega
  · -- k = 5
    right; right
    have h_mod3 : (3 * y) % D = (3 * D - 3) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    have h_mod7 : (7 * y) % D = (1 * D - 7) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    rw [h_mod3, h_mod7]
    omega
  · -- k = 6
    omega
  · -- k = 7
    right; right
    have h_mod3 : (3 * y) % D = (6 * D - 3) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    have h_mod7 : (7 * y) % D = (5 * D - 7) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    rw [h_mod3, h_mod7]
    omega
  · -- k = 8
    left
    have h_mod3 : (3 * y) % D = (3 * D - 3) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    have h_mod2 : (2 * y) % D = (2 * D - 2) / 9 := by
      rw [Nat.div_eq_iff_eq_mul_right (by decide) (by omega)]
      symm
      omega
    rw [h_mod3, h_mod2]
    omega


lemma sum_residue_eq (D n r : ℕ) (hD : D ≠ 0) (hr : r < D) :
    ∑ k ∈ range n, (if k % D = r then (1 : ℤ) else 0) = (n / D : ℤ) + (if r < n % D then 1 else 0) := by
  induction n with
  | zero =>
    simp [Nat.zero_div, Nat.zero_mod]
  | succ k ih =>
    rw [sum_range_succ, ih]
    have h_div_mod : (k + 1) / D = k / D + if (k % D + 1 = D) then 1 else 0 := by
      -- Nat division step
      omega
    have h_mod : (k + 1) % D = if (k % D + 1 = D) then 0 else k % D + 1 := by
      -- Nat modulo step
      omega
    rw [h_div_mod, h_mod]
    push_cast
    split_ifs <;> omega

lemma count_residue_le (D n r1 r2 : ℕ) (hr : r1 ≤ r2) (hD : D ≠ 0) (hr2 : r2 < D) :
    ∑ k ∈ range n, (if k % D = r1 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = r2 then (1 : ℤ) else 0) := by
  have hr1 : r1 < D := by omega
  rw [sum_residue_eq D n r1 hD hr1]
  rw [sum_residue_eq D n r2 hD hr2]
  split_ifs <;> omega


lemma count_ineq (D n r2 r3 r4 r7 : ℕ) (hD : D ≠ 0) (hr2 : r2 < D) (hr3 : r3 < D) (hr4 : r4 < D) (hr7 : r7 < D)
    (h_or : r3 ≥ r2 ∨ r3 ≥ r4 ∨ r3 ≥ r7) :
    ∑ k ∈ range n, (if k % D = r2 then (1 : ℤ) else 0) +
    ∑ k ∈ range n, (if k % D = r4 then (1 : ℤ) else 0) +
    ∑ k ∈ range n, (if k % D = r7 then (1 : ℤ) else 0) ≥
    ∑ k ∈ range n, (if k % D = r3 then (1 : ℤ) else 0) +
    2 * ∑ k ∈ range n, (if k % D = D - 1 then (1 : ℤ) else 0) := by
  have h_den_le2 : r2 ≤ D - 1 := by omega
  have h_den_le4 : r4 ≤ D - 1 := by omega
  have h_den_le7 : r7 ≤ D - 1 := by omega
  have h_le2 : ∑ k ∈ range n, (if k % D = r2 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = D - 1 then (1 : ℤ) else 0) :=
    count_residue_le D n r2 (D - 1) h_den_le2 hD (by omega)
  have h_le4 : ∑ k ∈ range n, (if k % D = r4 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = D - 1 then (1 : ℤ) else 0) :=
    count_residue_le D n r4 (D - 1) h_den_le4 hD (by omega)
  have h_le7 : ∑ k ∈ range n, (if k % D = r7 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = D - 1 then (1 : ℤ) else 0) :=
    count_residue_le D n r7 (D - 1) h_den_le7 hD (by omega)
  rcases h_or with h | h | h
  · have h_count : ∑ k ∈ range n, (if k % D = r2 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = r3 then (1 : ℤ) else 0) :=
      count_residue_le D n r2 r3 h hD hr3
    omega
  · have h_count : ∑ k ∈ range n, (if k % D = r4 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = r3 then (1 : ℤ) else 0) :=
      count_residue_le D n r4 r3 h hD hr3
    omega
  · have h_count : ∑ k ∈ range n, (if k % D = r7 then (1 : ℤ) else 0) ≥ ∑ k ∈ range n, (if k % D = r3 then (1 : ℤ) else 0) :=
      count_residue_le D n r7 r3 h hD hr3
    omega


