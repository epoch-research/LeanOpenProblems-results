import FormalConjectures.Util.ProblemImports

open Nat Set

private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

lemma sd_rec (n : ℕ) : sum_digits_10 n = n % 10 + sum_digits_10 (n / 10) := by
  unfold sum_digits_10
  by_cases hn : n = 0
  · subst hn; simp
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    rw [Nat.digits_def' (by norm_num : 1 < 10) hp]
    simp [List.sum_cons]

lemma div10_lt_self {n : ℕ} (hn : 0 < n) : n / 10 < n := by
  exact Nat.div_lt_self hn (by norm_num : 1 < 10)

lemma sd_carry_ineq (r : ℕ) : r % 10 + r / 10 ≤ r := by
  by_cases h : r < 10
  · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
    simp
  · have h10 : 10 ≤ r := by omega
    have hdivpos : 1 ≤ r / 10 := Nat.succ_le_iff.mp (Nat.div_pos h10 (by norm_num : 0 < 10))
    -- general identity r = r % 10 + 10 * (r / 10)
    have hid : r = r % 10 + 10 * (r / 10) := (Nat.mod_add_div r 10).symm
    omega

lemma sd_subadd (x y : ℕ) : sum_digits_10 (x + y) ≤ sum_digits_10 x + sum_digits_10 y := by
  let P : ℕ → Prop := fun n => ∀ x y, x + y = n → sum_digits_10 (x + y) ≤ sum_digits_10 x + sum_digits_10 y
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih x y hxy
    by_cases hn : n = 0
    · have hx : x = 0 := by omega
      have hy : y = 0 := by omega
      subst hx; subst hy; simp [sum_digits_10]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hxypos : 0 < x + y := by omega
      rw [sd_rec (x+y), sd_rec x, sd_rec y]
      let r := x % 10 + y % 10
      let q := x / 10 + y / 10 + r / 10
      have hxdec : x = x % 10 + 10 * (x / 10) := (Nat.mod_add_div x 10).symm
      have hydec : y = y % 10 + 10 * (y / 10) := (Nat.mod_add_div y 10).symm
      have hsum : x + y = r % 10 + 10 * q := by
        dsimp [r, q]
        omega
      have hmod : (x + y) % 10 = r % 10 := by
        rw [hsum]
        simp [Nat.add_mod, Nat.mul_mod_right]
      have hdiv : (x + y) / 10 = q := by
        rw [hsum]
        have hrlt : r % 10 < 10 := Nat.mod_lt _ (by norm_num : 0 < 10)
        rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 10), Nat.div_eq_of_lt hrlt]
        simp
      rw [hmod, hdiv]
      have hq_lt : q < n := by
        have : q = (x+y)/10 := by rw [hdiv]
        rw [this, ← hxy]
        exact Nat.div_lt_self hxypos (by norm_num : 1 < 10)
      have hq_le0 := ih q hq_lt (x/10) (y/10 + r/10) (by omega)
      have hq_le : sum_digits_10 q ≤ sum_digits_10 (x/10) + sum_digits_10 (y/10 + r/10) := by
        simpa [q, add_assoc] using hq_le0
      have hc_le : sum_digits_10 (r / 10) ≤ r / 10 := Nat.digit_sum_le 10 (r/10)
      have hsub2 : sum_digits_10 (y / 10 + r / 10) ≤ sum_digits_10 (y/10) + sum_digits_10 (r/10) := by
        have hlt2 : y/10 + r/10 < n := by
          calc y/10 + r/10 ≤ q := by dsimp [q]; omega
            _ < n := hq_lt
        exact ih (y/10 + r/10) hlt2 (y/10) (r/10) rfl
      have hcarry : r % 10 + r / 10 ≤ x % 10 + y % 10 := by
        exact sd_carry_ineq r
      calc
        r % 10 + sum_digits_10 q
            ≤ r % 10 + (sum_digits_10 (x/10) + sum_digits_10 (y/10 + r/10)) := by omega
        _ ≤ r % 10 + (sum_digits_10 (x/10) + (sum_digits_10 (y/10) + sum_digits_10 (r/10))) := by omega
        _ ≤ r % 10 + (sum_digits_10 (x/10) + (sum_digits_10 (y/10) + r/10)) := by omega
        _ ≤ x % 10 + sum_digits_10 (x/10) + (y % 10 + sum_digits_10 (y/10)) := by omega
  have hall : ∀ n, P n := fun n => Nat.strong_induction_on n hP
  exact hall (x+y) x y rfl
