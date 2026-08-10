import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

open Nat Set
private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum
private abbrev N : ℕ := 8181818181818181818181818181818181818181818181818182

private lemma pow10_big (q : ℕ) (hq : 10 ≤ q) : 100 * (q + 1) ≤ 10 ^ q := by
  -- induction from 10 upward
  have base : 100 * (10 + 1) ≤ 10 ^ (10:ℕ) := by norm_num
  refine Nat.le_induction base ?_ q hq
  intro q hq_ge ih
  calc
    100 * (q + 1 + 1) ≤ 10 * (100 * (q + 1)) := by omega
    _ ≤ 10 * 10 ^ q := by exact Nat.mul_le_mul_left 10 ih
    _ = 10 ^ (q + 1) := by ring

private lemma lt_pow_div100 (k : ℕ) (hk : 1000 ≤ k) : k < 10 ^ (k / 100) := by
  let q := k / 100
  have hq : 10 ≤ q := by
    dsimp [q]
    exact Nat.le_div_iff_mul_le (by norm_num : 0 < 100) |>.2 (by omega)
  have hklt : k < 100 * (q + 1) := by
    have hmod : k % 100 < 100 := Nat.mod_lt k (by norm_num : 0 < 100)
    have hdecomp : k = 100 * q + k % 100 := by
      dsimp [q]
      omega
    omega
  exact lt_of_lt_of_le hklt (pow10_big q hq)

private lemma digits_len_le_div100 (k : ℕ) (hk : 1000 ≤ k) :
    (Nat.digits 10 k).length ≤ k / 100 := by
  rw [Nat.digits_length_le_iff (by norm_num : 1 < 10)]
  exact lt_pow_div100 k hk

private lemma list_sum_le_nine_len (l : List ℕ) (h : ∀ x ∈ l, x ≤ 9) :
    l.sum ≤ 9 * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : a ≤ 9 := h a (by simp)
      have ht : ∀ x ∈ t, x ≤ 9 := by
        intro x hx; exact h x (by simp [hx])
      have iht := ih ht
      simp [List.sum_cons]
      omega

private lemma sd_le_nine_len (m : ℕ) :
    sum_digits_10 m ≤ 9 * (Nat.digits 10 m).length := by
  unfold sum_digits_10
  exact list_sum_le_nine_len _ (by
    intro x hx
    have hxlt : x < 10 := Nat.digits_lt_base (by norm_num : 1 < 10) hx
    omega)

private lemma len_mul_N_le (k : ℕ) (hk : 1000 ≤ k) :
    (Nat.digits 10 (k * N)).length ≤ (Nat.digits 10 k).length + 52 := by
  rw [Nat.digits_length_le_iff (by norm_num : 1 < 10)]
  have hkpow : k < 10 ^ (Nat.digits 10 k).length := Nat.lt_base_pow_length_digits (by norm_num : 1 < 10)
  have hN : N < 10 ^ (52:ℕ) := by norm_num [N]
  have hmul : k * N < 10 ^ (Nat.digits 10 k).length * 10 ^ (52:ℕ) := by
    exact Nat.mul_lt_mul'' hkpow hN
  have hp : 10 ^ (Nat.digits 10 k).length * 10 ^ (52:ℕ) = 10 ^ ((Nat.digits 10 k).length + 52) := by
    rw [← pow_add]
  simpa [hp]
    using hmul

private lemma valid_lt_500 (k : ℕ) (h : k = sum_digits_10 (k * N)) : k < 500 := by
  by_contra hnot
  have hk500 : 500 ≤ k := by omega
  have hsd := sd_le_nine_len (k * N)
  by_cases hk1000 : k < 1000
  · have hlenk : (Nat.digits 10 k).length ≤ 3 := by
      rw [Nat.digits_length_le_iff (by norm_num : 1 < 10)]
      norm_num
      exact hk1000
    have hlen : (Nat.digits 10 (k * N)).length ≤ (Nat.digits 10 k).length + 52 := by
      rw [Nat.digits_length_le_iff (by norm_num : 1 < 10)]
      have hkpow : k < 10 ^ (Nat.digits 10 k).length := Nat.lt_base_pow_length_digits (by norm_num : 1 < 10)
      have hN : N < 10 ^ (52:ℕ) := by norm_num [N]
      have hmul : k * N < 10 ^ (Nat.digits 10 k).length * 10 ^ (52:ℕ) := by
        exact Nat.mul_lt_mul'' hkpow hN
      have hp : 10 ^ (Nat.digits 10 k).length * 10 ^ (52:ℕ) = 10 ^ ((Nat.digits 10 k).length + 52) := by
        rw [← pow_add]
      simpa [hp] using hmul
    have hineq : k ≤ 9 * (3 + 52) := by
      calc
        k = sum_digits_10 (k * N) := h
        _ ≤ 9 * (Nat.digits 10 (k * N)).length := hsd
        _ ≤ 9 * ((Nat.digits 10 k).length + 52) := by omega
        _ ≤ 9 * (3 + 52) := by omega
    norm_num at hineq
    omega
  · have hk : 1000 ≤ k := by omega
    have hlen := len_mul_N_le k hk
    have hlenk := digits_len_le_div100 k hk
    have hineq : k ≤ 9 * (k / 100 + 52) := by
      calc
        k = sum_digits_10 (k * N) := h
        _ ≤ 9 * (Nat.digits 10 (k * N)).length := hsd
        _ ≤ 9 * ((Nat.digits 10 k).length + 52) := by omega
        _ ≤ 9 * (k / 100 + 52) := by omega
    have hlt : 9 * (k / 100 + 52) < k := by
      have hq : 10 ≤ k / 100 := Nat.le_div_iff_mul_le (by norm_num : 0 < 100) |>.2 (by omega)
      have hdecomp : k = 100 * (k / 100) + k % 100 := by omega
      omega
    omega

#check valid_lt_500
