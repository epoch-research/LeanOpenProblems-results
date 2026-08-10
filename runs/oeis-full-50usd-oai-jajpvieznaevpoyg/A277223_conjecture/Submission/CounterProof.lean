import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


open Nat Set
private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum
private abbrev N : ℕ := 8181818181818181818181818181818181818181818181818182

private def sd10 (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else n % 10 + sd10 (n / 10)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num : 1 < 10)

private lemma sd_rec (n : ℕ) : sum_digits_10 n = n % 10 + sum_digits_10 (n / 10) := by
  unfold sum_digits_10
  by_cases hn : n = 0
  · subst hn; simp
  · have hp : 0 < n := Nat.pos_of_ne_zero hn
    rw [Nat.digits_def' (by norm_num : 1 < 10) hp]
    simp [List.sum_cons]

private lemma sd10_eq_sum_digits (n : ℕ) : sd10 n = sum_digits_10 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      unfold sd10
      by_cases hn : n = 0
      · simp [hn, sum_digits_10]
      · simp [hn]
        rw [sd_rec n]
        have hlt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by norm_num : 1 < 10)
        rw [ih (n/10) hlt]

private def sd10F : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else n % 10 + sd10F fuel (n / 10)

private lemma sd10F_eq_sum_digits (fuel n : ℕ) (hn : n < 10 ^ fuel) :
    sd10F fuel n = sum_digits_10 n := by
  induction fuel generalizing n with
  | zero =>
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      simp [sd10F, sum_digits_10]
  | succ fuel ih =>
      unfold sd10F
      by_cases h0 : n = 0
      · simp [h0, sum_digits_10]
      · simp [h0]
        rw [sd_rec n]
        have hdiv : n / 10 < 10 ^ fuel := by
          rw [pow_succ'] at hn
          exact Nat.div_lt_of_lt_mul hn
        rw [ih (n/10) hdiv]




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
  calc
    k * N < 10 ^ (Nat.digits 10 k).length * 10 ^ (52:ℕ) := by
      exact Nat.mul_lt_mul'' hkpow hN
    _ = 10 ^ ((Nat.digits 10 k).length + 52) := by
      rw [← pow_add]

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
      calc
        k * N < 10 ^ (Nat.digits 10 k).length * 10 ^ (52:ℕ) := by
          exact Nat.mul_lt_mul'' hkpow hN
        _ = 10 ^ ((Nat.digits 10 k).length + 52) := by
          rw [← pow_add]
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

private lemma finite_check_all :
    ∀ i : Fin 500, ((i : ℕ) = sd10F 60 ((i : ℕ) * N) → (i : ℕ) = 0 ∨ (i : ℕ) = 11) := by
  decide

private lemma finite_check (k : ℕ) (hk : k < 500) (h : k = sum_digits_10 (k * N)) :
    k = 0 ∨ k = 11 := by
  have hbound : k * N < 10 ^ (60:ℕ) := by
    have hk3 : k < 10 ^ (3:ℕ) := by
      exact lt_trans hk (by norm_num : (500:ℕ) < 10 ^ (3:ℕ))
    have hN : N < 10 ^ (52:ℕ) := by norm_num [N]
    calc
      k * N < 10 ^ (3:ℕ) * 10 ^ (52:ℕ) := Nat.mul_lt_mul'' hk3 hN
      _ = 10 ^ (55:ℕ) := by norm_num [pow_add]
      _ < 10 ^ (60:ℕ) := by norm_num
  have h' : k = sd10F 60 (k * N) := by
    rw [sd10F_eq_sum_digits 60 (k * N) hbound]
    exact h
  exact finite_check_all ⟨k, hk⟩ h'

private theorem A_eq_11 :
    (let valid_multipliers : Set ℕ := { k | k = sum_digits_10 (k * N) }; sSup valid_multipliers) = 11 := by
  let S : Set ℕ := { k | k = sum_digits_10 (k * N) }
  have h11 : 11 ∈ S := by
    dsimp [S]
    norm_num [sum_digits_10, N]
  have hupper : ∀ k ∈ S, k ≤ 11 := by
    intro k hk
    have hkvalid : k = sum_digits_10 (k * N) := hk
    have hsmall : k < 500 := valid_lt_500 k hkvalid
    have hcases := finite_check k hsmall hkvalid
    omega
  have hg : IsGreatest S 11 := ⟨h11, hupper⟩
  change sSup S = 11
  exact hg.csSup_eq

#check A_eq_11
