import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

open List Nat

/-- Counts the number of times `pattern` appears as a contiguous sublist in `target`. -/
def list_count_infix {α : Type*} [DecidableEq α] (pattern : List α) (target : List α) : ℕ :=
  if pattern.isEmpty then 0
  else
    let n := pattern.length
    let m := target.length
    if n > m then 0
    else
      (List.range (m - n + 1)).countP fun i =>
        (target.drop i).take n = pattern

/--
The binary representation of a natural number $n$, most significant bit first, as a list of $0/1$ natural numbers.
For $n=0$, this is defined as the list $[0]$.
For $n>0$, it is the standard binary expansion without leading zeros.
We use `Nat.cast` to map the digits (which are $\mathbb{N}$) to themself.
-/
def binary_pattern_nat (n : ℕ) : List ℕ :=
  match n with
  | 0 => [0]
  | m + 1 => (Nat.digits 2 (m + 1)).reverse

/--
A076141: Number of times $n$ occurs as a binary sub-pattern of $n^2$.
Specifically, $a(n)$ is the number of times the binary pattern of $n$ is an infix of the binary pattern of $n^2$.
Let $B(k)$ be the list of $0/1$ digits of $k$ in base 2, MSB first. $a(n)$ is the number of times $B(n)$
occurs as a contiguous sublist in $B(n^2)$.
-/
def a (n : ℕ) : ℕ :=
  let pattern := binary_pattern_nat n
  let target := binary_pattern_nat (n^2)
  list_count_infix pattern target

/--
OEIS A076141 Conjecture: The number of times $n$ occurs as a binary sub-pattern of $n^2$ is at most 1 for all $n$.
A claim to Formalize: is a(n)<=1 for all n?
-/
lemma length_le_one_of_nodup_of_forall_eq {α : Type*} (l : List α) (hn : l.Nodup) (h : ∀ x ∈ l, ∀ y ∈ l, x = y) : l.length ≤ 1 := by
  match l with
  | [] => simp
  | [x] => simp
  | x :: y :: tl =>
    simp [List.nodup_cons] at hn
    have hx : x ∈ x :: y :: tl := by simp
    have hy : y ∈ x :: y :: tl := by simp
    have heq : x = y := h x hx y hy
    subst heq
    exact False.elim (hn.left.left rfl)

lemma nodup_matches (n : ℕ) : ((List.range ((binary_pattern_nat (n ^ 2)).length - (binary_pattern_nat n).length + 1)).filter (fun i => ((binary_pattern_nat (n ^ 2)).drop i).take (binary_pattern_nat n).length = binary_pattern_nat n)).Nodup := by
  apply List.Nodup.filter
  apply List.nodup_range

lemma periodic_of_overlapping_matches {α : Type*} (target pattern : List α) (x k : ℕ) (hk : k < pattern.length)
  (hx1 : (target.drop x).take pattern.length = pattern)
  (hx2 : (target.drop (x + k)).take pattern.length = pattern) :
  pattern.drop k = pattern.take (pattern.length - k) := by
  have h1 : pattern.drop k = ((target.drop x).take pattern.length).drop k := by rw [hx1]
  rw [List.drop_take] at h1
  have h2 : (target.drop x).drop k = target.drop (x + k) := by rw [List.drop_drop]
  rw [h2] at h1
  have h3 : ((target.drop (x + k)).take pattern.length).take (pattern.length - k) = pattern.take (pattern.length - k) := by
    rw [hx2]
  rw [List.take_take] at h3
  have h4 : min (pattern.length - k) pattern.length = pattern.length - k := by
    apply Nat.min_eq_left
    omega
  rw [h4] at h3
  rw [h3] at h1
  exact h1

lemma coprime_pow_dvd_mul {a b k : ℕ} (h_coprime : Coprime a b) (h_dvd : 2^k ∣ a * b) :
  2^k ∣ a ∨ 2^k ∣ b := by
  by_cases h2a : 2 ∣ a
  · have h2b : ¬ 2 ∣ b := by
      intro h2b
      have h2_gcd : 2 ∣ Nat.gcd a b := Nat.dvd_gcd h2a h2b
      rw [h_coprime.gcd_eq_one] at h2_gcd
      contradiction
    have h_cop : Coprime (2^k) b := by
      have hc : Coprime 2 b := (prime_two.coprime_iff_not_dvd).mpr h2b
      exact hc.pow_left k
    have hd : 2^k ∣ a := h_cop.dvd_of_dvd_mul_right h_dvd
    left; exact hd
  · have h_cop : Coprime (2^k) a := by
      have hc : Coprime 2 a := (prime_two.coprime_iff_not_dvd).mpr h2a
      exact hc.pow_left k
    have h_dvd' : 2^k ∣ b * a := by rwa [mul_comm] at h_dvd
    have hd : 2^k ∣ b := h_cop.dvd_of_dvd_mul_right h_dvd'
    right; exact hd

lemma coprime_self_sub_one (n : ℕ) (h : 1 ≤ n) : Coprime n (n - 1) := by
  rw [coprime_self_sub_right h]
  exact coprime_one_right n

lemma non_overlapping_impossible (n : ℕ) (L : ℕ) (h_n : n < 2^L) (h_n_pos : n > 0)
  (h_eq : n^2 = n * 2^L + n) : False := by
  have h_eq2 : n * n = n * (2^L + 1) := by
    calc n * n = n^2 := by ring
    _ = n * 2^L + n := h_eq
    _ = n * (2^L + 1) := by ring
  have h_div : n = 2^L + 1 := Nat.eq_of_mul_eq_mul_left h_n_pos h_eq2
  omega

lemma binary_pattern_nat_length_pow (n : ℕ) : (binary_pattern_nat (n^2)).length ≤ 2 * (binary_pattern_nat n).length := by
  rcases n with _ | m
  · simp [binary_pattern_nat]
  · have hn : m + 1 > 0 := by omega
    have h_len : (binary_pattern_nat (m + 1)).length = (digits 2 (m + 1)).length := by
      simp [binary_pattern_nat]
    have h_len2 : (binary_pattern_nat ((m + 1)^2)).length = (digits 2 ((m + 1)^2)).length := by
      have h_pos : (m + 1)^2 > 0 := by positivity
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos)
      simp [binary_pattern_nat, hk]
    rw [h_len, h_len2]
    have h2 : 1 < 2 := by decide
    rw [digits_length_le_iff h2]
    have h_bound : m + 1 < 2^(digits 2 (m + 1)).length := by
      rw [← digits_length_le_iff h2]
    have h_bound_sq : (m + 1)^2 < (2^(digits 2 (m + 1)).length)^2 := by
      nlinarith
    have h_pow_mul : (2^(digits 2 (m + 1)).length)^2 = 2^(2 * (digits 2 (m + 1)).length) := by
      rw [← pow_mul, mul_comm]
    rw [h_pow_mul] at h_bound_sq
    exact h_bound_sq

lemma k_lt_L (n x y : ℕ) (L M : ℕ)
  (hL : L = (binary_pattern_nat n).length)
  (hM : M = (binary_pattern_nat (n^2)).length)
  (hx : x ∈ List.range (M - L + 1))
  (hy : y ∈ List.range (M - L + 1))
  (hlt : x < y)
  (h_n_pos : n > 0)
  (hx_eq : ((binary_pattern_nat (n^2)).drop x).take L = binary_pattern_nat n)
  (hy_eq : ((binary_pattern_nat (n^2)).drop y).take L = binary_pattern_nat n) :
  y - x < L := by
  have h_m_le : M ≤ 2 * L := by
    rw [hL, hM]
    exact binary_pattern_nat_length_pow n
  have hy_lt : y < M - L + 1 := by
    rw [List.mem_range] at hy
    exact hy
  have hy_le : y ≤ M - L := by omega
  have h_y_le_L : y ≤ L := by omega
  have hk : y - x ≤ L := by omega
  by_cases h_eq : y - x = L
  · -- If k = L, then since y ≤ L and x < y, we must have y = L and x = 0
    have hy_eq_L : y = L := by omega
    have hx_eq_0 : x = 0 := by omega
    have hM_eq_2L : M = 2 * L := by omega
    -- We can show that binary_pattern_nat (n^2) = binary_pattern_nat n ++ binary_pattern_nat n
    have h_split : binary_pattern_nat (n^2) = binary_pattern_nat n ++ binary_pattern_nat n := by
      have h_len_eq : (binary_pattern_nat (n^2)).length = 2 * L := by rw [← hM, hM_eq_2L]
      have h_drop_0 : (binary_pattern_nat (n^2)).drop 0 = binary_pattern_nat (n^2) := by simp
      have h_take_L : (binary_pattern_nat (n^2)).take L = binary_pattern_nat n := by
        have h_take := hx_eq
        rw [hx_eq_0, h_drop_0] at h_take
        exact h_take
      have h_drop_L : (binary_pattern_nat (n^2)).drop L = binary_pattern_nat n := by
        have h_drop := hy_eq
        rw [hy_eq_L] at h_drop
        have h_len_drop : ((binary_pattern_nat (n^2)).drop L).length = L := by
          rw [List.length_drop, h_len_eq]
          omega
        have h_take_all : ((binary_pattern_nat (n^2)).drop L).take L = (binary_pattern_nat (n^2)).drop L := by
          have h_eq_take : ((binary_pattern_nat (n^2)).drop L).take ((binary_pattern_nat (n^2)).drop L).length = ((binary_pattern_nat (n^2)).drop L) := by
            exact List.take_length
          rw [h_len_drop] at h_eq_take
          exact h_eq_take
        rw [h_take_all] at h_drop
        exact h_drop
      have h_append : binary_pattern_nat (n^2) = (binary_pattern_nat (n^2)).take L ++ (binary_pattern_nat (n^2)).drop L := by
        exact (List.take_append_drop L (binary_pattern_nat (n^2))).symm
      rw [h_append, h_take_L, h_drop_L]
    -- Now we convert this to digits 2 (n^2) = digits 2 n ++ digits 2 n
    rcases n with _ | m
    · contradiction
    · have h_n_pos' : m + 1 > 0 := by omega
      have h_n2_pos : (m + 1)^2 > 0 := by positivity
      have h_digits_n : binary_pattern_nat (m + 1) = (digits 2 (m + 1)).reverse := by rfl
      have h_digits_n2 : binary_pattern_nat ((m + 1)^2) = (digits 2 ((m + 1)^2)).reverse := by
        have h_eq_succ : (m + 1)^2 = ((m + 1)^2 - 1) + 1 := (Nat.sub_add_cancel h_n2_pos).symm
        conv =>
          lhs
          unfold binary_pattern_nat
        rw [h_eq_succ]
      rw [h_digits_n, h_digits_n2] at h_split
      have h_split_rev : (digits 2 ((m + 1)^2)).reverse = ((digits 2 (m + 1)) ++ (digits 2 (m + 1))).reverse := by
        rw [h_split, List.reverse_append]
      have h_digits_eq : digits 2 ((m + 1)^2) = digits 2 (m + 1) ++ digits 2 (m + 1) := by
        apply List.reverse_injective
        exact h_split_rev
      have h_ofDigits_eq : ofDigits 2 (digits 2 ((m + 1)^2)) = ofDigits 2 (digits 2 (m + 1) ++ digits 2 (m + 1)) := by
        rw [h_digits_eq]
      rw [ofDigits_digits, ofDigits_digits_append_digits] at h_ofDigits_eq
      have h_L_eq : (digits 2 (m + 1)).length = L := by
        rw [hL]
        simp [binary_pattern_nat]
      rw [h_L_eq] at h_ofDigits_eq
      have h_pow_L : 2^L = 2^(binary_pattern_nat (m + 1)).length := by
        rw [hL]
      have h_bound : m + 1 < 2^L := by
        rw [h_pow_L]
        have h2 : 1 < 2 := by decide
        rw [← digits_length_le_iff h2]
        simp [binary_pattern_nat]
      have h_ring_eq : (m + 1)^2 = (m + 1) * 2^L + (m + 1) := by
        calc (m + 1)^2 = (m + 1) + 2^L * (m + 1) := h_ofDigits_eq
        _ = (m + 1) * 2^L + (m + 1) := by ring
      exact False.elim (non_overlapping_impossible (m + 1) L h_bound h_n_pos' h_ring_eq)
  · omega



lemma sq_neq_two_mod_eight (a : ℕ) : a^2 % 8 ≠ 2 := by
  have h_eq : a^2 % 8 = (a % 8)^2 % 8 := by
    rw [Nat.pow_two, Nat.mul_mod, Nat.pow_two]
  rw [h_eq]
  have h : a % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize hd : a % 8 = r at *
  interval_cases r <;> decide

lemma dvd_odd_contra (A B k : ℕ) (h_dvd : 2^A ∣ 2^B * (2*k + 1)) (h_gt : A > B) : False := by
  have hd : A = B + (A - B) := by omega
  have hd_pos : A - B ≥ 1 := by omega
  rw [hd] at h_dvd
  have h_pow : 2^(B + (A - B)) = 2^B * 2^(A - B) := by
    exact Nat.pow_add 2 B (A - B)
  rw [h_pow] at h_dvd
  have h_pos : 2^B > 0 := by positivity
  have h_cancel : 2^(A - B) ∣ 2*k + 1 := by
    exact Nat.dvd_of_mul_dvd_mul_left h_pos h_dvd
  have h_sub : A - B = (A - B - 1) + 1 := by omega
  have h_pow2 : 2^(A - B) = 2^(A - B - 1) * 2 := by
    rw [h_sub]
    have h_pow_add : 2^(A - B - 1 + 1) = 2^(A - B - 1) * 2^1 := Nat.pow_add 2 (A - B - 1) 1
    rw [h_pow_add]
    rfl
  have h_dvd_2 : 2 ∣ 2^(A - B) := by
    rw [h_pow2]
    exact dvd_mul_left 2 (2 ^ (A - B - 1))
  have h_dvd_odd : 2 ∣ 2*k + 1 := by
    exact dvd_trans h_dvd_2 h_cancel
  have h_dvd_1 : 2 ∣ 1 := by
    have h_dvd_2k : 2 ∣ 2*k := dvd_mul_right 2 k
    exact (Nat.dvd_add_right h_dvd_2k).mp h_dvd_odd
  omega

lemma eq_pow_of_div (n D : ℕ) (h_n : n > 0) (h_div : n^2 / 2^D = n) : n = 2^D := by
  have h_eq : n^2 = 2^D * (n^2 / 2^D) + n^2 % 2^D := by
    exact (Nat.div_add_mod (n^2) (2^D)).symm
  rw [h_div] at h_eq
  have h_rem : n^2 % 2^D < 2^D := Nat.mod_lt (n^2) (by positivity)
  have h_ge : n ≥ 2^D := by
    by_contra h_lt
    have h_lt' : n < 2^D := by omega
    have h_prod : n^2 < 2^D * n := by
      calc n^2 = n * n := by ring
      _ < 2^D * n := Nat.mul_lt_mul_of_pos_right h_lt' h_n
    omega
  have h_sub : n^2 - 2^D * n = n^2 % 2^D := by
    omega
  have h_factor : n^2 - 2^D * n = n * (n - 2^D) := by
    rw [Nat.mul_sub_left_distrib]
    congr 1
    · ring
    · ring
  rw [h_factor] at h_sub
  by_contra h_ne
  have h_gt : n - 2^D ≥ 1 := by omega
  have h_contra : n * (n - 2^D) ≥ n := by
    calc n * (n - 2^D) ≥ n * 1 := Nat.mul_le_mul_left n h_gt
    _ = n := by ring
  omega

lemma binary_pattern_nat_two_pow (D : ℕ) : binary_pattern_nat (2^D) = 1 :: List.replicate D 0 := by
  rcases D with _ | D
  · have h_d1 : digits 2 1 = [1] := digits_of_lt 2 1 (by decide) (by decide)
    simp [binary_pattern_nat]
  · have h_pos : 2^(D + 1) > 0 := by positivity
    have h_digits : binary_pattern_nat (2^(D + 1)) = (digits 2 (2^(D + 1))).reverse := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos)
      rw [hk]
      rfl
    rw [h_digits]
    have h_eq : digits 2 (2^(D + 1)) = List.replicate (D + 1) 0 ++ [1] := by
      have h_two : 1 < 2 := by decide
      have h_one : 0 < 1 := by decide
      have h_pow_mul : 2^(D + 1) = 2^(D + 1) * 1 := by ring
      rw [h_pow_mul]
      rw [digits_base_pow_mul h_two h_one]
      have h_d1 : digits 2 1 = [1] := digits_of_lt 2 1 (by decide) (by decide)
      rw [h_d1]
    rw [h_eq]
    rw [List.reverse_append, List.reverse_replicate]
    rfl

lemma div_pow_eq_of_take_eq (n : ℕ) (L M : ℕ)
  (hL : L = (binary_pattern_nat n).length)
  (hM : M = (binary_pattern_nat (n^2)).length)
  (h_take : (binary_pattern_nat (n^2)).take L = binary_pattern_nat n) :
  n^2 / 2^(M - L) = n := by
  rcases n with _ | m
  · simp
  · have h_n_pos : (m + 1)^2 > 0 := by positivity
    have h_digits_n : binary_pattern_nat (m + 1) = (digits 2 (m + 1)).reverse := by rfl
    have h_digits_n2 : binary_pattern_nat ((m + 1)^2) = (digits 2 ((m + 1)^2)).reverse := by
      have h_pos : (m + 1)^2 > 0 := by positivity
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos)
      rw [hk]
      rfl
    have h_L_eq : (digits 2 (m + 1)).length = L := by
      rw [hL]
      simp [binary_pattern_nat]
    have h_M_eq : (digits 2 ((m + 1)^2)).length = M := by
      rw [hM]
      have h_pos : (m + 1)^2 > 0 := by positivity
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos)
      simp only [binary_pattern_nat, hk, List.length_reverse]
    have h_take_rev : ((digits 2 ((m + 1)^2)).reverse.take L) = (digits 2 (m + 1)).reverse := by
      rw [← h_digits_n2, h_take, h_digits_n]
    have h_drop_eq : (digits 2 ((m + 1)^2)).drop (M - L) = digits 2 (m + 1) := by
      have h_rev_take_rev : (((digits 2 ((m + 1)^2)).reverse.take L).reverse) = (digits 2 (m + 1)) := by
        rw [h_take_rev, List.reverse_reverse]
      rw [List.reverse_take, List.reverse_reverse] at h_rev_take_rev
      rw [List.length_reverse] at h_rev_take_rev
      rw [h_M_eq] at h_rev_take_rev
      exact h_rev_take_rev
    have h_div : (m + 1)^2 / 2^(M - L) = ofDigits 2 ((digits 2 ((m + 1)^2)).drop (M - L)) := by
      rw [self_div_pow_eq_ofDigits_drop (M - L) ((m + 1)^2) (by decide : 2 ≤ 2)]
    rw [h_drop_eq, ofDigits_digits] at h_div
    exact h_div

lemma mod_pow_eq_of_drop_eq (n : ℕ) (L M : ℕ)
  (hL : L = (binary_pattern_nat n).length)
  (hM : M = (binary_pattern_nat (n^2)).length)
  (h_drop : (binary_pattern_nat (n^2)).drop (M - L) = binary_pattern_nat n) :
  n^2 % 2^L = n := by
  rcases n with _ | m
  · simp
  · have h_n_pos : (m + 1)^2 > 0 := by positivity
    have h_digits_n : binary_pattern_nat (m + 1) = (digits 2 (m + 1)).reverse := by rfl
    have h_digits_n2 : binary_pattern_nat ((m + 1)^2) = (digits 2 ((m + 1)^2)).reverse := by
      have h_pos : (m + 1)^2 > 0 := by positivity
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos)
      rw [hk]
      rfl
    have h_L_eq : (digits 2 (m + 1)).length = L := by
      rw [hL]
      simp [binary_pattern_nat]
    have h_M_eq : (digits 2 ((m + 1)^2)).length = M := by
      rw [hM]
      have h_pos : (m + 1)^2 > 0 := by positivity
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos)
      simp [binary_pattern_nat, hk]
    have h_drop_rev : ((digits 2 ((m + 1)^2)).reverse.drop (M - L)) = (digits 2 (m + 1)).reverse := by
      rw [← h_digits_n2, h_drop, h_digits_n]
    have h_take_eq : (digits 2 ((m + 1)^2)).take L = digits 2 (m + 1) := by
      have h_rev_drop_rev : (((digits 2 ((m + 1)^2)).reverse.drop (M - L)).reverse) = (digits 2 (m + 1)) := by
        rw [h_drop_rev, List.reverse_reverse]
      rw [List.reverse_drop, List.reverse_reverse] at h_rev_drop_rev
      rw [List.length_reverse] at h_rev_drop_rev
      rw [h_M_eq] at h_rev_drop_rev
      have h_sub : M - (M - L) = L := by
        have h_m_le : M ≤ 2 * L := by
          rw [hL, hM]
          exact binary_pattern_nat_length_pow (m + 1)
        have h_L_le : L ≤ M := by
          have h2 : 1 < 2 := by decide
          have h_M_bound : (m + 1)^2 < 2^M := by
            rw [hM]
            have h_pos : (m + 1)^2 > 0 := by positivity
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos)
            simp only [binary_pattern_nat, hk, List.length_reverse]
            rw [← digits_length_le_iff h2]
          have h_sq_ge : (m + 1)^2 ≥ m + 1 := by
            calc (m + 1)^2 = (m + 1) * (m + 1) := by ring
            _ ≥ (m + 1) * 1 := Nat.mul_le_mul_left (m + 1) (by omega)
            _ = m + 1 := by ring
          have h_n_bound : m + 1 < 2^M := by omega
          have h_L_le' : (digits 2 (m + 1)).length ≤ M := by
            rw [digits_length_le_iff h2]
            exact h_n_bound
          have h_L_eq' : (digits 2 (m + 1)).length = L := by
            rw [hL]
            simp [binary_pattern_nat]
          omega
        omega
      rw [h_sub] at h_rev_drop_rev
      exact h_rev_drop_rev
    have h_mod : (m + 1)^2 % 2^L = ofDigits 2 ((digits 2 ((m + 1)^2)).take L) := by
      have h_eq : (m + 1)^2 % 2^L = ofDigits 2 (digits 2 ((m + 1)^2)) % 2^L := by
        rw [ofDigits_digits 2 ((m + 1)^2)]
      rw [h_eq]
      exact ofDigits_mod_pow_eq_ofDigits_take L (by decide : 0 < 2) (digits 2 ((m + 1)^2)) (fun l hl => digits_lt_base (by decide : 2 ≤ 2) hl)
    rw [h_take_eq, ofDigits_digits] at h_mod
    exact h_mod

lemma mod_pow_div_eq_of_match (n : ℕ) (L M z s_z : ℕ)
  (hL : L = (binary_pattern_nat n).length)
  (hM : M = (binary_pattern_nat (n^2)).length)
  (hz_bound : z + L ≤ M)
  (h_sz : s_z = M - L - z)
  (h_match : ((binary_pattern_nat (n^2)).drop z).take L = binary_pattern_nat n) :
  (n^2 / 2^s_z) % 2^L = n := by
  rcases n with _ | m
  · simp
  · have h_n_pos : (m + 1)^2 > 0 := by positivity
    have h_digits_n : binary_pattern_nat (m + 1) = (digits 2 (m + 1)).reverse := by rfl
    have h_digits_n2 : binary_pattern_nat ((m + 1)^2) = (digits 2 ((m + 1)^2)).reverse := by
      have h_pos : (m + 1)^2 > 0 := by positivity
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos)
      rw [hk]
      rfl
    have h_L_eq : (digits 2 (m + 1)).length = L := by
      rw [hL]
      simp [binary_pattern_nat]
    have h_M_eq : (digits 2 ((m + 1)^2)).length = M := by
      rw [hM]
      have h_pos : (m + 1)^2 > 0 := by positivity
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_pos)
      simp only [binary_pattern_nat, hk, List.length_reverse]
    have h_take_rev : (((digits 2 ((m + 1)^2)).reverse.drop z).take L) = (digits 2 (m + 1)).reverse := by
      rw [← h_digits_n2, h_match, h_digits_n]
    have h_take_eq : ((digits 2 ((m + 1)^2)).drop s_z).take L = digits 2 (m + 1) := by
      apply List.reverse_injective
      have h_step : (((digits 2 ((m + 1)^2)).drop s_z).take L).reverse = ((digits 2 ((m + 1)^2)).reverse.drop z).take L := by
        rw [List.reverse_take]
        have h_len_drop : ((digits 2 ((m + 1)^2)).drop s_z).length = M - s_z := by
          rw [List.length_drop, h_M_eq]
        rw [h_len_drop]
        have h_sub_eq : M - s_z - L = z := by omega
        rw [h_sub_eq]
        have h_rev_drop := @List.reverse_drop ℕ (digits 2 ((m + 1)^2)) s_z
        rw [h_M_eq] at h_rev_drop
        rw [h_rev_drop]
        have h_sub_eq2 : M - s_z = z + L := by omega
        rw [h_sub_eq2]
        rw [List.drop_take]
        have h_sub_eq3 : z + L - z = L := by omega
        rw [h_sub_eq3]
      rw [h_step, h_take_rev]
    have h_mod : (m + 1)^2 / 2^s_z % 2^L = ofDigits 2 (((digits 2 ((m + 1)^2)).drop s_z).take L) := by
      have h_eq : (m + 1)^2 / 2^s_z % 2^L = ofDigits 2 ((digits 2 ((m + 1)^2)).drop s_z) % 2^L := by
        rw [self_div_pow_eq_ofDigits_drop s_z ((m + 1)^2) (by decide : 2 ≤ 2)]
      rw [h_eq]
      exact ofDigits_mod_pow_eq_ofDigits_take L (by decide : 0 < 2) ((digits 2 ((m + 1)^2)).drop s_z) (fun l hl => digits_lt_base (by decide : 2 ≤ 2) (List.mem_of_mem_drop hl))
    rw [h_take_eq, ofDigits_digits] at h_mod
    exact h_mod

lemma exists_odd_and_pow (n : ℕ) (h : n > 0) : ∃ (u v : ℕ), Odd u ∧ n = u * 2^v := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with h_even | h_odd
    · rcases h_even with ⟨m, rfl⟩
      have hm : m > 0 := by omega
      have hm_lt : m < m + m := by omega
      rcases ih m hm_lt hm with ⟨u, v, hu, rfl⟩
      use u, v + 1
      refine ⟨hu, ?_⟩
      ring
    · use n, 0
      simp [h_odd]

lemma div_pow_mul_eq_mul_div {u v k : ℕ} (hu : Odd u) (hk_le : k ≤ v) :
  (u * 2^v) / 2^k = u * 2^(v-k) := by
  have h_eq : u * 2^v = (u * 2^(v-k)) * 2^k := by
    rw [mul_assoc]
    congr 1
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [h_eq]
  exact Nat.mul_div_cancel (u * 2^(v-k)) (by positivity)

lemma div_pow_mul_eq_div_pow {u v k : ℕ} (hk_gt : k > v) :
  (u * 2^v) / 2^k = u / 2^(k-v) := by
  have h_eq : 2^k = 2^v * 2^(k-v) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [h_eq]
  rw [mul_comm u (2^v)]
  have h_pos : 2^v > 0 := by positivity
  exact Nat.mul_div_mul_left u (2^(k-v)) h_pos

lemma dvd_mod_pow {u v L k n : ℕ} (h_n : n = u * 2^v) (h_L_sub_k : L - k ≥ v) :
  2^v ∣ n % 2^(L-k) := by
  rw [Nat.mod_def]
  apply Nat.dvd_sub
  · rw [h_n]
    exact dvd_mul_left (2^v) u
  · exact dvd_mul_of_dvd_left (by
      have h_pow : 2^(L-k) = 2^(L-k-v) * 2^v := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [h_pow]
      exact dvd_mul_left (2^v) (2^(L-k-v))
    ) (n / 2^(L-k))

lemma div_eq_mod_of_periodic {n L k : ℕ} (h_n : n > 0)
  (h_L : L = (digits 2 n).length)
  (hk : k < L)
  (h_periodic : ((digits 2 n).reverse.drop k) = ((digits 2 n).reverse.take (L - k))) :
  n / 2^k = n % 2^(L - k) := by
  have h_len : (digits 2 n).length = L := h_L.symm
  have h_drop_rev : ((digits 2 n).reverse.drop k).reverse = (((digits 2 n).reverse).take (L - k)).reverse := by
    rw [h_periodic]
  have h_rev_drop : ((digits 2 n).reverse.drop k).reverse = (digits 2 n).take (L - k) := by
    rw [List.reverse_drop]
    rw [List.length_reverse, h_len, List.reverse_reverse]
  have h_rev_take : (((digits 2 n).reverse).take (L - k)).reverse = (digits 2 n).drop k := by
    rw [List.reverse_take]
    rw [List.length_reverse, h_len, List.reverse_reverse]
    have h_sub : L - (L - k) = k := by omega
    rw [h_sub]
  rw [h_rev_drop, h_rev_take] at h_drop_rev
  have h_ofDigits_eq : ofDigits 2 ((digits 2 n).drop k) = ofDigits 2 ((digits 2 n).take (L - k)) := by
    rw [h_drop_rev]
  have h_div : n / 2^k = ofDigits 2 ((digits 2 n).drop k) := by
    exact self_div_pow_eq_ofDigits_drop k n (by decide : 2 ≤ 2)
  have h_mod : n % 2^(L - k) = ofDigits 2 ((digits 2 n).take (L - k)) := by
    have h_eq : n % 2^(L - k) = ofDigits 2 (digits 2 n) % 2^(L - k) := by
      rw [ofDigits_digits]
    rw [h_eq]
    exact ofDigits_mod_pow_eq_ofDigits_take (L - k) (by decide : 0 < 2) (digits 2 n) (fun l hl => digits_lt_base (by decide : 2 ≤ 2) hl)
  rw [h_div, h_mod, h_ofDigits_eq]

lemma sy_le_v_of_dvd (u v s L : ℕ) (hu : Odd u) (hL : v < L) (hv : v ≥ 1) (h_cases : s ≤ 2 * v) (h_ge : (u^2 * 2^(2*v)) / 2^s ≥ u * 2^v) (h_dvd : 2^L ∣ (u^2 * 2^(2*v)) / 2^s - u * 2^v) (hs : s ≥ 1) : s ≤ v := by
  by_contra h_gt
  have h_sy_gt_v : s > v := by omega
  have h_pow : 2^(v+1) ∣ 2^L := Nat.pow_dvd_pow 2 hL
  have h_dvd' : 2^(v+1) ∣ (u^2 * 2^(2*v)) / 2^s - u * 2^v := dvd_trans h_pow h_dvd
  have h_eq : (u^2 * 2^(2*v)) / 2^s = u^2 * 2^(2*v - s) := by
    rw [Nat.mul_div_assoc]
    · congr 1
      have h_pow_dvd : 2^s ∣ 2^(2*v) := Nat.pow_dvd_pow 2 h_cases
      rw [Nat.div_eq_iff_eq_mul_right (by positivity) h_pow_dvd]
      rw [← Nat.pow_add]
      congr 1
      omega
    · exact Nat.pow_dvd_pow 2 h_cases
  rw [h_eq] at h_dvd'
  have h_sub_eq : 2 * v - s + (s - v) = v := by omega
  have h_factor : u^2 * 2^(2*v - s) - u * 2^v = 2^(2*v - s) * (u^2 - u * 2^(s - v)) := by
    rw [Nat.mul_sub_left_distrib]
    congr 1
    · ring
    · rw [mul_comm (2^(2*v - s)), mul_assoc, ← Nat.pow_add, add_comm (s - v), h_sub_eq]
  rw [h_factor] at h_dvd'
  have h_dvd_cancel : 2^(v + 1 - (2*v - s)) ∣ u^2 - u * 2^(s - v) := by
    have h_lt : 2*v - s < v + 1 := by omega
    have h_pow_add : 2^(v + 1) = 2^(2*v - s) * 2^(v + 1 - (2*v - s)) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [h_pow_add] at h_dvd'
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h_dvd'
  have h_odd : ¬ 2 ∣ u^2 - u * 2^(s - v) := by
    intro h_even
    have h_dvd_pow : 2 ∣ u * 2^(s - v) := by
      have h_s_gt_v : s - v ≥ 1 := by omega
      have h_pow2 : 2^(s - v) = 2^(s - v - 1) * 2 := by
        have h_sub : s - v = (s - v - 1) + 1 := by omega
        nth_rw 1 [h_sub]
        rfl
      rw [h_pow2]
      exact dvd_mul_of_dvd_right (dvd_mul_left 2 (2 ^ (s - v - 1))) u
    have h_ge' : u^2 * 2^(2*v - s) ≥ u * 2^v := by
      rwa [← h_eq]
    have h_rw : (u * 2^(s - v)) * 2^(2*v - s) = u * 2^v := by
      rw [mul_assoc, ← Nat.pow_add, add_comm (s - v), h_sub_eq]
    have h_ge'' : u^2 * 2^(2*v - s) ≥ (u * 2^(s - v)) * 2^(2*v - s) := by
      rw [← h_rw] at h_ge'
      exact h_ge'
    have h_le_u2 : u^2 ≥ u * 2^(s - v) := Nat.le_of_mul_le_mul_right h_ge'' (by positivity)
    have h_add : u^2 = (u^2 - u * 2^(s - v)) + u * 2^(s - v) := (Nat.sub_add_cancel h_le_u2).symm
    have h_dvd_u2 : 2 ∣ u^2 := by
      rw [h_add]
      exact dvd_add h_even h_dvd_pow
    have h_dvd_u : 2 ∣ u := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h_dvd_u2
    have h_not_odd : ¬ Odd u := Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h_dvd_u)
    exact h_not_odd hu
  have h_contra_dvd : 2 ∣ u^2 - u * 2^(s - v) := by
    have h_lt2 : v + 1 - (2*v - s) ≥ 1 := by omega
    have h_pow3 : 2^(v + 1 - (2*v - s)) = 2^(v + 1 - (2*v - s) - 1) * 2 := by
      have h_sub : v + 1 - (2*v - s) = (v + 1 - (2*v - s) - 1) + 1 := by omega
      nth_rw 1 [h_sub]
      rfl
    rw [h_pow3] at h_dvd_cancel
    exact dvd_trans (dvd_mul_left 2 (2 ^ (v + 1 - (2*v - s) - 1))) h_dvd_cancel
  contradiction

lemma div_pow_mul_eq_mul_div_sq (u v s : ℕ) (hs : s ≤ 2 * v) :
  (u^2 * 2^(2*v)) / 2^s = u^2 * 2^(2*v - s) := by
  have h_eq : u^2 * 2^(2*v) = (u^2 * 2^(2*v - s)) * 2^s := by
    rw [mul_assoc]
    congr 1
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [h_eq]
  exact Nat.mul_div_cancel _ (by positivity)

lemma sy_ge_v (u v s L : ℕ) (hu : Odd u) (hL : v < L) (hv : v ≥ 1) 
  (h_ge : (u^2 * 2^(2*v)) / 2^s ≥ u * 2^v)
  (h_dvd : 2^L ∣ (u^2 * 2^(2*v)) / 2^s - u * 2^v) (hs : s < v) : False := by
  have h_2v_sub_s : 2*v - s ≥ v + 1 := by omega
  have h_div : (u^2 * 2^(2*v)) / 2^s = u^2 * 2^(2*v - s) := by
    exact div_pow_mul_eq_mul_div_sq u v s (by omega)
  rw [h_div] at h_dvd
  have h_pow : 2^(v+1) ∣ 2^L := Nat.pow_dvd_pow 2 hL
  have h_dvd' : 2^(v+1) ∣ u^2 * 2^(2*v - s) - u * 2^v := dvd_trans h_pow h_dvd
  have h_dvd_left : 2^(v+1) ∣ u^2 * 2^(2*v - s) := by
    have h_pow2 : 2^(v+1) ∣ 2^(2*v - s) := Nat.pow_dvd_pow 2 h_2v_sub_s
    exact dvd_mul_of_dvd_right h_pow2 (u^2)
  have h_dvd_right : 2^(v+1) ∣ u * 2^v := by
    have h_add : u * 2^v = u^2 * 2^(2*v - s) - (u^2 * 2^(2*v - s) - u * 2^v) := by omega
    rw [h_add]
    exact dvd_sub h_dvd_left h_dvd'
  have h_pow_v1 : 2^(v+1) = 2^v * 2 := by ring
  rw [h_pow_v1] at h_dvd_right
  have h_dvd_2 : 2 ∣ u := by
    have h_mul_comm : 2^v * 2 ∣ 2^v * u := by
      rwa [mul_comm u (2^v)] at h_dvd_right
    have h_pos : 2^v > 0 := by positivity
    exact Nat.dvd_of_mul_dvd_mul_left h_pos h_mul_comm
  have h_not_odd : ¬ Odd u := Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h_dvd_2)
  exact h_not_odd hu

lemma sy_eq_v_implies (u v L : ℕ) (hL : v < L) :
  2^L ∣ u^2 * 2^v - u * 2^v → 2^(L-v) ∣ u * (u - 1) := by
  intro h_dvd
  have h_factor : u^2 * 2^v - u * 2^v = 2^v * (u * (u - 1)) := by
    have h_eq : u^2 * 2^v - u * 2^v = (u^2 - u) * 2^v := by
      rw [Nat.sub_mul]
    have h_u2 : u^2 - u = u * (u - 1) := by
      rw [Nat.mul_sub_left_distrib]
      congr 1
      · rw [Nat.pow_two]
      · ring
    rw [h_eq, h_u2, mul_comm]
  rw [h_factor] at h_dvd
  have h_pow : 2^L = 2^v * 2^(L-v) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [h_pow] at h_dvd
  have h_pos : 2^v > 0 := by positivity
  exact Nat.dvd_of_mul_dvd_mul_left h_pos h_dvd

lemma coprime_two_odd (u : ℕ) (hu : Odd u) : Nat.Coprime 2 u := by
  rw [Nat.Coprime]
  have h_gcd : Nat.gcd 2 u ∣ 2 := Nat.gcd_dvd_left 2 u
  have h_dvd2 : Nat.gcd 2 u = 1 ∨ Nat.gcd 2 u = 2 := by
    have h_divs := (Nat.dvd_prime Nat.prime_two).mp h_gcd
    rcases h_divs with h1 | h2
    · left; exact h1
    · right; exact h2
  rcases h_dvd2 with h_eq1 | h_eq2
  · exact h_eq1
  · have h_dvd_u : 2 ∣ u := by
      have h_gcd_dvd := Nat.gcd_dvd_right 2 u
      rwa [h_eq2] at h_gcd_dvd
    have h_even : Even u := even_iff_two_dvd.mpr h_dvd_u
    have h_not_odd : ¬ Odd u := Nat.not_odd_iff_even.mpr h_even
    contradiction

lemma coprime_dvd_contra (u L v : ℕ) (hu : Odd u) (hu_lt : u < 2^(L-v)) (h_dvd : 2^(L-v) ∣ u * (u - 1)) : u = 1 := by
  have h_cop : Coprime 2 u := coprime_two_odd u hu
  have h_cop_pow : Coprime (2^(L-v)) u := Coprime.pow_left (L-v) h_cop
  have h_dvd_sub : 2^(L-v) ∣ u - 1 := by
    have h_dvd' : 2^(L-v) ∣ (u - 1) * u := by
      rwa [mul_comm] at h_dvd
    exact Coprime.dvd_of_dvd_mul_right h_cop_pow h_dvd'
  have h_zero : u - 1 = 0 := by
    by_contra h_ne
    generalize hK : 2^(L-v) = K at h_dvd_sub hu_lt
    have h_ge : u - 1 ≥ K := Nat.le_of_dvd (by omega) h_dvd_sub
    omega
  have hu_pos : u ≥ 1 := by
    obtain ⟨j, hj⟩ := hu
    omega
  omega

lemma replicate_zero_match_only_zero (v z : ℕ) (h_match : ((1 :: replicate (2*v) 0).drop z).take (v + 1) = 1 :: replicate v 0) : z = 0 := by
  rcases z with _ | z1
  · rfl
  · have h_drop : (1 :: replicate (2*v) 0).drop (z1 + 1) = (replicate (2*v) 0).drop z1 := by rfl
    rw [h_drop] at h_match
    rw [drop_replicate] at h_match
    rw [take_replicate] at h_match
    have h_head : (replicate (min (v + 1) (2*v - z1)) 0).head? = (1 :: replicate v 0).head? := by
      rw [h_match]
    have h_rhs : (1 :: replicate v 0).head? = Option.some 1 := rfl
    rw [h_rhs] at h_head
    have h_lhs : (replicate (min (v + 1) (2*v - z1)) 0).head? = none ∨ (replicate (min (v + 1) (2*v - z1)) 0).head? = Option.some 0 := by
      generalize hK : min (v + 1) (2*v - z1) = K
      rcases K with _ | K1
      · left; rfl
      · right; rfl
    rcases h_lhs with h_none | h_some
    · rw [h_none] at h_head
      contradiction
    · rw [h_some] at h_head
      contradiction

lemma sy_gt_v_implies_gt_two_v (u v s L : ℕ) (hu : Odd u) (hL : v < L) (hv : v ≥ 1)
  (h_ge : (u^2 * 2^(2*v)) / 2^s ≥ u * 2^v)
  (h_dvd : 2^L ∣ (u^2 * 2^(2*v)) / 2^s - u * 2^v) (hs : s > v) : s > 2 * v := by
  by_contra h_le
  have h_le' : s ≤ 2 * v := by omega
  have hs1 : s ≥ 1 := by omega
  have h_le_v : s ≤ v := sy_le_v_of_dvd u v s L hu hL hv h_le' h_ge h_dvd hs1
  omega

lemma coprime_two_pow_sub_one (k : ℕ) (hk : k ≥ 1) : Nat.Coprime 2 (2^k - 1) := by
  have h_dvd : ¬ 2 ∣ 2^k - 1 := by
    intro h_dvd'
    have h_div : 2 ∣ 2^k := dvd_pow_self 2 (by omega)
    have h_dvd1 : 2 ∣ 1 := by
      have h_pow_pos : 2^k > 0 := by positivity
      have h_add : 1 = 2^k - (2^k - 1) := by omega
      rw [h_add]
      exact Nat.dvd_sub h_div h_dvd'
    omega
  have h_gcd : Nat.gcd 2 (2^k - 1) ∣ 2 := Nat.gcd_dvd_left 2 (2^k - 1)
  have h_divs := (Nat.dvd_prime Nat.prime_two).mp h_gcd
  rcases h_divs with h1 | h2
  · exact h1
  · have h_gcd_dvd := Nat.gcd_dvd_right 2 (2^k - 1)
    rw [h2] at h_gcd_dvd
    contradiction

lemma distinct_matches_impossible (n x y : ℕ)
  (hx_range : x ∈ List.range ((binary_pattern_nat (n ^ 2)).length - (binary_pattern_nat n).length + 1))
  (hy_range : y ∈ List.range ((binary_pattern_nat (n ^ 2)).length - (binary_pattern_nat n).length + 1))
  (hx_eq : ((binary_pattern_nat (n ^ 2)).drop x).take (binary_pattern_nat n).length = binary_pattern_nat n)
  (hy_eq : ((binary_pattern_nat (n ^ 2)).drop y).take (binary_pattern_nat n).length = binary_pattern_nat n)
  (hlt : x < y) : False := by
  rcases n with _ | n
  · have hL : (binary_pattern_nat 0).length = 1 := by rfl
    have hM : (binary_pattern_nat (0^2)).length = 1 := by rfl
    rw [hL, hM] at hx_range hy_range
    simp at hx_range hy_range
    omega
  · rcases n with _ | n
    · have hL : (binary_pattern_nat 1).length = 1 := by simp [binary_pattern_nat]
      have hM : (binary_pattern_nat (1^2)).length = 1 := by simp [binary_pattern_nat]
      rw [hL, hM] at hx_range hy_range
      simp at hx_range hy_range
      omega
    · -- n = m + 2 >= 2
      have h_n_pos : n + 2 > 0 := by omega
      set n_val := n + 2
      change x ∈ List.range ((binary_pattern_nat (n_val ^ 2)).length - (binary_pattern_nat n_val).length + 1) at hx_range
      change y ∈ List.range ((binary_pattern_nat (n_val ^ 2)).length - (binary_pattern_nat n_val).length + 1) at hy_range
      change ((binary_pattern_nat (n_val ^ 2)).drop x).take (binary_pattern_nat n_val).length = binary_pattern_nat n_val at hx_eq
      change ((binary_pattern_nat (n_val ^ 2)).drop y).take (binary_pattern_nat n_val).length = binary_pattern_nat n_val at hy_eq
      generalize hL : (binary_pattern_nat n_val).length = L
      generalize hM : (binary_pattern_nat (n_val^2)).length = M
      obtain ⟨u, v, hu, h_n_eq⟩ := exists_odd_and_pow n_val h_n_pos
      rw [hL, hM] at hx_range hy_range
      have hx_eq' : ((binary_pattern_nat (n_val^2)).drop x).take L = binary_pattern_nat n_val := by
        rwa [hL] at hx_eq
      have hy_eq' : ((binary_pattern_nat (n_val^2)).drop y).take L = binary_pattern_nat n_val := by
        rwa [hL] at hy_eq
      have h_L_eq_digits : (digits 2 n_val).length = L := by
        rw [← hL]
        have h_dig : binary_pattern_nat n_val = (digits 2 n_val).reverse := rfl
        rw [h_dig, List.length_reverse]
      have hk_lt : y - x < L := by
        apply k_lt_L n_val x y L M hL.symm hM.symm hx_range hy_range hlt h_n_pos hx_eq' hy_eq'
      set k := y - x
      have hk_ge1 : k ≥ 1 := by omega
      have h_periodic : (binary_pattern_nat n_val).drop k = (binary_pattern_nat n_val).take (L - k) := by
        have h_p := periodic_of_overlapping_matches (binary_pattern_nat (n_val^2)) (binary_pattern_nat n_val) x k (by omega) hx_eq
        rw [hL] at h_p
        apply h_p
        have h_eq_add : x + k = y := by omega
        rw [h_eq_add]
        exact hy_eq'
      have h_periodic' : ((digits 2 n_val).reverse.drop k) = ((digits 2 n_val).reverse.take (L - k)) := by
        have h_dig : binary_pattern_nat n_val = (digits 2 n_val).reverse := rfl
        rwa [h_dig] at h_periodic
      have h_div_eq_mod : n_val / 2^k = n_val % 2^(L - k) := by
        exact div_eq_mod_of_periodic h_n_pos h_L_eq_digits.symm hk_lt h_periodic'
      have h_n_lt_powL : n_val < 2^L := by
        have h2 : 1 < 2 := by decide
        rw [← digits_length_le_iff h2]
        rw [h_L_eq_digits]
      have hu_ge1 : u ≥ 1 := by
        obtain ⟨m', hm'⟩ := hu
        omega
      have h_powv_le_n : 2^v ≤ n_val := by
        rw [h_n_eq]
        calc 2^v = 1 * 2^v := by ring
        _ ≤ u * 2^v := Nat.mul_le_mul_right (2^v) hu_ge1
      have h_powv_lt_powL : 2^v < 2^L := lt_of_le_of_lt h_powv_le_n h_n_lt_powL
      have hv_lt_L : v < L := by
        by_contra h_ge
        have h_pow_ge : 2^v ≥ 2^L := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      -- get s_y and s_x
      have hx_range' : x + L ≤ M := by
        rw [List.mem_range] at hx_range hy_range
        omega
      have hy_range' : y + L ≤ M := by
        rw [List.mem_range] at hx_range hy_range
        omega
      set s_y := M - L - y
      set s_x := M - L - x
      have hs_y_eq : s_y = M - L - y := rfl
      have hs_x_eq : s_x = M - L - x := rfl
      have h_match_y : (n_val^2 / 2^s_y) % 2^L = n_val := by
        apply mod_pow_div_eq_of_match n_val L M y s_y hL.symm hM.symm hy_range' hs_y_eq hy_eq'
      have h_match_x : (n_val^2 / 2^s_x) % 2^L = n_val := by
        apply mod_pow_div_eq_of_match n_val L M x s_x hL.symm hM.symm hx_range' hs_x_eq hx_eq'
      have h_sy_pos : s_y ≥ 0 := by omega
      have h_sx_pos : s_x ≥ 1 := by omega
      have h_sx_sy : s_x = s_y + k := by omega
      -- proof that s_y = 0 is impossible
      have h_sy_ne_zero : s_y ≠ 0 := by
        intro h_zero
        have h_match_y' : n_val^2 % 2^L = n_val := by
          have h_rw : s_y = 0 := h_zero
          rw [h_rw] at h_match_y
          simp at h_match_y
          exact h_match_y
        have h_dvd : 2^L ∣ n_val^2 - n_val := Nat.dvd_of_mod_eq_zero (Nat.mod_eq_zero_of_dvd (by
          have h_sub_eq : n_val^2 - n_val = 2^L * (n_val^2 / 2^L) := by
            have h_eq := Nat.div_add_mod (n_val^2) (2^L)
            omega
          rw [h_sub_eq]
          exact dvd_mul_right (2^L) (n_val^2 / 2^L)
        ))
        -- wait, we can just prove 2^L | n_val * (n_val - 1)
        have h_factor : n_val^2 - n_val = n_val * (n_val - 1) := by
          rw [Nat.pow_two, Nat.mul_sub_left_distrib]
          ring
        rw [h_factor] at h_dvd
        have h_cop : Coprime n_val (n_val - 1) := coprime_self_sub_one n_val (by omega)
        have h_or : 2^L ∣ n_val ∨ 2^L ∣ n_val - 1 := coprime_pow_dvd_mul h_cop h_dvd
        rcases h_or with hd1 | hd2
        · have h_le := Nat.le_of_dvd h_n_pos hd1
          omega
        · have h_pos : n_val - 1 > 0 := by omega
          have h_le := Nat.le_of_dvd h_pos hd2
          omega
      have h_sy_ge1 : s_y ≥ 1 := by omega
      rcases le_or_gt k v with hk_le_v | hk_gt_v
      · -- Case 1: k <= v
        have h_div : n_val / 2^k = u * 2^(v-k) := by
          rw [h_n_eq]
          exact div_pow_mul_eq_mul_div hu hk_le_v
        have h_sub_eq : n_val - n_val % 2^(L-k) = 2^(L-k) * (n_val / 2^(L-k)) := by
          have h_eq := Nat.div_add_mod n_val (2^(L-k))
          omega
        have h_dvd_sub : 2^(L-k) ∣ n_val - n_val % 2^(L-k) := by
          rw [h_sub_eq]
          exact dvd_mul_right (2^(L-k)) (n_val / 2^(L-k))
        have h_div_eq_mod' : u * 2^(v-k) = n_val % 2^(L-k) := by
          rw [← h_div, h_div_eq_mod]
        rw [← h_div_eq_mod'] at h_dvd_sub
        rw [h_n_eq] at h_dvd_sub
        have h_sub_simplify : u * 2^v - u * 2^(v-k) = u * 2^(v-k) * (2^k - 1) := by
          have h_eq : u * 2^v = u * 2^(v-k) * 2^k := by
            rw [mul_assoc]
            congr 1
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [h_eq]
          have h_term2 : u * 2^(v-k) = u * 2^(v-k) * 1 := by ring
          nth_rw 2 [h_term2]
          rw [← Nat.mul_sub_left_distrib]
        rw [h_sub_simplify] at h_dvd_sub
        have h_cop1 : Nat.Coprime (2^(L-k)) (2^k - 1) := by
          have h_cop_base : Nat.Coprime 2 (2^k - 1) := coprime_two_pow_sub_one k hk_ge1
          exact Nat.Coprime.pow_left (L - k) h_cop_base
        have h_dvd_mul1 : 2^(L-k) ∣ u * 2^(v-k) := by
          have h_dvd_mul_comm : 2^(L-k) ∣ (u * 2^(v-k)) * (2^k - 1) := h_dvd_sub
          exact Nat.Coprime.dvd_of_dvd_mul_right h_cop1 h_dvd_mul_comm
        have h_cop2 : Nat.Coprime (2^(L-k)) u := by
          have h_cop_base : Nat.Coprime 2 u := coprime_two_odd u hu
          exact Nat.Coprime.pow_left (L - k) h_cop_base
        have h_dvd_mul2 : 2^(L-k) ∣ 2^(v-k) := by
          have h_dvd_comm2 : 2^(L-k) ∣ 2^(v-k) * u := by
            rwa [mul_comm] at h_dvd_mul1
          exact Nat.Coprime.dvd_of_dvd_mul_right h_cop2 h_dvd_comm2
        have h_le_sub : L - k ≤ v - k := by
          have h_pow_le : 2^(L-k) ≤ 2^(v-k) := Nat.le_of_dvd (by positivity) h_dvd_mul2
          rwa [Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at h_pow_le
        omega
      · -- Case 2: k > v
        -- get h_ge for y and x
        have h_div_y : n_val^2 / 2^s_y = (u^2 * 2^(2*v)) / 2^s_y := by
          rw [h_n_eq]
          ring_nf
        have h_div_x : n_val^2 / 2^s_x = (u^2 * 2^(2*v)) / 2^s_x := by
          rw [h_n_eq]
          ring_nf
        have h_ge_match : n_val^2 / 2^s_y ≥ n_val := by
          have h_mod_le := Nat.mod_le (n_val^2 / 2^s_y) (2^L)
          omega
        have h_ge_y : (u^2 * 2^(2*v)) / 2^s_y ≥ u * 2^v := by
          rwa [h_div_y, h_n_eq] at h_ge_match
        have h_dvd_y : 2^L ∣ (u^2 * 2^(2*v)) / 2^s_y - u * 2^v := by
          have h_dvd_div : 2^L ∣ n_val^2 / 2^s_y - n_val := by
            have h_eq := Nat.div_add_mod (n_val^2 / 2^s_y) (2^L)
            have h_sub_eq : n_val^2 / 2^s_y - n_val = 2^L * ((n_val^2 / 2^s_y) / 2^L) := by
              omega
            rw [h_sub_eq]
            exact dvd_mul_right (2^L) ((n_val^2 / 2^s_y) / 2^L)
          rw [h_div_y, h_n_eq] at h_dvd_div
          exact h_dvd_div
        have h_sy_ge_v : s_y ≥ v := by
          by_cases hv_zero : v = 0
          · rw [hv_zero]
            omega
          · have hv : v ≥ 1 := by omega
            by_contra h_lt
            have h_lt' : s_y < v := by omega
            exact sy_ge_v u v s_y L hu hv_lt_L hv h_ge_y h_dvd_y h_lt'
        by_cases h_sy_eq : s_y = v
        · have hv : v ≥ 1 := by
            by_contra hv_zero
            have hv_zero' : v = 0 := by omega
            have h_sy_zero : s_y = 0 := by omega
            exact h_sy_ne_zero h_sy_zero
          have h_dvd_y_v : 2^L ∣ u^2 * 2^v - u * 2^v := by
            have h_rw : s_y = v := h_sy_eq
            rw [h_rw] at h_dvd_y
            have h_div_sq : (u^2 * 2^(2*v)) / 2^v = u^2 * 2^v := by
              have h_div_sq' := div_pow_mul_eq_mul_div_sq u v v (by omega)
              have h_sub : 2 * v - v = v := by omega
              rw [h_sub] at h_div_sq'
              exact h_div_sq'
            rwa [h_div_sq] at h_dvd_y
          have h_dvd_v_imp : 2^(L-v) ∣ u * (u - 1) := by
            exact sy_eq_v_implies u v L hv_lt_L h_dvd_y_v
          have hu_lt : u < 2^(L-v) := by
            have h_div : n_val / 2^v = u := by
              rw [h_n_eq]
              exact Nat.mul_div_cancel u (by positivity)
            rw [← h_div]
            have h_pow : 2^L = 2^v * 2^(L-v) := by
              rw [← Nat.pow_add]
              congr 1
              omega
            rw [h_pow] at h_n_lt_powL
            exact Nat.div_lt_of_lt_mul h_n_lt_powL
          have hu_eq_1 : u = 1 := coprime_dvd_contra u L v hu hu_lt h_dvd_v_imp
          -- if u = 1, then n_val = 2^v
          have h_n_pow2 : n_val = 2^v := by
            rw [h_n_eq, hu_eq_1, one_mul]
          have h_match_replicate : ((1 :: replicate (2*v) 0).drop y).take (v + 1) = 1 :: replicate v 0 := by
            have h_pattern : binary_pattern_nat n_val = 1 :: replicate v 0 := by
              rw [h_n_pow2]
              exact binary_pattern_nat_two_pow v
            have h_target : binary_pattern_nat (n_val^2) = 1 :: replicate (2*v) 0 := by
              have h_eq : n_val^2 = 2^(2*v) := by
                rw [h_n_pow2]
                ring
              rw [h_eq]
              exact binary_pattern_nat_two_pow (2*v)
            have h_len : (binary_pattern_nat n_val).length = v + 1 := by
              rw [h_pattern]
              simp
            have hy_eq_copy := hy_eq
            rw [h_len, h_pattern, h_target] at hy_eq_copy
            exact hy_eq_copy
          have hy_zero : y = 0 := replicate_zero_match_only_zero v y h_match_replicate
          omega
        · have h_sy_gt_v : s_y > v := by omega
          have h_sx_gt_2v : s_x > 2 * v := by omega
          have h_div_x_pow : (u^2 * 2^(2*v)) / 2^s_x = u^2 / 2^(s_x - 2*v) := div_pow_mul_eq_div_pow h_sx_gt_2v
          have h_match_x_rw : (u^2 * 2^(2*v) / 2^s_x) % 2^L = u * 2^v := by
            rw [← h_div_x, h_match_x, h_n_eq]
          rw [h_div_x_pow] at h_match_x_rw
          have h_le_div : u * 2^v ≤ u^2 / 2^(s_x - 2*v) := by
            have h_le := Nat.mod_le (u^2 / 2^(s_x - 2*v)) (2^L)
            omega
          have h_mul_le : u * 2^v * 2^(s_x - 2*v) ≤ u^2 := by
            have h_le_mul_mono : (u * 2^v) * 2^(s_x - 2*v) ≤ (u^2 / 2^(s_x - 2*v)) * 2^(s_x - 2*v) := Nat.mul_le_mul_right (2^(s_x - 2*v)) h_le_div
            have h_div_mul := Nat.div_mul_le_self (u^2) (2^(s_x - 2*v))
            omega
          have h_pow_add_x : 2^v * 2^(s_x - 2*v) = 2^(s_x - v) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          have h_expr : u * 2^v * 2^(s_x - 2*v) = u * 2^(s_x - v) := by
            calc u * 2^v * 2^(s_x - 2*v) = u * (2^v * 2^(s_x - 2*v)) := by ring
            _ = u * 2^(s_x - v) := by rw [h_pow_add_x]
          rw [h_expr] at h_mul_le
          have h_sq_u : u^2 = u * u := by ring
          rw [h_sq_u] at h_mul_le
          have h_le_u : 2^(s_x - v) ≤ u := Nat.le_of_mul_le_mul_left h_mul_le (by omega)
          have hu_lt : u < 2^(L-v) := by
            have h_div : n_val / 2^v = u := by
              rw [h_n_eq]
              exact Nat.mul_div_cancel u (by positivity)
            rw [← h_div]
            have h_pow : 2^L = 2^v * 2^(L-v) := by
              rw [← Nat.pow_add]
              congr 1
              omega
            rw [h_pow] at h_n_lt_powL
            exact Nat.div_lt_of_lt_mul h_n_lt_powL
          have h_sx_lt_L : s_x < L := by
            by_contra h_ge
            have h_pow_ge : 2^(s_x - v) ≥ 2^(L - v) := Nat.pow_le_pow_right (by decide) (by omega)
            omega
          set w_x := n_val^2 / 2^s_x
          have h_wx_val : w_x = u^2 / 2^(s_x - 2*v) := by
            calc w_x = n_val^2 / 2^s_x := rfl
            _ = (u^2 * 2^(2*v)) / 2^s_x := h_div_x
            _ = u^2 / 2^(s_x - 2*v) := h_div_x_pow
          have h_match_x_rw' : w_x % 2^L = u * 2^v := by
            rw [h_match_x, h_n_eq]
          have h_Q_x_pos : w_x / 2^L ≥ 1 := by
            by_contra h_lt
            have h_Q_x_zero : w_x / 2^L = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ (Nat.not_le.mp h_lt))
            have h_w_x_val_eq : w_x = u * 2^v := by
              have h_div_add := Nat.div_add_mod w_x (2^L)
              rw [h_Q_x_zero] at h_div_add
              rw [h_match_x_rw'] at h_div_add
              simp at h_div_add
              exact h_div_add.symm
            rw [h_wx_val] at h_w_x_val_eq
            have h_mul_eq : (u^2 / 2^(s_x - 2*v)) * 2^(s_x - 2*v) = u * 2^v * 2^(s_x - 2*v) := by
              rw [h_w_x_val_eq]
            have h_pow_add_x' : 2^v * 2^(s_x - 2*v) = 2^(s_x - v) := by
              rw [← Nat.pow_add]
              congr 1
              omega
            have h_u_sq_eq : u^2 = u * 2^(s_x - v) + u^2 % 2^(s_x - 2*v) := by
              have h_eq := Nat.div_add_mod (u^2) (2^(s_x - 2*v))
              rw [h_w_x_val_eq] at h_eq
              have h_term_eq2 : 2^(s_x - 2*v) * (u * 2^v) = u * 2^(s_x - v) := by
                calc 2^(s_x - 2*v) * (u * 2^v) = u * (2^v * 2^(s_x - 2*v)) := by ring
                _ = u * 2^(s_x - v) := by rw [h_pow_add_x']
              rw [h_term_eq2] at h_eq
              exact h_eq.symm
            have h_sub_lt : u^2 - u * 2^(s_x - v) < 2^(s_x - 2*v) := by
              have h_rem_lt : u^2 % 2^(s_x - 2*v) < 2^(s_x - 2*v) := Nat.mod_lt (u^2) (by positivity)
              have h_sub_eq_rem : u^2 - u * 2^(s_x - v) = u^2 % 2^(s_x - 2*v) := by
                omega
              rw [h_sub_eq_rem]
              exact h_rem_lt
            have h_factor : u^2 - u * 2^(s_x - v) = u * (u - 2^(s_x - v)) := by
              rw [h_sq_u]
              rw [← Nat.mul_sub_left_distrib]
            rw [h_factor] at h_sub_lt
            have h_u_gt : u > 2^(s_x - v) := by
              have h_sx_sub_v_ge1 : s_x - v ≥ 1 := by omega
              have h_pow_even : Even (2^(s_x - v)) := by
                have h_sub_eq_succ : s_x - v = (s_x - v - 1) + 1 := by omega
                rw [h_sub_eq_succ]
                rw [pow_succ]
                use 2^(s_x - v - 1)
                ring
              have h_not_eq : u ≠ 2^(s_x - v) := by
                intro h_eq_pow
                have h_even : Even u := by
                  rw [h_eq_pow]
                  exact h_pow_even
                have h_not_odd' : ¬ Odd u := Nat.not_odd_iff_even.mpr h_even
                contradiction
              omega
            have h_sub_ge1 : u - 2^(s_x - v) ≥ 1 := by omega
            have h_mul_ge_u : u * (u - 2^(s_x - v)) ≥ u := by
              calc u * (u - 2^(s_x - v)) ≥ u * 1 := Nat.mul_le_mul_left u h_sub_ge1
              _ = u := by ring
            have h_u_gt_pow : u > 2^(s_x - 2*v) := by
              have h_pow_le : 2^(s_x - 2*v) ≤ 2^(s_x - v) := Nat.pow_le_pow_right (by decide) (by omega)
              omega
            omega
          set w_y := n_val^2 / 2^s_y
          have h_match_y' : w_y % 2^L = n_val := h_match_y
          have h_div_k : w_x = w_y / 2^k := by
            change n_val^2 / 2^s_x = (n_val^2 / 2^s_y) / 2^k
            rw [h_sx_sy]
            have h_pow : 2^(s_y + k) = 2^s_y * 2^k := Nat.pow_add 2 s_y k
            rw [h_pow]
            exact (Nat.div_div_eq_div_mul (n_val^2) (2^s_y) (2^k)).symm
          have h_rem_eq : w_y % 2^k = n_val % 2^k := by
            have h_dvd : 2^k ∣ 2^L := Nat.pow_dvd_pow 2 (by omega)
            have h_mod := Nat.mod_mod_of_dvd w_y h_dvd
            rw [h_match_y'] at h_mod
            exact h_mod.symm
          have h_wy_eq : w_y = (w_y / 2^L) * 2^L + n_val := by
            have h_div := Nat.div_add_mod w_y (2^L)
            rw [h_match_y'] at h_div
            rw [mul_comm] at h_div
            exact h_div.symm
          have h_wx_eq : w_x = (w_x / 2^L) * 2^L + n_val := by
            have h_div := Nat.div_add_mod w_x (2^L)
            rw [h_match_x] at h_div
            rw [mul_comm] at h_div
            exact h_div.symm
          have h_sum_eq : (w_y / 2^L) * 2^L + n_val + 2^k * n_val = 2^k * ((w_x / 2^L) * 2^L + n_val) + n_val % 2^k + 2^k * n_val := by
            have h_div := Nat.div_add_mod w_y (2^k)
            rw [← h_div_k] at h_div
            rw [h_rem_eq] at h_div
            rw [h_wy_eq, h_wx_eq] at h_div
            rw [← h_div]
          have h_algebra_add : 2^k * (w_x / 2^L) * 2^L + 2^k * n_val + n_val % 2^k = (w_y / 2^L) * 2^L + n_val := by
            have h_sum_cancel : (w_y / 2^L) * 2^L + n_val = 2^k * ((w_x / 2^L) * 2^L + n_val) + n_val % 2^k := by
              exact Nat.add_right_cancel h_sum_eq
            calc 2^k * (w_x / 2^L) * 2^L + 2^k * n_val + n_val % 2^k = 2^k * ((w_x / 2^L) * 2^L + n_val) + n_val % 2^k := by ring
            _ = (w_y / 2^L) * 2^L + n_val := h_sum_cancel.symm
          have h_algebra : 2^k * n_val + n_val % 2^k - n_val = (w_y / 2^L - 2^k * (w_x / 2^L)) * 2^L := by
            generalize hY : w_y / 2^L = Y at h_algebra_add ⊢
            generalize hX : w_x / 2^L = X at h_algebra_add ⊢
            have h_distrib : (Y - 2^k * X) * 2^L = Y * 2^L - 2^k * X * 2^L := Nat.sub_mul Y (2^k * X) (2^L)
            rw [h_distrib]
            rw [mul_comm Y (2^L)] at h_algebra_add ⊢
            have h_commX : 2^k * X * 2^L = 2^k * (X * 2^L) := by ring
            rw [h_commX] at h_algebra_add ⊢
            omega
          have h_dvd_L : 2^L ∣ 2^k * n_val + n_val % 2^k - n_val := by
            rw [h_algebra]
            exact dvd_mul_left (2^L) (w_y / 2^L - 2^k * (w_x / 2^L))
          have h_algebra2 : 2^k * n_val + n_val % 2^k - n_val = 2^k * (n_val - n_val / 2^k) := by
            have h_div := Nat.div_add_mod n_val (2^k)
            generalize hD : n_val / 2^k = D at h_div ⊢
            generalize hR : n_val % 2^k = R at h_div ⊢
            rw [Nat.mul_sub_left_distrib]
            omega
          have h_dvd_L2 : 2^L ∣ 2^k * (n_val - n_val / 2^k) := by
            rwa [h_algebra2] at h_dvd_L
          have h_dvd_L3 : 2^(L-k) ∣ n_val - n_val / 2^k := by
            have h_pow : 2^L = 2^k * 2^(L-k) := by
              rw [← Nat.pow_add]
              congr 1
              omega
            rw [h_pow] at h_dvd_L2
            exact Nat.dvd_of_mul_dvd_mul_left (by positivity) h_dvd_L2
          have h_n_div : n_val / 2^k = u / 2^(k-v) := by
            rw [h_n_eq]
            exact div_pow_mul_eq_div_pow hk_gt_v
          have h_dvd_L4 : 2^(L-k) ∣ u * 2^v - u / 2^(k-v) := by
            rw [h_n_div] at h_dvd_L3
            rwa [h_n_eq] at h_dvd_L3
          have h_v_lt_sub : v < L - k := by
            omega
          have h_dvd_v : 2^v ∣ u / 2^(k-v) := by
            have h_pow_dvd : 2^v ∣ 2^(L-k) := Nat.pow_dvd_pow 2 (by omega)
            have h_dvd' : 2^v ∣ u * 2^v - u / 2^(k-v) := dvd_trans h_pow_dvd h_dvd_L4
            have h_dvd_mul : 2^v ∣ u * 2^v := dvd_mul_left (2^v) u
            have h_sub_eq : u / 2^(k-v) = u * 2^v - (u * 2^v - u / 2^(k-v)) := by
              have h_le : u / 2^(k-v) ≤ u * 2^v := by
                calc u / 2^(k-v) ≤ u := Nat.div_le_self u (2^(k-v))
                _ ≤ u * 2^v := Nat.le_mul_of_pos_right u (Nat.pow_pos (by decide : 0 < 2))
              omega
            rw [h_sub_eq]
            exact dvd_sub h_dvd_mul h_dvd'
          have h_zero : u / 2^(k-v) = 0 := by
            by_contra h_ne
            have h_pos : u / 2^(k-v) > 0 := Nat.pos_of_ne_zero h_ne
            have h_le : 2^v ≤ u / 2^(k-v) := Nat.le_of_dvd h_pos h_dvd_v
            have h_mul : 2^v * 2^(k-v) ≤ (u / 2^(k-v)) * 2^(k-v) := Nat.mul_le_mul_right (2^(k-v)) h_le
            have h_pow_add : 2^v * 2^(k-v) = 2^k := by
              rw [← Nat.pow_add]
              congr 1
              clear * - hk_gt_v
              omega
            have h_div_mul : (u / 2^(k-v)) * 2^(k-v) ≤ u := Nat.div_mul_le_self u (2^(k-v))
            have h_lt : 2^k ≤ u := by
              have h_mul_rw : 2^k ≤ (u / 2^(k-v)) * 2^(k-v) := by
                rwa [← h_pow_add]
              exact le_trans h_mul_rw h_div_mul
            have h_sx_ge : s_x - v ≥ k + 1 := by
              clear * - h_sx_sy h_sy_gt_v
              omega
            have h_pow_le : 2^(k+1) ≤ 2^(s_x - v) := Nat.pow_le_pow_right (by decide) h_sx_ge
            have h_u_ge : 2^(k+1) ≤ u := le_trans h_pow_le h_le_u
            have h_pow_lt : 2^(k+1) > 2^k := by
              have h_pow_step : 2^(k+1) = 2^k * 2 := rfl
              omega
            nonsense_tactic
          have h_sub_lt : s_x - v < k - v := by
            have h_zero' : u / 2^(k-v) = 0 := h_zero
            have h_ne : 2^(k-v) ≠ 0 := by positivity
            have h_lt : u < 2^(k-v) := Or.resolve_left (Nat.div_eq_zero_iff.mp h_zero') h_ne
            have h_pow_le : 2^(s_x - v) < 2^(k-v) := lt_of_le_of_lt h_le_u h_lt
            rwa [Nat.pow_lt_pow_iff_right (by decide : 1 < 2)] at h_pow_le
          have h_sx_lt_k : s_x < k := by
            omega
          have h_sx_ge_k : s_x ≥ k := by
            omega
          omega

theorem oeis_a076141_conjecture : ∀ n : ℕ, a n ≤ 1 := by
  intro n
  dsimp [a, list_count_infix]
  split_ifs
  · omega
  · omega
  · rw [List.countP_eq_length_filter]
    have h_nodup := nodup_matches n
    have h_eq : ∀ x ∈ ((List.range ((binary_pattern_nat (n ^ 2)).length - (binary_pattern_nat n).length + 1)).filter (fun i => ((binary_pattern_nat (n ^ 2)).drop i).take (binary_pattern_nat n).length = binary_pattern_nat n)),
                 ∀ y ∈ ((List.range ((binary_pattern_nat (n ^ 2)).length - (binary_pattern_nat n).length + 1)).filter (fun i => ((binary_pattern_nat (n ^ 2)).drop i).take (binary_pattern_nat n).length = binary_pattern_nat n)), x = y := by
      intro x hx y hy
      rw [List.mem_filter] at hx hy
      rcases hx with ⟨hx_range, hx_eq⟩
      rcases hy with ⟨hy_range, hy_eq⟩
      rcases lt_trichotomy x y with hlt | rfl | hgt
      · exact False.elim (distinct_matches_impossible n x y hx_range hy_range (of_decide_eq_true hx_eq) (of_decide_eq_true hy_eq) hlt)
      · rfl
      · exact False.elim (distinct_matches_impossible n y x hy_range hx_range (of_decide_eq_true hy_eq) (of_decide_eq_true hx_eq) hgt)
    exact length_le_one_of_nodup_of_forall_eq _ h_nodup h_eq
