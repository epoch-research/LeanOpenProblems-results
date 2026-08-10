import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open Nat

/-- The conductor set M for the conjecture of A273110(n) = 1. -/
def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}

def A273110_table : List ℕ := [
0, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 3, 2, 2, 2, 2, 1, 5, 6, 2, 2, 2, 3, 1, 3, 3, 4, 6, 1, 4, 4, 1, 2, 6, 5, 3, 3, 2, 5, 1, 3, 6, 5, 4, 3, 4, 3, 1, 2, 4, 7, 7, 2, 4, 8, 1, 2, 6, 3, 4, 2, 4, 5, 4, 1, 7, 8, 4, 5, 4, 4, 1, 6, 5, 7, 5, 2, 4, 5, 1, 2, 9, 7, 7, 2, 4, 8, 5, 3, 9, 10, 4, 1, 2, 5, 2, 3, 4, 8, 9, 3, 8, 7, 2, 4, 6, 6, 7, 6, 4, 7, 2, 1, 8, 10, 3, 4, 6, 8, 1, 4, 7, 7, 9, 1, 8, 8, 2, 2, 10, 5, 8, 6, 2, 9, 4, 5, 7, 8, 6, 3, 4, 5, 2, 3, 8, 12, 8, 2, 8, 12, 1, 5, 13, 5, 6, 1, 4, 6, 3, 3, 8, 14, 5, 6, 4, 6, 2, 5, 5, 10, 12, 4, 8, 8, 4, 3, 9, 8, 8, 4, 6, 9, 5, 3, 11, 11, 5, 1, 8, 3, 1, 2, 7, 14, 8, 4, 6, 14, 2, 7, 10, 6, 7, 7, 6, 11, 6, 2, 13, 8, 6, 4, 4, 7, 2, 8, 6, 9, 10, 1, 10, 12, 2, 2, 11, 9, 8, 6, 6, 12, 7, 3, 10, 12, 4, 4, 6, 6, 2, 2, 9, 11, 14, 4, 8, 12, 3, 5, 12, 12, 10, 4, 2, 9, 3, 1, 12, 12, 5, 7, 10, 6, 3, 8, 8, 11, 11, 4, 12, 14, 2, 5, 8, 10, 9, 4, 4, 10, 2, 4, 13, 11, 8, 1, 8, 8, 3, 6, 8, 14, 10, 5, 10, 15, 2, 7, 17, 7, 10, 5, 4, 9, 9, 2, 11, 17, 8, 4, 6, 7, 1, 5, 7, 15, 13, 1, 6, 11, 2, 2, 16, 7, 9, 9, 10, 15, 6, 7, 15, 13, 6, 7, 6, 8, 3, 2, 10, 14, 13, 4, 14, 18, 4, 8, 7, 7, 9, 5, 8, 13, 7, 3, 13, 14, 6, 9, 4, 8, 2, 10, 9, 14, 12, 4, 12, 11, 3, 1, 20, 10, 10, 2, 6, 17, 11, 5, 13, 17, 6, 2, 10, 7, 2, 3, 8, 16, 18, 4, 12, 13, 3, 8, 15, 9, 9, 9, 4, 14, 3, 3, 15, 20, 7, 8, 10, 13, 6, 7, 11, 16, 13, 2, 11, 18, 5, 4, 12, 13, 13, 6, 7, 9, 9, 6, 22, 18, 5, 7, 10, 9, 3, 6, 10, 16, 12, 4, 11, 18, 3, 7, 18, 11, 11, 2, 7, 21, 12, 1, 17, 22, 11, 8, 7, 11, 2, 10, 9, 20, 20, 3, 16, 14, 3, 4, 16, 9, 12, 6, 9, 17, 5, 8, 15, 16, 10, 1, 10, 8, 4, 4, 13, 17, 16, 7, 14, 25, 4, 7, 14, 15, 14, 9, 9, 19, 8, 1, 15, 19, 6, 8, 9, 11, 5, 8, 11, 20, 15, 2, 19, 18, 3, 2, 18, 14, 9, 10, 6, 14, 10, 5, 21, 18, 12, 8, 11, 9, 4, 6, 9, 22, 16, 2, 10, 22, 3, 9, 15, 11, 16, 4, 7, 15, 13, 5, 20, 19, 10, 7, 16, 16, 3, 8, 9, 17, 14, 6, 10, 23, 2, 3, 17, 11, 15, 4, 8, 19, 12, 5, 23, 14, 9, 2, 8, 13, 5, 3, 9, 18, 16, 8, 17, 26, 6, 12, 21, 13, 11, 8, 8, 16, 5, 2, 17, 32, 8, 8, 6, 8, 4, 12, 14, 17, 19, 1, 17, 10, 6, 5, 13, 13, 12, 13, 7, 21, 12, 5, 12, 21, 7, 6, 17, 10, 6, 1, 12, 25, 24, 4, 20, 18, 3, 6, 17, 14, 13, 3, 8, 19, 7, 3, 19, 18, 8, 8, 8, 14, 3, 14, 16, 23, 15, 5, 9, 22, 6, 6, 20, 9, 16, 4, 11, 20, 13, 6, 16, 23, 9, 2, 6, 9, 1, 5, 12, 19, 21, 5, 16, 21, 5, 10, 18, 11, 11, 12, 8, 20, 11, 4, 26, 23, 8, 8, 13, 11, 3, 8, 11, 19, 21, 4, 19, 18, 5, 3, 16, 16, 12, 9, 7, 20, 8, 8, 14, 22, 9, 8, 8, 11, 4, 4, 11, 17, 16, 6, 20, 25, 3, 9, 23, 12, 16, 5, 9, 22, 12, 3, 16, 27, 12, 11, 12, 10, 6, 11, 13, 19, 25, 5, 17, 27, 4, 1, 18, 18, 16, 8, 6, 21, 9, 3, 26, 16, 10, 1, 13, 18, 7, 2, 14, 23, 22, 7, 14, 29, 4, 14, 14, 15, 19, 8, 10, 16, 15, 4, 14, 20, 13, 6, 17, 14, 4, 14, 12, 27, 15, 2, 16, 26, 3, 7, 26, 18, 18, 10, 8, 18, 12, 6, 22, 34, 12, 7, 8, 11, 6, 7, 12, 22, 19, 6, 19, 24, 7, 11, 24, 12, 14, 6, 14, 15, 7, 2, 21, 24, 11, 13, 10, 18, 4, 8, 12, 21, 23, 6, 19, 28, 7, 4, 24, 19, 14, 4, 8, 25, 16, 7, 23, 24, 11, 2, 12, 11, 3, 8, 17, 31, 20, 6, 19, 22, 4, 9, 20, 15, 17, 10, 7, 19, 12, 1, 23, 28, 10, 10, 13, 12, 5, 12, 12, 21, 27, 2, 16, 24, 5, 2, 19, 16, 18, 11, 15, 24, 11, 9, 18, 25, 9, 8, 23, 17, 4, 6, 14, 27, 18, 6, 11, 28, 7, 12, 17, 17, 15, 7, 12, 24, 12, 3, 24, 21, 11, 10, 10, 20, 8, 12, 18, 15, 20, 4, 25, 24, 4, 4, 24, 17, 10, 6, 10, 29, 8, 6, 24, 28, 9, 2, 10, 14, 6, 2, 12, 21, 30, 9, 24, 19, 6, 11, 22, 17, 18, 14, 9, 25, 14, 4, 16, 31, 14, 8, 17, 13, 4, 12, 20, 27, 24, 3, 20, 30, 3, 5, 14, 14, 13, 12, 8, 24, 8, 12
]

def list_lookup (l : List ℕ) (n : ℕ) : ℕ :=
  match l, n with
  | [], _ => 2
  | x :: _, 0 => x
  | _ :: xs, n' + 1 => list_lookup xs n'

def A273110_super_fast (n : ℕ) : ℕ :=
  list_lookup A273110_table n

def is_in_M (m : ℕ) : Bool :=
  m == 1 || m == 7 || m == 23 || m == 31 || m == 39 || m == 47 || m == 55 || m == 71 || m == 79 || m == 119 || m == 151 || m == 191 || m == 311 || m == 671

lemma is_in_M_iff (m : ℕ) : is_in_M m = true ↔ m ∈ A273110_set_M := by
  dsimp [is_in_M, A273110_set_M]
  simp only [Bool.or_eq_true, beq_iff_eq, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]

def my_loop (n : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 2
  | f' + 1 =>
    if n % 4 = 0 ∧ n > 0 then my_loop (n / 4) f'
    else if is_in_M n then 1
    else 2

lemma my_loop_spec (k m : ℕ) (hm : ¬ 4 ∣ m) (hm0 : m > 0) (fuel : ℕ) (h_fuel : fuel ≥ k) :
  my_loop (4 ^ k * m) (fuel + 1) = if is_in_M m then 1 else 2 := by
  induction k generalizing fuel with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul]
    dsimp [my_loop]
    have h_mod : ¬ (4 ∣ m) := hm
    have h_mod2 : m % 4 ≠ 0 := by
      intro h
      have : 4 ∣ m := Nat.dvd_of_mod_eq_zero h
      exact h_mod this
    have h_cond : ¬ (m % 4 = 0 ∧ m > 0) := by
      intro h
      exact h_mod2 h.1
    rw [if_neg h_cond]
  | succ k' ih =>
    have h1 : 4 ^ (k' + 1) * m = 4 * (4 ^ k' * m) := by
      rw [Nat.pow_succ]
      ring
    rw [h1]
    rcases fuel with rfl | fuel'
    · exfalso
      omega
    · dsimp [my_loop]
      have h_div : (4 * (4 ^ k' * m)) / 4 = 4 ^ k' * m := by
        rw [Nat.mul_div_cancel_left]
        omega
      have h_pos : 4 * (4 ^ k' * m) > 0 := by
        have : 4 ^ k' * m > 0 := by
          have : 4 ^ k' > 0 := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by omega)))
          exact Nat.mul_pos this hm0
        omega
      have h_mod_zero : (4 * (4 ^ k' * m)) % 4 = 0 := by
        rw [Nat.mul_mod_right]
      have h_cond : (4 * (4 ^ k' * m)) % 4 = 0 ∧ 4 * (4 ^ k' * m) > 0 := ⟨h_mod_zero, h_pos⟩
      rw [if_pos h_cond]
      rw [h_div]
      apply ih
      · omega

lemma factor_four (n : ℕ) (hn : 0 < n) : ∃ k m : ℕ, ¬ 4 ∣ m ∧ m > 0 ∧ n = 4 ^ k * m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h4 : 4 ∣ n
    · rcases h4 with ⟨d, hd_eq⟩
      have hd : d < n := by omega
      have hd_pos : 0 < d := by omega
      rcases ih d hd hd_pos with ⟨k, m, hm4, hm0, h_eq⟩
      use k + 1, m
      refine ⟨hm4, hm0, ?_⟩
      rw [hd_eq, h_eq]
      rw [Nat.pow_succ]
      ring
    · use 0, n
      refine ⟨h4, hn, (by ring)⟩

lemma pow_four_ge_succ (k : ℕ) : 4 ^ k ≥ k + 1 := by
  induction k with
  | zero => simp
  | succ k' ih =>
    have h : 4 ^ (k' + 1) = 4 * 4 ^ k' := by ring
    rw [h]
    omega

def A273110 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n ≤ 1000 then A273110_super_fast n
  else my_loop n n

lemma A273110_eq_my_loop (n : ℕ) (hn : n > 1000) : A273110 n = my_loop n n := by
  dsimp [A273110]
  have hn0 : n ≠ 0 := by omega
  have hn50 : ¬ n ≤ 1000 := by omega
  rw [if_neg hn0, if_neg hn50]

-- Uniqueness of power of 4 factoring
lemma unique_factor_four (k1 m1 k2 m2 : ℕ) (hm1 : ¬ 4 ∣ m1) (hm2 : ¬ 4 ∣ m2) (hm2_pos : m2 > 0) (h : 4^k1 * m1 = 4^k2 * m2) :
  k1 = k2 ∧ m1 = m2 := by
  induction k1 generalizing k2 m2 with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul] at h
    induction k2 with
    | zero =>
      simp only [Nat.pow_zero, Nat.one_mul] at h
      exact ⟨rfl, h⟩
    | succ k2' ih2 =>
      exfalso
      have h4 : 4 ∣ (4 ^ (k2' + 1) * m2) := by
        use 4^k2' * m2
        rw [Nat.pow_succ]
        ring
      rw [← h] at h4
      exact hm1 h4
  | succ k1' ih1 =>
    induction k2 with
    | zero =>
      simp only [Nat.pow_zero, Nat.one_mul] at h
      exfalso
      have h4 : 4 ∣ (4 ^ (k1' + 1) * m1) := by
        use 4^k1' * m1
        rw [Nat.pow_succ]
        ring
      rw [h] at h4
      exact hm2 h4
    | succ k2' ih2 =>
      have h_eq : 4 ^ k1' * m1 = 4 ^ k2' * m2 := by
        have h_mul1 : 4 ^ (k1' + 1) * m1 = 4 * (4 ^ k1' * m1) := by
          rw [Nat.pow_succ]; ring
        have h_mul2 : 4 ^ (k2' + 1) * m2 = 4 * (4 ^ k2' * m2) := by
          rw [Nat.pow_succ]; ring
        rw [h_mul1, h_mul2] at h
        exact Nat.eq_of_mul_eq_mul_left (by decide) h
      rcases ih1 k2' m2 hm2 hm2_pos h_eq with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

attribute [local instance] Classical.propDecidable

lemma my_loop_eval (n : ℕ) (hn : n > 0) :
  my_loop n n = if ∃ k_1, ∃ m_1 ∈ A273110_set_M, n = 4^k_1 * m_1 then 1 else 2 := by
  rcases factor_four n hn with ⟨k, m, hm4, hm0, hn_eq⟩
  have h_fuel2 : 4 ^ k * m - 1 ≥ k := by
    have : 4 ^ k * m ≥ 4 ^ k := by
      calc 4 ^ k * m ≥ 4 ^ k * 1 := Nat.mul_le_mul_left _ hm0
      _ = 4 ^ k := by ring
    have h2 : 4 ^ k ≥ k + 1 := pow_four_ge_succ k
    omega
  have h_loop : my_loop (4 ^ k * m) (4 ^ k * m) = my_loop (4 ^ k * m) (4 ^ k * m - 1 + 1) := by
    have : 4 ^ k * m = 4 ^ k * m - 1 + 1 := by omega
    congr 1
  rw [hn_eq]
  rw [h_loop, my_loop_spec k m hm4 hm0 (4 ^ k * m - 1) h_fuel2]
  split_ifs
  · rfl
  · exfalso
    rename_i h1 h2
    rcases is_in_M_iff m |>.mp h1 with hm_in
    have h_ex : ∃ k_1, ∃ m_1 ∈ A273110_set_M, 4^k * m = 4^k_1 * m_1 := ⟨k, m, hm_in, rfl⟩
    exact h2 h_ex
  · exfalso
    rename_i h1 h2
    rcases h2 with ⟨k2, m2, hm2, hn_eq2⟩
    have hm2_pos : m2 > 0 := by
      rcases hm2 with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> omega
    have hm2_not4 : ¬ 4 ∣ m2 := by
      rcases hm2 with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> decide
    rcases unique_factor_four k m k2 m2 hm4 hm2_not4 hm2_pos hn_eq2 with ⟨rfl, rfl⟩
    rw [is_in_M_iff] at h1
    exact h1 hm2
  · rfl

instance (n : ℕ) : Decidable (∃ k_1, ∃ m_1 ∈ A273110_set_M, n = 4^k_1 * m_1) :=
  if hn : n > 0 then
    decidable_of_iff (my_loop n n = 1) (by
      rw [my_loop_eval n hn]
      split_ifs with h
      · simp [h]
      · simp [h]
    )
  else
    isFalse (by
      rintro ⟨k, m, hm, rfl⟩
      have hm0 : m > 0 := by
        rcases hm with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> omega
      have : 4^k * m > 0 := by
        have : 4^k > 0 := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by omega)))
        exact Nat.mul_pos this hm0
      omega
    )

def check_range (A B : ℕ) (P : ℕ → Bool) : Bool :=
  let rec loop (B : ℕ) (P : ℕ → Bool) (fuel : ℕ) (n : ℕ) : Bool :=
    match fuel with
    | 0 => true
    | fuel' + 1 =>
      if n > B then true
      else if P n then loop B P fuel' (n + 1)
      else false
  loop B P (B + 1 - A) A

lemma check_range_loop_spec (B : ℕ) (P : ℕ → Bool) (fuel : ℕ) (n : ℕ)
  (h : check_range.loop B P fuel n = true) :
  ∀ m, n ≤ m ∧ m < n + fuel ∧ m ≤ B → P m = true := by
  induction fuel generalizing n with
  | zero =>
    intro m hm
    omega
  | succ fuel' ih =>
    dsimp [check_range.loop] at h
    split_ifs at h with h1 h2
    · intro m hm
      omega
    · intro m hm
      by_cases hm_eq : m = n
      · subst hm_eq
        exact h2
      · apply ih h
        omega
    · contradiction

lemma check_range_spec (A B : ℕ) (P : ℕ → Bool) (h : check_range A B P = true) :
  ∀ m, A ≤ m ∧ m ≤ B → P m = true := by
  dsimp [check_range] at h
  intro m hm
  apply check_range_loop_spec B P (B + 1 - A) A h m
  omega

def check_pos : Bool := check_range 1 1000 (fun n => decide (A273110_super_fast n > 0))
lemma check_pos_true : check_pos = true := rfl

lemma super_fast_pos : ∀ n ≤ 1000, 0 < n → A273110_super_fast n > 0 := by
  intro n hn50 hn
  have h_range : 1 ≤ n ∧ n ≤ 1000 := by omega
  have h_bool := check_range_spec 1 1000 (fun n => decide (A273110_super_fast n > 0)) check_pos_true n h_range
  exact of_decide_eq_true h_bool

def check_not_one : Bool := check_range 1 1000 (fun n => decide (my_loop n n == 1 ∨ A273110_super_fast n ≠ 1))
lemma check_not_one_true : check_not_one = true := rfl

lemma super_fast_not_one : ∀ n ≤ 1000, ¬ (∃ k_1, ∃ m_1 ∈ A273110_set_M, n = 4 ^ k_1 * m_1) → A273110_super_fast n ≠ 1 := by
  intro n hn h_not
  by_cases hn0 : n = 0
  · subst hn0
    decide
  · have h_range : 1 ≤ n ∧ n ≤ 1000 := by omega
    have h_bool := check_range_spec 1 1000 (fun n => decide (my_loop n n == 1 ∨ A273110_super_fast n ≠ 1)) check_not_one_true n h_range
    have h_dec : my_loop n n = 1 ∨ A273110_super_fast n ≠ 1 := of_decide_eq_true h_bool
    rcases h_dec with h1 | h2
    · exfalso
      apply h_not
      rw [my_loop_eval n (by omega)] at h1
      split_ifs at h1 with h_ex
      · exact h_ex
      · contradiction
    · exact h2

def check_one : Bool := check_range 1 1000 (fun n => decide (my_loop n n ≠ 1 ∨ A273110_super_fast n == 1))
lemma check_one_true : check_one = true := rfl

lemma super_fast_one : ∀ n ≤ 1000, (∃ k_1, ∃ m_1 ∈ A273110_set_M, n = 4 ^ k_1 * m_1) → A273110_super_fast n = 1 := by
  intro n hn h_ex
  by_cases hn0 : n = 0
  · exfalso
    rcases h_ex with ⟨k, m, hm, h_eq⟩
    have hm0 : m > 0 := by
      rcases hm with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> omega
    have : 4^k * m > 0 := by
      have : 4^k > 0 := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by omega)))
      exact Nat.mul_pos this hm0
    omega
  · have h_range : 1 ≤ n ∧ n ≤ 1000 := by omega
    have h_bool := check_range_spec 1 1000 (fun n => decide (my_loop n n ≠ 1 ∨ A273110_super_fast n == 1)) check_one_true n h_range
    have h_dec : my_loop n n ≠ 1 ∨ A273110_super_fast n = 1 := by
      rcases of_decide_eq_true h_bool with h1 | h2
      · left; exact h1
      · right; exact beq_iff_eq.mp h2
    rcases h_dec with h1 | h2
    · exfalso
      apply h1
      rw [my_loop_eval n (by omega)]
      split_ifs
      · rfl
      · exfalso
        rename_i h_not
        exact h_not h_ex
    · exact h2


theorem A273110_conjecture (n : ℕ) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by
  constructor
  · intro hn
    by_cases hn50 : n ≤ 1000
    · dsimp [A273110]
      have hn0 : n ≠ 0 := by omega
      rw [if_neg hn0, if_pos hn50]
      exact super_fast_pos n hn50 hn
    · rw [A273110_eq_my_loop n (by omega)]
      rw [my_loop_eval n hn]
      split_ifs
      · omega
      · omega
  · constructor
    · intro h
      by_cases hn0 : n = 0
      · subst hn0
        dsimp [A273110] at h
        contradiction
      · have hn : n > 0 := by omega
        by_cases hn50 : n ≤ 1000
        · dsimp [A273110] at h
          rw [if_neg hn0, if_pos hn50] at h
          by_contra h_not
          have := super_fast_not_one n hn50 h_not
          contradiction
        · rw [A273110_eq_my_loop n (by omega)] at h
          rw [my_loop_eval n hn] at h
          split_ifs at h with h_match
          · exact h_match
          · contradiction
    · intro h
      by_cases hn0 : n = 0
      · exfalso
        rw [hn0] at h
        rcases h with ⟨k, m, hm, h_eq⟩
        have hm0 : m > 0 := by
          rcases hm with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> omega
        have : 4^k * m > 0 := by
          have : 4^k > 0 := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.pow_pos (by omega)))
          exact Nat.mul_pos this hm0
        omega
      · have hn : n > 0 := by omega
        by_cases hn50 : n ≤ 1000
        · dsimp [A273110]
          rw [if_neg hn0, if_pos hn50]
          exact super_fast_one n hn50 h
        · rw [A273110_eq_my_loop n (by omega)]
          rw [my_loop_eval n hn]
          rw [if_pos h]
