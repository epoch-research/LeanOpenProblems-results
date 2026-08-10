import FormalConjectures.Util.ProblemImports

open Nat

/--
A030101: The number whose binary expansion is the reversal of the binary expansion of $n$.
-/
def A030101 (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (List.reverse (Nat.digits 2 n))

/--
A339602: $a(n) = (a(n-2) \oplus A030101(a(n-1))) + 1$, $a(0) = 0$, $a(1) = 1$.
-/
def a : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => (a n).xor (A030101 (a (n + 1))) + 1
termination_by n => n

def digits_fast_aux : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % 2) :: digits_fast_aux fuel (n / 2)

def A030101_fast (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (List.reverse (digits_fast_aux n n))

def a_aux : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 =>
    let (x, y) := a_aux n
    (y, x.xor (A030101_fast y) + 1)

def a_fast (n : ℕ) : ℕ :=
  (a_aux n).1

theorem digits_fast_aux_eq (fuel n : ℕ) (h_fuel : n < 2^fuel) : digits_fast_aux fuel n = Nat.digits 2 n := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this
    simp [digits_fast_aux, digits_zero]
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst hn
      simp [digits_fast_aux, digits_zero]
    · dsimp [digits_fast_aux]
      rw [if_neg hn]
      have h2 : n / 2 < 2^fuel := by
        have h_lt : n < 2^fuel * 2 := by
          rw [pow_succ] at h_fuel
          exact h_fuel
        omega
      rw [ih (n / 2) h2]
      rw [Nat.digits_def' (by omega) (Nat.pos_of_ne_zero hn)]

theorem digits_fast_aux_self (n : ℕ) : digits_fast_aux n n = Nat.digits 2 n := by
  by_cases hn : n = 0
  · subst hn
    simp [digits_fast_aux, digits_zero]
  · apply digits_fast_aux_eq
    exact Nat.lt_pow_self (by decide)

theorem A030101_fast_eq (n : ℕ) : A030101_fast n = A030101 n := by
  simp [A030101_fast, A030101, digits_fast_aux_self]

theorem a_aux_eq (n : ℕ) : a_aux n = (a n, a (n + 1)) := by
  induction n with
  | zero =>
    dsimp [a_aux]
    rw [a, a]
  | succ n ih =>
    dsimp [a_aux]
    rw [ih]
    simp [A030101_fast_eq]
    rw [show n + 1 + 1 = n + 2 by omega]
    rw [a]

theorem a_eq_fast (n : ℕ) : a n = (a_aux n).1 := by
  rw [a_aux_eq]

theorem head!_reverse (l : List ℕ) (h : l ≠ []) : l.reverse.head! = l.getLast h := by
  have h1 : l.reverse.head? = some l.reverse.head! := by
    cases h_rev : l.reverse with
    | nil =>
      have : l = [] := List.reverse_eq_nil_iff.mp h_rev
      contradiction
    | cons x xs => rfl
  have h2 : l.getLast? = some (l.getLast h) := List.getLast?_eq_getLast_of_ne_nil h
  rw [← List.head?_reverse] at h2
  rw [h1] at h2
  injection h2

theorem A030101_odd (m : ℕ) (hm : m ≠ 0) : A030101 m % 2 = 1 := by
  dsimp [A030101]
  rw [Nat.ofDigits_mod_eq_head!]
  have h_ne : Nat.digits 2 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
  have h_rev_head : (List.reverse (Nat.digits 2 m)).head! = (Nat.digits 2 m).getLast h_ne := head!_reverse (Nat.digits 2 m) h_ne
  rw [h_rev_head]
  have h_mem : (Nat.digits 2 m).getLast h_ne ∈ Nat.digits 2 m := List.getLast_mem h_ne
  have h_lt : (Nat.digits 2 m).getLast h_ne < 2 := Nat.digits_lt_base (by decide) h_mem
  have h_nz := Nat.getLast_digit_ne_zero 2 hm
  have h_eq_one : (Nat.digits 2 m).getLast h_ne = 1 := by omega
  rw [h_eq_one]

theorem A030101_lt (n : ℕ) : A030101 n < 2 ^ (Nat.digits 2 n).length := by
  dsimp [A030101]
  have h_len : (Nat.digits 2 n).length = (Nat.digits 2 n).reverse.length := by
    rw [List.length_reverse]
  rw [h_len]
  apply Nat.ofDigits_lt_base_pow_length (by decide)
  intro x hx
  rw [List.mem_reverse] at hx
  exact Nat.digits_lt_base (by decide) hx

theorem ofDigits_append_zero {α : Type*} [Semiring α] (b : α) (l : List ℕ) :
    ofDigits b (l ++ [0]) = ofDigits b l := by
  induction l with
  | nil => simp [ofDigits]
  | cons h t ih =>
    simp [ofDigits, ih]

theorem A030101_lt_even (m : ℕ) (hm : m ≠ 0) (h_mod : m % 2 = 0) :
    A030101 m < 2 ^ ((Nat.digits 2 m).length - 1) := by
  dsimp [A030101]
  have h_digits : Nat.digits 2 m = 0 :: Nat.digits 2 (m / 2) := by
    rw [Nat.digits_def' (by decide) (Nat.pos_of_ne_zero hm)]
    rw [h_mod]
  rw [h_digits]
  simp only [List.reverse_cons]
  rw [ofDigits_append_zero]
  have h_len : (Nat.digits 2 (m / 2)).length = (Nat.digits 2 (m / 2)).reverse.length := by
    rw [List.length_reverse]
  have h_lt : Nat.ofDigits 2 (Nat.digits 2 (m / 2)).reverse < 2 ^ (Nat.digits 2 (m / 2)).reverse.length := by
    apply Nat.ofDigits_lt_base_pow_length (by decide)
    intro x hx
    rw [List.mem_reverse] at hx
    exact Nat.digits_lt_base (by decide) hx
  change ofDigits 2 (digits 2 (m / 2)).reverse < 2 ^ (digits 2 (m / 2)).length
  rw [← h_len] at h_lt
  exact h_lt

theorem a_pos (k : ℕ) (hk : k ≠ 0) : a k ≠ 0 := by
  cases k with
  | zero => contradiction
  | succ k' =>
    cases k' with
    | zero =>
      rw [a]
      decide
    | succ k'' =>
      rw [a]
      omega

theorem a_parity (n : ℕ) : a n % 2 = n % 2 := by
  induction' n using a.induct with n ih1 ih2
  · rw [a]
  · rw [a]
  · rw [a]
    have h_pos : a (n + 1) ≠ 0 := a_pos (n + 1) (by omega)
    have h_odd := A030101_odd (a (n + 1)) h_pos
    have h_xor : ((a n).xor (A030101 (a (n + 1)))) % 2 = ((a n) + A030101 (a (n + 1))) % 2 := Nat.xor_mod_two_eq
    omega

theorem a_lt_two_pow_div_two (n : ℕ) : a n < 2 ^ (n / 2 + 1) := by
  induction' n using a.induct with n ih1 ih2
  · rw [a]
    decide
  · rw [a]
    decide
  · rw [a]
    by_cases hn : n % 2 = 0
    · have h1 : (n + 1) / 2 = n / 2 := by omega
      have h2 : (n + 2) / 2 = n / 2 + 1 := by omega
      rw [h1] at ih2
      rw [h2]
      have h2_len : (Nat.digits 2 (a (n + 1))).length ≤ n / 2 + 1 := by
        rw [Nat.digits_length_le_iff (by decide)]
        exact ih2
      have h2_pow : 2 ^ (Nat.digits 2 (a (n + 1))).length ≤ 2 ^ (n / 2 + 1) := by
        gcongr
        decide
      have h2' : A030101 (a (n + 1)) < 2 ^ (n / 2 + 1) := lt_of_lt_of_le (A030101_lt (a (n + 1))) h2_pow
      have h_xor : (a n).xor (A030101 (a (n + 1))) < 2 ^ (n / 2 + 1) := Nat.bitwise_lt_two_pow ih1 h2'
      omega
    · have hn1 : n % 2 = 1 := by omega
      have h1 : (n + 1) / 2 = n / 2 + 1 := by omega
      have h2 : (n + 2) / 2 = n / 2 + 1 := by omega
      rw [h1] at ih2
      rw [h2]
      have h_pos : a (n + 1) ≠ 0 := a_pos (n + 1) (by omega)
      have h_mod : a (n + 1) % 2 = 0 := by
        rw [a_parity]
        omega
      have h2_even := A030101_lt_even (a (n + 1)) h_pos h_mod
      have h2_len : (Nat.digits 2 (a (n + 1))).length ≤ n / 2 + 2 := by
        rw [Nat.digits_length_le_iff (by decide)]
        exact ih2
      have h2_pow : 2 ^ ((Nat.digits 2 (a (n + 1))).length - 1) ≤ 2 ^ (n / 2 + 1) := by
        gcongr
        · decide
        · omega
      have h2' : A030101 (a (n + 1)) < 2 ^ (n / 2 + 1) := lt_of_lt_of_le h2_even h2_pow
      have h_xor : (a n).xor (A030101 (a (n + 1))) < 2 ^ (n / 2 + 1) := Nat.bitwise_lt_two_pow ih1 h2'
      omega
