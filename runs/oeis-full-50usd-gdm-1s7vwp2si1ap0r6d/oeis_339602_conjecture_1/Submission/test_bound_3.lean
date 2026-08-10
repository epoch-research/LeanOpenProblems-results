import FormalConjectures.Util.ProblemImports

open Nat

def A030101 (n : ℕ) : ℕ :=
  Nat.ofDigits 2 (List.reverse (Nat.digits 2 n))

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

theorem a_lt_large_even (n : ℕ) (hn : n % 2 = 0) : a n < 2^100 := by
  induction' n using Nat.strong_induction_on with n ih
  rcases n with _ | _ | n
  · rw [a]; decide
  · contradiction
  · rw [a]
    -- Since n+2 is even, we have (n+2)%2 = 0, so n is even.
    have hn_even : n % 2 = 0 := by omega
    -- We want to show a (n+2) < 2^100.
    -- We have a n < 2^100 by ih since n < n+2 and n is even.
    have ih_n : a n < 2^100 := ih n (by omega) hn_even
    -- For a (n+1), n+1 is odd.
    -- We have by a_lt_two_pow_div_two: a (n+1) < 2 ^ ((n+1)/2 + 1).
    -- Since n is even, let n = 2k.
    -- Then n+1 = 2k+1, and (n+1)/2 = k = n/2.
    -- So a (n+1) < 2 ^ (n/2 + 1).
    -- We also have A030101 (a (n+1)) < 2 ^ ((Nat.digits 2 (a (n+1))).length).
    -- Since a (n+1) < 2 ^ (n/2 + 1), we have (Nat.digits 2 (a (n+1))).length ≤ n/2 + 1.
    -- So A030101 (a (n+1)) < 2 ^ (n/2 + 1).
    -- We can analyze based on whether n/2 + 1 ≤ 100.
    by_cases h_bound : n/2 + 1 ≤ 100
    · -- In this case, both a n and A030101 (a (n+1)) are < 2^100.
      -- Wait, a n < 2^100 is always true by ih.
      -- What about A030101 (a (n+1))?
      -- We have A030101 (a (n+1)) < 2 ^ (n/2 + 1) ≤ 2^100.
      -- So their XOR is < 2^100.
      -- So a (n+2) = XOR + 1 < 2^100 + 1, so a (n+2) ≤ 2^100.
      -- But we want strict inequality a (n+2) < 2^100!
      -- Since n+2 is even, a (n+2) % 2 = 0 by a_parity.
      -- Since 2^100 % 2 = 0, and a (n+2) ≤ 2^100, we cannot have a (n+2) = 2^100?
      -- Wait! If a (n+2) ≤ 2^100, could it be 2^100?
      -- Let's check: if (a n).xor (A030101 (a (n+1))) < 2^100,
      -- then (a n).xor (A030101 (a (n+1))) ≤ 2^100 - 1.
      -- So a (n+2) = XOR + 1 ≤ 2^100.
      -- If a (n+2) = 2^100, then XOR = 2^100 - 1.
      -- But XOR < 2^100, and if the two terms in XOR are both < 2^(n/2 + 1) and n/2 + 1 ≤ 100,
      -- then we can get a stronger bound.
      -- Specifically, if n/2 + 1 < 100, then both terms are < 2^99, so XOR < 2^99, so a (n+2) < 2^99 + 1 ≤ 2^100.
      -- What if n/2 + 1 = 100? Then n = 198.
      -- In this case, we have:
      -- a n < 2^100 by ih (since n = 198 is even).
      -- But actually, we can show a 198 < 2^99!
      -- Let's prove a stronger version of the induction, or just prove:
      -- A030101 (a (n+1)) < 2^100.
      -- Actually, since n+1 is odd, a (n+1) % 2 = 1.
      -- Wait, is a (n+1) % 2 = 1? Yes, by a_parity.
      -- So A030101 (a (n+1)) is odd? No, A030101 of an odd number has LSB determined by the MSB of the number, which is 1, so it is odd.
      -- More importantly, if we can show a n < 2^100 and A030101 (a (n+1)) < 2^100,
      -- then their XOR is < 2^100.
      -- Is this always true? Yes, because if X < 2^100 and Y < 2^100, then X.xor Y < 2^100.
      -- So XOR + 1 ≤ 2^100.
      -- Since n+2 is even, a (n+2) % 2 = 0.
      -- But 2^100 is even. So a (n+2) could potentially be 2^100?
      -- Yes, if XOR + 1 = 2^100, then XOR = 2^100 - 1.
      -- Since XOR < 2^100, is it possible that XOR = 2^100 - 1?
      -- Yes, if X and Y are bitwise complements under 100 bits.
      -- But wait! If X < 2^99 and Y < 2^99, then X.xor Y < 2^99 < 2^100 - 1.
      -- If n/2 + 1 < 100, then both a n < 2^100 (actually much smaller) and A030101 (a (n+1)) < 2^(n/2 + 1) ≤ 2^99.
      -- So indeed, if n/2 + 1 ≤ 99, then XOR < 2^99, so a (n+2) < 2^100.
      -- What if n/2 + 1 ≥ 100?
      -- Then n ≥ 198.
      -- But wait! If n ≥ 198, we can write n = m + 2 where m is even.
      -- Since m < n and m is even, we can use ih on m!
      -- So we have a m < 2^100.
      -- Actually, we can prove the bound a n < 2^100 for all even n by showing:
      -- For n < 198, a n < 2^99 < 2^100.
      -- For n ≥ 198, both a n and A030101 (a (n+1)) are much smaller!
      -- Indeed, if n ≥ 198, is A030101 (a (n+1)) < 2^100?
      -- Yes, because a (n+1) < 2^100 + 1 (since n+1 is odd, and we can prove a_lt_large).
      -- Let's prove a_lt_large and a_lt_large_even simultaneously!
      sorry
    · sorry

