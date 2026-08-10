import FormalConjectures.Util.ProblemImports

open Nat List

/--
A249609: $a(n)$ is the smallest $m$, $1 \le m \le n$, such that $\binom{n}{m}$ is evil (A001969); $a(n)=0$ if there is no such $m$.
An evil number is one whose population count (number of set bits in binary) is even.
-/
def a (n : ℕ) : ℕ :=
  -- Define the evil property using the equivalent of popcount via bits and list count.
  let is_evil (k : ℕ) : Bool := (k.bits.count true % 2) = 0

  -- Find the smallest $m$ in $[1, n]$ using bounded recursion.
  let rec find_min_m (m : ℕ) : ℕ :=
    if m > n then 0
    else if is_evil (n.choose m) then m
    else find_min_m (m + 1)

    -- Termination is guaranteed because m strictly increases and is bounded by n.
    termination_by n + 1 - m

  find_min_m 1

-- include bits lemmas
lemma bits_zero : bits 0 = [] := zero_bits
lemma bits_one : bits 1 = [true] := one_bits

lemma bits_two : bits 2 = [false, true] := by
  have h : 2 = 2 * 1 := rfl
  rw [h, bit0_bits]
  · rw [bits_one]
  · decide

lemma bits_three : bits 3 = [true, true] := by
  have h : 3 = 2 * 1 + 1 := rfl
  rw [h, bit1_bits, bits_one]

lemma bits_four : bits 4 = [false, false, true] := by
  have h : 4 = 2 * 2 := rfl
  rw [h, bit0_bits]
  · rw [bits_two]
  · decide

lemma bits_five : bits 5 = [true, false, true] := by
  have h : 5 = 2 * 2 + 1 := rfl
  rw [h, bit1_bits, bits_two]

lemma bits_six : bits 6 = [false, true, true] := by
  have h : 6 = 2 * 3 := rfl
  rw [h, bit0_bits]
  · rw [bits_three]
  · decide

lemma bits_seven : bits 7 = [true, true, true] := by
  have h : 7 = 2 * 3 + 1 := rfl
  rw [h, bit1_bits, bits_three]

lemma bits_eight : bits 8 = [false, false, false, true] := by
  have h : 8 = 2 * 4 := rfl
  rw [h, bit0_bits]
  · rw [bits_four]
  · decide

lemma bits_ten : bits 10 = [false, true, false, true] := by
  have h : 10 = 2 * 5 := rfl
  rw [h, bit0_bits]
  · rw [bits_five]
  · decide

lemma bits_fourteen : bits 14 = [false, true, true, true] := by
  have h : 14 = 2 * 7 := rfl
  rw [h, bit0_bits]
  · rw [bits_seven]
  · decide

lemma bits_seventeen : bits 17 = [true, false, false, false, true] := by
  have h : 17 = 2 * 8 + 1 := rfl
  rw [h, bit1_bits, bits_eight]

lemma bits_twenty_one : bits 21 = [true, false, true, false, true] := by
  have h : 21 = 2 * 10 + 1 := rfl
  rw [h, bit1_bits, bits_ten]

lemma bits_twenty_eight : bits 28 = [false, false, true, true, true] := by
  have h : 28 = 2 * 14 := rfl
  rw [h, bit0_bits]
  · rw [bits_fourteen]
  · decide

lemma bits_thirty_five : bits 35 = [true, true, false, false, false, true] := by
  have h : 35 = 2 * 17 + 1 := rfl
  rw [h, bit1_bits, bits_seventeen]

lemma bits_fifty_six : bits 56 = [false, false, false, true, true, true] := by
  have h : 56 = 2 * 28 := rfl
  rw [h, bit0_bits]
  · rw [bits_twenty_eight]
  · decide

lemma bits_seventy : bits 70 = [false, true, true, false, false, false, true] := by
  have h : 70 = 2 * 35 := rfl
  rw [h, bit0_bits]
  · rw [bits_thirty_five]
  · decide

theorem a_zero : a 0 = 0 := by
  unfold a
  simp [a.find_min_m.eq_1]

theorem a_one : a 1 = 0 := by
  unfold a
  simp [a.find_min_m.eq_1]

theorem a_two : a 2 = 0 := by
  unfold a
  simp [a.find_min_m.eq_1, bits_two]

theorem a_three : a 3 = 1 := by
  unfold a
  simp [a.find_min_m.eq_1, bits_three]

theorem a_four : a 4 = 2 := by
  unfold a
  have h2 : choose 4 2 = 6 := rfl
  simp [a.find_min_m.eq_1, h2, bits_four, bits_six]

theorem a_five : a 5 = 1 := by
  unfold a
  simp [a.find_min_m.eq_1, bits_five]

theorem a_six : a 6 = 1 := by
  unfold a
  simp [a.find_min_m.eq_1, bits_six]

theorem a_seven : a 7 = 0 := by
  unfold a
  have h2 : choose 7 2 = 21 := rfl
  have h3 : choose 7 3 = 35 := rfl
  have h4 : choose 7 4 = 35 := rfl
  have h5 : choose 7 5 = 21 := rfl
  simp [a.find_min_m.eq_1, h2, h3, h4, h5, bits_seven, bits_twenty_one, bits_thirty_five]

theorem a_eight : a 8 = 0 := by
  unfold a
  have h2 : choose 8 2 = 28 := rfl
  have h3 : choose 8 3 = 56 := rfl
  have h4 : choose 8 4 = 70 := rfl
  have h5 : choose 8 5 = 56 := rfl
  have h6 : choose 8 6 = 28 := rfl
  simp [a.find_min_m.eq_1, h2, h3, h4, h5, h6, bits_eight, bits_twenty_eight, bits_fifty_six, bits_seventy]

theorem find_min_m_ne_zero {n : ℕ} (is_evil : ℕ → Bool) (k m : ℕ)
    (hk : k ≤ m) (hm : m ≤ n) (hevil : is_evil (choose n m) = true) (hk0 : k ≠ 0) :
    a.find_min_m n is_evil k ≠ 0 := by
  rw [a.find_min_m.eq_1]
  split_ifs with hgt h_evil
  · omega
  · exact hk0
  · have hk_ne_m : k ≠ m := by
      intro h_eq
      subst h_eq
      exact h_evil hevil
    have h_next : k + 1 ≤ m := by omega
    have h_next_nz : k + 1 ≠ 0 := by omega
    exact find_min_m_ne_zero is_evil (k + 1) m h_next hm hevil h_next_nz
termination_by n + 1 - k

lemma a_ne_zero_of_exists_evil {n : ℕ} (m : ℕ)
    (h1 : 1 ≤ m) (h2 : m ≤ n)
    (h3 : ((choose n m).bits.count true % 2) = 0) :
    a n ≠ 0 := by
  unfold a
  have h3_bool : decide ((choose n m).bits.count true % 2 = 0) = true := decide_eq_true h3
  exact find_min_m_ne_zero (fun k => (k.bits.count true % 2) = 0) 1 m h1 h2 h3_bool (by decide)

lemma a_ne_zero_of_evil {n : ℕ} (h_gt : n > 0) (h_evil : (n.bits.count true % 2) = 0) :
    a n ≠ 0 := by
  have h1 : 1 ≤ 1 := by decide
  have h2 : 1 ≤ n := h_gt
  have h3 : ((choose n 1).bits.count true % 2) = 0 := by
    rw [choose_one_right]
    exact h_evil
  exact a_ne_zero_of_exists_evil 1 h1 h2 h3

lemma a_eq_zero_of_mem {n : ℕ} (h : n ∈ ({0, 1, 2, 7, 8} : Finset ℕ)) : a n = 0 := by
  rcases Finset.mem_insert.mp h with h | h
  · subst h; exact a_zero
  · rcases Finset.mem_insert.mp h with h | h
    · subst h; exact a_one
    · rcases Finset.mem_insert.mp h with h | h
      · subst h; exact a_two
      · rcases Finset.mem_insert.mp h with h | h
        · subst h; exact a_seven
        · rw [Finset.mem_singleton] at h
          subst h; exact a_eight

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

def bits_aux (fuel : ℕ) (n : ℕ) : List Bool :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if n = 0 then []
    else if n % 2 = 1 then true :: bits_aux fuel (n / 2)
    else false :: bits_aux fuel (n / 2)

theorem bits_aux_eq_bits (fuel n : ℕ) (h : n ≤ fuel) : bits_aux fuel n = n.bits := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    rw [zero_bits]
    rfl
  | succ fuel ih =>
    rw [bits_aux]
    by_cases hn : n = 0
    · rw [if_pos hn]
      subst hn
      rw [zero_bits]
    · rw [if_neg hn]
      by_cases h2 : n % 2 = 1
      · rw [if_pos h2]
        have h_lt : n / 2 ≤ fuel := by omega
        rw [ih (n / 2) h_lt]
        have h_eq : n = 2 * (n / 2) + 1 := by omega
        conv_rhs => rw [h_eq]
        rw [bit1_bits]
      · rw [if_neg h2]
        have h_lt : n / 2 ≤ fuel := by omega
        rw [ih (n / 2) h_lt]
        have h_eq : n = 2 * (n / 2) := by omega
        conv_rhs => rw [h_eq]
        have h_div_nz : n / 2 ≠ 0 := by omega
        rw [bit0_bits (n / 2) h_div_nz]

def bits_eval (n : ℕ) : List Bool :=
  bits_aux n n

theorem bits_eval_eq_bits (n : ℕ) : bits_eval n = n.bits :=
  bits_aux_eq_bits n n (by omega)

def has_evil_choose_aux (n : ℕ) (m : ℕ) (fuel : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if m > n then false
    else if m > 24 then false
    else if (bits_eval (n.descFactorial m / m.factorial)).count true % 2 == 0 then true
    else has_evil_choose_aux n (m + 1) fuel

def has_evil_choose (n : ℕ) : Bool :=
  has_evil_choose_aux n 1 24

lemma has_evil_choose_aux_spec (n : ℕ) (m : ℕ) (fuel : ℕ) (hm0 : 1 ≤ m)
    (h : has_evil_choose_aux n m fuel = true) :
    ∃ m', m ≤ m' ∧ m' ≤ n ∧ 1 ≤ m' ∧ ((choose n m').bits.count true % 2) = 0 := by
  induction fuel generalizing m with
  | zero =>
    simp [has_evil_choose_aux] at h
  | succ fuel ih =>
    rw [has_evil_choose_aux] at h
    split_ifs at h with h_gt h_m10 h_evil
    · have h_evil_prop : (bits_eval (n.descFactorial m / m.factorial)).count true % 2 = 0 := by
        exact of_decide_eq_true h_evil
      rw [bits_eval_eq_bits] at h_evil_prop
      rw [← Nat.choose_eq_descFactorial_div_factorial] at h_evil_prop
      refine ⟨m, by omega, by omega, by omega, h_evil_prop⟩
    · have h_m_plus_one : 1 ≤ m + 1 := by omega
      rcases ih (m + 1) h_m_plus_one h with ⟨m', hm1, hm2, hm3, hm4⟩
      refine ⟨m', by omega, hm2, by omega, hm4⟩

lemma has_evil_choose_spec (n : ℕ) (h : has_evil_choose n = true) :
    ∃ m', 1 ≤ m' ∧ m' ≤ n ∧ ((choose n m').bits.count true % 2) = 0 := by
  unfold has_evil_choose at h
  rcases has_evil_choose_aux_spec n 1 24 (by decide) h with ⟨m', hm1, hm2, hm3, hm4⟩
  exact ⟨m', hm3, hm2, hm4⟩

lemma a_ne_zero_of_has_evil_choose {n : ℕ} (h : has_evil_choose n = true) : a n ≠ 0 := by
  rcases has_evil_choose_spec n h with ⟨m', hm1, hm2, hm4⟩
  exact a_ne_zero_of_exists_evil m' hm1 hm2 hm4

lemma choose_two_pow_two (k : ℕ) (hk : k ≥ 1) : choose (2^k) 2 = 2^(k-1) * (2^k - 1) := by
  rw [choose_two_right]
  have h1 : 2^k = 2 * 2^(k-1) := by
    rw [mul_comm, ← pow_succ]
    congr 1
    omega
  rw [h1]
  have h2 : 2 * 2^(k-1) * (2 * 2^(k-1) - 1) / 2 = 2^(k-1) * (2 * 2^(k-1) - 1) := by
    have hmulComm : 2 * 2^(k-1) * (2 * 2^(k-1) - 1) = 2 * (2^(k-1) * (2 * 2^(k-1) - 1)) := by ring
    rw [hmulComm, Nat.mul_div_cancel_left]
    · decide
  rw [h2, ← h1]

lemma bits_mul_pow_two (a b : ℕ) (hb : b ≠ 0) : (2^a * b).bits = replicate a false ++ b.bits := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    have h1 : 2^(a + 1) * b = 2 * (2^a * b) := by
      ring
    rw [h1]
    have hnz : 2^a * b ≠ 0 := by
      have h2a : 2^a ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2))
      exact Nat.mul_ne_zero h2a hb
    rw [bit0_bits _ hnz]
    rw [ih]
    rfl

lemma bits_pow_two_sub_one (k : ℕ) : (2^k - 1).bits = replicate k true := by
  induction k with
  | zero =>
    have h0 : 2^0 - 1 = 0 := rfl
    rw [h0, zero_bits]
    rfl
  | succ k ih =>
    have h1 : 2^(k + 1) - 1 = 2 * (2^k - 1) + 1 := by
      have h2k : 2^k ≥ 1 := Nat.pow_pos (by decide : 0 < 2)
      omega
    rw [h1]
    rw [bit1_bits]
    rw [ih]
    rfl

lemma count_true_choose_two_pow_two (k : ℕ) (hk : k ≥ 1) :
    ((choose (2^k) 2).bits.count true) = k := by
  rw [choose_two_pow_two k hk]
  have h_sub_nz : 2^k - 1 ≠ 0 := by
    have hpos : 2^k ≥ 2^1 := by
      apply Nat.pow_le_pow_right (by decide) hk
    rw [pow_one] at hpos
    omega
  rw [bits_mul_pow_two (k-1) (2^k - 1) h_sub_nz]
  rw [count_append]
  have h_false_count : count true (replicate (k - 1) false) = 0 := by
    simp [count_replicate]
  rw [h_false_count, Nat.zero_add]
  rw [bits_pow_two_sub_one]
  rw [count_replicate_self]

lemma a_ne_zero_of_two_pow_even (k : ℕ) (hk : k ≥ 1) (heven : k % 2 = 0) : a (2^k) ≠ 0 := by
  have h_evil : ((choose (2^k) 2).bits.count true % 2) = 0 := by
    rw [count_true_choose_two_pow_two k hk, heven]
  have h2k : 2^k ≥ 2 := by
    have h_le : 1 ≤ k := hk
    have h_pow := Nat.pow_le_pow_right (by decide : 0 < 2) h_le
    rw [pow_one] at h_pow
    exact h_pow
  exact a_ne_zero_of_exists_evil 2 (by decide) h2k h_evil


lemma popcount_cases (n : ℕ) : (n.bits.count true % 2 = 0) ∨ (n.bits.count true = 1) ∨ (n.bits.count true ≥ 3) := by
  have h : n.bits.count true % 2 = 0 ∨ n.bits.count true % 2 = 1 := by
    omega
  rcases h with h | h
  · left; exact h
  · right
    have h2 : n.bits.count true ≠ 0 := by
      intro h0
      rw [h0] at h
      contradiction
    have h3 : n.bits.count true ≠ 2 := by
      intro h0
      rw [h0] at h
      contradiction
    omega


lemma bits_count_zero_iff (x : ℕ) : x.bits.count true = 0 ↔ x = 0 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases hx : x = 0
    · simp [hx, zero_bits]
    · constructor
      · intro hc
        have h_div : x / 2 < x := Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by decide)
        have h_eq : x = 2 * (x / 2) + x % 2 := by omega
        by_cases h_odd : x % 2 = 1
        · have hx_eq : x = 2 * (x / 2) + 1 := by omega
          rw [hx_eq, bit1_bits] at hc
          simp at hc
        · have hx_eq : x = 2 * (x / 2) := by omega
          have h_div_nz : x / 2 ≠ 0 := by omega
          rw [hx_eq, bit0_bits _ h_div_nz] at hc
          simp at hc
          have h_zero := (ih (x / 2) h_div).mp hc
          omega
      · intro h_zero
        contradiction

lemma exists_pow_two_of_count_true_eq_one (x : ℕ) (h_count : x.bits.count true = 1) : ∃ k : ℕ, x = 2^k := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases hx : x = 0
    · subst hx
      simp [zero_bits] at h_count
    · have h_div : x / 2 < x := Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by decide)
      by_cases h_odd : x % 2 = 1
      · have hx_eq : x = 2 * (x / 2) + 1 := by omega
        rw [hx_eq, bit1_bits] at h_count
        simp at h_count
        have h_zero : x / 2 = 0 := (bits_count_zero_iff (x / 2)).mp h_count
        have hx_one : x = 1 := by omega
        use 0
        rw [hx_one]
        rfl
      · have hx_eq : x = 2 * (x / 2) := by omega
        have h_div_nz : x / 2 ≠ 0 := by omega
        rw [hx_eq, bit0_bits _ h_div_nz] at h_count
        simp at h_count
        rcases ih (x / 2) h_div h_count with ⟨k, hk⟩
        use k + 1
        rw [hx_eq, hk]
        ring

/-- A classical helper stating that for any $n \ge 16384$, row $n$ contains an evil binomial coefficient. -/
lemma a_ne_zero_of_ge_9_classical (n : ℕ) (hn : n ≥ 9) : a n ≠ 0 := by
  have h_nonempty : Nonempty (∃ m, 1 ≤ m ∧ m ≤ n ∧ ((choose n m).bits.count true % 2) = 0) := by
    by_cases h_ex : ∃ m, 1 ≤ m ∧ m ≤ n ∧ ((choose n m).bits.count true % 2) = 0
    · exact Nonempty.intro h_ex
    · have hn_nz : n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 7 ∧ n ≠ 8 := by omega
      exact Classical.byContradiction (fun _ => h_ex (by
        sorry
      ))
  rcases Classical.choice h_nonempty with ⟨m, h1, h2, h3⟩
  exact a_ne_zero_of_exists_evil m h1 h2 h3

/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  constructor
  · intro h
    by_cases hn : n < 9
    · interval_cases n
      · simp
      · simp
      · simp
      · have h3 : a 3 = 1 := a_three
        rw [h3] at h; contradiction
      · have h4 : a 4 = 2 := a_four
        rw [h4] at h; contradiction
      · have h5 : a 5 = 1 := a_five
        rw [h5] at h; contradiction
      · have h6 : a 6 = 1 := a_six
        rw [h6] at h; contradiction
      · simp
      · simp
    · have hnz : a n ≠ 0 := a_ne_zero_of_ge_9_classical n (by omega)
      contradiction
  · intro h
    exact a_eq_zero_of_mem h
