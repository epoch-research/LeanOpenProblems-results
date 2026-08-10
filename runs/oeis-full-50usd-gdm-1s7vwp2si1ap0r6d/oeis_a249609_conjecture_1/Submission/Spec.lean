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

def my_bits_aux (fuel : ℕ) (n : ℕ) : List Bool :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    if n = 0 then []
    else decide (n % 2 = 1) :: my_bits_aux fuel' (n / 2)

theorem bits_decomp (n : ℕ) (hn : n ≠ 0) : n.bits = decide (n % 2 = 1) :: (n / 2).bits := by
  by_cases h : n % 2 = 0
  · have h2 : n = 2 * (n / 2) := by omega
    have hn2 : n / 2 ≠ 0 := by omega
    have hdiv : 2 * (n / 2) / 2 = n / 2 := by omega
    have hmod : decide (2 * (n / 2) % 2 = 1) = false := by
      rw [decide_eq_false_iff_not]
      omega
    rw [h2]
    rw [bit0_bits (n / 2) hn2]
    rw [hdiv, hmod]
  · have h : n % 2 = 1 := by omega
    have h2 : n = 2 * (n / 2) + 1 := by omega
    have hdiv : (2 * (n / 2) + 1) / 2 = n / 2 := by omega
    have hmod : decide ((2 * (n / 2) + 1) % 2 = 1) = true := by
      rw [decide_eq_true_iff]
      omega
    rw [h2]
    rw [bit1_bits (n / 2)]
    rw [hdiv, hmod]

theorem my_bits_aux_eq (fuel : ℕ) : ∀ n, n < 2^fuel → my_bits_aux fuel n = n.bits := by
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    rw [this]
    rw [zero_bits]
    rfl
  | succ fuel' ih =>
    intro n hn
    unfold my_bits_aux
    by_cases hn0 : n = 0
    · rw [hn0]
      rw [zero_bits]
      rfl
    · simp [hn0]
      have h_div : n / 2 < 2^fuel' := by
        have hpow : 2^(fuel' + 1) = 2^fuel' * 2 := by rfl
        omega
      rw [ih (n / 2) h_div]
      exact (bits_decomp n hn0).symm

theorem lt_two_pow (n : ℕ) : n < 2^n := by
  induction n with
  | zero => decide
  | succ n' ih =>
    have : 2^(n' + 1) = 2^n' + 2^n' := by
      have : 2^(n' + 1) = 2^n' * 2 := rfl
      omega
    omega

theorem my_bits_eq (n : ℕ) : my_bits_aux n n = n.bits := by
  exact my_bits_aux_eq n n (lt_two_pow n)

-- Define fast versions
def is_evil_fast (k : ℕ) : Bool :=
  decide ((my_bits_aux k k).count true % 2 = 0)

def find_min_m_fast (n : ℕ) (m : ℕ) (steps : ℕ) : ℕ :=
  match steps with
  | 0 => 0
  | steps' + 1 =>
    if m > n then 0
    else if is_evil_fast (n.choose m) then m
    else find_min_m_fast n (m + 1) steps'

theorem is_evil_fast_eq_is_evil (k : ℕ) : is_evil_fast k = decide (k.bits.count true % 2 = 0) := by
  unfold is_evil_fast
  rw [my_bits_eq]

theorem find_min_m_fast_eq_a_find_min_m (n : ℕ) (m : ℕ) (steps : ℕ) (h_steps : steps ≥ n + 1 - m) :
    find_min_m_fast n m steps = a.find_min_m n (fun k => decide (k.bits.count true % 2 = 0)) m := by
  induction steps generalizing m with
  | zero =>
    have : n + 1 - m = 0 := by omega
    have h_gt : m > n := by omega
    unfold find_min_m_fast
    rw [a.find_min_m.eq_1]
    simp [h_gt]
  | succ steps' ih =>
    unfold find_min_m_fast
    rw [a.find_min_m.eq_1]
    by_cases h_gt : m > n
    · simp [h_gt]
    · simp [h_gt]
      simp only [is_evil_fast_eq_is_evil]
      by_cases h_evil : (n.choose m).bits.count true % 2 = 0
      · simp [h_evil]
      · simp [h_evil]
        have h_steps' : steps' ≥ n + 1 - (m + 1) := by omega
        exact ih (m + 1) h_steps'

theorem a_eq_fast (n : ℕ) : a n = find_min_m_fast n 1 (n + 1) := by
  unfold a
  rw [find_min_m_fast_eq_a_find_min_m]
  omega

theorem a_eq_zero_iff_lt_nine (n : ℕ) (hn : n < 9) :
    a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  interval_cases n
  · rw [a_eq_fast 0]; decide
  · rw [a_eq_fast 1]; decide
  · rw [a_eq_fast 2]; decide
  · rw [a_eq_fast 3]; decide
  · rw [a_eq_fast 4]; decide
  · rw [a_eq_fast 5]; decide
  · rw [a_eq_fast 6]; decide
  · rw [a_eq_fast 7]; decide
  · rw [a_eq_fast 8]; decide

theorem a_eq_one_of_evil (n : ℕ) (hn : n ≥ 1) (he : n.bits.count true % 2 = 0) : a n = 1 := by
  rw [a_eq_fast]
  unfold find_min_m_fast
  have h1 : ¬(1 > n) := by omega
  simp only [h1, ↓reduceIte]
  unfold is_evil_fast
  rw [my_bits_eq]
  rw [choose_one_right]
  have h_dec : decide (n.bits.count true % 2 = 0) = true := by
    rw [decide_eq_true_iff]
    exact he
  rw [h_dec]
  rfl


theorem find_min_m_fast_ne_zero_of_exists (n : ℕ) (k : ℕ) (m : ℕ) (steps : ℕ)
    (hm1 : m ≥ 1) (hk2 : k ≤ n) (he : (n.choose k).bits.count true % 2 = 0) :
    k ≥ m → steps ≥ n + 1 - m → find_min_m_fast n m steps ≠ 0 := by
  induction steps generalizing m with
  | zero =>
    intro _ h_steps
    have : n + 1 - m = 0 := by omega
    omega
  | succ steps' ih =>
    intro hk1 h_steps
    unfold find_min_m_fast
    by_cases h_gt : m > n
    · omega
    · simp only [h_gt, ↓reduceIte]
      by_cases h_evil : is_evil_fast (n.choose m)
      · simp only [h_evil, ↓reduceIte]
        omega
      · simp only [h_evil, ↓reduceIte]
        by_cases h_eq : m = k
        · rw [h_eq] at h_evil
          rw [is_evil_fast_eq_is_evil] at h_evil
          have h_dec : decide ((n.choose k).bits.count true % 2 = 0) = true := by
            rw [decide_eq_true_iff]
            exact he
          rw [h_dec] at h_evil
          contradiction
        · have hk1' : k ≥ m + 1 := by omega
          have h_steps' : steps' ≥ n + 1 - (m + 1) := by omega
          have hm1' : m + 1 ≥ 1 := by omega
          exact ih (m + 1) hm1' hk1' h_steps'

theorem a_ne_zero_of_exists_evil_choose (n : ℕ) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n)
    (he : (n.choose k).bits.count true % 2 = 0) : a n ≠ 0 := by
  rw [a_eq_fast]
  have h_steps : n + 1 ≥ n + 1 - 1 := by omega
  have h_ne := find_min_m_fast_ne_zero_of_exists n k 1 (n + 1) (by omega) hk2 he (by omega) h_steps
  exact h_ne

theorem a_ne_zero_of_ge_nine (n : ℕ) (hn : n ≥ 9) : a n ≠ 0 := by
  by_cases h_lt : n < 100
  · interval_cases n
    · rw [a_eq_fast 9]; decide
    · rw [a_eq_fast 10]; decide
    · rw [a_eq_fast 11]; decide
    · rw [a_eq_fast 12]; decide
    · rw [a_eq_fast 13]; decide
    · rw [a_eq_fast 14]; decide
    · rw [a_eq_fast 15]; decide
    · rw [a_eq_fast 16]; decide
    · rw [a_eq_fast 17]; decide
    · rw [a_eq_fast 18]; decide
    · rw [a_eq_fast 19]; decide
    · rw [a_eq_fast 20]; decide
    · rw [a_eq_fast 21]; decide
    · rw [a_eq_fast 22]; decide
    · rw [a_eq_fast 23]; decide
    · rw [a_eq_fast 24]; decide
    · rw [a_eq_fast 25]; decide
    · rw [a_eq_fast 26]; decide
    · rw [a_eq_fast 27]; decide
    · rw [a_eq_fast 28]; decide
    · rw [a_eq_fast 29]; decide
    · rw [a_eq_fast 30]; decide
    · rw [a_eq_fast 31]; decide
    · rw [a_eq_fast 32]; decide
    · rw [a_eq_fast 33]; decide
    · rw [a_eq_fast 34]; decide
    · rw [a_eq_fast 35]; decide
    · rw [a_eq_fast 36]; decide
    · rw [a_eq_fast 37]; decide
    · rw [a_eq_fast 38]; decide
    · rw [a_eq_fast 39]; decide
    · rw [a_eq_fast 40]; decide
    · rw [a_eq_fast 41]; decide
    · rw [a_eq_fast 42]; decide
    · rw [a_eq_fast 43]; decide
    · rw [a_eq_fast 44]; decide
    · rw [a_eq_fast 45]; decide
    · rw [a_eq_fast 46]; decide
    · rw [a_eq_fast 47]; decide
    · rw [a_eq_fast 48]; decide
    · rw [a_eq_fast 49]; decide
    · rw [a_eq_fast 50]; decide
    · rw [a_eq_fast 51]; decide
    · rw [a_eq_fast 52]; decide
    · rw [a_eq_fast 53]; decide
    · rw [a_eq_fast 54]; decide
    · rw [a_eq_fast 55]; decide
    · rw [a_eq_fast 56]; decide
    · rw [a_eq_fast 57]; decide
    · rw [a_eq_fast 58]; decide
    · rw [a_eq_fast 59]; decide
    · rw [a_eq_fast 60]; decide
    · rw [a_eq_fast 61]; decide
    · rw [a_eq_fast 62]; decide
    · rw [a_eq_fast 63]; decide
    · rw [a_eq_fast 64]; decide
    · rw [a_eq_fast 65]; decide
    · rw [a_eq_fast 66]; decide
    · rw [a_eq_fast 67]; decide
    · rw [a_eq_fast 68]; decide
    · rw [a_eq_fast 69]; decide
    · rw [a_eq_fast 70]; decide
    · rw [a_eq_fast 71]; decide
    · rw [a_eq_fast 72]; decide
    · rw [a_eq_fast 73]; decide
    · rw [a_eq_fast 74]; decide
    · rw [a_eq_fast 75]; decide
    · rw [a_eq_fast 76]; decide
    · rw [a_eq_fast 77]; decide
    · rw [a_eq_fast 78]; decide
    · rw [a_eq_fast 79]; decide
    · rw [a_eq_fast 80]; decide
    · rw [a_eq_fast 81]; decide
    · rw [a_eq_fast 82]; decide
    · rw [a_eq_fast 83]; decide
    · rw [a_eq_fast 84]; decide
    · rw [a_eq_fast 85]; decide
    · rw [a_eq_fast 86]; decide
    · rw [a_eq_fast 87]; decide
    · rw [a_eq_fast 88]; decide
    · rw [a_eq_fast 89]; decide
    · rw [a_eq_fast 90]; decide
    · rw [a_eq_fast 91]; decide
    · rw [a_eq_fast 92]; decide
    · rw [a_eq_fast 93]; decide
    · rw [a_eq_fast 94]; decide
    · rw [a_eq_fast 95]; decide
    · rw [a_eq_fast 96]; decide
    · rw [a_eq_fast 97]; decide
    · rw [a_eq_fast 98]; decide
    · rw [a_eq_fast 99]; decide
  · sorry

/--
Conjecture: there are only five n: 0,1,2,7,8, for which all entries of the n-th Pascal row (A007318) are odious (A000069).

The condition that all entries of the n-th Pascal row are odious is equivalent to $a(n)=0$.
An odious number is one whose population count is odd.
-/
theorem oeis_a249609_conjecture_1 (n : ℕ) : a n = 0 ↔ n ∈ ({0, 1, 2, 7, 8} : Finset ℕ) := by
  by_cases hn : n < 9
  · exact a_eq_zero_iff_lt_nine n hn
  · have h_ge : n ≥ 9 := by omega
    have h_a : a n ≠ 0 := a_ne_zero_of_ge_nine n h_ge
    have h_not_mem : n ∉ ({0, 1, 2, 7, 8} : Finset ℕ) := by
      intro h_mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
      rcases h_mem with h | h | h | h | h
      · omega
      · omega
      · omega
      · omega
      · omega
    simp [h_a, h_not_mem]
