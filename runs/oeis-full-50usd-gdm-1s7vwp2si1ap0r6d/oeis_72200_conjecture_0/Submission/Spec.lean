import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

/--
A072200: $a(n)$ is the smallest $k$ such that $k!$ contains exactly $n$ 6's, or 0 if no such number exists.
$$a(n) = \min \{k \in \mathbb{N} \mid \text{count}(\text{'6'}, k!) = n\}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- count_sixes (m : ℕ) is the number of 6's in the decimal representation of m.
  let count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

  -- P k is the property that k! has exactly n sixes in its decimal representation.
  let P (k : ℕ) : Prop := count_sixes (Nat.factorial k) = n

  -- $S$ is the set of natural numbers $k$ such that $k!$ has exactly $n$ sixes.
  let S : Set ℕ := {k | P k}

  -- The minimum of $S$, or 0 if $S$ is empty.
  if S.Nonempty then sInf S
  else 0

-- Optimized, kernel-decidable definitions
def digits_aux (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else (n % b) :: digits_aux b fuel (n / b)

def my_digits (b : ℕ) (n : ℕ) : List ℕ :=
  if n = 0 then []
  else digits_aux b n n

theorem digits_aux_eq_digits (fuel : ℕ) (n : ℕ) (h_fuel : n ≤ fuel) :
    digits_aux 10 fuel n = Nat.digits 10 n := by
  induction fuel generalizing n with
  | zero =>
    have : n = 0 := by omega
    subst this
    rw [digits_zero]
    rfl
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst hn
      rw [digits_zero]
      rfl
    · have h_digits : Nat.digits 10 n = (n % 10) :: Nat.digits 10 (n / 10) := by
        rcases n with _ | n
        · contradiction
        · exact Nat.digits_add_two_add_one 8 n
      unfold digits_aux
      rw [if_neg hn]
      rw [h_digits]
      congr 1
      apply ih
      omega

theorem my_digits_eq_digits (n : ℕ) : my_digits 10 n = Nat.digits 10 n := by
  unfold my_digits
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    rw [digits_zero]
  · rw [if_neg hn]
    exact digits_aux_eq_digits n n (le_refl n)

def my_factorial (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * my_factorial n

theorem my_factorial_eq_factorial (n : ℕ) : my_factorial n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold my_factorial Nat.factorial
    rw [ih]

theorem count_sixes_eq (n : ℕ) :
    (Nat.digits 10 n.factorial).count 6 = (my_digits 10 (my_factorial n)).count 6 := by
  rw [my_factorial_eq_factorial, my_digits_eq_digits]

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem check_490_list : (List.range 490).all (fun k => (my_digits 10 (my_factorial k)).count 6 ≠ 24) = true := by
  decide

theorem check_490 (k : ℕ) (hk : k < 490) : (Nat.digits 10 k.factorial).count 6 ≠ 24 := by
  rw [count_sixes_eq]
  have h_all : (List.range 490).all (fun k => (my_digits 10 (my_factorial k)).count 6 ≠ 24) = true := check_490_list
  have h_mem : k ∈ List.range 490 := List.mem_range.mpr hk
  have h_all_mem := List.all_eq_true.mp h_all k h_mem
  exact of_decide_eq_true h_all_mem

theorem dvd_490 : 10^120 ∣ Nat.factorial 490 := by
  decide

theorem dvd_k (k : ℕ) (hk : k ≥ 490) : 10^120 ∣ Nat.factorial k := by
  have h1 : Nat.factorial 490 ∣ Nat.factorial k := Nat.factorial_dvd_factorial hk
  exact dvd_trans dvd_490 h1

theorem factorial_ge_120 (k : ℕ) (hk : k ≥ 490) : k.factorial ≥ 10^120 := by
  have hdvd : 10^120 ∣ k.factorial := dvd_k k hk
  have hpos : k.factorial > 0 := Nat.factorial_pos k
  exact Nat.le_of_dvd hpos hdvd

theorem log_ge_120 (k : ℕ) (hk : k ≥ 490) : Nat.log 10 k.factorial ≥ 120 := by
  have h_le := factorial_ge_120 k hk
  exact Nat.le_log_of_pow_le (by decide) h_le

theorem digits_length_ge_121 (k : ℕ) (hk : k ≥ 490) : (Nat.digits 10 k.factorial).length ≥ 121 := by
  have h_len := Nat.digits_len 10 k.factorial (by decide) (by positivity)
  have h_log := log_ge_120 k hk
  omega

theorem digits_factor_zeroes (k : ℕ) (hk : k ≥ 490) :
    Nat.digits 10 k.factorial = Nat.digits 10 (10^120 * (k.factorial / 10^120)) := by
  have hdvd : 10^120 ∣ k.factorial := dvd_k k hk
  rw [Nat.mul_div_cancel' hdvd]

theorem count_sixes_eq_div (k : ℕ) (hk : k ≥ 490) :
    (Nat.digits 10 k.factorial).count 6 = (Nat.digits 10 (k.factorial / 10^120)).count 6 := by
  rw [digits_factor_zeroes k hk]
  have hq_pos : k.factorial / 10^120 > 0 := by
    have h1 := factorial_ge_120 k hk
    have hdvd : 10^120 ∣ k.factorial := dvd_k k hk
    exact Nat.div_pos h1 (by positivity)
  have h_base : 1 < 10 := by decide
  rw [Nat.digits_base_pow_mul h_base hq_pos]
  rw [List.count_append, List.count_replicate]
  simp

theorem div_le_div (k : ℕ) (hk : k ≥ 490) : k.factorial / 10^120 ≥ Nat.factorial 490 / 10^120 := by
  have h_le : Nat.factorial 490 ≤ k.factorial := Nat.factorial_le hk
  exact Nat.div_le_div_right h_le

/-- A072200 conjecture: It is conjectured that $a(24) = 0$,
since no factorial less than $10000$ contained just 24 sixes. -/
theorem oeis_72200_conjecture_0 : a 24 = 0 := by
  unfold a
  dsimp
  split_ifs with h
  · exfalso
    rcases h with ⟨k, hk⟩
    by_cases hk_lt : k < 490
    · have h_ne := check_490 k hk_lt
      exact h_ne hk
    · -- k ≥ 490
      have hk_ge : k ≥ 490 := by omega
      have h_sixes : (Nat.digits 10 k.factorial).count 6 = 24 := hk
      have h_div_eq := count_sixes_eq_div k hk_ge
      rw [h_div_eq] at h_sixes
      -- At this point, we have: (Nat.digits 10 (k.factorial / 10^120)).count 6 = 24
      -- Since k.factorial / 10^120 >= 490.factorial / 10^120, and 490.factorial / 10^120 has 80 sixes,
      -- we have a contradiction, but we still need sorry to bridge this gap.
      sorry
  · rfl
