import FormalConjectures.Util.ProblemImports

open Nat Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

-- Formal definition of Goldbach's Conjecture
def goldbach_conjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q

-- Formal definition of Lemoine's Conjecture (or Levy's Conjecture)
def lemoine_conjecture : Prop :=
  ∀ n : ℕ, 7 ≤ n → Odd n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q

-- Formalization of the conjecture that there are infinitely many cousin primes (p, p+6)
def six_prime_gap_conjecture : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ (p + 6).Prime}

/--
The core conjecture about the sequence A219055:
a(n) > 0 for all even n > 8012 and odd n > 15727.
-/
def a219055_core_conjecture : Prop :=
  ∀ n : ℕ, (Even n ∧ 8012 < n) ∨ (Odd n ∧ 15727 < n) → A219055 n > 0

-- Helper structures and algorithms for certified interval checking
def primes_under_182 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181]

theorem primes_under_182_prime : ∀ p ∈ primes_under_182, Nat.Prime p := by
  decide

def goldbach_decide (n : ℕ) : Bool :=
  primes_under_182.any (fun p => p < n && decide (Nat.Prime (n - p)))

def check_all_goldbach_range (low : ℕ) (len : ℕ) (depth : ℕ) : Bool :=
  match depth with
  | 0 => true
  | d + 1 =>
    if len == 0 then true
    else if len == 1 then
      if 4 ≤ low && low % 2 == 0 then goldbach_decide low else true
    else
      let half := len / 2
      check_all_goldbach_range low half d && check_all_goldbach_range (low + half) (len - half) d

lemma check_all_goldbach_range_correct (depth : ℕ) :
    ∀ low len, len ≤ 2^depth → check_all_goldbach_range low len (depth + 1) = true →
    ∀ n, low ≤ n → n < low + len → 4 ≤ n → Even n → goldbach_decide n = true := by
  induction depth with
  | zero =>
    intro low len h_len h_bool n hn1 hn2 h4 heven
    simp only [pow_zero] at h_len
    rcases len with _ | _ | k
    · omega
    · have h_eq : n = low := by omega
      subst h_eq
      dsimp [check_all_goldbach_range] at h_bool
      have h_cond : 4 ≤ n ∧ n % 2 = 0 := ⟨h4, Nat.even_iff.mp heven⟩
      have h_cond_bool : (4 ≤ n && n % 2 == 0) = true := by
        simp [h_cond.1, h_cond.2]
      rw [h_cond_bool] at h_bool
      exact h_bool
    · omega
  | succ d ih =>
    intro low len h_len h_bool n hn1 hn2 h4 heven
    rcases len with _ | _ | k
    · omega
    · have h_eq : n = low := by omega
      subst h_eq
      dsimp [check_all_goldbach_range] at h_bool
      have h_cond : 4 ≤ n ∧ n % 2 = 0 := ⟨h4, Nat.even_iff.mp heven⟩
      have h_cond_bool : (4 ≤ n && n % 2 == 0) = true := by
        simp [h_cond.1, h_cond.2]
      rw [h_cond_bool] at h_bool
      exact h_bool
    · dsimp [check_all_goldbach_range] at h_bool
      rw [Bool.and_eq_true] at h_bool
      rcases h_bool with ⟨h_left, h_right⟩
      have h_half : (k + 2) / 2 ≤ 2^d := by
        have : k + 2 ≤ 2^d * 2 := by
          have h_pow : 2^(d + 1) = 2^d * 2 := by ring
          omega
        omega
      have h_half2 : (k + 2) - (k + 2) / 2 ≤ 2^d := by
        have : k + 2 ≤ 2^d * 2 := by
          have h_pow : 2^(d + 1) = 2^d * 2 := by ring
          omega
        omega
      have h_sum : (k + 2) / 2 + ((k + 2) - (k + 2) / 2) = k + 2 := by omega
      have hn_lt2 : n < low + (k + 2) / 2 + ((k + 2) - (k + 2) / 2) := by omega
      by_cases hn_half : n < low + (k + 2) / 2
      · exact ih low ((k + 2) / 2) h_half h_left n hn1 hn_half h4 heven
      · have hn_ge : low + (k + 2) / 2 ≤ n := by omega
        exact ih (low + (k + 2) / 2) ((k + 2) - (k + 2) / 2) h_half2 h_right n hn_ge hn_lt2 h4 heven

theorem goldbach_of_decide (n : ℕ) (h : goldbach_decide n = true) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  dsimp [goldbach_decide] at h
  rw [List.any_eq_true] at h
  rcases h with ⟨p, hp_mem, hp_cond⟩
  rw [Bool.and_eq_true] at hp_cond
  rcases hp_cond with ⟨hp_lt, hp_prime_dec⟩
  have h_lt : p < n := of_decide_eq_true hp_lt
  have hq_prime : (n - p).Prime := of_decide_eq_true hp_prime_dec
  have hp_prime : p.Prime := primes_under_182_prime p hp_mem
  use n - p, p
  refine ⟨hq_prime, hp_prime, ?_⟩
  omega

theorem goldbach_small_test (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 500) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  have h_cases : n < 250 ∨ (250 ≤ n ∧ n ≤ 500) := by omega
  rcases h_cases with h | h
  · exact goldbach_of_decide n (check_all_goldbach_range_correct 8 0 250 (by decide) (by decide) n (by omega) (by omega) h4 he)
  · exact goldbach_of_decide n (check_all_goldbach_range_correct 8 250 251 (by decide) (by decide) n h.1 (by omega) h4 he)
