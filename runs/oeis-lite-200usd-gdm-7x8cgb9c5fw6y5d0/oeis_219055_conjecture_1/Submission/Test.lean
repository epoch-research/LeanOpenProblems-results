import FormalConjectures.Util.ProblemImports

open Nat

def primes_under_182 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181]

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


set_option maxRecDepth 2000
theorem primes_under_182_prime : ∀ p ∈ primes_under_182, Nat.Prime p := by
  decide

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

def lemoine_decide (n : ℕ) : Bool :=
  primes_under_182.any (fun q => 2 * q < n && decide (Nat.Prime (n - 2 * q)))

def check_all_lemoine_range (low : ℕ) (len : ℕ) (depth : ℕ) : Bool :=
  match depth with
  | 0 => true
  | d + 1 =>
    if len == 0 then true
    else if len == 1 then
      if 7 ≤ low && low % 2 == 1 then lemoine_decide low else true
    else
      let half := len / 2
      check_all_lemoine_range low half d && check_all_lemoine_range (low + half) (len - half) d

lemma check_all_lemoine_range_correct (depth : ℕ) :
    ∀ low len, len ≤ 2^depth → check_all_lemoine_range low len (depth + 1) = true →
    ∀ n, low ≤ n → n < low + len → 7 ≤ n → Odd n → lemoine_decide n = true := by
  induction depth with
  | zero =>
    intro low len h_len h_bool n hn1 hn2 h7 hodd
    simp only [pow_zero] at h_len
    rcases len with _ | _ | k
    · omega
    · have h_eq : n = low := by omega
      subst h_eq
      dsimp [check_all_lemoine_range] at h_bool
      have h_cond : 7 ≤ n ∧ n % 2 = 1 := ⟨h7, Nat.odd_iff.mp hodd⟩
      have h_cond_bool : (7 ≤ n && n % 2 == 1) = true := by
        simp [h_cond.1, h_cond.2]
      rw [h_cond_bool] at h_bool
      exact h_bool
    · omega
  | succ d ih =>
    intro low len h_len h_bool n hn1 hn2 h7 hodd
    rcases len with _ | _ | k
    · omega
    · have h_eq : n = low := by omega
      subst h_eq
      dsimp [check_all_lemoine_range] at h_bool
      have h_cond : 7 ≤ n ∧ n % 2 = 1 := ⟨h7, Nat.odd_iff.mp hodd⟩
      have h_cond_bool : (7 ≤ n && n % 2 == 1) = true := by
        simp [h_cond.1, h_cond.2]
      rw [h_cond_bool] at h_bool
      exact h_bool
    · dsimp [check_all_lemoine_range] at h_bool
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
      · exact ih low ((k + 2) / 2) h_half h_left n hn1 hn_half h7 hodd
      · have hn_ge : low + (k + 2) / 2 ≤ n := by omega
        exact ih (low + (k + 2) / 2) ((k + 2) - (k + 2) / 2) h_half2 h_right n hn_ge hn_lt2 h7 hodd

theorem lemoine_of_decide (n : ℕ) (h : lemoine_decide n = true) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  dsimp [lemoine_decide] at h
  rw [List.any_eq_true] at h
  rcases h with ⟨q, hq_mem, hq_cond⟩
  rw [Bool.and_eq_true] at hq_cond
  rcases hq_cond with ⟨hq_lt, hq_prime_dec⟩
  have h_lt : 2 * q < n := of_decide_eq_true hq_lt
  have hp_prime : (n - 2 * q).Prime := of_decide_eq_true hq_prime_dec
  have hq_prime : q.Prime := primes_under_182_prime q hq_mem
  use n - 2 * q, q
  refine ⟨hp_prime, hq_prime, ?_⟩
  omega
