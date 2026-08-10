import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 200000

def goldbach_primes : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
  157, 163, 167, 173
]

def goldbach_decidable (n : ℕ) : Bool :=
  goldbach_primes.any (fun p => decide (p < n) && decide (n - p).Prime)

lemma prime_of_mem_goldbach_primes {p : ℕ} (h : p ∈ goldbach_primes) : p.Prime := by
  have h_all : goldbach_primes.all (fun x => decide x.Prime) = true := rfl
  rw [List.all_eq_true] at h_all
  have hp_dec := h_all p h
  exact decide_eq_true_iff.mp hp_dec

lemma goldbach_of_decidable (n : ℕ) (h : goldbach_decidable n = true) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q := by
  have h1 : ∃ p ∈ goldbach_primes, (decide (p < n) && decide (n - p).Prime) = true := by
    exact List.any_eq_true.mp h
  rcases h1 with ⟨p, hp_mem, hp_cond⟩
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hp_cond
  rcases hp_cond with ⟨hp_lt, hnp_prime⟩
  have hp_prime : p.Prime := prime_of_mem_goldbach_primes hp_mem
  use p, n - p
  refine ⟨hp_prime, hnp_prime, ?_⟩
  omega

def check_interval_fuel (fuel a b : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if b < a then true
    else if a == b then
      if 4 ≤ a && a % 2 == 0 then goldbach_decidable a else true
    else
      let mid := (a + b) / 2
      check_interval_fuel f a mid && check_interval_fuel f (mid + 1) b

lemma check_interval_fuel_sound (fuel : ℕ) (a b x : ℕ) (h : check_interval_fuel fuel a b = true)
    (hx1 : a ≤ x) (hx2 : x ≤ b) (h4 : 4 ≤ x) (heven : Even x) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ x = p + q := by
  induction fuel generalizing a b with
  | zero =>
    rw [check_interval_fuel] at h
    contradiction
  | succ f ih =>
    rw [check_interval_fuel] at h
    by_cases h1 : b < a
    · rw [if_pos h1] at h
      omega
    · rw [if_neg h1] at h
      by_cases h2 : a = b
      · have h2_b : (a == b) = true := beq_iff_eq.mpr h2
        rw [if_pos h2_b] at h
        have ha_eq : a = x := by omega
        rw [ha_eq] at h
        have h_cond_x : (decide (4 ≤ x) && (x % 2 == 0)) = true := by
          rw [Bool.and_eq_true, decide_eq_true_iff]
          have hx2 : x % 2 = 0 := Nat.even_iff.mp heven
          rw [hx2]
          exact ⟨h4, rfl⟩
        rw [h_cond_x] at h
        exact goldbach_of_decidable x h
      · have h2_b : (a == b) = false := decide_eq_false h2
        have h2_b_ne : (a == b) ≠ true := by rw [h2_b]; decide
        rw [if_neg h2_b_ne] at h
        rw [Bool.and_eq_true] at h
        rcases h with ⟨h_left, h_right⟩
        let mid := (a + b) / 2
        by_cases hx_mid : x ≤ mid
        · exact ih a mid h_left hx1 hx_mid
        · have hx_gt : x ≥ mid + 1 := by omega
          exact ih (mid + 1) b h_right hx_gt hx2

def lemoine_primes : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
  157, 163, 167, 173, 179, 181
]

def lemoine_decidable (n : ℕ) : Bool :=
  lemoine_primes.any (fun q => decide (2 * q < n) && decide (n - 2 * q).Prime)

lemma prime_of_mem_lemoine_primes {p : ℕ} (h : p ∈ lemoine_primes) : p.Prime := by
  have h_all : lemoine_primes.all (fun x => decide x.Prime) = true := rfl
  rw [List.all_eq_true] at h_all
  have hp_dec := h_all p h
  exact decide_eq_true_iff.mp hp_dec

lemma lemoine_of_decidable (n : ℕ) (h : lemoine_decidable n = true) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + 2 * q := by
  have h1 : ∃ q ∈ lemoine_primes, (decide (2 * q < n) && decide (n - 2 * q).Prime) = true := by
    exact List.any_eq_true.mp h
  rcases h1 with ⟨q, hq_mem, hq_cond⟩
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hq_cond
  rcases hq_cond with ⟨hq_lt, hp_prime⟩
  have hq_prime : q.Prime := prime_of_mem_lemoine_primes hq_mem
  use n - 2 * q, q
  refine ⟨hp_prime, hq_prime, ?_⟩
  omega

def check_lemoine_interval_fuel (fuel a b : ℕ) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    if b < a then true
    else if a == b then
      if 7 ≤ a && a % 2 == 1 then lemoine_decidable a else true
    else
      let mid := (a + b) / 2
      check_lemoine_interval_fuel f a mid && check_lemoine_interval_fuel f (mid + 1) b

lemma check_lemoine_interval_fuel_sound (fuel : ℕ) (a b x : ℕ) (h : check_lemoine_interval_fuel fuel a b = true)
    (hx1 : a ≤ x) (hx2 : x ≤ b) (h7 : 7 ≤ x) (hodd : Odd x) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ x = p + 2 * q := by
  induction fuel generalizing a b with
  | zero =>
    rw [check_lemoine_interval_fuel] at h
    contradiction
  | succ f ih =>
    rw [check_lemoine_interval_fuel] at h
    by_cases h1 : b < a
    · rw [if_pos h1] at h
      omega
    · rw [if_neg h1] at h
      by_cases h2 : a = b
      · have h2_b : (a == b) = true := beq_iff_eq.mpr h2
        rw [if_pos h2_b] at h
        have ha_eq : a = x := by omega
        rw [ha_eq] at h
        have h_cond_x : (decide (7 ≤ x) && (x % 2 == 1)) = true := by
          rw [Bool.and_eq_true, decide_eq_true_iff]
          have hx2 : x % 2 = 1 := Nat.odd_iff.mp hodd
          rw [hx2]
          exact ⟨h7, rfl⟩
        rw [h_cond_x] at h
        exact lemoine_of_decidable x h
      · have h2_b : (a == b) = false := decide_eq_false h2
        have h2_b_ne : (a == b) ≠ true := by rw [h2_b]; decide
        rw [if_neg h2_b_ne] at h
        rw [Bool.and_eq_true] at h
        rcases h with ⟨h_left, h_right⟩
        let mid := (a + b) / 2
        by_cases hx_mid : x ≤ mid
        · exact ih a mid h_left hx1 hx_mid
        · have hx_gt : x ≥ mid + 1 := by omega
          exact ih (mid + 1) b h_right hx_gt hx2

#eval check_interval_fuel 15 0 8012
#eval check_lemoine_interval_fuel 16 0 15727

lemma goldbach_of_core (hcore : a219055_core_conjecture) : goldbach_conjecture := by
  intro n hn heven
  by_cases hn_gt : n > 8012
  · have hpos : A219055 n > 0 := by
      apply hcore n
      left
      exact ⟨heven, hn_gt⟩
    rcases exists_of_A219055_even n heven hpos with ⟨q, hq_lt, _, hq_prime, _, hp_prime, _⟩
    use n - q, q
    refine ⟨hp_prime, hq_prime, ?_⟩
    omega
  · have hn_le : n ≤ 8012 := by omega
    have h_dec : check_interval_fuel 15 0 8012 = true := by native_decide
    exact check_interval_fuel_sound 15 0 8012 n h_dec (by omega) (by omega) hn heven
