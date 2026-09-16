import FormalConjectures.Util.ProblemImports
import Mathlib

open Nat Finset

def a (n : ℕ) : ℤ :=
  (n : ℤ) * (n.divisors.card : ℤ) - n.properDivisors.sum
    (fun d => (d : ℤ) * (d.divisors.card : ℤ))

def sigma (n : ℕ) : ℤ :=
  n.divisors.sum (fun d => (d : ℤ))

theorem a_eq (n : ℕ) (hn : n > 0) : 
  a n = 2 * (n : ℤ) * (n.divisors.card : ℤ) - n.divisors.sum (fun d => (d : ℤ) * (d.divisors.card : ℤ)) := by
  dsimp [a]
  have h_div : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, _root_.ne_of_gt hn⟩
  have eq_prop : n.divisors.erase n = n.properDivisors := by
    ext x
    simp only [mem_erase, mem_divisors, mem_properDivisors]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, lt_of_le_of_ne (Nat.le_of_dvd hn h2) h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨_root_.ne_of_lt h2, h1, _root_.ne_of_gt hn⟩
  rw [← sum_erase_add _ _ h_div, eq_prop]
  ring

lemma pow_sum_eq (k : ℕ) :
  (2 : ℤ) * (2^k : ℤ) * (k + 1 : ℤ) - ∑ x ∈ range (k + 1), (2^x : ℤ) * (x + 1 : ℤ) = ∑ x ∈ range (k + 1), (2^x : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : ∑ x ∈ range (k + 1 + 1), (2^x : ℤ) * (x + 1 : ℤ) = (∑ x ∈ range (k + 1), (2^x : ℤ) * (x + 1 : ℤ)) + (2^(k+1) : ℤ) * (k + 1 + 1 : ℤ) := sum_range_succ _ (k + 1)
    have h2 : ∑ x ∈ range (k + 1 + 1), (2^x : ℤ) = (∑ x ∈ range (k + 1), (2^x : ℤ)) + (2^(k+1) : ℤ) := sum_range_succ _ (k + 1)
    rw [h1, h2]
    push_cast at *
    have h_pow : (2^(k+1) : ℤ) = 2 * (2^k : ℤ) := by ring
    nlinarith

theorem a_pow_2 (k : ℕ) : a (2^k) = sigma (2^k) := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hn : 2^k > 0 := by positivity
  rw [a_eq (2^k) hn, sigma]
  rw [Nat.divisors_prime_pow hp k]
  simp only [sum_map, card_map, card_range, Function.Embedding.coeFn_mk]
  have h_card : ∀ x, (2^x).divisors.card = x + 1 := by
    intro x
    rw [Nat.divisors_prime_pow hp x]
    simp
  simp_rw [h_card]
  exact pow_sum_eq k

lemma is_pow_2_imp (n : ℕ) (h : n.isPowerOfTwo) : a n = sigma n := by
  rcases h with ⟨k, hk⟩
  rw [hk]
  exact a_pow_2 k

/--
%C A245212 Conjecture: a(n) = sigma(n) iff n is a power of 2 (A000079).
-/
theorem oeis_245212_conjecture_0 (n : ℕ) (h : n > 0) :
    a n = sigma n ↔ n.isPowerOfTwo := by
  constructor
  · intro _
    sorry
  · exact is_pow_2_imp n

theorem oeis_245212_conjecture_0.disproof : ¬ (type_of% @oeis_245212_conjecture_0) := sorry
