import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 10000000
open Nat

/--
Numbers whose prime divisors all end in the same digit.
-/
def A381159_condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
A381159: Numbers whose prime divisors all end in the same digit.
-/
noncomputable def A381159 (n : ℕ) : ℕ := n.nth A381159_condition

lemma not_A381159_condition_of_two_prime_factors {m p1 p2 : ℕ} (hm : m ≠ 0)
    (hp1 : p1.Prime) (hp2 : p2.Prime) (hdvd1 : p1 ∣ m) (hdvd2 : p2 ∣ m)
    (hdiff : p1 % 10 ≠ p2 % 10) : ¬ A381159_condition m := by
  intro hc
  unfold A381159_condition at hc
  rw [Finset.card_le_one] at hc
  have h1 : p1 % 10 ∈ m.primeFactors.image (fun p => p % 10) := by
    rw [Finset.mem_image]
    exact ⟨p1, hp1.mem_primeFactors hdvd1 hm, rfl⟩
  have h2 : p2 % 10 ∈ m.primeFactors.image (fun p => p % 10) := by
    rw [Finset.mem_image]
    exact ⟨p2, hp2.mem_primeFactors hdvd2 hm, rfl⟩
  have heq := hc (p1 % 10) h1 (p2 % 10) h2
  exact hdiff heq

lemma zmod_test (a d N : ℕ) (hN : 1 < N) (h_coprime : Coprime d N) :
    ∃ i < N, N ∣ a + i * d := by
  have : NeZero N := ⟨by omega⟩
  let i_z : ZMod N := - (a : ZMod N) * (d : ZMod N)⁻¹
  let i := i_z.val
  use i
  constructor
  · exact ZMod.val_lt i_z
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    have : (i : ZMod N) = i_z := ZMod.natCast_zmod_val i_z
    rw [this]
    dsimp [i_z]
    rw [mul_assoc]
    have h_unit : (d : ZMod N)⁻¹ * (d : ZMod N) = 1 := by
      rw [mul_comm, ZMod.coe_mul_inv_eq_one d h_coprime]
    rw [h_unit, mul_one]
    exact add_neg_cancel (a : ZMod N)

lemma coprime_mul_of_primes {p1 p2 d : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hp1_d : ¬ p1 ∣ d) (hp2_d : ¬ p2 ∣ d) : Coprime d (p1 * p2) := by
  have hc1 : Coprime p1 d := hp1.coprime_iff_not_dvd.mpr hp1_d
  have hc2 : Coprime p2 d := hp2.coprime_iff_not_dvd.mpr hp2_d
  have hc1' : Coprime d p1 := hc1.symm
  have hc2' : Coprime d p2 := hc2.symm
  exact hc1'.mul_right hc2'

lemma exists_bad_index_helper {a d : ℕ} (ha : 2 ≤ a) (p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hp1_d : ¬ p1 ∣ d) (hp2_d : ¬ p2 ∣ d) (h_le : p1 * p2 ≤ 150) (hdiff : p1 % 10 ≠ p2 % 10) :
    ∃ (i : Fin 150), ¬ A381159_condition (a + i.val * d) := by
  have h_coprime : Coprime d (p1 * p2) := coprime_mul_of_primes hp1 hp2 hp1_d hp2_d
  have h_prod_gt : 1 < p1 * p2 := by
    have h1 : 2 ≤ p1 := hp1.two_le
    have h2 : 2 ≤ p2 := hp2.two_le
    nlinarith
  obtain ⟨i, hi_lt, h_div⟩ := zmod_test a d (p1 * p2) h_prod_gt h_coprime
  have hi_150 : i < 150 := by omega
  use ⟨i, hi_150⟩
  have h_not_zero : a + i * d ≠ 0 := by omega
  have hdvd1 : p1 ∣ a + i * d := by
    have : p1 ∣ p1 * p2 := dvd_mul_right p1 p2
    exact dvd_trans this h_div
  have hdvd2 : p2 ∣ a + i * d := by
    have : p2 ∣ p1 * p2 := dvd_mul_left p2 p1
    exact dvd_trans this h_div
  exact not_A381159_condition_of_two_prime_factors h_not_zero hp1 hp2 hdvd1 hdvd2 hdiff

def find_prime_pair_loop2 (d p1 : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | p2 :: l2 =>
    if p1 * p2 ≤ 150 ∧ p1 % 10 ≠ p2 % 10 ∧ d % p1 ≠ 0 ∧ d % p2 ≠ 0 then
      (p1, p2)
    else
      find_prime_pair_loop2 d p1 l2

def find_prime_pair_loop1 (d : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | p1 :: l1 =>
    match find_prime_pair_loop2 d p1 l1 with
    | (0, 0) => find_prime_pair_loop1 d l1
    | other => other

def find_prime_pair (d : ℕ) : ℕ × ℕ :=
  let primes := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149]
  find_prime_pair_loop1 d primes

lemma find_prime_pair_works (d : ℕ) (hd_ge : 1 ≤ d) (hd_le : d ≤ 2025) :
    let pair := find_prime_pair d
    pair.1.Prime ∧
    pair.2.Prime ∧
    ¬ pair.1 ∣ d ∧
    ¬ pair.2 ∣ d ∧
    pair.1 * pair.2 ≤ 150 ∧
    pair.1 % 10 ≠ pair.2 % 10 := by
  interval_cases d <;> decide

lemma exists_bad_index {a d : ℕ} (ha : 2 ≤ a) (hd_ge : 1 ≤ d) (hd_le : d ≤ 2025) :
    ∃ (i : Fin 150), ¬ A381159_condition (a + i.val * d) := by
  have h_pair := find_prime_pair_works d hd_ge hd_le
  let pair := find_prime_pair d
  have hp1 : pair.1.Prime := h_pair.1
  have hp2 : pair.2.Prime := h_pair.2.1
  have hp1_d : ¬ pair.1 ∣ d := h_pair.2.2.1
  have hp2_d : ¬ pair.2 ∣ d := h_pair.2.2.2.1
  have h_le : pair.1 * pair.2 ≤ 150 := h_pair.2.2.2.2.1
  have hdiff : pair.1 % 10 ≠ pair.2 % 10 := h_pair.2.2.2.2.2
  exact exists_bad_index_helper ha pair.1 pair.2 hp1 hp2 hp1_d hp2_d h_le hdiff

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

We formalize the positive answer to the question/conjecture.
The condition for "lopsided" for n > 1 is exactly A381159_condition n.
We require the starting term a to be at least 2 to ensure all terms are > 1.
-/
theorem oeis_381159_conjecture_0.disproof :
  ¬ ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d) := by
  rintro ⟨a, d, ha, hd_ge, hd_le, h_all⟩
  obtain ⟨i, hi⟩ := exists_bad_index ha hd_ge hd_le
  exact hi (h_all i)

