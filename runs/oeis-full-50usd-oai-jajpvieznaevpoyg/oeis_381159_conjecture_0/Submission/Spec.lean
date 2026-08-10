import FormalConjectures.Util.ProblemImports

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

/-- If two primes with different final digits divide `n`, then `n` is not lopsided. -/
private lemma A381159_not_condition_of_two_prime_dvd {n p q : ℕ} (hn : n ≠ 0)
    (hpprime : p.Prime) (hqprime : q.Prime)
    (hpdvd : p ∣ n) (hqdvd : q ∣ n) (hneq : p % 10 ≠ q % 10) :
    ¬ A381159_condition n := by
  intro h
  have hpmem0 : p ∈ n.primeFactors := hpprime.mem_primeFactors hpdvd hn
  have hqmem0 : q ∈ n.primeFactors := hqprime.mem_primeFactors hqdvd hn
  have hpmem : p % 10 ∈ n.primeFactors.image (fun p => p % 10) := by
    exact Finset.mem_image.mpr ⟨p, hpmem0, rfl⟩
  have hqmem : q % 10 ∈ n.primeFactors.image (fun p => p % 10) := by
    exact Finset.mem_image.mpr ⟨q, hqmem0, rfl⟩
  exact hneq ((Finset.card_le_one.mp h) (p % 10) hpmem (q % 10) hqmem)

private lemma coprime_mul_of_not_dvd {p q d : ℕ} (hpprime : p.Prime) (hqprime : q.Prime)
    (hp : ¬ p ∣ d) (hq : ¬ q ∣ d) : Nat.Coprime d (p * q) := by
  rw [Nat.coprime_mul_iff_right]
  constructor
  · rw [Nat.coprime_comm, hpprime.coprime_iff_not_dvd]
    exact hp
  · rw [Nat.coprime_comm, hqprime.coprime_iff_not_dvd]
    exact hq

/--
If `p*q ≤ 150` and neither prime divides the common difference, then some one of the
150 terms is divisible by both `p` and `q`.
-/
private lemma exists_index_mul_dvd (a d p q : ℕ) (hpprime : p.Prime) (hqprime : q.Prime)
    (hp : ¬ p ∣ d) (hq : ¬ q ∣ d) (hpqle : p * q ≤ 150) :
    ∃ i : Fin 150, p * q ∣ a + i.val * d := by
  have hMne : p * q ≠ 0 := Nat.mul_ne_zero hpprime.ne_zero hqprime.ne_zero
  letI : NeZero (p * q) := ⟨hMne⟩
  let u : (ZMod (p * q))ˣ :=
    ZMod.unitOfCoprime d (coprime_mul_of_not_dvd hpprime hqprime hp hq)
  let x : ZMod (p * q) := - (a : ZMod (p * q)) * ↑u⁻¹
  refine ⟨⟨x.val, by have hxlt := ZMod.val_lt x; omega⟩, ?_⟩
  have hx : (a : ZMod (p * q)) + (x.val : ZMod (p * q)) * d = 0 := by
    rw [ZMod.natCast_zmod_val x]
    rw [show (d : ZMod (p * q)) = (u : ZMod (p * q)) by
      exact (ZMod.coe_unitOfCoprime d
        (coprime_mul_of_not_dvd hpprime hqprime hp hq)).symm]
    simp [x, mul_comm, mul_left_comm]
  exact (ZMod.natCast_eq_zero_iff (a + x.val * d) (p * q)).mp (by simpa using hx)

private lemma contradiction_of_active_pair (a d p q : ℕ) (ha : 2 ≤ a)
    (hpprime : p.Prime) (hqprime : q.Prime) (hp : ¬ p ∣ d) (hq : ¬ q ∣ d)
    (hpqle : p * q ≤ 150) (hneq : p % 10 ≠ q % 10)
    (hall : ∀ (i : Fin 150), A381159_condition (a + i.val * d)) : False := by
  rcases exists_index_mul_dvd a d p q hpprime hqprime hp hq hpqle with ⟨i, hdiv⟩
  let n := a + i.val * d
  have hn : n ≠ 0 := by omega
  have hpdvd : p ∣ n := dvd_trans (Nat.dvd_mul_right p q) hdiv
  have hqdvd : q ∣ n := by
    have hqprod : q ∣ p * q := by
      rw [Nat.mul_comm]
      exact Nat.dvd_mul_right q p
    exact dvd_trans hqprod hdiv
  exact A381159_not_condition_of_two_prime_dvd hn hpprime hqprime hpdvd hqdvd hneq (hall i)

set_option maxHeartbeats 800000 in
private lemma exists_active_pair (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 2025) :
    (¬ 11 ∣ d ∧ ¬ 13 ∣ d) ∨
    (¬ 7 ∣ d ∧ ¬ 19 ∣ d) ∨
    (¬ 5 ∣ d ∧ ¬ 29 ∣ d) ∨
    (¬ 7 ∣ d ∧ ¬ 13 ∣ d) ∨
    (¬ 7 ∣ d ∧ ¬ 11 ∣ d) ∨
    (¬ 3 ∣ d ∧ ¬ 47 ∣ d) ∨
    (¬ 2 ∣ d ∧ ¬ 73 ∣ d) := by
  interval_cases d <;> decide

/--
A381159 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)

The proposed positive formalization is false: no such progression exists.
-/
theorem oeis_381159_conjecture_0.disproof :
  ¬ ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), A381159_condition (a + i.val * d) := by
  rintro ⟨a, d, ha, hd1, hd2, hall⟩
  rcases exists_active_pair d hd1 hd2 with h | h | h | h | h | h | h
  · exact contradiction_of_active_pair a d 11 13 ha (by norm_num) (by norm_num)
      h.1 h.2 (by norm_num) (by norm_num) hall
  · exact contradiction_of_active_pair a d 7 19 ha (by norm_num) (by norm_num)
      h.1 h.2 (by norm_num) (by norm_num) hall
  · exact contradiction_of_active_pair a d 5 29 ha (by norm_num) (by norm_num)
      h.1 h.2 (by norm_num) (by norm_num) hall
  · exact contradiction_of_active_pair a d 7 13 ha (by norm_num) (by norm_num)
      h.1 h.2 (by norm_num) (by norm_num) hall
  · exact contradiction_of_active_pair a d 7 11 ha (by norm_num) (by norm_num)
      h.1 h.2 (by norm_num) (by norm_num) hall
  · exact contradiction_of_active_pair a d 3 47 ha (by norm_num) (by norm_num)
      h.1 h.2 (by norm_num) (by norm_num) hall
  · exact contradiction_of_active_pair a d 2 73 ha (by norm_num) (by norm_num)
      h.1 h.2 (by norm_num) (by norm_num) hall
