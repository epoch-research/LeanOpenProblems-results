import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A338777: $a(n) = \prod_{k \in \text{GB}(2n)} k$, where $\text{GB}(m)$ is the set of primes $p$
such that $\sqrt{m} < p \le m/2$ and no prime $q \le \sqrt{m}$ divides $p(p - m)$.
The condition $q \nmid p(p-m)$ is equivalent to $p \not\equiv m \pmod q$ for $p \in \text{GB}(m)$.
-/
def A338777 (n : ℕ) : ℕ :=
  let m := 2 * n
  -- The product over an empty set is 1, which handles a(0), a(1), a(2) correctly.
  if m = 0 then 1 else

  let r := Nat.sqrt m
  -- The set of primes q that are candidates for dividing p(p-m).
  let small_primes : Finset ℕ := (Finset.range (r + 1)).filter Nat.Prime

  -- A number p is Goldbach-associated with m if it satisfies the criteria.
  let is_gb_associated (p : ℕ) : Prop :=
    Nat.Prime p ∧
    r < p ∧
    p ≤ m / 2 ∧
    (∀ q ∈ small_primes, p % q ≠ m % q)

  -- GB(m) is the set of primes p up to m/2 that satisfy the condition.
  let GB_2n : Finset ℕ :=
    (Finset.range (m / 2 + 1)).filter is_gb_associated

  GB_2n.prod id

-- An auxiliary definition for the Goldbach-associated set GB(m) for use in the conjecture.
def GB_set (m : ℕ) : Finset ℕ :=
  if m = 0 then ∅ else
  let r := Nat.sqrt m
  let small_primes : Finset ℕ := (Finset.range (r + 1)).filter Nat.Prime

  let is_gb_associated (p : ℕ) : Prop :=
    Nat.Prime p ∧
    r < p ∧
    p ≤ m / 2 ∧
    (∀ q ∈ small_primes, p % q ≠ m % q)

  (Finset.range (m / 2 + 1)).filter is_gb_associated

/-- The Goldbach conjecture states that every even integer greater than 2 is the sum of two primes. -/
def goldbach_conjecture : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ p1 p2 : ℕ, Nat.Prime p1 ∧ Nat.Prime p2 ∧ 2 * n = p1 + p2


lemma gb_complement_prime {M p : ℕ} (hM : M ≠ 0) (hp_mem : p ∈ GB_set M) : Nat.Prime (M - p) := by
  have hp_prime : Nat.Prime p := by
    unfold GB_set at hp_mem
    simp [hM] at hp_mem
    exact hp_mem.2.1
  have hp_le_half : p ≤ M / 2 := by
    unfold GB_set at hp_mem
    simp [hM] at hp_mem
    exact hp_mem.2.2.2.1
  have hnotmod : ∀ q, q ≤ Nat.sqrt M → Nat.Prime q → p % q ≠ M % q := by
    unfold GB_set at hp_mem
    simp [hM] at hp_mem
    exact hp_mem.2.2.2.2
  have hp_le_M : p ≤ M := le_trans hp_le_half (Nat.div_le_self M 2)
  have hcomp_ge_p : p ≤ M - p := by
    have h2p : p * 2 ≤ M := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).1 hp_le_half
    omega
  have hcomp_ge2 : 2 ≤ M - p := le_trans hp_prime.two_le hcomp_ge_p
  rw [Nat.prime_def_le_sqrt]
  constructor
  · exact hcomp_ge2
  · intro d hd2 hd_sqrt hdvd
    have hd_ne1 : d ≠ 1 := by omega
    obtain ⟨q, hqprime, hq_dvd_d⟩ := Nat.exists_prime_and_dvd hd_ne1
    have hq_dvd_comp : q ∣ M - p := dvd_trans hq_dvd_d hdvd
    have hq_le_d : q ≤ d := Nat.le_of_dvd (by omega) hq_dvd_d
    have hq_le_sqrt_comp : q ≤ Nat.sqrt (M - p) := le_trans hq_le_d hd_sqrt
    have hcomp_le_M : M - p ≤ M := Nat.sub_le _ _
    have hq_le_sqrt_M : q ≤ Nat.sqrt M := le_trans hq_le_sqrt_comp (Nat.sqrt_le_sqrt hcomp_le_M)
    have hmodeq : p % q = M % q := by
      exact (Nat.modEq_iff_dvd' hp_le_M).2 hq_dvd_comp
    exact (hnotmod q hq_le_sqrt_M hqprime) hmodeq

/-- oeis_338777_conjecture_0: If a(n) != 1 for n >= 3 then Goldbach's conjecture is true.
The underlying claim is that for any such $n$, $m = \max(\text{GB}(2n))$ exists and $(2n - m, m)$
is a Goldbach partition of $2n$. -/
theorem oeis_338777_conjecture_0 :
  -- The claim that the sequence property implies Goldbach's conjecture globally.
  ( (∀ k : ℕ, 3 ≤ k → A338777 k ≠ 1) → goldbach_conjecture ) ∧
  -- The local constructive claim for each n: A(n) != 1 implies a specific Goldbach partition.
  (∀ n : ℕ, 3 ≤ n →
    A338777 n ≠ 1 →
      let m2n := 2 * n
      let GB_2n := GB_set m2n
      -- A(n) != 1 implies GB(2n) is Nonempty, thus a maximum exists.
      GB_2n.Nonempty ∧
      -- Existential quantification for the maximum element m in GB(2n)
      ∃ m : ℕ, m ∈ GB_2n ∧ (∀ k ∈ GB_2n, k ≤ m) ∧
      -- Since m is a prime in GB_2n, the conjecture is that the complement is also prime.
      Nat.Prime (m2n - m)
      ) := by
  constructor
  · intro hA n hn
    let s := GB_set (2 * n)
    have hM : 2 * n ≠ 0 := by omega
    have hs : s.Nonempty := by
      have hprod : s.prod id ≠ 1 := by
        simpa [s, A338777, GB_set, hM] using hA n hn
      exact Finset.nonempty_of_prod_ne_one hprod
    let m := s.max' hs
    have hm_mem : m ∈ s := Finset.max'_mem s hs
    refine ⟨2 * n - m, m, ?_, ?_, ?_⟩
    · exact gb_complement_prime hM hm_mem
    · have : Nat.Prime m := by
        simp [s, GB_set, hM] at hm_mem
        exact hm_mem.2.1
      exact this
    · have hm_le_half : m ≤ (2 * n) / 2 := by
        have hm_le_n : m ≤ n := by
          simp [s, GB_set, hM] at hm_mem
          exact hm_mem.2.2.2.1
        simpa using hm_le_n
      have hm_le_M : m ≤ 2 * n := le_trans hm_le_half (Nat.div_le_self (2 * n) 2)
      omega
  · intro n hn hA
    let m2n := 2 * n
    let s := GB_set m2n
    have hM : m2n ≠ 0 := by omega
    have hs : s.Nonempty := by
      have hprod : s.prod id ≠ 1 := by
        simpa [s, m2n, A338777, GB_set, hM] using hA
      exact Finset.nonempty_of_prod_ne_one hprod
    constructor
    · exact hs
    · let m := s.max' hs
      refine ⟨m, Finset.max'_mem s hs, ?_, ?_⟩
      · intro k hk
        exact Finset.le_max' s k hk
      · exact gb_complement_prime hM (Finset.max'_mem s hs)
