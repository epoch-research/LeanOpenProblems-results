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

/-- For any `p` in `GB_set m`, the complement `m - p` is prime. This is because no prime
`q ≤ √m` divides `m - p` (by the defining congruence condition), and any number `> 1` all of
whose prime factors exceed its square root must be prime. -/
lemma gb_compl_prime (m p : ℕ) (hp : p ∈ GB_set m) : Nat.Prime (m - p) := by
  rw [GB_set] at hp
  split at hp
  · simp at hp
  · simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hrange, hprime, hrlt, hple, hcond⟩ := hp
    have h2p : p * 2 ≤ m := (Nat.le_div_iff_mul_le (by norm_num)).mp hple
    have hpm : p ≤ m := le_trans (by omega) h2p
    set d := m - p with hd
    have hpd : p ≤ d := by omega
    have hd2 : 2 ≤ d := le_trans hprime.two_le hpd
    have hdm : d ≤ m := by omega
    by_contra hdnp
    have hd0 : 0 < d := by omega
    have hd1 : d ≠ 1 := by omega
    set q := Nat.minFac d with hq
    have hqp : q.Prime := Nat.minFac_prime hd1
    have hqd : q ∣ d := Nat.minFac_dvd d
    have hqsq : q * q ≤ d := by
      have := Nat.minFac_sq_le_self hd0 hdnp
      rw [pow_two] at this
      exact this
    have hqle : q ≤ Nat.sqrt m := by
      have h1 : q ≤ Nat.sqrt d := Nat.le_sqrt.mpr hqsq
      exact le_trans h1 (Nat.sqrt_le_sqrt hdm)
    have hne := hcond q ⟨by omega, hqp⟩
    have hmod : p % q = m % q := (Nat.modEq_iff_dvd' hpm).mpr hqd
    exact hne hmod

/-- Any element of `GB_set m` is a prime that is at most `m`. -/
lemma gb_props (m p : ℕ) (hp : p ∈ GB_set m) : p.Prime ∧ p ≤ m := by
  rw [GB_set] at hp
  split at hp
  · simp at hp
  · simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hrange, hprime, hrlt, hple, hcond⟩ := hp
    exact ⟨hprime, by omega⟩

/-- `A338777 n` is exactly the product over `GB_set (2 * n)`. -/
lemma A338777_eq (n : ℕ) (hn : n ≠ 0) : A338777 n = (GB_set (2 * n)).prod id := by
  have h2 : 2 * n ≠ 0 := by omega
  rw [A338777, GB_set]
  simp only [h2, if_false]

/-- If `A338777 n ≠ 1` then `GB_set (2 * n)` is nonempty. -/
lemma gb_nonempty_of_ne (n : ℕ) (hn : n ≠ 0) (h : A338777 n ≠ 1) :
    (GB_set (2 * n)).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  apply h
  rw [A338777_eq n hn, hne, Finset.prod_empty]

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
  · rintro h n hn
    have hn0 : n ≠ 0 := by omega
    obtain ⟨p, hp⟩ := gb_nonempty_of_ne n hn0 (h n hn)
    have hpc := gb_compl_prime (2 * n) p hp
    obtain ⟨hpp, hple⟩ := gb_props (2 * n) p hp
    exact ⟨p, 2 * n - p, hpp, hpc, by omega⟩
  · rintro n hn hne
    have hn0 : n ≠ 0 := by omega
    intro m2n GB_2n
    have hnonempty : GB_2n.Nonempty := gb_nonempty_of_ne n hn0 hne
    refine ⟨hnonempty, GB_2n.max' hnonempty, GB_2n.max'_mem hnonempty, ?_, ?_⟩
    · intro k hk
      exact GB_2n.le_max' k hk
    · exact gb_compl_prime (2 * n) (GB_2n.max' hnonempty) (GB_2n.max'_mem hnonempty)
