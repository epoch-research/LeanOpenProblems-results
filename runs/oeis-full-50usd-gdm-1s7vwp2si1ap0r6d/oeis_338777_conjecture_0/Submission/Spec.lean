import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Classical

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

/-- oeis_338777_conjecture_0: If a(n) != 1 for n >= 3 then Goldbach's conjecture is true.
The underlying claim is that for any such $n$, $m = \max(\text{GB}(2n))$ exists and $(2n - m, m)$
is a Goldbach partition of $2n$. -/


theorem test_lemma (p : ℕ) (h1 : 2 ≤ p) (h2 : ∀ q, Nat.Prime q → q ≤ Nat.sqrt p → ¬q ∣ p) : Nat.Prime p := by
  rw [prime_def_le_sqrt]
  refine ⟨h1, ?_⟩
  intro m hm1 hm2 hdiv
  -- m has a prime factor
  have : ∃ q, Nat.Prime q ∧ q ∣ m := by
    exact exists_prime_and_dvd (by omega)
  rcases this with ⟨q, hq, hqdiv⟩
  have hq_le : q ≤ Nat.sqrt p := by
    have : q ≤ m := Nat.le_of_dvd (by omega) hqdiv
    omega
  have hq_div_p : q ∣ p := Nat.dvd_trans hqdiv hdiv
  exact h2 q hq hq_le hq_div_p


lemma GB_set_eq_of_ne_zero {m : ℕ} (h : m ≠ 0) :
  GB_set m = (Finset.range (m / 2 + 1)).filter (fun p =>
    Nat.Prime p ∧
    Nat.sqrt m < p ∧
    p ≤ m / 2 ∧
    (∀ q ∈ (Finset.range (Nat.sqrt m + 1)).filter Nat.Prime, p % q ≠ m % q)) := by
  unfold GB_set
  rw [if_neg h]
  ext p
  simp


lemma A338777_eq_prod_GB_set (n : ℕ) :
  A338777 n = (GB_set (2 * n)).prod id := by
  unfold A338777 GB_set
  split_ifs with h
  · have h2 : n = 0 := by omega
    subst h2
    simp
  · simp [h]


lemma GB_set_properties {m2n p : ℕ} (hnz : m2n ≠ 0) (hp : p ∈ GB_set m2n) :
  Nat.Prime p ∧ (Nat.sqrt m2n) < p ∧ p ≤ m2n / 2 ∧
  (∀ q ∈ (Finset.range (Nat.sqrt m2n + 1)).filter Nat.Prime, p % q ≠ m2n % q) := by
  simp [GB_set_eq_of_ne_zero hnz] at hp
  refine ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_⟩
  simp
  exact hp.2.2.2.2


lemma test_mod_dvd (a b q : ℕ) (h_le : b ≤ a) (hdvd : q ∣ a - b) : a % q = b % q := by
  have h_eq : a = (a - b) + b := by omega
  nth_rw 1 [h_eq]
  rw [Nat.add_mod]
  have h_dvd : (a - b) % q = 0 := Nat.mod_eq_zero_of_dvd hdvd
  rw [h_dvd, zero_add]
  rw [Nat.mod_mod]


theorem oeis_338777_conjecture_0_part2 (n : ℕ) (hn : 3 ≤ n) (ha : A338777 n ≠ 1) :
  let m2n := 2 * n
  let GB_2n := GB_set m2n
  GB_2n.Nonempty ∧
  ∃ m : ℕ, m ∈ GB_2n ∧ (∀ k ∈ GB_2n, k ≤ m) ∧
  Nat.Prime (m2n - m) := by
  intro m2n GB_2n
  have hnz : m2n ≠ 0 := by omega
  have h_prod : A338777 n = GB_2n.prod id := A338777_eq_prod_GB_set n
  have h_ne : GB_2n ≠ ∅ := by
    intro h_empty
    rw [h_empty] at h_prod
    simp [h_prod] at ha
  have h_nonempty : GB_2n.Nonempty := Finset.nonempty_of_ne_empty h_ne
  refine ⟨h_nonempty, ?_⟩
  let m := GB_2n.max' h_nonempty
  use m
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.max'_mem GB_2n h_nonempty
  · intro k hk
    exact GB_2n.le_max' k hk
  · -- Prove Nat.Prime (m2n - m) using test_lemma
    have hm_in : m ∈ GB_2n := Finset.max'_mem GB_2n h_nonempty
    have h_props := GB_set_properties hnz hm_in
    have m_prime : Nat.Prime m := h_props.1
    have r_lt_m : Nat.sqrt m2n < m := h_props.2.1
    have m_le_n : m ≤ n := by
      have h_le := h_props.2.2.1
      omega
    have h_mod : ∀ q ∈ (Finset.range (Nat.sqrt m2n + 1)).filter Nat.Prime, m % q ≠ m2n % q := h_props.2.2.2

    apply test_lemma (m2n - m)
    · -- 2 ≤ m2n - m
      omega
    · -- ∀ q, Prime q → q ≤ sqrt (m2n - m) → ¬q ∣ m2n - m
      intro q hq_prime hq_le hdvd
      -- we show q ≤ sqrt m2n
      have h_lt_succ : m2n < (Nat.sqrt m2n + 1) * (Nat.sqrt m2n + 1) := lt_succ_sqrt m2n
      have h_sub_lt : m2n - m < (Nat.sqrt m2n + 1) * (Nat.sqrt m2n + 1) := by omega
      have h_sqrt_lt : Nat.sqrt (m2n - m) < Nat.sqrt m2n + 1 := by
        rwa [← sqrt_lt] at h_sub_lt
      have h_q_le : q ≤ Nat.sqrt m2n := by omega

      -- q ∈ small_primes
      have hq_in : q ∈ (Finset.range (Nat.sqrt m2n + 1)).filter Nat.Prime := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hq_prime⟩

      -- apply h_mod
      have h_neq := h_mod q hq_in
      -- but m2n % q = m % q by hdvd
      have h_eq : m2n % q = m % q := test_mod_dvd m2n m q (by omega) hdvd
      exact h_neq h_eq.symm

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
  refine ⟨?_ , ?_⟩
  · intro H n hn
    have h_part2 := oeis_338777_conjecture_0_part2 n hn (H n hn)
    rcases h_part2 with ⟨h_nonempty, m, hm_in, hm_max, hm_prime⟩
    use m, 2 * n - m
    refine ⟨?_, hm_prime, ?_⟩
    · have hnz : 2 * n ≠ 0 := by omega
      have h_props := GB_set_properties hnz hm_in
      exact h_props.1
    · have hnz : 2 * n ≠ 0 := by omega
      have h_props := GB_set_properties hnz hm_in
      have hm_le : m ≤ n := by
        have h_le := h_props.2.2.1
        omega
      omega
  · intro n hn ha
    exact oeis_338777_conjecture_0_part2 n hn ha
