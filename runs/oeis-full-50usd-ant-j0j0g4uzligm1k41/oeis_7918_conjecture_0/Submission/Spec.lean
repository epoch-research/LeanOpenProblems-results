import FormalConjectures.Util.ProblemImports

open Nat

/--
A007918: Least prime $\ge n$ (version 1 of the "next prime" function).
-/
noncomputable def a (n : ℕ) : ℕ :=
  @Nat.find (fun p => Nat.Prime p ∧ n ≤ p) (by infer_instance) (by
    rcases Nat.exists_infinite_primes n with ⟨p, h_le, h_prime⟩
    exact ⟨p, h_prime, h_le⟩
  )

-- Auxiliary theorems for small values are omitted as they were causing compilation issues.
-- The focus is on the formalizing the conjecture.

/--
The initial term $p_0$ and common difference $d$ form an arithmetic progression of
length `n` consisting entirely of prime numbers.
We require $d > 0$ for it to be an increasing progression.
-/
def is_ap_of_n_primes (n p0 d : ℕ) : Prop :=
  d > 0 ∧ ∀ k < n, Nat.Prime (p0 + k * d)

/-- Any starting point of an arithmetic progression of `n ≥ 1` primes is itself prime
(the `k = 0` term). -/
lemma mem_prime {n p0 : ℕ} (hn : 0 < n) (h : ∃ d, is_ap_of_n_primes n p0 d) :
    Nat.Prime p0 := by
  obtain ⟨d, hd, hp⟩ := h
  simpa using hp 0 hn

/-- A prime `p0 < n` can never begin an arithmetic progression of `n` primes: if `p0 ∣ d`
then the `k = 1` term `p0 + d` is a nontrivial multiple of `p0`, and otherwise the `k = p0`
term `p0 + p0*d = p0*(1 + d)` is a nontrivial multiple of `p0`. In both cases the relevant
index is `< n`, giving a composite required term. Hence every element of the set is `≥ n`. -/
lemma mem_ge {n p0 : ℕ} (hn : 0 < n) (h : ∃ d, is_ap_of_n_primes n p0 d) :
    n ≤ p0 := by
  by_contra hlt
  push_neg at hlt
  have hp : Nat.Prime p0 := mem_prime hn h
  obtain ⟨d, hd, hprime⟩ := h
  by_cases hdvd : p0 ∣ d
  · have h1 : (1 : ℕ) < n := by have := hp.two_le; omega
    have hpr := hprime 1 h1
    rw [one_mul] at hpr
    have hdd : p0 ∣ (p0 + d) := Dvd.dvd.add (dvd_refl _) hdvd
    rcases hpr.eq_one_or_self_of_dvd p0 hdd with h | h
    · exact hp.ne_one h
    · omega
  · have hk : p0 < n := hlt
    have hpr := hprime p0 hk
    have hdd : p0 ∣ (p0 + p0 * d) := Dvd.dvd.add (dvd_refl _) (Dvd.intro d rfl)
    rcases hpr.eq_one_or_self_of_dvd p0 hdd with h | h
    · exact hp.ne_one h
    · have hzero : p0 * d = 0 := by omega
      rcases Nat.mul_eq_zero.mp hzero with h0 | h0
      · exact hp.ne_zero h0
      · omega

/-- `a n` is a lower bound for the set: it is the least prime `≥ n`, and every element of the
set is a prime `≥ n`. -/
lemma a_le_of_mem {n p0 : ℕ} (hn : 0 < n) (h : ∃ d, is_ap_of_n_primes n p0 d) :
    a n ≤ p0 :=
  Nat.find_le ⟨mem_prime hn h, mem_ge hn h⟩

/--
The crux of the conjecture: the least prime `≥ n` is the first term of *some* arithmetic
progression of `n` primes.

This is precisely an instance of Dickson's conjecture (equivalently, the Hardy–Littlewood
`k`-tuple conjecture, as noted in the OEIS entry for A007918). Indeed, the required common
difference `d` must be divisible by every prime `< n`; writing `d = P·t` with `P` the primorial,
the `n - 1` linear forms `a n + k·P·t` (`1 ≤ k ≤ n - 1`) have no fixed prime divisor
(they are *admissible*), so Dickson's conjecture predicts infinitely many `t` making all of
`a n, a n + d, …, a n + (n-1)d` simultaneously prime. This has been verified for every small
`n`, but a proof for all `n` is open: it would establish an unproven case of the simultaneous
primality of several linear forms (already open for `n = 3`), for which no method is available
(sieve theory is blocked by the parity problem, and Mathlib provides only Dirichlet's theorem,
which handles a single form).
-/
lemma a_mem (n : ℕ) (hn : 0 < n) :
    ∃ d : ℕ, is_ap_of_n_primes n (a n) d := by
  sorry

/--
A007918 According to the "k-tuple" conjecture, a(n) is the initial term of the
lexicographically earliest increasing arithmetic progression of n primes;
the corresponding common differences are given by A061558.
-/
theorem oeis_7918_conjecture_0 (n : ℕ) (hn : n > 0) :
    a n = sInf { p0 : ℕ | ∃ d : ℕ, is_ap_of_n_primes n p0 d } := by
  have hmem : a n ∈ { p0 : ℕ | ∃ d : ℕ, is_ap_of_n_primes n p0 d } := a_mem n hn
  refine le_antisymm ?_ (Nat.sInf_le hmem)
  have hne : { p0 : ℕ | ∃ d : ℕ, is_ap_of_n_primes n p0 d }.Nonempty := ⟨a n, hmem⟩
  exact a_le_of_mem hn (Nat.sInf_mem hne)
