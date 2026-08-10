import FormalConjectures.Util.ProblemImports

open Nat

/--
A051903: Maximum exponent in the prime factorization of $n$.
-/
def a (n : ℕ) : ℕ :=
  n.factorization.support.sup n.factorization

/-! ### Auxiliary lemmas for the reduction -/

/-- For `e ≥ 3` we have `e < 2 ^ (e - 1)`. -/
theorem e_lt_two_pow {e : ℕ} (he : 3 ≤ e) : e < 2 ^ (e - 1) := by
  induction e with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k <;> simp_all
    · have h1 := ih (by omega)
      simp only [Nat.add_sub_cancel]
      have h3 : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
      omega

/-- If `q ^ e ‖ n` with `q` prime and `e ≥ 1`, then `q ^ (e-1)` divides `φ n`. -/
theorem pow_pred_dvd_totient {n q e : ℕ} (hn : n ≠ 0) (hq : q.Prime)
    (hfq : n.factorization q = e) (he : 1 ≤ e) : q ^ (e - 1) ∣ n.totient := by
  set m := ordCompl[q] n with hm
  have hsplit : n = q ^ e * m := by
    rw [hm, ← hfq]; exact (Nat.ordProj_mul_ordCompl_eq_self n q).symm
  have hcop : Nat.Coprime (q ^ e) m := (Nat.coprime_ordCompl hq hn).pow_left e
  have htot : n.totient = (q ^ e).totient * m.totient := by
    rw [hsplit, Nat.totient_mul hcop]
  rw [htot, Nat.totient_prime_pow hq he]
  exact (dvd_mul_right (q ^ (e - 1)) (q - 1)).mul_right _

/-- For squarefree `n` the maximal exponent `a n` is at most `1`. -/
theorem a_le_one_of_squarefree {n : ℕ} (hn : Squarefree n) : a n ≤ 1 := by
  unfold a; apply Finset.sup_le; intro p hp; exact hn.natFactorization_le_one p

/-- For `n ≥ 2` the maximal exponent `a n` is at least `1`. -/
theorem one_le_a_of_two_le {n : ℕ} (hn : 2 ≤ n) : 1 ≤ a n := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  unfold a
  have hmem : p ∈ n.factorization.support := by
    rw [Nat.support_factorization, Nat.mem_primeFactors]; exact ⟨hp, hpd, by omega⟩
  have h1 : 1 ≤ n.factorization p := by
    rw [← hp.dvd_iff_one_le_factorization (by omega)]; exact hpd
  exact le_trans h1 (Finset.le_sup hmem)

/--
**Non-squarefree case is impossible.**

If `n > 4` is *not* squarefree and `φ n ∣ (n - a n)`, we derive a contradiction.

Sketch: let `e = a n ≥ 2` be the maximal exponent, attained at a prime `q`
(so `q ^ e ‖ n`).  Then `q ^ (e-1) ∣ φ n ∣ (n - e)` and `q ^ (e-1) ∣ n`, hence
`q ^ (e-1) ∣ e`.  Since `q ≥ 2` this forces `2 ^ (e-1) ≤ e`, i.e. `e ≤ 2`, so
`e = 2` and `q = 2`.  Writing `n = 4 t` with `t` odd, `t ≥ 3`, the hypothesis
becomes `φ t ∣ 2 t - 1`; but `φ t` is even while `2 t - 1` is odd. -/
theorem nonsquarefree_impossible {n : ℕ} (hn4 : 4 < n) (hsf : ¬ Squarefree n)
    (hdvd : n.totient ∣ (n - a n)) : False := by
  have hn0 : n ≠ 0 := by omega
  set e := a n with he_def
  have hsupp_ne : n.factorization.support.Nonempty := by
    rw [Nat.support_factorization, Nat.nonempty_primeFactors]; omega
  obtain ⟨q, hqmem, hqsup⟩ := Finset.exists_mem_eq_sup _ hsupp_ne n.factorization
  have hq : q.Prime := Nat.prime_of_mem_primeFactors (by rwa [← Nat.support_factorization])
  have hfq : n.factorization q = e := by rw [he_def]; unfold a; rw [← hqsup]
  have hq2le := hq.two_le
  have he2 : 2 ≤ e := by
    rw [Nat.squarefree_iff_factorization_le_one hn0, not_forall] at hsf
    obtain ⟨p, hp⟩ := hsf
    have hp2 : 2 ≤ n.factorization p := by omega
    have hpmem : p ∈ n.factorization.support := by rw [Finsupp.mem_support_iff]; omega
    have hle : n.factorization p ≤ e := Finset.le_sup hpmem
    omega
  have hpt : q ^ (e - 1) ∣ n.totient := pow_pred_dvd_totient hn0 hq hfq (by omega)
  have hpne : q ^ (e - 1) ∣ (n - e) := hpt.trans hdvd
  have hqe_n : q ^ e ∣ n := by rw [← hfq]; exact Nat.ordProj_dvd n q
  have hpn : q ^ (e - 1) ∣ n := (pow_dvd_pow q (by omega)).trans hqe_n
  have hen : e ≤ n := by
    have hqen : q ^ e ≤ n := Nat.le_of_dvd (by omega) hqe_n
    have h2e : e < 2 ^ e := Nat.lt_two_pow_self
    have hpq : (2 : ℕ) ^ e ≤ q ^ e := Nat.pow_le_pow_left hq2le e
    omega
  have hpe : q ^ (e - 1) ∣ e := by
    have := Nat.dvd_sub hpn hpne
    rwa [Nat.sub_sub_self hen] at this
  have hle : q ^ (e - 1) ≤ e := Nat.le_of_dvd (by omega) hpe
  have he_eq : e = 2 := by
    by_contra h
    have he3 : 3 ≤ e := by omega
    have hlt : e < 2 ^ (e - 1) := e_lt_two_pow he3
    have hpq : (2 : ℕ) ^ (e - 1) ≤ q ^ (e - 1) := Nat.pow_le_pow_left hq2le (e - 1)
    omega
  have hq_eq : q = 2 := by
    rw [he_eq] at hpe
    have hqd : q ∣ 2 := by simpa using hpe
    have : q ≤ 2 := Nat.le_of_dvd (by norm_num) hqd
    omega
  subst hq_eq
  rw [he_eq] at hfq
  set t := ordCompl[2] n with ht
  have hsplit : n = 4 * t := by
    have hmm : ordProj[2] n * t = n := Nat.ordProj_mul_ordCompl_eq_self n 2
    have hop : ordProj[2] n = 4 := by
      show 2 ^ (n.factorization 2) = 4
      rw [hfq]; norm_num
    rw [hop] at hmm
    omega
  have hcop : Nat.Coprime 4 t := by
    have hc := (Nat.coprime_ordCompl Nat.prime_two hn0).pow_left 2
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rwa [h4] at hc
  have htot4 : n.totient = 2 * t.totient := by
    have h4t : Nat.totient 4 = 2 := by decide
    rw [hsplit, Nat.totient_mul hcop, h4t]
  have ht_odd : ¬ 2 ∣ t := Nat.not_dvd_ordCompl Nat.prime_two hn0
  have ht3 : 3 ≤ t := by
    rcases Nat.lt_or_ge t 3 with h | h
    · interval_cases t <;> omega
    · exact h
  have htot_even : Even t.totient := Nat.totient_even (by omega)
  rw [htot4, he_eq] at hdvd
  have h4dvd : (4 : ℕ) ∣ 2 * t.totient := by
    obtain ⟨s, hs⟩ := htot_even
    exact ⟨s, by rw [hs]; ring⟩
  have hfin : (4 : ℕ) ∣ (n - 2) := h4dvd.trans hdvd
  rw [hsplit] at hfin
  omega

/--
A051903 (*) Are there composite numbers n > 4 such that n == a(n) (mod phi(n))?
This formalizes the conjecture that there are no such numbers.
Note: We use `¬ Nat.Prime n ∧ 4 < n` to formally express $n$ is a composite number greater than 4, as $4 < n$ implies $1 < n$.

Mathematical status of this formalization.
The statement is *equivalent to Lehmer's totient problem* (open since 1932:
"does there exist a composite `n` with `φ n ∣ (n - 1)`?").  A counterexample `n`
(composite, `n > 4`, `φ n ∣ (n - a n)`) must be squarefree — proved
unconditionally in `nonsquarefree_impossible` — and for squarefree `n` one has
`a n = 1`, so the condition reads `φ n ∣ (n - 1)` with `n` composite, i.e. `n`
is a Lehmer number.  Thus the conjecture holds iff no Lehmer numbers exist.
The reduction is fully formalized below; the remaining squarefree branch is the
open Lehmer core.
-/
theorem oeis_51903_conjecture_0 :
  ¬ ∃ n, (¬ Nat.Prime n) ∧ 4 < n ∧ Nat.totient n ∣ (n - a n) := by
  rintro ⟨n, hnp, hn4, hdvd⟩
  by_cases hsf : Squarefree n
  · -- Squarefree case: `a n = 1`, so `hdvd : φ n ∣ (n - 1)` with `n` composite,
    -- i.e. `n` is a Lehmer number.
    have ha1 : a n = 1 :=
      le_antisymm (a_le_one_of_squarefree hsf) (one_le_a_of_two_le (by omega))
    rw [ha1] at hdvd
    -- `n` must be odd: if `n` were even then `φ n` is even but `n - 1` is odd.
    have hodd : ¬ 2 ∣ n := by
      intro hev
      have he : Even n.totient := Nat.totient_even (by omega)
      exact (by omega : ¬ 2 ∣ (n - 1)) (he.two_dvd.trans hdvd)
    -- The remaining case — `n` an odd squarefree composite with `φ n ∣ (n - 1)` —
    -- is exactly the set of Lehmer numbers, whose non-existence is Lehmer's
    -- totient problem (open since 1932).  No such `n` is known.
    sorry
  · -- Non-squarefree case: impossible.
    exact nonsquarefree_impossible hn4 hsf hdvd

