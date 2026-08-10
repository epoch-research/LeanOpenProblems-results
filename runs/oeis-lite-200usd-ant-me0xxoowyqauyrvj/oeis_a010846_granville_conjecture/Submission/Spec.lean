import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A010846: Number of numbers $\le n$ whose set of prime factors is a subset of the set of prime factors of $n$.
-/
def a (n : ℕ) : ℕ :=
  (Icc 1 n).filter (fun k => primeFactors k ⊆ primeFactors n) |>.card

/-
Granville's ABC-Conjecture implies that for any $\epsilon > 0$,
the function $a(n)$ is bounded below by $(\log n)^{1 - \epsilon}$ for sufficiently large $n$.
This is a formalization of a claim implied by the context:
OEIS C: "This function of n appears in an ABC-conjecture by Andrew Granville. See Goldfeld."
Granville (via Goldfeld) showed that ABC conjecture $\iff$ $\forall \epsilon > 0, \exists N, \forall n > N, a(n) \ge (\log n)^{1-\epsilon}$.
-/
/-- Auxiliary lemma: for a prime `p`, the only `k ∈ [1, p]` whose prime factors are a
subset of those of `p` are `k = 1` and `k = p`, hence `a p = 2`. -/
theorem a_prime (p : ℕ) (hp : p.Prime) : a p = 2 := by
  unfold a
  have hset : ((Icc 1 p).filter (fun k => primeFactors k ⊆ primeFactors p)) = {1, p} := by
    ext k
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hk1, hkp⟩, hsub⟩
      rcases eq_or_lt_of_le hk1 with h | h
      · left; exact h.symm
      · right
        have hk1' : 1 < k := h
        have hpos : 0 < k := by omega
        rw [hp.primeFactors] at hsub
        have hne : (primeFactors k).Nonempty := by
          rw [Nat.nonempty_primeFactors]
          exact hk1'
        obtain ⟨q, hq⟩ := hne
        have hqp : q = p := by
          have := hsub hq
          simpa using this
        subst hqp
        have hqdvd := Nat.dvd_of_mem_primeFactors hq
        have hle := Nat.le_of_dvd hpos hqdvd
        omega
    · rintro (rfl | rfl)
      · refine ⟨⟨le_refl 1, hp.one_le⟩, ?_⟩
        simp
      · refine ⟨⟨hp.one_le, le_refl k⟩, subset_refl _⟩
  rw [hset]
  rw [Finset.card_pair hp.ne_one.symm]

/-- The conjecture as literally stated is **false**: for any prime `p` we have `a p = 2`,
but `(log p)^{1-ε} → ∞`, so the lower bound fails for arbitrarily large (prime) `n`. -/
theorem oeis_a010846_granville_conjecture.disproof :
  ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (Real.log n) ^ (1 - ε) ≤ a n) := by
  intro h
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max N 60)
  have hpge : N ≤ p := le_trans (le_max_left _ _) hpN
  have hp60 : (55:ℝ) ≤ p := by
    have : (60:ℕ) ≤ p := le_trans (le_max_right _ _) hpN
    have := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at this ⊢; linarith
  have hkey := hN p hpge
  rw [a_prime p hp] at hkey
  have hexp : (1:ℝ) - 1/2 = 1/2 := by norm_num
  rw [hexp] at hkey
  have hlog : (4:ℝ) < Real.log p := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have heq : Real.exp 4 = (Real.exp 1)^4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [heq]
    have he := Real.exp_one_lt_d9
    have hpos := Real.exp_pos (1:ℝ)
    have h2 : Real.exp 1 ^ 2 < 7.4 := by nlinarith
    nlinarith [h2, sq_nonneg (Real.exp 1)]
  have h4 : (4:ℝ)^((1:ℝ)/2) = 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, ← Real.rpow_natCast (2:ℝ) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hgt : (2:ℝ) < (Real.log p)^((1:ℝ)/2) :=
    calc (2:ℝ) = (4:ℝ)^((1:ℝ)/2) := h4.symm
      _ < (Real.log p)^((1:ℝ)/2) := Real.rpow_lt_rpow (by norm_num) hlog (by norm_num)
  push_cast at hkey
  linarith
