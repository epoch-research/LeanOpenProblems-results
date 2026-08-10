import Submission.Jacob

open Finset

namespace Jacob

open Polynomial

/-- **Tower level 1 (ring version).**  In a commutative ring `R` in which
`(p:R)^6 = 0`, and with `p ∣ A`, `p ∣ B`, we have `C(pA, pB) = C(A, B)`.

The proof reuses the polynomial machinery of `choose_mul_congr_aux`
(the polynomial `Q`, the identity `(1+X)^p = 1 + X^p + p•Q`, and the coefficient
lemmas).  The binomial expansion writes the difference as a finite sum

  `C(pA,pB) - C(A,B) = ∑_{k<A} p^{A-k} · C(A,k) · coeff_{pB}((1+X^p)^k · Q^{A-k})`.

All terms with `A-k = 1` (one `Q`-factor) or `A-k ≥ 6` vanish and are handled
here, sorry-free, reducing the whole statement to the **critical sum** over the
indices with `2 ≤ A-k ≤ 5`.  That critical sum is where the higher-order
Wolstenholme / Glaisher congruences are needed; it is isolated as the single
labelled `sorry` `hcrit`. -/
lemma choose_mul_congr_tower {R : Type*} [CommRing R] (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp6 : (p : R) ^ 6 = 0) (A B : ℕ) (hpA : p ∣ A) (hpB : p ∣ B) :
    ((Nat.choose (p * A) (p * B) : R)) = (Nat.choose A B : R) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  -- The polynomial Q with Q.coeff k = ↑(C(p,k)/p)  (verbatim from `choose_mul_congr_aux`)
  set Q : R[X] := ∑ k ∈ Finset.Icc 1 (p - 1),
      Polynomial.monomial k ((Nat.choose p k / p : ℕ) : R) with hQdef
  have hQnat : ∀ i, ¬ (1 ≤ i ∧ i ≤ p - 1) → Nat.choose p i / p = 0 := by
    intro i hi
    rw [not_and_or] at hi
    rcases hi with h | h
    · have hi0 : i = 0 := by omega
      subst hi0
      rw [Nat.choose_zero_right]
      exact Nat.div_eq_of_lt (by omega)
    · have hip : p ≤ i := by omega
      rcases eq_or_lt_of_le hip with h1 | h1
      · rw [← h1, Nat.choose_self]
        exact Nat.div_eq_of_lt (by omega)
      · rw [Nat.choose_eq_zero_of_lt h1, Nat.zero_div]
  have hQc : ∀ i, Q.coeff i = ((Nat.choose p i / p : ℕ) : R) := by
    intro i
    rw [hQdef, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.Icc 1 (p - 1)) i
        (fun k => ((Nat.choose p k / p : ℕ) : R))]
    by_cases hi : i ∈ Finset.Icc 1 (p - 1)
    · rw [if_pos hi]
    · rw [if_neg hi]
      rw [Finset.mem_Icc] at hi
      rw [hQnat i hi]; simp
  have hQout : ∀ i, ¬ (1 ≤ i ∧ i ≤ p - 1) → Q.coeff i = 0 := by
    intro i hi
    rw [hQc, hQnat i hi]; simp
  have hQsupp : ∀ j, p ∣ j → Q.coeff j = 0 := by
    intro j hj
    apply hQout
    rintro ⟨h1, h2⟩
    have := Nat.le_of_dvd (by omega) hj
    omega
  have hAcoeff : ∀ (n i : ℕ), ((1 + X ^ p : R[X]) ^ n).coeff i
      = if p ∣ i then ((Nat.choose n (i / p) : ℕ) : R) else 0 := by
    intro n i
    have hexp : Polynomial.expand R p ((1 + X) ^ n) = (1 + X ^ p) ^ n := by
      rw [map_pow, map_add, map_one, Polynomial.expand_X]
    rw [← hexp, Polynomial.coeff_expand (show 0 < p by omega)]
    by_cases hpi : p ∣ i
    · rw [if_pos hpi, if_pos hpi, Polynomial.coeff_one_add_X_pow]
    · rw [if_neg hpi, if_neg hpi]
  have hAsupp : ∀ (n i : ℕ), ¬ (p ∣ i) → ((1 + X ^ p : R[X]) ^ n).coeff i = 0 := by
    intro n i hi
    rw [hAcoeff n i, if_neg hi]
  have hprodzero : ∀ (U V : R[X]), (∀ i, ¬ (p ∣ i) → U.coeff i = 0) →
      (∀ j, p ∣ j → V.coeff j = 0) → ∀ m, p ∣ m → (U * V).coeff m = 0 := by
    intro U V hU hV m hm
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    by_cases h1 : p ∣ ij.1
    · have hm' : p ∣ ij.1 + ij.2 := by rw [hij]; exact hm
      have h2 : p ∣ ij.2 := (Nat.dvd_add_right h1).mp hm'
      rw [hV ij.2 h2, mul_zero]
    · rw [hU ij.1 h1, zero_mul]
  -- the fundamental identity (1+X)^p = 1 + X^p + p • Q
  have hP : ((1 + X : R[X])) ^ p = (1 + X ^ p) + (p : R) • Q := by
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_one_add_X_pow, Polynomial.coeff_add, Polynomial.coeff_add,
        Polynomial.coeff_one, Polynomial.coeff_X_pow, Polynomial.coeff_smul, hQc, smul_eq_mul]
    by_cases h0 : n = 0
    · rw [if_pos h0, if_neg (show ¬ n = p by omega)]
      subst h0
      rw [Nat.choose_zero_right, Nat.div_eq_of_lt (show 1 < p by omega)]
      simp
    · by_cases hp' : n = p
      · rw [if_neg h0, if_pos hp', hp']
        rw [Nat.choose_self, Nat.div_eq_of_lt (show 1 < p by omega)]
        simp
      · rw [if_neg h0, if_neg hp']
        by_cases hle : n ≤ p - 1
        · have hdvd : p ∣ Nat.choose p n := hp.dvd_choose_self h0 (by omega)
          have hc : p * (Nat.choose p n / p) = Nat.choose p n := Nat.mul_div_cancel' hdvd
          have hcR : ((Nat.choose p n : ℕ) : R) = (p : R) * ((Nat.choose p n / p : ℕ) : R) := by
            rw [← Nat.cast_mul, hc]
          rw [hcR]; ring
        · have hgt : p < n := by omega
          rw [Nat.choose_eq_zero_of_lt hgt]
          simp
  -- the term function of the binomial expansion (indexed by k = number of (1+X^p)-factors)
  set f : ℕ → R := fun k =>
      (p : R) ^ (A - k) * ((1 + X ^ p : R[X]) ^ k * Q ^ (A - k)).coeff (p * B)
        * (Nat.choose A k : R) with hf
  -- binomial expansion of C(pA,pB)
  have hexpand : (Nat.choose (p * A) (p * B) : R) = ∑ k ∈ Finset.range (A + 1), f k := by
    rw [show ((Nat.choose (p * A) (p * B) : R)) = ((1 + X : R[X]) ^ (p * A)).coeff (p * B) from
          (Polynomial.coeff_one_add_X_pow R (p * A) (p * B)).symm,
        pow_mul, hP, add_pow, Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [hf]
    rw [_root_.smul_pow, ← map_natCast (Polynomial.C) (Nat.choose A k),
        Polynomial.coeff_mul_C, mul_smul_comm, Polynomial.coeff_smul, smul_eq_mul]
  -- the k = A term equals C(A,B)
  have hlast : f A = (Nat.choose A B : R) := by
    simp only [hf, Nat.sub_self, pow_zero, mul_one, one_mul, Nat.choose_self, Nat.cast_one]
    rw [hAcoeff A (p * B), if_pos ⟨B, rfl⟩, Nat.mul_div_cancel_left B hp.pos]
  -- terms with A-k = 1 or A-k ≥ 6 vanish
  have hvanish : ∀ k ∈ Finset.range A,
      k ∉ (Finset.range A).filter (fun k => 2 ≤ A - k ∧ A - k ≤ 5) → f k = 0 := by
    intro k hk hkS
    rw [Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_range] at hkS
    push_neg at hkS
    have hnP := hkS hk
    simp only [hf]
    rcases (by omega : A - k = 1 ∨ 6 ≤ A - k) with h1 | h6
    · rw [h1, pow_one, pow_one,
        hprodzero ((1 + X ^ p) ^ k) Q (hAsupp k) hQsupp (p * B) ⟨B, rfl⟩]
      ring
    · have hz : (p : R) ^ (A - k) = 0 := by
        obtain ⟨d, hd⟩ : ∃ d, A - k = 6 + d := ⟨A - k - 6, by omega⟩
        rw [hd, pow_add, hp6, zero_mul]
      rw [hz]; ring
  -- the CRITICAL sum: the k=2,3,4,5 (in #Q-factors) terms sum to zero.
  -- This is where the higher-order Wolstenholme/Glaisher congruences enter.
  have hcrit : ∑ k ∈ (Finset.range A).filter (fun k => 2 ≤ A - k ∧ A - k ≤ 5), f k = 0 := by
    -- The two boundary cases `A = 0` and `B = 0` are elementary and dispatched here,
    -- leaving only the genuine second-order case `A, B ≥ p`.
    rcases Nat.eq_zero_or_pos A with hA0 | hApos
    · -- `A = 0`: the index set `range 0` is empty, so the sum is empty.
      subst hA0; simp
    rcases Nat.eq_zero_or_pos B with hB0 | hBpos
    · -- `B = 0`: every term has a coefficient of `X^0`, and since `Q` has no constant
      -- term while each critical term carries at least two `Q`-factors, that coefficient
      -- vanishes.
      subst hB0
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      simp only [hf, Nat.mul_zero]
      have hcoeff0 : ((1 + X ^ p : R[X]) ^ k * Q ^ (A - k)).coeff 0 = 0 := by
        rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul,
            Polynomial.eval_pow, Polynomial.eval_pow]
        have hQe : (Q : R[X]).eval 0 = 0 := by
          rw [← Polynomial.coeff_zero_eq_eval_zero]; exact hQout 0 (by omega)
        rw [hQe, zero_pow (by omega : A - k ≠ 0), mul_zero]
      rw [hcoeff0, mul_zero, zero_mul]
    · -- **The genuine second-order case: `A ≥ p ≥ 5` and `B ≥ p ≥ 5`.**
      -- This is the heart of the Jacobsthal–Kazandzidis "tower level 1".  Writing
      -- `j = A - k` for the number of `Q`-factors, the sum is
      --   `∑_{j=2}^{5} p^j · C(A,j) · g_j`,
      -- with `g_j = ∑_i C(A-j, i) · (Q^j).coeff (p·(B-i))`.
      -- Because `p ∣ A` and `p ∣ B` (so `v_p(A), v_p(B), v_p(A-B) ≥ 1`), the required
      -- congruence is Jacobsthal's refinement
      --   `p^{3 + v_p(A) + v_p(B) + v_p(A-B)} ∣ C(pA,pB) - C(A,B)`,
      -- whose leading order `3` comes from Wolstenholme (`Wolst.sum_inv` mod `p²`,
      -- `Wolst.sum_inv_sq` mod `p`), and whose extra factor of `p^3` here requires the
      -- *second-order* harmonic congruences of Glaisher type:
      --   `H_1 := ∑_{r=1}^{p-1} 1/r ≡ -(p²/3)·B_{p-3}  (mod p³)`  and
      --   `H_2 := ∑_{r=1}^{p-1} 1/r² ≡ (2p/3)·B_{p-3}   (mod p²)`,
      -- the Bernoulli terms cancelling between the `j=2` (`H_2`) and the folded-`H_1`
      -- contributions via the exact rational identity  `2·H_1 = p·∑_r 1/(r(p-r))`.
      -- Formalizing this cancellation (Bernoulli `B_{p-3}` bookkeeping) is the sole
      -- remaining gap.
      sorry
  -- the whole "range A" sum vanishes, reducing to the critical sum
  have hsum0 : ∑ k ∈ Finset.range A, f k = 0 := by
    rw [← Finset.sum_subset (Finset.filter_subset _ _) hvanish]
    exact hcrit
  -- assemble
  rw [hexpand, Finset.sum_range_succ, hlast, hsum0, zero_add]

/-- **Tower level 1** of the Jacobsthal–Kazandzidis congruence:
if `p ≥ 5` is prime and `p ∣ A`, `p ∣ B`, then
`p^6 ∣ C(pA, pB) - C(A, B)`. -/
theorem tower1 (p A B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hBA : B ≤ A) (hpA : p ∣ A) (hpB : p ∣ B) :
    (p : ℤ) ^ 6 ∣ ((Nat.choose (p * A) (p * B) : ℤ) - Nat.choose A B) := by
  have hp6 : ((p : ZMod (p ^ 6))) ^ 6 = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hcong := choose_mul_congr_tower (R := ZMod (p ^ 6)) p hp hp5 hp6 A B hpA hpB
  rw [show (p ^ 6 : ℤ) = ((p ^ 6 : ℕ) : ℤ) from by push_cast; ring,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [sub_eq_zero]
  exact hcong

end Jacob

#print axioms Jacob.tower1
