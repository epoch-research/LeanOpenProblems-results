import Submission.PrivateSquares

/-!
# A finite obstruction to polynomial graphs of complementary factors

Let `R` be a finite set of natural numbers, represented as `n = m n * p n ^ 2`,
and suppose `(b : ℤ) * m n = F.eval (n : ℤ)` on `R` for an integer polynomial `F`.
The polynomial is evaluated at the actual number `n`, not at an interval offset.

* If `F.eval 0 ≠ 0`, every cofactor divides `F.eval 0`. Distinct cofactors therefore
  bound `R.card` by the number of positive divisors of `Int.natAbs (F.eval 0)`.
  This case needs only `m n ∣ n`, not primality or positivity of the cofactors.
* If `F.eval 0 = 0`, factoring out `X` and cancelling the positive cofactors shows
  that every `p n ^ 2` divides `b`. For distinct prime bases their product divides
  `b`. If also `H < p n` and `0 < b`, then `H ^ (2 * R.card) ≤ b`.

Consequently, under `2 ≤ H` and `b ≤ H ^ C`, either the nonzero-constant divisor
bound holds or `2 * R.card ≤ C`. These are finite necessary conditions for such
an arithmetic graph, not a squarefree-gap conjecture or an asymptotic divisor bound.
The empty set is allowed throughout; its product is `1`, and `0 < b` ensures `1 ≤ b`.
-/

open Finset

namespace PolynomialGraph

/-- A cofactor dividing both the argument and the polynomial value divides the
constant value. No prime-square representation is needed. -/
theorem dvd_eval_zero_of_dvd_eval (F : Polynomial ℤ) (n m : ℕ)
    (hmn : m ∣ n) (hmF : (m : ℤ) ∣ F.eval (n : ℤ)) :
    (m : ℤ) ∣ F.eval 0 := by
  have hnF : (n : ℤ) ∣ F.eval (n : ℤ) - F.eval 0 := by
    simpa only [sub_zero] using Polynomial.sub_dvd_eval_sub (n : ℤ) 0 F
  have hmnZ : (m : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hmn
  simpa only [sub_sub_cancel] using dvd_sub hmF (hmnZ.trans hnF)

/-- The nonzero-constant case: injective cofactors map into the positive divisors
of the absolute constant value. Neither primality nor `0 < b` is required. -/
theorem card_le_divisors_of_eval_zero_ne_zero
    (R : Finset ℕ) (m : ℕ → ℕ) (F : Polynomial ℤ) (b : ℕ)
    (hmn : ∀ n ∈ R, m n ∣ n) (hminj : Set.InjOn m (R : Set ℕ))
    (hgraph : ∀ n ∈ R, (b : ℤ) * (m n : ℤ) = F.eval (n : ℤ))
    (hF : F.eval 0 ≠ 0) :
    R.card ≤ (Int.natAbs (F.eval 0)).divisors.card := by
  apply card_le_card_of_injOn m ?_ hminj
  intro n hn
  apply Nat.mem_divisors.mpr
  refine ⟨?_, Int.natAbs_ne_zero.mpr hF⟩
  apply Int.natCast_dvd.mp
  apply dvd_eval_zero_of_dvd_eval F n (m n) (hmn n hn)
  rw [← hgraph n hn]
  exact dvd_mul_left (m n : ℤ) (b : ℤ)

/-- Factoring out `X` in the zero-constant case gives an exact integer equality
for `b` after cancelling each positive cofactor. Primality is not needed. -/
theorem exists_factor_of_eval_zero_eq_zero
    (R : Finset ℕ) (p m : ℕ → ℕ) (F : Polynomial ℤ) (b : ℕ)
    (hm : ∀ n ∈ R, 0 < m n)
    (hrep : ∀ n ∈ R, m n * p n ^ 2 = n)
    (hgraph : ∀ n ∈ R, (b : ℤ) * (m n : ℤ) = F.eval (n : ℤ))
    (hF : F.eval 0 = 0) :
    ∃ G : Polynomial ℤ, F = Polynomial.X * G ∧
      ∀ n ∈ R, (b : ℤ) = (p n : ℤ) ^ 2 * G.eval (n : ℤ) := by
  have hXdvd : (Polynomial.X : Polynomial ℤ) ∣ F := by
    simpa only [Polynomial.C_0, sub_zero] using
      (Polynomial.dvd_iff_isRoot.mpr hF : Polynomial.X - Polynomial.C (0 : ℤ) ∣ F)
  obtain ⟨G, hG⟩ := hXdvd
  refine ⟨G, hG, ?_⟩
  intro n hn
  have hmZ : (m n : ℤ) ≠ 0 := by exact_mod_cast (hm n hn).ne'
  have hrepZ : (m n : ℤ) * (p n : ℤ) ^ 2 = (n : ℤ) := by
    exact_mod_cast hrep n hn
  apply mul_left_cancel₀ hmZ
  calc
    (m n : ℤ) * (b : ℤ) = (b : ℤ) * (m n : ℤ) := mul_comm _ _
    _ = F.eval (n : ℤ) := hgraph n hn
    _ = (n : ℤ) * G.eval (n : ℤ) := by
      rw [hG, Polynomial.eval_mul, Polynomial.eval_X]
    _ = (m n : ℤ) * ((p n : ℤ) ^ 2 * G.eval (n : ℤ)) := by
      rw [← hrepZ, mul_assoc]

/-- Every represented square divides the denominator in the zero-constant case.
This assertion is in `ℕ`, even though the polynomial has integer coefficients. -/
theorem squares_dvd_of_eval_zero_eq_zero
    (R : Finset ℕ) (p m : ℕ → ℕ) (F : Polynomial ℤ) (b : ℕ)
    (hm : ∀ n ∈ R, 0 < m n)
    (hrep : ∀ n ∈ R, m n * p n ^ 2 = n)
    (hgraph : ∀ n ∈ R, (b : ℤ) * (m n : ℤ) = F.eval (n : ℤ))
    (hF : F.eval 0 = 0) :
    ∀ n ∈ R, p n ^ 2 ∣ b := by
  obtain ⟨G, _, hG⟩ := exists_factor_of_eval_zero_eq_zero R p m F b hm hrep hgraph hF
  intro n hn
  apply Int.natCast_dvd_natCast.mp
  refine ⟨G.eval (n : ℤ), ?_⟩
  simpa only [Nat.cast_pow] using hG n hn

/-- Squares of distinct primes are pairwise coprime, so individual divisibility
implies divisibility by their entire finite product, including the empty product. -/
theorem prod_prime_squares_dvd (R : Finset ℕ) (p : ℕ → ℕ) (b : ℕ)
    (hp : ∀ n ∈ R, (p n).Prime) (hpinj : Set.InjOn p (R : Set ℕ))
    (hdiv : ∀ n ∈ R, p n ^ 2 ∣ b) :
    (∏ n ∈ R, p n ^ 2) ∣ b := by
  apply Finset.prod_dvd_of_isRelPrime ?_ hdiv
  intro n hn n' hn' hne
  apply Nat.coprime_iff_isRelPrime.mp
  exact Nat.coprime_pow_primes 2 2 (hp n hn) (hp n' hn')
    (fun he => hne (hpinj hn hn' he))

/-- The product of the distinct prime squares divides `b` when the constant
value vanishes. Injectivity of the complementary factors is not required. -/
theorem prod_squares_dvd_of_eval_zero_eq_zero
    (R : Finset ℕ) (p m : ℕ → ℕ) (F : Polynomial ℤ) (b : ℕ)
    (hm : ∀ n ∈ R, 0 < m n) (hp : ∀ n ∈ R, (p n).Prime)
    (hrep : ∀ n ∈ R, m n * p n ^ 2 = n)
    (hpinj : Set.InjOn p (R : Set ℕ))
    (hgraph : ∀ n ∈ R, (b : ℤ) * (m n : ℤ) = F.eval (n : ℤ))
    (hF : F.eval 0 = 0) :
    (∏ n ∈ R, p n ^ 2) ∣ b := by
  exact prod_prime_squares_dvd R p b hp hpinj
    (squares_dvd_of_eval_zero_eq_zero R p m F b hm hrep hgraph hF)

/-- Large prime bases force exponential growth in the size of `R` in the
zero-constant case. This even holds without a positivity hypothesis on `H`.
For `R = ∅`, the conclusion is `1 ≤ b`, supplied by `hb`. -/
theorem pow_card_le_of_eval_zero_eq_zero
    (R : Finset ℕ) (p m : ℕ → ℕ) (F : Polynomial ℤ) (H b : ℕ)
    (hb : 0 < b)
    (hrep : ∀ n ∈ R, (p n).Prime ∧ H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n)
    (hpinj : Set.InjOn p (R : Set ℕ))
    (hgraph : ∀ n ∈ R, (b : ℤ) * (m n : ℤ) = F.eval (n : ℤ))
    (hF : F.eval 0 = 0) :
    H ^ (2 * R.card) ≤ b := by
  have hdiv : (∏ n ∈ R, p n ^ 2) ∣ b :=
    prod_squares_dvd_of_eval_zero_eq_zero R p m F b
      (fun n hn => (hrep n hn).2.2.1) (fun n hn => (hrep n hn).1)
      (fun n hn => (hrep n hn).2.2.2) hpinj hgraph hF
  calc
    H ^ (2 * R.card) = ∏ _n ∈ R, H ^ 2 := by rw [prod_const, pow_mul]
    _ ≤ ∏ n ∈ R, p n ^ 2 :=
      prod_le_prod' (fun n hn => Nat.pow_le_pow_left (hrep n hn).2.1.le 2)
    _ ≤ b := Nat.le_of_dvd hb hdiv

/-- If `b ≤ H ^ C` with `H ≥ 2`, the zero-constant case has at most `C / 2`
points, expressed without division as `2 * R.card ≤ C`. -/
theorem two_mul_card_le_of_eval_zero_eq_zero
    (R : Finset ℕ) (p m : ℕ → ℕ) (F : Polynomial ℤ) (H b C : ℕ)
    (hb : 0 < b) (hH : 2 ≤ H) (hbC : b ≤ H ^ C)
    (hrep : ∀ n ∈ R, (p n).Prime ∧ H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n)
    (hpinj : Set.InjOn p (R : Set ℕ))
    (hgraph : ∀ n ∈ R, (b : ℤ) * (m n : ℤ) = F.eval (n : ℤ))
    (hF : F.eval 0 = 0) :
    2 * R.card ≤ C := by
  apply (Nat.pow_le_pow_iff_right (show 1 < H by omega)).mp
  exact (pow_card_le_of_eval_zero_eq_zero R p m F H b hb hrep hpinj hgraph hF).trans hbC

/-- The natural-number division version of the zero-constant cardinality bound. -/
theorem card_le_half_of_eval_zero_eq_zero
    (R : Finset ℕ) (p m : ℕ → ℕ) (F : Polynomial ℤ) (H b C : ℕ)
    (hb : 0 < b) (hH : 2 ≤ H) (hbC : b ≤ H ^ C)
    (hrep : ∀ n ∈ R, (p n).Prime ∧ H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n)
    (hpinj : Set.InjOn p (R : Set ℕ))
    (hgraph : ∀ n ∈ R, (b : ℤ) * (m n : ℤ) = F.eval (n : ℤ))
    (hF : F.eval 0 = 0) :
    R.card ≤ C / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  simpa only [mul_comm] using
    two_mul_card_le_of_eval_zero_eq_zero R p m F H b C hb hH hbC hrep hpinj hgraph hF

/-- Finite polynomial-graph obstruction: either the nonzero constant bounds the
number of distinct cofactors by its divisor count, or the denominator exponent
bounds twice the number of points. No asymptotic divisor estimate is assumed. -/
theorem polynomial_graph_card_bound
    (R : Finset ℕ) (p m : ℕ → ℕ) (F : Polynomial ℤ) (H b C : ℕ)
    (hb : 0 < b) (hH : 2 ≤ H) (hbC : b ≤ H ^ C)
    (hrep : ∀ n ∈ R, (p n).Prime ∧ H < p n ∧ 0 < m n ∧ m n * p n ^ 2 = n)
    (hpinj : Set.InjOn p (R : Set ℕ)) (hminj : Set.InjOn m (R : Set ℕ))
    (hgraph : ∀ n ∈ R, (b : ℤ) * (m n : ℤ) = F.eval (n : ℤ)) :
    (F.eval 0 ≠ 0 ∧ R.card ≤ (Int.natAbs (F.eval 0)).divisors.card) ∨
      2 * R.card ≤ C := by
  by_cases hF : F.eval 0 = 0
  · exact Or.inr
      (two_mul_card_le_of_eval_zero_eq_zero R p m F H b C hb hH hbC hrep hpinj hgraph hF)
  · refine Or.inl ⟨hF, ?_⟩
    apply card_le_divisors_of_eval_zero_ne_zero R m F b ?_ hminj hgraph hF
    intro n hn
    exact ⟨p n ^ 2, (hrep n hn).2.2.2.symm⟩

end PolynomialGraph
