import Submission.SmoothPrimePigeonhole

/-!
# A conditional endpoint criterion for totient fibers

This file proves a conditional bridge, not a settlement of the endpoint
conjecture. `SmoothPrimeEndpointCertificates` is a proposition describing
finite smooth-prime certificates for every pair of natural numbers `r, B`.
It is an explicit hypothesis of the endpoint theorem; its existence is not
asserted here, and no new axiom is introduced.

The finite pigeonhole theorem supplies a positive `n ≥ B` with `n ≤ X ^ k`
and `choose P.card k ≤ fiberCard n * C`, where
`C = (k * X + 1) ^ (Y + 1)`. The certificate's strict inequality, together
with these bounds, gives `n ^ r < fiberCard n ^ (r + 1)` by cancellation in
`ℕ`. A generic Archimedean and real-power argument then gives infinitely
many `n` with `fiberCard n > n ^ (1 - ε)` for each `ε > 0`.

Independently of the certificate hypothesis, the range `ε ≥ 1` follows
from two explicit preimages of each totient value `2 ^ (k + 1)`.
All cardinalities use the existing `fiberCard` definition and finite-fiber
lemmas. This file does not import `Submission.Spec` or use its theorems.
-/

namespace Erdos821Aux

open Nat

/-- Taking a positive real power converts a natural power inequality to
an inequality with exponent `r / (r + 1)`. No positivity assumption on
`n` or `a` is needed for this conversion. -/
theorem rpow_ratio_lt_of_nat_pow_lt {n a r : ℕ}
    (h : n ^ r < a ^ (r + 1)) :
    (n : ℝ) ^ ((r : ℝ) / ((r : ℝ) + 1)) < (a : ℝ) := by
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hcast : (n : ℝ) ^ r < (a : ℝ) ^ (r + 1) := by exact_mod_cast h
  apply (Real.rpow_lt_rpow_iff
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Nat.cast_nonneg a) hr).mp
  rw [← Real.rpow_mul (Nat.cast_nonneg n),
    div_mul_cancel₀ _ hr.ne', Real.rpow_natCast]
  simpa only [← Real.rpow_natCast, Nat.cast_add, Nat.cast_one] using hcast

/-- Generic endpoint criterion: unbounded positive natural witnesses to
`n ^ r < f n ^ (r + 1)`, for every `r`, imply every positive-ε endpoint
inequality infinitely often. This theorem asserts only an implication. -/
theorem endpoint_of_unbounded_nat_power_lt (f : ℕ → ℕ)
    (h : ∀ r B : ℕ, ∃ n : ℕ, B ≤ n ∧ 0 < n ∧ n ^ r < f n ^ (r + 1)) :
    ∀ ε > (0 : ℝ), {n : ℕ | (f n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  intro ε hε
  -- The Archimedean property makes the reciprocal smaller than any positive ε.
  obtain ⟨r, hr⟩ := exists_nat_one_div_lt hε
  have hrecip : 1 / ((r : ℝ) + 1) ≤ ε := hr.le
  have hexp : 1 - ε ≤ (r : ℝ) / ((r : ℝ) + 1) := by
    have heq : (r : ℝ) / ((r : ℝ) + 1) = 1 - 1 / ((r : ℝ) + 1) := by
      field_simp
      ring
    rw [heq]
    linarith
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨n, hnB, hnpos, hnpow⟩ := h r (B + 1)
  refine ⟨n, ?_, lt_of_lt_of_le (Nat.lt_succ_self B) hnB⟩
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hnpos
  exact (Real.rpow_le_rpow_of_exponent_le hnreal hexp).trans_lt
    (rpow_ratio_lt_of_nat_pow_lt hnpow)

/-- A natural finite-certificate hypothesis for the endpoint bridge.
For every exponent parameter `r` and lower threshold `B`, a finite family
of smooth shifted primes satisfies the displayed strict counting gap.
This is a defined proposition, not an axiom or a claimed existence theorem. -/
def SmoothPrimeEndpointCertificates : Prop :=
  ∀ r B : ℕ, ∃ (P : Finset ℕ) (X Y k : ℕ),
    (∀ p ∈ P, p.Prime ∧ p ≤ X ∧ ∀ q ∈ (p - 1).primeFactors, q ≤ Y) ∧
    k ≤ P.card ∧ B ≤ 2 ^ (k - 1) ∧
    X ^ (k * r) * ((k * X + 1) ^ (Y + 1)) ^ (r + 1) <
      (Nat.choose P.card k) ^ (r + 1)

/-- The quantitative squarefree pigeonhole theorem turns the finite
certificates into unbounded positive witnesses to the natural power
inequalities for the full totient fibers. -/
theorem unbounded_nat_power_lt_of_smooth_prime_certificates
    (hcert : SmoothPrimeEndpointCertificates) :
    ∀ r B : ℕ, ∃ n : ℕ,
      B ≤ n ∧ 0 < n ∧ n ^ r < fiberCard n ^ (r + 1) := by
  intro r B
  obtain ⟨P, X, Y, k, hP, hk, hB, hgap⟩ := hcert r B
  obtain ⟨n, hnpos, hlower, hupper, _, hcount⟩ :=
    smooth_prime_pigeonhole_squarefree_with_bounds P X Y k hP hk
  let C : ℕ := (k * X + 1) ^ (Y + 1)
  change X ^ (k * r) * C ^ (r + 1) < (Nat.choose P.card k) ^ (r + 1) at hgap
  have hcountFull : Nat.choose P.card k ≤ fiberCard n * C :=
    hcount.trans (Nat.mul_le_mul_right C (squarefreeFiberCard_le_fiberCard n))
  have hupperpow : n ^ r ≤ X ^ (k * r) := by
    simpa only [Nat.pow_mul] using Nat.pow_le_pow_left hupper r
  have hstrict : n ^ r * C ^ (r + 1) < fiberCard n ^ (r + 1) * C ^ (r + 1) := by
    calc
      n ^ r * C ^ (r + 1) ≤ X ^ (k * r) * C ^ (r + 1) :=
        Nat.mul_le_mul_right _ hupperpow
      _ < (Nat.choose P.card k) ^ (r + 1) := hgap
      _ ≤ (fiberCard n * C) ^ (r + 1) := Nat.pow_le_pow_left hcountFull _
      _ = fiberCard n ^ (r + 1) * C ^ (r + 1) := mul_pow _ _ _
  exact ⟨n, hB.trans hlower, hnpos, Nat.lt_of_mul_lt_mul_right hstrict⟩

/-- Conditional endpoint bridge for the existing totient-fiber cardinality.
The finite-certificate hypothesis is required and is not established in
this file; consequently this does not settle the endpoint conjecture. -/
theorem endpoint_of_smooth_prime_certificates
    (hcert : SmoothPrimeEndpointCertificates) :
    ∀ ε > (0 : ℝ),
      {n : ℕ | (fiberCard n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite :=
  endpoint_of_unbounded_nat_power_lt fiberCard
    (unbounded_nat_power_lt_of_smooth_prime_certificates hcert)

/-- The two distinct inputs `2 ^ (k + 2)` and `3 * 2 ^ (k + 1)`
both have totient `2 ^ (k + 1)`. -/
theorem two_le_fiberCard_two_pow (k : ℕ) : 2 ≤ fiberCard (2 ^ (k + 1)) := by
  let a := 2 ^ (k + 2)
  let b := 3 * 2 ^ (k + 1)
  have ha : totient a = 2 ^ (k + 1) := by
    dsimp [a]
    convert totient_prime_pow_succ prime_two (k + 1) using 1
    simp
  have hb : totient b = 2 ^ (k + 1) := by
    dsimp [b]
    rw [totient_mul ((by decide : Nat.Coprime 3 2).pow_right (k + 1)),
      totient_prime_pow_succ prime_two, totient_prime (by decide : Nat.Prime 3)]
    simp only [Nat.reduceSub, mul_one, pow_succ]
    ring
  have hab : a ≠ b := by
    dsimp [a, b]
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    have hp : 0 < 2 ^ (k + 1) := pow_pos (by decide) _
    nlinarith
  have hsub : ({a, b} : Set ℕ) ⊆ {m : ℕ | totient m = 2 ^ (k + 1)} := by
    intro m hm
    rcases Set.mem_insert_iff.mp hm with rfl | hm
    · exact ha
    · have hm' : m = b := Set.mem_singleton_iff.mp hm
      simpa only [hm'] using hb
  have hcard := Set.ncard_le_ncard hsub (totient_fiber_finite (2 ^ (k + 1)))
  rw [Set.ncard_pair hab] at hcard
  exact hcard

/-- Unconditional endpoint inequality for the range `ε ≥ 1`.
This result does not use `SmoothPrimeEndpointCertificates`. -/
theorem conjecture_for_epsilon_ge_one (ε : ℝ) (hε : 1 ≤ ε) :
    {n : ℕ | (fiberCard n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => 2 ^ (k + 1)) := by
    intro k l h
    exact Nat.succ.inj ((Nat.pow_right_injective (by decide : 2 ≤ 2)) h)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro n ⟨k, rfl⟩
  have hbase : (1 : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) (k + 1))
  have hbound : ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 - ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hg : (1 : ℝ) < (fiberCard (2 ^ (k + 1)) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) (two_le_fiberCard_two_pow k))
  exact lt_of_le_of_lt hbound hg

end Erdos821Aux

#print axioms Erdos821Aux.rpow_ratio_lt_of_nat_pow_lt
#print axioms Erdos821Aux.endpoint_of_unbounded_nat_power_lt
#print axioms Erdos821Aux.SmoothPrimeEndpointCertificates
#print axioms Erdos821Aux.unbounded_nat_power_lt_of_smooth_prime_certificates
#print axioms Erdos821Aux.endpoint_of_smooth_prime_certificates
#print axioms Erdos821Aux.two_le_fiberCard_two_pow
#print axioms Erdos821Aux.conjecture_for_epsilon_ge_one
