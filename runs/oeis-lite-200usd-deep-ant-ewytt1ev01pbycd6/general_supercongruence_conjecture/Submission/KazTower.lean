import Submission.JacobRef

/-!
# Jacobsthal–Kazandzidis "tower" congruence — scratch / feasibility file

Goal theorem:

  `theorem tower_congr (p t A B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
      (hB : 0 < B) (hBA : B < A) (hA : p^t ∣ A) (hB' : p^t ∣ B) :
      (p:ℤ)^(3*(t+1)) ∣ ((Nat.choose (p*A) (p*B) : ℤ) - Nat.choose A B)`

## Status summary (see the long comment at the bottom for the full assessment)

* `tower_reduction` — **fully proven, sorry-free.** Reduces the goal for *any*
  modulus exponent `K` to a divisibility statement about the coprime-to-`p`
  factorial products `P`, namely `(p:ℤ)^K ∣ P A - P B · P (A-B)`. This is the
  clean, purely algebraic part and it compiles with clean axioms.

* `P_tower_dvd` — the genuine mathematical core (the Kazandzidis content). It is
  **NOT proven**; it is stated with an explicit `sorry`, clearly labelled. The
  base case `K = 3` (i.e. `t = 0`) is already available as
  `JacobRef.P_diff_dvd`; the extra factor `p^{3t}` requires the delicate
  Bernoulli/Wolstenholme–Glaisher cancellation described below.

* `tower_congr` — assembled from `tower_reduction` + `P_tower_dvd`, hence its
  proof is complete *modulo* the single labelled `sorry` in `P_tower_dvd`.
-/

open Finset JacobRef

namespace KazTower

/-! ## 1. The clean reduction (fully proven, sorry-free).

For any exponent `K`, divisibility of the `P`-difference transfers to
divisibility of the binomial difference, using the exact identity
`choose_prod_identity` together with the coprimality of `P` to `p`. This mirrors
the endgame of `JacobRef.jacobsthal_choose_refined`. -/

/-- **Reduction lemma.** If `p^K ∣ P A - P B · P (A-B)` (as integers), then
`p^K ∣ C(pA, pB) - C(A, B)`. No lower bound on `K`, no `p ≥ 5` needed. -/
theorem tower_reduction (p A B K : ℕ) (hp : p.Prime) (hBA : B < A)
    (hPdiff : (p : ℤ) ^ K ∣
      ((P p A : ℤ) - (P p B : ℤ) * (P p (A - B) : ℤ))) :
    (p : ℤ) ^ K ∣ ((Nat.choose (p * A) (p * B) : ℤ) - Nat.choose A B) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- The exact block-product identity, cast to ℤ.
  have hident : (Nat.choose (p * A) (p * B) : ℤ) * (P p B : ℤ) * (P p (A - B) : ℤ)
      = (Nat.choose A B : ℤ) * (P p A : ℤ) := by
    exact_mod_cast choose_prod_identity p A B hp.pos (le_of_lt hBA)
  -- Rearrange into the "diamond" identity.
  have hdiamond : ((Nat.choose (p * A) (p * B) : ℤ) - Nat.choose A B)
        * ((P p B : ℤ) * (P p (A - B) : ℤ))
      = (Nat.choose A B : ℤ)
        * ((P p A : ℤ) - (P p B : ℤ) * (P p (A - B) : ℤ)) := by
    linear_combination hident
  -- `p^K` divides the right-hand side, hence the left-hand side product.
  have hLHS : (p : ℤ) ^ K ∣
      ((Nat.choose (p * A) (p * B) : ℤ) - Nat.choose A B)
        * ((P p B : ℤ) * (P p (A - B) : ℤ)) := by
    rw [hdiamond]
    exact Dvd.dvd.mul_left hPdiff _
  -- `p^K` is coprime to `P B · P (A-B)`, so it divides the first factor.
  have hcop : IsCoprime ((p : ℤ) ^ K) ((P p B : ℤ) * (P p (A - B) : ℤ)) := by
    apply IsCoprime.pow_left
    rw [show ((P p B : ℤ) * (P p (A - B) : ℤ)) = (((P p B * P p (A - B) : ℕ)) : ℤ) from by
      push_cast; ring]
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.mul_right (P_coprime p hp B).symm (P_coprime p hp (A - B)).symm
  exact hcop.dvd_of_dvd_mul_right hLHS

/-! ## 2. The genuine mathematical core (OPEN — labelled `sorry`).

The following divisibility is the actual Kazandzidis content. It is **not
proven**. The base case `K = 3` (`t = 0`) is `JacobRef.P_diff_dvd`; the extra
`p^{3t}` is the hard part.

Write `P n / ((p-1)!)^n = ∏_{j=0}^{n-1} f(jp)` with
`f(x) = ∏_{r=1}^{p-1}(1 + x/r)`. Taking p-adic logarithms,
`log(P(A) / P(B)·P(A-B)) = ∑_{i≥1} ((-1)^{i-1}/i) p^i H_i D_i`,
where `H_i = ∑_{r=1}^{p-1} r^{-i}` and `D_i = S_i(A) - S_i(B) - S_i(A-B)`,
`S_i(n) = ∑_{j<n} j^i`.

Numerically (verified for this file, e.g. `p=5, t=1, A=10, B=5`):
`v_p(term_1) = v_p(term_2) = 5 < 6 = 3(t+1)`, but `v_p(term_1 + term_2) = 6`.
So the modulus is **not** reached term-by-term: it requires the cancellation
between `term_1 = p·H_1·B(A-B)` and `term_2 = -(p²/2)·H_2·D_2`, driven by the
Wolstenholme–Glaisher relation between `H_1 (mod p^5)` and `H_2 (mod p^4)`
mediated by the Bernoulli number `B_{p-3}`. Mathlib has neither these
higher harmonic-sum congruences nor a p-adic logarithm. -/

/-- **OPEN.** `p^{3(t+1)} ∣ P A - P B · P (A-B)` when `p^t ∣ A` and `p^t ∣ B`.
This is the Kazandzidis core and is left as a clearly-labelled `sorry`. -/
theorem P_tower_dvd (p t A B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B < A) (hA : p ^ t ∣ A) (hB' : p ^ t ∣ B) :
    (p : ℤ) ^ (3 * (t + 1)) ∣
      ((P p A : ℤ) - (P p B : ℤ) * (P p (A - B) : ℤ)) := by
  sorry

/-! ## 3. The target theorem, assembled from the two pieces.

Complete *modulo* the single `sorry` in `P_tower_dvd`. -/

/-- Jacobsthal–Kazandzidis tower congruence. Proof is complete except for the
labelled `sorry` inside `P_tower_dvd`. -/
theorem tower_congr (p t A B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB : 0 < B) (hBA : B < A) (hA : p ^ t ∣ A) (hB' : p ^ t ∣ B) :
    (p : ℤ) ^ (3 * (t + 1)) ∣ ((Nat.choose (p * A) (p * B) : ℤ) - Nat.choose A B) :=
  tower_reduction p A B (3 * (t + 1)) hp hBA (P_tower_dvd p t A B hp hp5 hBA hA hB')

end KazTower

-- Axiom checks (diagnostic):
#print axioms KazTower.tower_reduction
#print axioms KazTower.tower_congr
