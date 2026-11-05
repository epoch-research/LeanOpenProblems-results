/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Submission.RootMeanBasic
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Finite-modulus Hensel lifting for polynomial root counts

At a prime where every residue root of an integer polynomial is simple,
reduction from roots modulo `p ^ k` to roots modulo `p` is a bijection for
`1 ≤ k`. Consequently its root count is constant on positive prime powers.
No monicity or irreducibility is required for lifting.

The proof is directly in finite residue rings: a lift has the form
`r.val + t.val * p ^ k`, with `t : ZMod p`, and the equation for `t` is linear
with nonzero derivative coefficient. The first-order expansion is Mathlib's
`Polynomial.eval_add_of_sq_eq_zero`; no external Hensel theorem or specialized
quadratic root-counting code is copied.

There is also a proved uniform bound at arbitrary primes: if `f` is
nonconstant and `R = f.resultant f.derivative` is nonzero, then
`rootCount (polynomialAbsValue f) (p ^ k) ≤ p ^ (2 * padicValInt p R + 1)`.
This uses Mathlib's integral `Polynomial.binomExpansion` and resultant Bézout
certificate to bound derivative valuations and separate approximate roots.
For every nonconstant irreducible integer polynomial, rational separability
supplies `R ≠ 0`. Discriminant-good monic polynomials satisfy the simplicity
hypothesis, and the good-prime degree bound follows from `RootMeanBasic`.

These are local algebraic foundations, not a proof of the general polynomial
root-mean theorem or of the balanced divisor-sum limit in Erdős 975.
-/

namespace Erdos975Support

open Polynomial

/-- The precise good-prime condition used here: every root modulo `p` has
nonvanishing derivative modulo `p`. It does not require that every element is
a root, nor any hypothesis on the leading coefficient. -/
def PolynomialSimpleRootsMod (f : ℤ[X]) (p : ℕ) : Prop :=
  ∀ x : ZMod p, f.eval₂ (Int.castRingHom (ZMod p)) x = 0 →
    f.derivative.eval₂ (Int.castRingHom (ZMod p)) x ≠ 0

/-- Evaluation commutes with reduction of the modulus. -/
theorem polynomial_eval₂_castHom (f : ℤ[X]) {m n : ℕ} (h : m ∣ n)
    (x : ZMod n) :
    ZMod.castHom h (ZMod m) (f.eval₂ (Int.castRingHom (ZMod n)) x) =
      f.eval₂ (Int.castRingHom (ZMod m)) (ZMod.castHom h (ZMod m) x) := by
  rw [f.hom_eval₂, RingHom.ext_int
    ((ZMod.castHom h (ZMod m)).comp (Int.castRingHom (ZMod n)))
    (Int.castRingHom (ZMod m))]

/-- A residue root is an integer approximate root at its natural representative. -/
theorem polynomial_eval_val_dvd_iff (f : ℤ[X]) (q : ℕ) [NeZero q] (r : ZMod q) :
    (q : ℤ) ∣ f.eval (r.val : ℤ) ↔
      f.eval₂ (Int.castRingHom (ZMod q)) r = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change Int.castRingHom (ZMod q) (f.eval (r.val : ℤ)) = 0 ↔ _
  rw [← eval₂_at_natCast, ZMod.natCast_zmod_val]

/-- Reduction sends a natural representative to the same natural integer
in the smaller residue ring. -/
theorem zmod_castHom_eq_natCast_val {m n : ℕ} [NeZero n] (h : m ∣ n)
    (x : ZMod n) : ZMod.castHom h (ZMod m) x = (x.val : ZMod m) := by
  have hx := map_natCast (ZMod.castHom h (ZMod m)) x.val
  rw [ZMod.natCast_zmod_val] at hx
  exact hx

/-- Reduction of a polynomial root along divisibility of the moduli. -/
def polynomialRootsReduction (f : ℤ[X]) {m n : ℕ} (h : m ∣ n) :
    {x : ZMod n // f.eval₂ (Int.castRingHom (ZMod n)) x = 0} →
      {x : ZMod m // f.eval₂ (Int.castRingHom (ZMod m)) x = 0} :=
  fun x ↦ ⟨ZMod.castHom h (ZMod m) x.1, by
    rw [← polynomial_eval₂_castHom, x.2, map_zero]⟩

@[simp]
theorem polynomialRootsReduction_self (f : ℤ[X]) (n : ℕ) :
    polynomialRootsReduction f (dvd_refl n) = id := by
  funext x
  apply Subtype.ext
  simp [polynomialRootsReduction]

/-- Reduction between equal moduli is bijective, independently of how the
modulus equality and divisibility are proved. -/
theorem polynomialRootsReduction_bijective_of_eq (f : ℤ[X]) {m n : ℕ}
    (h : m ∣ n) (he : m = n) : Function.Bijective (polynomialRootsReduction f h) := by
  subst n
  change Function.Bijective (polynomialRootsReduction f (dvd_refl m))
  rw [polynomialRootsReduction_self]
  exact Function.bijective_id

/-- Successive reductions agree with direct reduction, also on root sets. -/
theorem polynomialRootsReduction_comp (f : ℤ[X]) {m n q : ℕ}
    (hm : m ∣ n) (hn : n ∣ q) :
    polynomialRootsReduction f (dvd_trans hm hn) =
      polynomialRootsReduction f hm ∘ polynomialRootsReduction f hn := by
  funext x
  apply Subtype.ext
  change ZMod.castHom (dvd_trans hm hn) (ZMod m) x.1 =
    ZMod.castHom hm (ZMod m) (ZMod.castHom hn (ZMod n) x.1)
  rw [← RingHom.comp_apply, ZMod.castHom_comp]

/-- Cancel the integer factor `q` when testing vanishing modulo `q * p`.
This is cancellation in `ℤ`, not cancellation of a zero divisor in `ZMod`. -/
theorem zmod_cofactor_mul_eq_zero_iff (q p : ℕ) (hq : q ≠ 0) (a : ℤ) :
    (q : ZMod (q * p)) * (a : ZMod (q * p)) = 0 ↔ (a : ZMod p) = 0 := by
  rw [← Int.cast_natCast q, ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul,
    mul_dvd_mul_iff_left (show (q : ℤ) ≠ 0 by exact_mod_cast hq)]

/-- A fiber of reduction modulo `q` is parametrized by its last base-`p`
digit. Both moduli must be nonzero so that natural representatives exist. -/
theorem zmod_reduction_fiber_digits (q p : ℕ) [NeZero q] [NeZero p]
    (r : ZMod q) (y : ZMod (q * p)) :
    ZMod.castHom (dvd_mul_right q p) (ZMod q) y = r ↔
      ∃ t : ZMod p, y = (r.val : ZMod (q * p)) +
        (t.val : ZMod (q * p)) * (q : ZMod (q * p)) := by
  constructor
  · intro hy
    have hv : (y.val : ZMod q) = r := by
      rw [← map_natCast (ZMod.castHom (dvd_mul_right q p) (ZMod q)) y.val,
        ZMod.natCast_zmod_val, hy]
    obtain ⟨u, hu⟩ := (ZMod.natCast_eq_iff q y.val r).mp hv
    have hup : u < p := Nat.lt_of_mul_lt_mul_left (a := q) (by
      have := y.val_lt
      rw [hu] at this
      omega)
    refine ⟨(u : ZMod p), ?_⟩
    rw [ZMod.val_natCast_of_lt hup, ← Nat.cast_mul, ← Nat.cast_add,
      mul_comm u q, ← hu, ZMod.natCast_zmod_val]
  · rintro ⟨t, rfl⟩
    simp only [map_add, map_mul, map_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_self, mul_zero, add_zero]

/-- Different final digits give different elements in a reduction fiber. -/
theorem zmod_fiber_digit_injective (q p : ℕ) (hq : q ≠ 0) [NeZero p]
    (r : ZMod q) :
    Function.Injective (fun t : ZMod p ↦ (r.val : ZMod (q * p)) +
      (t.val : ZMod (q * p)) * (q : ZMod (q * p))) := by
  intro t u h
  have hz : (q : ZMod (q * p)) *
      (((t.val : ℤ) - (u.val : ℤ) : ℤ) : ZMod (q * p)) = 0 := by
    push_cast
    linear_combination h
  have hpz := (zmod_cofactor_mul_eq_zero_iff q p hq _).mp hz
  simpa only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    sub_eq_zero] using hpz

/-- First-order Taylor expansion at the next prime-power modulus. Since
`k ≥ 1`, the square of the increment vanishes modulo `p ^ (k + 1)`.
Primality is not needed for this identity. -/
theorem polynomial_eval₂_add_prime_pow (f : ℤ[X]) (p k : ℕ) (hk : 1 ≤ k)
    (r t : ZMod (p ^ (k + 1))) :
    f.eval₂ (Int.castRingHom (ZMod (p ^ (k + 1))))
        (r + t * (p ^ k : ℕ)) =
      f.eval₂ (Int.castRingHom (ZMod (p ^ (k + 1)))) r +
        f.derivative.eval₂ (Int.castRingHom (ZMod (p ^ (k + 1)))) r *
          (t * (p ^ k : ℕ)) := by
  have hsq : ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff, ← pow_mul]
    exact pow_dvd_pow p (by omega)
  have ht : (t * (p ^ k : ℕ)) ^ 2 = (0 : ZMod (p ^ (k + 1))) := by
    rw [mul_pow, hsq, mul_zero]
  simpa only [eval_map, derivative_map] using
    Polynomial.eval_add_of_sq_eq_zero
      (f.map (Int.castRingHom (ZMod (p ^ (k + 1))))) r _ ht

/-- The equation for a last digit of a root is a linear equation modulo `p`.
Here `L` is the exact integer quotient `f(r.val) / p ^ k`. -/
theorem polynomial_prime_pow_lift_iff (f : ℤ[X]) (p k : ℕ) (hp : p ≠ 0)
    (hk : 1 ≤ k) (r : ZMod (p ^ k)) (L : ℤ)
    (hL : f.eval (r.val : ℤ) = (p ^ k : ℕ) * L) (t : ZMod p) :
    f.eval₂ (Int.castRingHom (ZMod (p ^ (k + 1))))
        ((r.val : ZMod (p ^ (k + 1))) +
          (t.val : ZMod (p ^ (k + 1))) * (p ^ k : ℕ)) = 0 ↔
      (L : ZMod p) + t *
        f.derivative.eval₂ (Int.castRingHom (ZMod p)) (r.val : ZMod p) = 0 := by
  letI : NeZero p := ⟨hp⟩
  rw [polynomial_eval₂_add_prime_pow f p k hk]
  simp only [eval₂_at_natCast, Int.coe_castRingHom]
  rw [hL]
  have heq : (((p ^ k : ℕ) * L : ℤ) : ZMod (p ^ (k + 1))) +
      ((f.derivative.eval (r.val : ℤ) : ℤ) : ZMod (p ^ (k + 1))) *
        ((t.val : ZMod (p ^ (k + 1))) * (p ^ k : ℕ)) =
      (p ^ k : ℕ) * ((L + (t.val : ℤ) * f.derivative.eval (r.val : ℤ) : ℤ) :
        ZMod (p ^ (k + 1))) := by
    push_cast
    ring
  rw [heq]
  have hcancel := zmod_cofactor_mul_eq_zero_iff (p ^ k) p (pow_ne_zero _ hp)
    (L + (t.val : ℤ) * f.derivative.eval (r.val : ℤ))
  simpa only [pow_succ, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_zmod_val] using hcancel

/-- Finite Hensel's lemma in digit form: a root with simple reduction has
exactly one last digit yielding a root at the next prime-power modulus. -/
theorem polynomial_hensel_unique_digit (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (k : ℕ) (hk : 1 ≤ k) (r : ZMod (p ^ k))
    (hr : f.eval₂ (Int.castRingHom (ZMod (p ^ k))) r = 0)
    (hd : f.derivative.eval₂ (Int.castRingHom (ZMod p)) (r.val : ZMod p) ≠ 0) :
    ∃! t : ZMod p,
      f.eval₂ (Int.castRingHom (ZMod (p ^ (k + 1))))
        ((r.val : ZMod (p ^ (k + 1))) +
          (t.val : ZMod (p ^ (k + 1))) * (p ^ k : ℕ)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hdiv := (polynomial_eval_val_dvd_iff f (p ^ k) r).mpr hr
  obtain ⟨L, hL⟩ := hdiv
  let d := f.derivative.eval₂ (Int.castRingHom (ZMod p)) (r.val : ZMod p)
  let t : ZMod p := -(L : ZMod p) * d⁻¹
  have ht : (L : ZMod p) + t * d = 0 := by
    dsimp [t]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one, add_neg_cancel]
  refine ⟨t, (polynomial_prime_pow_lift_iff f p k hp.ne_zero hk r L hL t).mpr ht, ?_⟩
  intro u hu
  have hu' := (polynomial_prime_pow_lift_iff f p k hp.ne_zero hk r L hL u).mp hu
  apply mul_left_injective₀ hd
  dsimp [d] at ht ⊢
  linear_combination hu' - ht

/-- The same unique last digit, using the natural representatives requested
by the original `Finset.range` definition of `rootCount`. -/
theorem polynomial_hensel_unique_digit_range (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (k : ℕ) (hk : 1 ≤ k) (r : ZMod (p ^ k))
    (hr : f.eval₂ (Int.castRingHom (ZMod (p ^ k))) r = 0)
    (hd : f.derivative.eval₂ (Int.castRingHom (ZMod p)) (r.val : ZMod p) ≠ 0) :
    ∃! t : ℕ, t ∈ Finset.range p ∧
      f.eval₂ (Int.castRingHom (ZMod (p ^ (k + 1))))
        ((r.val : ZMod (p ^ (k + 1))) +
          (t : ZMod (p ^ (k + 1))) * (p ^ k : ℕ)) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, huniq⟩ := polynomial_hensel_unique_digit f p hp k hk r hr hd
  refine ⟨t.val, ⟨Finset.mem_range.mpr t.val_lt, ht⟩, ?_⟩
  intro u hu
  have huval : (u : ZMod p).val = u :=
    ZMod.val_natCast_of_lt (Finset.mem_range.mp hu.1)
  have hueq := huniq (u : ZMod p) (by simpa only [huval] using hu.2)
  exact huval.symm.trans (congrArg ZMod.val hueq)

/-- Finite Hensel's lemma as unique lifting of an element of a residue ring.
Only simplicity of this particular root's reduction is needed. -/
theorem polynomial_hensel_unique_lift (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (k : ℕ) (hk : 1 ≤ k) (r : ZMod (p ^ k))
    (hr : f.eval₂ (Int.castRingHom (ZMod (p ^ k))) r = 0)
    (hd : f.derivative.eval₂ (Int.castRingHom (ZMod p)) (r.val : ZMod p) ≠ 0) :
    ∃! y : ZMod (p ^ (k + 1)),
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) y = r ∧
        f.eval₂ (Int.castRingHom (ZMod (p ^ (k + 1)))) y = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, huniq⟩ := polynomial_hensel_unique_digit f p hp k hk r hr hd
  have hfiber : ∀ y : ZMod (p ^ (k + 1)),
      ZMod.castHom (pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k)) y = r ↔
        ∃ t : ZMod p, y = (r.val : ZMod (p ^ (k + 1))) +
          (t.val : ZMod (p ^ (k + 1))) * (p ^ k : ℕ) := by
    simpa only [pow_succ] using zmod_reduction_fiber_digits (p ^ k) p r
  refine ⟨(r.val : ZMod (p ^ (k + 1))) +
      (t.val : ZMod (p ^ (k + 1))) * (p ^ k : ℕ), ⟨?_, ht⟩, ?_⟩
  · exact (hfiber _).mpr ⟨t, rfl⟩
  · intro y hy
    obtain ⟨u, hu⟩ := (hfiber y).mp hy.1
    have hueq : u = t := huniq u (by simpa only [hu] using hy.2)
    rw [hu, hueq]

/-- Every root modulo a positive power of a good prime has simple reduction. -/
theorem polynomial_derivative_ne_zero_of_root_prime_pow (f : ℤ[X])
    (p : ℕ) (hp : p.Prime) (hs : PolynomialSimpleRootsMod f p)
    (k : ℕ) (hk : 1 ≤ k) (r : ZMod (p ^ k))
    (hr : f.eval₂ (Int.castRingHom (ZMod (p ^ k))) r = 0) :
    f.derivative.eval₂ (Int.castRingHom (ZMod p)) (r.val : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  apply hs (r.val : ZMod p)
  have hred : p ∣ p ^ k := dvd_pow_self p (by omega)
  have he := polynomial_eval₂_castHom f hred r
  rw [hr, map_zero, zmod_castHom_eq_natCast_val] at he
  exact he.symm

/-- One-step reduction is a bijection on roots at a good prime. -/
theorem polynomialRootsReduction_succ_bijective (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (hs : PolynomialSimpleRootsMod f p) (k : ℕ) (hk : 1 ≤ k) :
    Function.Bijective
      (polynomialRootsReduction f (pow_dvd_pow p (Nat.le_succ k))) := by
  apply (Function.bijective_iff_existsUnique _).mpr
  intro r
  have hd := polynomial_derivative_ne_zero_of_root_prime_pow f p hp hs k hk r.1 r.2
  obtain ⟨y, hy, huniq⟩ := polynomial_hensel_unique_lift f p hp k hk r.1 r.2 hd
  refine ⟨⟨y, hy.2⟩, Subtype.ext hy.1, ?_⟩
  intro z hz
  apply Subtype.ext
  exact huniq z.1 ⟨congrArg Subtype.val hz, z.2⟩

/-- Direct reduction from any positive prime power to the prime is bijective.
The divisibility proof `h` is arbitrary; the map is the usual reduction. -/
theorem polynomialRootsReduction_prime_pow_bijective (f : ℤ[X])
    (p : ℕ) (hp : p.Prime) (hs : PolynomialSimpleRootsMod f p)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ h : p ∣ p ^ k, Function.Bijective (polynomialRootsReduction f h) := by
  induction k, hk using Nat.le_induction with
  | base =>
      intro h
      exact polynomialRootsReduction_bijective_of_eq f h (pow_one p).symm
  | succ k hk ih =>
      intro h
      have hcomp : polynomialRootsReduction f h =
          polynomialRootsReduction f (dvd_pow_self p (by omega)) ∘
            polynomialRootsReduction f (pow_dvd_pow p (Nat.le_succ k)) :=
        polynomialRootsReduction_comp f _ _
      rw [hcomp]
      exact (ih _).comp (polynomialRootsReduction_succ_bijective f p hp hs k hk)

/-- The finite Hensel bijection is specifically reduction to `ZMod p`. -/
noncomputable def polynomialRootsPrimePowEquiv (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (hs : PolynomialSimpleRootsMod f p) (k : ℕ) (hk : 1 ≤ k) :
    {x : ZMod (p ^ k) // f.eval₂ (Int.castRingHom (ZMod (p ^ k))) x = 0} ≃
      {x : ZMod p // f.eval₂ (Int.castRingHom (ZMod p)) x = 0} :=
  Equiv.ofBijective (polynomialRootsReduction f (dvd_pow_self p (by omega)))
    (polynomialRootsReduction_prime_pow_bijective f p hp hs k hk _)

@[simp]
theorem polynomialRootsPrimePowEquiv_apply_val (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (hs : PolynomialSimpleRootsMod f p) (k : ℕ) (hk : 1 ≤ k)
    (r : {x : ZMod (p ^ k) // f.eval₂ (Int.castRingHom (ZMod (p ^ k))) x = 0}) :
    (polynomialRootsPrimePowEquiv f p hp hs k hk r).1 = (r.1.val : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  change ZMod.castHom _ (ZMod p) r.1 = (r.1.val : ZMod p)
  exact zmod_castHom_eq_natCast_val _ r.1

/-- At a prime where every residue root is simple, the original root count
is constant on all positive powers of that prime. -/
theorem rootCount_polynomial_prime_pow_eq (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (hs : PolynomialSimpleRootsMod f p) (k : ℕ) (hk : 1 ≤ k) :
    rootCount (polynomialAbsValue f) (p ^ k) = rootCount (polynomialAbsValue f) p := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [rootCount_polynomial_eq_card_zmod, rootCount_polynomial_eq_card_zmod]
  exact Nat.card_congr (polynomialRootsPrimePowEquiv f p hp hs k hk)

/-- The good-prime degree bound, using the primitive-polynomial prime bound
from `RootMeanBasic`. It is uniform in the positive exponent. -/
theorem rootCount_polynomial_prime_pow_le (f : ℤ[X]) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) (hs : PolynomialSimpleRootsMod f p)
    (k : ℕ) (hk : 1 ≤ k) :
    rootCount (polynomialAbsValue f) (p ^ k) ≤ f.natDegree := by
  rw [rootCount_polynomial_prime_pow_eq f p hp hs k hk]
  exact rootCount_polynomial_prime_le f hf p hp

/-- The uniform degree bound for a nonconstant irreducible polynomial at a
prime with simple residue roots. Monicity is not required. -/
theorem rootCount_irreducible_polynomial_prime_pow_le (f : ℤ[X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) (p : ℕ) (hp : p.Prime)
    (hs : PolynomialSimpleRootsMod f p) (k : ℕ) (hk : 1 ≤ k) :
    rootCount (polynomialAbsValue f) (p ^ k) ≤ f.natDegree :=
  rootCount_polynomial_prime_pow_le f (hf.isPrimitive hdeg) p hp hs k hk

/-- Separability of the reduced polynomial implies the rootwise good-prime
hypothesis. The converse is not asserted: repeated non-linear factors can
have no roots in the prime residue field. -/
theorem polynomialSimpleRootsMod_of_separable_map (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (hs : (f.map (Int.castRingHom (ZMod p))).Separable) :
    PolynomialSimpleRootsMod f p := by
  letI : Fact p.Prime := ⟨hp⟩
  intro x hx
  have hd := hs.eval₂_derivative_ne_zero (RingHom.id (ZMod p))
    (by simpa only [eval₂_id, eval_map] using hx)
  simpa only [eval₂_id, derivative_map, eval_map] using hd

/- ## Resultant control at primes which need not be good -/

/-- A Bézout certificate bounds derivative divisibility at approximate roots.
No primality hypothesis is needed for this elementary observation. -/
theorem polynomial_derivative_not_dvd_of_bezout (f A B : ℤ[X]) (D : ℤ)
    (hbez : f * A + f.derivative * B = C D) (p e : ℕ)
    (hD : ¬ (p : ℤ) ^ e ∣ D) (a : ℤ) (ha : (p : ℤ) ^ e ∣ f.eval a) :
    ¬ (p : ℤ) ^ e ∣ f.derivative.eval a := by
  intro hd
  apply hD
  have he := congrArg (fun g : ℤ[X] ↦ g.eval a) hbez
  simp only [eval_add, eval_mul, eval_C] at he
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left hd _)

/-- For a nonconstant polynomial the resultant supplies the Bézout certificate.
The hypothesis is exactly an upper bound on its `p`-adic valuation, written
without the exceptional convention for the valuation of zero. -/
theorem polynomial_derivative_not_dvd_of_resultant (f : ℤ[X])
    (hdeg : 0 < f.natDegree) (p v : ℕ)
    (hR : ¬ (p : ℤ) ^ (v + 1) ∣ f.resultant f.derivative)
    (a : ℤ) (ha : (p : ℤ) ^ (v + 1) ∣ f.eval a) :
    ¬ (p : ℤ) ^ (v + 1) ∣ f.derivative.eval a := by
  obtain ⟨A, B, _, _, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    f f.derivative le_rfl le_rfl (Or.inl (ne_of_gt hdeg))
  exact polynomial_derivative_not_dvd_of_bezout f A B _ hbez p (v + 1) hR a ha

/-- Nondivisibility of the resultant is a sufficient good-prime test, without
assuming that reduction preserves the degree. Nonconstancy is essential. -/
theorem polynomialSimpleRootsMod_of_not_dvd_resultant (f : ℤ[X])
    (hdeg : 0 < f.natDegree) (p : ℕ) (hp : p.Prime)
    (hR : ¬ (p : ℤ) ∣ f.resultant f.derivative) : PolynomialSimpleRootsMod f p := by
  letI : Fact p.Prime := ⟨hp⟩
  intro x hx hd
  have hfx := (polynomial_eval_val_dvd_iff f p x).mpr hx
  have hdx := (polynomial_eval_val_dvd_iff f.derivative p x).mpr hd
  exact polynomial_derivative_not_dvd_of_resultant f hdeg p 0
    (by simpa only [zero_add, pow_one] using hR) _
    (by simpa only [zero_add, pow_one] using hfx)
    (by simpa only [zero_add, pow_one] using hdx)

/-- For a monic nonconstant polynomial, a prime not dividing the integer
discriminant has only simple residue roots. The degree hypothesis also
handles the genuine constant-polynomial exception to the resultant identity. -/
theorem polynomialSimpleRootsMod_of_monic_not_dvd_discr (f : ℤ[X]) (hm : f.Monic)
    (hdeg : 0 < f.natDegree) (p : ℕ) (hp : p.Prime)
    (hdisc : ¬ (p : ℤ) ∣ f.discr) : PolynomialSimpleRootsMod f p := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, B, _, _, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f f.derivative
    le_rfl (natDegree_derivative_le f) (Or.inl (ne_of_gt hdeg))
  have hR : ¬ (p : ℤ) ∣ f.resultant f.derivative f.natDegree (f.natDegree - 1) := by
    rw [Polynomial.resultant_deriv (natDegree_pos_iff_degree_pos.mp hdeg), hm.leadingCoeff,
      mul_one, ((isUnit_neg_one : IsUnit (-1 : ℤ)).pow _).dvd_mul_left]
    exact hdisc
  intro x hx hd
  have hfx := (polynomial_eval_val_dvd_iff f p x).mpr hx
  have hdx := (polynomial_eval_val_dvd_iff f.derivative p x).mpr hd
  exact polynomial_derivative_not_dvd_of_bezout f A B _ hbez p 1
    (by simpa only [pow_one] using hR) _ (by simpa only [pow_one] using hfx)
    (by simpa only [pow_one] using hdx)

/-- The discriminant-good version of prime-power root-count stability. -/
theorem rootCount_monic_polynomial_prime_pow_eq_of_not_dvd_discr (f : ℤ[X]) (hm : f.Monic)
    (hdeg : 0 < f.natDegree) (p : ℕ) (hp : p.Prime) (hdisc : ¬ (p : ℤ) ∣ f.discr)
    (k : ℕ) (hk : 1 ≤ k) :
    rootCount (polynomialAbsValue f) (p ^ k) = rootCount (polynomialAbsValue f) p :=
  rootCount_polynomial_prime_pow_eq f p hp
    (polynomialSimpleRootsMod_of_monic_not_dvd_discr f hm hdeg p hp hdisc) k hk

/-- If the second factor has `p`-adic valuation at most `v`, divisibility of
its product by `p ^ k` forces divisibility of the first factor by `p ^ (k-v)`.
The proof factors out the finite multiplicity in `ℤ`. -/
theorem int_prime_pow_dvd_factor_of_not_dvd (p : ℕ) (hp : p.Prime)
    (k v : ℕ) (a b : ℤ) (hab : (p : ℤ) ^ k ∣ a * b)
    (hb : ¬ (p : ℤ) ^ (v + 1) ∣ b) : (p : ℤ) ^ (k - v) ∣ a := by
  by_cases hkv : k ≤ v
  · simp only [Nat.sub_eq_zero_of_le hkv, pow_zero, one_dvd]
  have hfin : FiniteMultiplicity (p : ℤ) b := ⟨v, hb⟩
  let s := multiplicity (p : ℤ) b
  have hsv : s ≤ v := by
    have hslt := (hfin.multiplicity_lt_iff_not_dvd).mpr hb
    exact Nat.le_of_lt_succ hslt
  obtain ⟨c, hbc, hc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hsk : s ≤ k := by omega
  have hsplit : (p : ℤ) ^ k = (p : ℤ) ^ s * (p : ℤ) ^ (k - s) := by
    rw [← pow_add, Nat.add_sub_cancel' hsk]
  have hprod : (p : ℤ) ^ (k - s) ∣ a * c := by
    rw [hbc, hsplit, ← mul_assoc, mul_comm a ((p : ℤ) ^ s), mul_assoc,
      mul_dvd_mul_iff_left (pow_ne_zero _ (Nat.prime_iff_prime_int.mp hp).ne_zero)] at hab
    exact hab
  have ha := (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_right (k - s) hc hprod
  exact (pow_dvd_pow (p : ℤ) (by omega : k - v ≤ k - s)).trans ha

/-- Approximate roots in the same class modulo `p ^ (v+1)` are in the same
class modulo `p ^ (k-v)`, provided the derivative valuation at approximate
roots is at most `v`. This is a separation lemma, not a lifting assertion. -/
theorem polynomial_root_separation_of_derivative_bound (f : ℤ[X])
    (p : ℕ) (hp : p.Prime) (v k : ℕ) (hk : v + 1 ≤ k)
    (hderiv : ∀ a : ℤ, (p : ℤ) ^ (v + 1) ∣ f.eval a →
      ¬ (p : ℤ) ^ (v + 1) ∣ f.derivative.eval a)
    (a b : ℤ) (ha : (p : ℤ) ^ k ∣ f.eval a) (hb : (p : ℤ) ^ k ∣ f.eval b)
    (hab : (p : ℤ) ^ (v + 1) ∣ b - a) : (p : ℤ) ^ (k - v) ∣ b - a := by
  obtain ⟨c, hc⟩ := f.binomExpansion a (b - a)
  have heq : a + (b - a) = b := by ring
  rw [heq] at hc
  have hdiff : f.eval b - f.eval a =
      (b - a) * (f.derivative.eval a + c * (b - a)) := by
    linear_combination hc
  have hprod : (p : ℤ) ^ k ∣ (b - a) * (f.derivative.eval a + c * (b - a)) := by
    rw [← hdiff]
    exact dvd_sub hb ha
  have hd := hderiv a ((pow_dvd_pow (p : ℤ) hk).trans ha)
  have hnot : ¬ (p : ℤ) ^ (v + 1) ∣ f.derivative.eval a + c * (b - a) := by
    intro h
    apply hd
    have hsub := dvd_sub h (dvd_mul_of_dvd_right hab c)
    simpa only [add_sub_cancel_right] using hsub
  exact int_prime_pow_dvd_factor_of_not_dvd p hp k v _ _ hprod hnot

/-- A uniform bound at an arbitrary prime under an actual derivative-valuation
hypothesis. The constant may depend on `p` and `v`, but not on the exponent.
It includes `k = 0`, where the modulus is one. -/
theorem rootCount_polynomial_prime_pow_le_of_derivative_bound (f : ℤ[X])
    (p : ℕ) (hp : p.Prime) (v : ℕ)
    (hderiv : ∀ a : ℤ, (p : ℤ) ^ (v + 1) ∣ f.eval a →
      ¬ (p : ℤ) ^ (v + 1) ∣ f.derivative.eval a) (k : ℕ) :
    rootCount (polynomialAbsValue f) (p ^ k) ≤ p ^ (2 * v + 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hk : k ≤ 2 * v + 1
  · calc
      rootCount (polynomialAbsValue f) (p ^ k) ≤ p ^ k := by
        simpa only [rootCount, Finset.card_range] using
          (Finset.card_filter_le (Finset.range (p ^ k))
            (fun r ↦ p ^ k ∣ polynomialAbsValue f r))
      _ ≤ p ^ (2 * v + 1) := Nat.pow_le_pow_right hp.pos hk
  have hvk : v + 1 ≤ k := by omega
  have hsplit : p ^ (k - v) * p ^ v = p ^ k := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : v ≤ k)]
  let Φ : {x : ZMod (p ^ k) // f.eval₂ (Int.castRingHom (ZMod (p ^ k))) x = 0} →
      ZMod (p ^ (v + 1)) × Fin (p ^ v) :=
    fun r ↦ ((r.1.val : ZMod (p ^ (v + 1))),
      ⟨r.1.val / p ^ (k - v), Nat.div_lt_of_lt_mul (by rw [hsplit]; exact r.1.val_lt)⟩)
  have hΦ : Function.Injective Φ := by
    intro r s h
    have hlow : (r.1.val : ZMod (p ^ (v + 1))) = (s.1.val : ZMod (p ^ (v + 1))) :=
      congrArg Prod.fst h
    have hlowdvd : (p : ℤ) ^ (v + 1) ∣ (s.1.val : ℤ) - (r.1.val : ℤ) := by
      have hcast : ((r.1.val : ℤ) : ZMod (p ^ (v + 1))) =
          ((s.1.val : ℤ) : ZMod (p ^ (v + 1))) := by
        simpa only [Int.cast_natCast] using hlow
      simpa only [Nat.cast_pow] using
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ (v + 1))).mp hcast
    have hr : (p : ℤ) ^ k ∣ f.eval (r.1.val : ℤ) := by
      simpa only [Nat.cast_pow] using (polynomial_eval_val_dvd_iff f (p ^ k) r.1).mpr r.2
    have hs : (p : ℤ) ^ k ∣ f.eval (s.1.val : ℤ) := by
      simpa only [Nat.cast_pow] using (polynomial_eval_val_dvd_iff f (p ^ k) s.1).mpr s.2
    have hsep := polynomial_root_separation_of_derivative_bound f p hp v k hvk
      hderiv _ _ hr hs hlowdvd
    have hmod : r.1.val % p ^ (k - v) = s.1.val % p ^ (k - v) := by
      apply Nat.modEq_iff_dvd.mpr
      simpa only [Nat.cast_pow] using hsep
    have hdiv : r.1.val / p ^ (k - v) = s.1.val / p ^ (k - v) :=
      congrArg (fun z : ZMod (p ^ (v + 1)) × Fin (p ^ v) ↦ z.2.val) h
    apply Subtype.ext
    apply ZMod.val_injective
    have hrdecomp := Nat.div_add_mod r.1.val (p ^ (k - v))
    have hsdecomp := Nat.div_add_mod s.1.val (p ^ (k - v))
    rw [hdiv, hmod] at hrdecomp
    exact hrdecomp.symm.trans hsdecomp
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  rw [rootCount_polynomial_eq_card_zmod]
  have hmul : p ^ (v + 1) * p ^ v = p ^ (2 * v + 1) := by
    rw [← pow_add]
    congr 1
    omega
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card,
    Fintype.card_fin, hmul] using hcard

/-- Fully explicit bad-prime bound via the resultant: if its valuation at `p`
is at most `v`, there are at most `p ^ (2*v+1)` roots modulo every `p ^ k`.
No simplicity, primitivity, monicity, or irreducibility is assumed. -/
theorem rootCount_polynomial_prime_pow_le_of_resultant (f : ℤ[X])
    (hdeg : 0 < f.natDegree) (p : ℕ) (hp : p.Prime) (v : ℕ)
    (hR : ¬ (p : ℤ) ^ (v + 1) ∣ f.resultant f.derivative) (k : ℕ) :
    rootCount (polynomialAbsValue f) (p ^ k) ≤ p ^ (2 * v + 1) :=
  rootCount_polynomial_prime_pow_le_of_derivative_bound f p hp v
    (polynomial_derivative_not_dvd_of_resultant f hdeg p v hR) k

/-- In particular, a nonzero resultant gives a genuine uniform bound at
every prime, including its finitely many prime divisors. -/
theorem rootCount_polynomial_prime_pow_le_resultant_valuation (f : ℤ[X])
    (hdeg : 0 < f.natDegree) (p : ℕ) (hp : p.Prime)
    (hR : f.resultant f.derivative ≠ 0) (k : ℕ) :
    rootCount (polynomialAbsValue f) (p ^ k) ≤
      p ^ (2 * padicValInt p (f.resultant f.derivative) + 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply rootCount_polynomial_prime_pow_le_of_resultant f hdeg p hp
    (padicValInt p (f.resultant f.derivative)) _ k
  rw [padicValInt_dvd_iff]
  simp only [hR, false_or, Nat.not_succ_le_self, not_false_eq_true]

/-- Rational separability guarantees the nonzero integer resultant needed
for the bad-prime bounds. No preservation of degree at primes is presumed. -/
theorem polynomial_resultant_derivative_ne_zero_of_separable_map (f : ℤ[X])
    (hs : (f.map (Int.castRingHom ℚ)).Separable) : f.resultant f.derivative ≠ 0 := by
  intro hR
  have hzero : (f.map (Int.castRingHom ℚ)).resultant
      (f.map (Int.castRingHom ℚ)).derivative = 0 := by
    rw [derivative_map,
      Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective,
      Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℚ) Int.cast_injective,
      resultant_map_map, hR, map_zero]
  exact (Polynomial.resultant_eq_zero_iff.mp hzero).2 (separable_def _ |>.mp hs)

/-- Nonconstant irreducible integer polynomials have nonzero derivative
resultant, via Gauss's lemma and characteristic-zero separability. -/
theorem polynomial_resultant_derivative_ne_zero_of_irreducible (f : ℤ[X])
    (hf : Irreducible f) (hdeg : f.natDegree ≠ 0) : f.resultant f.derivative ≠ 0 := by
  have hF := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    (hf.isPrimitive hdeg)).mp hf
  exact polynomial_resultant_derivative_ne_zero_of_separable_map f hF.separable

/-- Thus the bad-prime bound is unconditional for every nonconstant
irreducible integer polynomial, not merely conditional on a resultant axiom. -/
theorem rootCount_irreducible_polynomial_prime_pow_le_resultant_valuation (f : ℤ[X])
    (hf : Irreducible f) (hdeg : f.natDegree ≠ 0) (p : ℕ) (hp : p.Prime) (k : ℕ) :
    rootCount (polynomialAbsValue f) (p ^ k) ≤
      p ^ (2 * padicValInt p (f.resultant f.derivative) + 1) :=
  rootCount_polynomial_prime_pow_le_resultant_valuation f (Nat.pos_of_ne_zero hdeg) p hp
    (polynomial_resultant_derivative_ne_zero_of_irreducible f hf hdeg) k

/-- There is an actual nonzero exceptional modulus for simplicity, namely
the absolute value of the derivative resultant. Its prime divisors are finite.
This does not identify polynomial and maximal-order root counts at bad primes. -/
theorem exists_good_prime_modulus_of_irreducible (f : ℤ[X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) :
    ∃ D > 0, ∀ p : ℕ, p.Prime → ¬ p ∣ D → PolynomialSimpleRootsMod f p := by
  have hR := polynomial_resultant_derivative_ne_zero_of_irreducible f hf hdeg
  refine ⟨(f.resultant f.derivative).natAbs, Int.natAbs_pos.mpr hR, ?_⟩
  intro p hp hpD
  exact polynomialSimpleRootsMod_of_not_dvd_resultant f (Nat.pos_of_ne_zero hdeg) p hp
    (by rwa [Int.natCast_dvd])

end Erdos975Support
