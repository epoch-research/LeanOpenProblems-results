import Submission.PolynomialSetup

/-!
# Algebraic foundations for the polynomial root-count mean

This file identifies the existing residue root count with roots in `ZMod q`,
proves its multiplicativity by the Chinese remainder theorem, and proves the
prime-modulus degree bound for primitive integer polynomials. These are local
algebraic results, not an assertion of the general root-count mean theorem.
-/

namespace Erdos975Support

open Polynomial

/-- Divisibility of the absolute value is exactly vanishing modulo `q`. -/
theorem polynomialAbsValue_dvd_iff_eval₂_eq_zero (f : ℤ[X]) (q n : ℕ) :
    q ∣ polynomialAbsValue f n ↔
      f.eval₂ (Int.castRingHom (ZMod q)) (n : ZMod q) = 0 := by
  rw [Polynomial.eval₂_at_natCast, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd,
    Int.natCast_dvd]
  rfl

/-- Representatives in the filtered range correspond to polynomial roots in
`ZMod q`. The positivity restriction is essential: `rootCount g 0 = 0`,
whereas `ZMod 0` is the infinite ring of integers. -/
def polynomialResidueRootsEquiv (f : ℤ[X]) (q : ℕ) [NeZero q] :
    {r // r ∈ (Finset.range q).filter (fun r ↦ q ∣ polynomialAbsValue f r)} ≃
      {x : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) x = 0} where
  toFun r := ⟨(r.1 : ZMod q),
    (polynomialAbsValue_dvd_iff_eval₂_eq_zero f q r.1).mp
      (Finset.mem_filter.mp r.2).2⟩
  invFun x := ⟨x.1.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.1.val_lt,
    (polynomialAbsValue_dvd_iff_eval₂_eq_zero f q x.1.val).mpr (by
      simpa only [ZMod.natCast_zmod_val] using x.2)⟩⟩
  left_inv r := Subtype.ext (ZMod.val_natCast_of_lt
    (Finset.mem_range.mp (Finset.mem_filter.mp r.2).1))
  right_inv x := Subtype.ext (ZMod.natCast_zmod_val x.1)

/-- The root count is the cardinality of the set of roots in the finite
residue ring. No monicity or irreducibility hypothesis is needed. -/
theorem rootCount_polynomial_eq_card_zmod (f : ℤ[X]) (q : ℕ) [NeZero q] :
    rootCount (polynomialAbsValue f) q =
      Nat.card {x : ZMod q // f.eval₂ (Int.castRingHom (ZMod q)) x = 0} := by
  have h := Nat.card_congr (polynomialResidueRootsEquiv f q)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, rootCount] using h

/-- The CRT also identifies the root sets, not just their cardinalities. -/
def polynomialRootsChineseRemainder (f : ℤ[X]) {m n : ℕ} (h : m.Coprime n) :
    {x : ZMod (m * n) // f.eval₂ (Int.castRingHom (ZMod (m * n))) x = 0} ≃
      {x : ZMod m // f.eval₂ (Int.castRingHom (ZMod m)) x = 0} ×
        {x : ZMod n // f.eval₂ (Int.castRingHom (ZMod n)) x = 0} := by
  let e := ZMod.chineseRemainder h
  have heval (x : ZMod (m * n)) :
      e (f.eval₂ (Int.castRingHom (ZMod (m * n))) x) =
        (f.eval₂ (Int.castRingHom (ZMod m)) (e x).1,
          f.eval₂ (Int.castRingHom (ZMod n)) (e x).2) := by
    ext
    · simpa only [RingHom.comp_apply] using
        (f.hom_eval₂ (Int.castRingHom (ZMod (m * n)))
          ((RingHom.fst (ZMod m) (ZMod n)).comp e.toRingHom) x).trans
          (congrArg (fun i ↦ f.eval₂ i (e x).1) (RingHom.ext_int _ _))
    · simpa only [RingHom.comp_apply] using
        (f.hom_eval₂ (Int.castRingHom (ZMod (m * n)))
          ((RingHom.snd (ZMod m) (ZMod n)).comp e.toRingHom) x).trans
          (congrArg (fun i ↦ f.eval₂ i (e x).2) (RingHom.ext_int _ _))
  have hzero (x : ZMod (m * n)) :
      f.eval₂ (Int.castRingHom (ZMod (m * n))) x = 0 ↔
        f.eval₂ (Int.castRingHom (ZMod m)) (e x).1 = 0 ∧
          f.eval₂ (Int.castRingHom (ZMod n)) (e x).2 = 0 := by
    rw [← e.map_eq_zero_iff, heval, Prod.mk_eq_zero]
  exact (Equiv.subtypeEquiv e.toEquiv hzero).trans Equiv.subtypeProdEquivProd

@[simp]
theorem rootCount_polynomial_zero (f : ℤ[X]) :
    rootCount (polynomialAbsValue f) 0 = 0 := by
  simp [rootCount]

@[simp]
theorem rootCount_polynomial_one (f : ℤ[X]) :
    rootCount (polynomialAbsValue f) 1 = 1 := by
  simp [rootCount]

/-- Polynomial root counts are multiplicative, including the zero-modulus
convention of the existing definition. -/
theorem rootCount_polynomial_mul (f : ℤ[X]) {m n : ℕ} (h : m.Coprime n) :
    rootCount (polynomialAbsValue f) (m * n) =
      rootCount (polynomialAbsValue f) m * rootCount (polynomialAbsValue f) n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  letI : NeZero m := ⟨hm⟩
  letI : NeZero n := ⟨hn⟩
  letI : NeZero (m * n) := ⟨mul_ne_zero hm hn⟩
  rw [rootCount_polynomial_eq_card_zmod, rootCount_polynomial_eq_card_zmod,
    rootCount_polynomial_eq_card_zmod,
    Nat.card_congr (polynomialRootsChineseRemainder f h), Nat.card_prod]

/-- A primitive integer polynomial cannot reduce to zero modulo a prime.
In particular, primes dividing the leading coefficient still cause no
zero-polynomial exception to the prime-modulus degree bound. -/
theorem polynomial_map_zmod_ne_zero_of_isPrimitive (f : ℤ[X]) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hzero
  have hdiv : C (p : ℤ) ∣ f := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    have hi := congrArg (fun g : (ZMod p)[X] ↦ g.coeff i) hzero
    simpa only [coeff_map, Int.coe_castRingHom, coeff_zero] using hi
  have hu := (Int.isUnit_iff_natAbs_eq.mp (hf (p : ℤ) hdiv))
  simp only [Int.natAbs_natCast] at hu
  exact hp.ne_one hu

/-- Over a prime residue field, distinct roots of a primitive polynomial
are bounded by the original degree (even at leading-coefficient bad primes). -/
theorem rootCount_polynomial_prime_le (f : ℤ[X]) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) : rootCount (polynomialAbsValue f) p ≤ f.natDegree := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [rootCount_polynomial_eq_card_zmod]
  let F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := polynomial_map_zmod_ne_zero_of_isPrimitive f hf p hp
  have hbound : Nat.card {x : ZMod p // f.eval₂ (Int.castRingHom (ZMod p)) x = 0} ≤
      F.natDegree := by
    rw [Nat.card_eq_fintype_card]
    by_contra h
    apply hF
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero F Subtype.val_injective
      (fun x ↦ ?_) (lt_of_not_ge h)
    simpa only [F, eval_map] using x.2
  exact hbound.trans natDegree_map_le

/-- Irreducibility and nonconstancy supply primitivity automatically. -/
theorem rootCount_irreducible_polynomial_prime_le (f : ℤ[X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) (p : ℕ) (hp : p.Prime) :
    rootCount (polynomialAbsValue f) p ≤ f.natDegree :=
  rootCount_polynomial_prime_le f (hf.isPrimitive hdeg) p hp

end Erdos975Support
