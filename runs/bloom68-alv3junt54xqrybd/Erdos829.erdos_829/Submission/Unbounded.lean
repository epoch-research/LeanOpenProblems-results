import Submission.TangentInvariant
import Submission.TangentPositive
import Submission.DivisorBound

/-!
# Cofinal unboundedness of the number of sums of two cubes

Finitely many positive points of the primitive tangent orbit can be scaled to
natural root pairs with one common cube sum. Primitive-coordinate uniqueness
ensures that these root pairs are distinct. The common scale can be made large
enough to put the cube sum in any prescribed tail.

Consequently the representation count is not Big-O of a constant, and the
exponent-zero logarithmic bound fails. This does not negate the existential
polylogarithmic assertion in Erdős Problem 829.
-/

open scoped BigOperators
open AdditiveCombinatorics Asymptotics Filter

namespace Erdos829Aux

open Tangent

/-- Clear a positive triple's denominator using a natural common multiple. -/
private def scaledRoots (D : ℕ) (p : Triple) : ℕ × ℕ :=
  (p.a.toNat * (D / p.w.toNat), p.b.toNat * (D / p.w.toNat))

private theorem scaledRoots_mem {p : Triple} {D : ℕ}
    (hp : Good p) (hpos : Positive p) (hdiv : p.w.toNat ∣ D) :
    scaledRoots D p ∈ rootPairs (9 * D ^ 3) := by
  have hc : p.a.toNat ^ 3 + p.b.toNat ^ 3 = 9 * p.w.toNat ^ 3 := by
    have hcZ : (p.a.toNat : ℤ) ^ 3 + (p.b.toNat : ℤ) ^ 3 =
        9 * (p.w.toNat : ℤ) ^ 3 := by
      simpa only [Int.toNat_of_nonneg hpos.1.le, Int.toNat_of_nonneg hpos.2.le,
        Int.toNat_of_nonneg hp.1.le] using hp.2.2
    exact_mod_cast hcZ
  apply mem_rootPairs.mpr
  change (p.a.toNat * (D / p.w.toNat)) ^ 3 +
    (p.b.toNat * (D / p.w.toNat)) ^ 3 = 9 * D ^ 3
  calc
    _ = (p.a.toNat ^ 3 + p.b.toNat ^ 3) * (D / p.w.toNat) ^ 3 := by ring
    _ = 9 * (p.w.toNat * (D / p.w.toNat)) ^ 3 := by rw [hc]; ring
    _ = _ := by rw [Nat.mul_div_cancel' hdiv]

/-- Equal scaled coordinates imply equality after cross-multiplication. -/
private theorem cross_mul_of_scaled_eq {D x y w v : ℕ}
    (hD : D ≠ 0) (hw : w ∣ D) (hv : v ∣ D)
    (h : x * (D / w) = y * (D / v)) : x * v = y * w := by
  apply mul_right_cancel₀ hD
  calc
    (x * v) * D = (x * (D / w)) * (w * v) := by
      calc
        _ = (x * v) * (w * (D / w)) := by rw [Nat.mul_div_cancel' hw]
        _ = _ := by ring
    _ = (y * (D / v)) * (w * v) := by rw [h]
    _ = (y * w) * D := by
      calc
        _ = (y * w) * (v * (D / v)) := by ring
        _ = _ := by rw [Nat.mul_div_cancel' hv]

private theorem scaledRoots_eq {p q : Triple} {D : ℕ}
    (hp : Good p) (hq : Good q) (hposp : Positive p) (hposq : Positive q)
    (hD : D ≠ 0) (hpdiv : p.w.toNat ∣ D) (hqdiv : q.w.toNat ∣ D)
    (h : scaledRoots D p = scaledRoots D q) : p = q := by
  have ha : p.a.toNat * q.w.toNat = q.a.toNat * p.w.toNat :=
    cross_mul_of_scaled_eq hD hpdiv hqdiv (congrArg Prod.fst h)
  have hb : p.b.toNat * q.w.toNat = q.b.toNat * p.w.toNat :=
    cross_mul_of_scaled_eq hD hpdiv hqdiv (congrArg Prod.snd h)
  apply good_eq_of_cross_mul hp hq
  · have haZ : (p.a.toNat : ℤ) * (q.w.toNat : ℤ) =
        (q.a.toNat : ℤ) * (p.w.toNat : ℤ) := by exact_mod_cast ha
    simpa only [Int.toNat_of_nonneg hposp.1.le, Int.toNat_of_nonneg hposq.1.le,
      Int.toNat_of_nonneg hp.1.le, Int.toNat_of_nonneg hq.1.le] using haZ
  · have hbZ : (p.b.toNat : ℤ) * (q.w.toNat : ℤ) =
        (q.b.toNat : ℤ) * (p.w.toNat : ℤ) := by exact_mod_cast hb
    simpa only [Int.toNat_of_nonneg hposp.2.le, Int.toNat_of_nonneg hposq.2.le,
      Int.toNat_of_nonneg hp.1.le, Int.toNat_of_nonneg hq.1.le] using hbZ

/-- Every tail contains a number with arbitrarily many ordered representations
as a sum of two natural cubes. -/
theorem sumRep_cubes_cofinally_unbounded (K N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ K ≤ sumRep cubes n := by
  classical
  have hinf : {k : ℕ | Positive (orbit k)}.Infinite :=
    infinite_positive_indices orbit good_orbit (fun _ => rfl)
  obtain ⟨s, hs, hcard⟩ := hinf.exists_subset_card_eq K
  let W : ℕ := ∏ i ∈ s, (orbit i).w.toNat
  let D : ℕ := (N + 1) * W
  have hWpos : 0 < W := by
    apply Finset.prod_pos
    intro i hi
    exact Int.pos_iff_toNat_pos.mp (good_orbit i).1
  have hDpos : 0 < D := Nat.mul_pos (by omega) hWpos
  have hDge : N + 1 ≤ D := Nat.le_mul_of_pos_right (N + 1) hWpos
  have hdiv : ∀ i ∈ s, (orbit i).w.toNat ∣ D := by
    intro i hi
    exact dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem (fun j => (orbit j).w.toNat) hi) (N + 1)
  have hcount : s.card ≤ (rootPairs (9 * D ^ 3)).card := by
    apply Finset.card_le_card_of_injOn (fun i => scaledRoots D (orbit i))
    · intro i hi
      exact scaledRoots_mem (good_orbit i) (hs hi) (hdiv i hi)
    · intro i hi j hj hij
      apply orbit_injective
      exact scaledRoots_eq (good_orbit i) (good_orbit j) (hs hi) (hs hj)
        hDpos.ne' (hdiv i hi) (hdiv j hj) hij
  refine ⟨9 * D ^ 3, ?_, ?_⟩
  · calc
      N ≤ D := (Nat.le_succ N).trans hDge
      _ ≤ D ^ 3 := Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) D
      _ ≤ 9 * D ^ 3 := Nat.le_mul_of_pos_left _ (by norm_num)
  · rw [sumRep_cubes_eq_card_rootPairs]
    simpa only [hcard] using hcount

/-- The representation count is not Big-O of any real constant. -/
theorem sumRep_cubes_not_isBigO_const (c : ℝ) :
    ¬ ((fun n : ℕ => (sumRep cubes n : ℝ)) =O[atTop]
      (fun _ : ℕ => c)) := by
  intro h
  obtain ⟨A, hA⟩ := isBigO_iff.mp h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hA
  obtain ⟨K, hK⟩ := exists_nat_gt (A * ‖c‖)
  obtain ⟨n, hn, hk⟩ := sumRep_cubes_cofinally_unbounded K N
  have hle : (sumRep cubes n : ℝ) ≤ A * ‖c‖ := by
    simpa only [Real.norm_natCast] using hN n hn
  have hge : (K : ℝ) ≤ (sumRep cubes n : ℝ) := by exact_mod_cast hk
  exact (not_lt_of_ge (hge.trans hle)) hK

/-- In particular, the representation count is not `O(1)` at infinity. -/
theorem sumRep_cubes_not_isBigO_one :
    ¬ ((fun n : ℕ => (sumRep cubes n : ℝ)) =O[atTop]
      (fun _ : ℕ => (1 : ℝ))) :=
  sumRep_cubes_not_isBigO_const 1

/-- The logarithmic bound with exponent zero fails. This does not rule out
bounds with a positive exponent. -/
theorem sumRep_cubes_not_isBigO_log_pow_zero :
    ¬ ((fun n : ℕ => (sumRep cubes n : ℝ)) =O[atTop]
      (fun n : ℕ => (Real.log n) ^ (0 : ℕ))) := by
  simpa only [pow_zero] using sumRep_cubes_not_isBigO_one

/-- Any natural exponent giving a logarithmic Big-O bound must be nonzero. -/
theorem sumRep_cubes_log_pow_exponent_ne_zero {C : ℕ}
    (h : (fun n : ℕ => (sumRep cubes n : ℝ)) =O[atTop]
      (fun n : ℕ => (Real.log n) ^ C)) : C ≠ 0 := by
  intro hC
  apply sumRep_cubes_not_isBigO_log_pow_zero
  simpa only [hC] using h

end Erdos829Aux
