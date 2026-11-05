import Submission.ResidueBlockCounts

/-!
# Distance valuation and the same-side bound

For distinct positive natural labels, the baseline is also a lower bound
for the valuation of their natural distance.  Removing the doubled-label
self levels counts exactly the excess over that baseline.  The retained
same-side blocks form only a subcollection of those levels.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux.ResidueBlocks

theorem min_factorization_le_factorization_dist {p x y : ℕ} (hp : p.Prime)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    min (x.factorization p) (y.factorization p) ≤ (Nat.dist x y).factorization p := by
  have hd : Nat.dist x y ≠ 0 := (Nat.dist_pos_of_ne hxy).ne'
  apply (hp.pow_dvd_iff_le_factorization hd).1
  have hdx : p ^ min (x.factorization p) (y.factorization p) ∣ x :=
    (hp.pow_dvd_iff_le_factorization hx.ne').2 (min_le_left _ _)
  have hdy : p ^ min (x.factorization p) (y.factorization p) ∣ y :=
    (hp.pow_dvd_iff_le_factorization hy.ne').2 (min_le_right _ _)
  exact (modEq_iff_dvd_dist _ _ _).1 (hdx.modEq_zero_nat.trans hdy.modEq_zero_nat.symm)

theorem factorization_dist_eq_left_of_lt {p x y : ℕ} (hp : p.Prime)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y)
    (h : x.factorization p < y.factorization p) :
    (Nat.dist x y).factorization p = x.factorization p := by
  have hlo := min_factorization_le_factorization_dist hp hx hy hxy
  rw [min_eq_left h.le] at hlo
  have hhi : (Nat.dist x y).factorization p ≤ x.factorization p := by
    by_contra hhi
    have hdd : p ^ (x.factorization p + 1) ∣ Nat.dist x y :=
      (hp.pow_dvd_iff_le_factorization (Nat.dist_pos_of_ne hxy).ne').2 (by omega)
    have hdy : p ^ (x.factorization p + 1) ∣ y :=
      (hp.pow_dvd_iff_le_factorization hy.ne').2 (by omega)
    have hdx : p ^ (x.factorization p + 1) ∣ x :=
      Nat.modEq_zero_iff_dvd.1 (((modEq_iff_dvd_dist _ _ _).2 hdd).trans hdy.modEq_zero_nat)
    exact Nat.pow_succ_factorization_not_dvd hx.ne' hp hdx
  exact Nat.le_antisymm hhi hlo

theorem factorization_dist_eq_min_of_ne {p x y : ℕ} (hp : p.Prime)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y)
    (h : x.factorization p ≠ y.factorization p) :
    (Nat.dist x y).factorization p = min (x.factorization p) (y.factorization p) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [factorization_dist_eq_left_of_lt hp hx hy hxy hlt, min_eq_left hlt.le]
  · rw [Nat.dist_comm, factorization_dist_eq_left_of_lt hp hy hx hxy.symm hgt,
      min_eq_right hgt.le]

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- The same baseline is removable from both sum and distance valuations. -/
theorem primeBaseline_le_factorization_dist (a : ι → ℕ) (p : ℕ) (i j : ι)
    (hp : p.Prime) (hi : 0 < a i) (hj : 0 < a j) (hij : a i ≠ a j) :
    primeBaseline a p i j ≤ ((Nat.dist (a i) (a j)).factorization p : ℝ) := by
  by_cases heq : (a i).factorization p = (a j).factorization p
  · have hbase := baseline_eq_double_of_heights_eq a p i j hi heq
    rw [hbase]
    have hs := primeBaseline_le_factorization_add a hp i j hi hj
    rw [hbase] at hs
    have hsum : (2 * a i).factorization p ≤ (a i + a j).factorization p := by
      exact_mod_cast hs
    have hsd : p ^ (2 * a i).factorization p ∣ a i + a j :=
      (hp.pow_dvd_iff_le_factorization (by omega : a i + a j ≠ 0)).2 hsum
    have hdd : p ^ (2 * a i).factorization p ∣ 2 * a i :=
      (hp.pow_dvd_iff_le_factorization (by omega : 2 * a i ≠ 0)).2 (le_refl _)
    have hd : p ^ (2 * a i).factorization p ∣ Nat.dist (a i) (a j) := by
      apply (modEq_iff_dvd_dist _ _ _).1
      have hdd' : a i + a i ≡ 0 [MOD p ^ (2 * a i).factorization p] := by
        simpa only [two_mul] using hdd.modEq_zero_nat
      exact (hdd'.trans hsd.modEq_zero_nat.symm).add_left_cancel' (a i)
    exact_mod_cast (hp.pow_dvd_iff_le_factorization (Nat.dist_pos_of_ne hij).ne').1 hd
  · rw [primeBaseline_eq_min_of_ne a p i j heq]
    exact_mod_cast min_factorization_le_factorization_dist hp hi hj hij

omit [Fintype ι] in
theorem distance_double_excess_eq (a : ι → ℕ) (p : ℕ) (i j : ι)
    (hp : p.Prime) (hi : 0 < a i) (hj : 0 < a j) (hij : a i ≠ a j) :
    (((Nat.dist (a i) (a j)).factorization p - (2 * a i).factorization p : ℕ) : ℝ) =
      ((Nat.dist (a i) (a j)).factorization p : ℝ) - primeBaseline a p i j := by
  by_cases heq : (a i).factorization p = (a j).factorization p
  · rw [baseline_eq_double_of_heights_eq a p i j hi heq]
    apply Nat.cast_sub
    have hb := primeBaseline_le_factorization_dist a p i j hp hi hj hij
    rw [baseline_eq_double_of_heights_eq a p i j hi heq] at hb
    exact_mod_cast hb
  · rw [primeBaseline_eq_min_of_ne a p i j heq,
      factorization_dist_eq_min_of_ne hp hi hj hij heq, sub_self]
    have hle : min ((a i).factorization p) ((a j).factorization p) ≤
        (2 * a i).factorization p := by
      rw [factorization_two_mul hi]
      exact (min_le_left _ _).trans (Nat.le_add_right _ _)
    simp only [Nat.sub_eq_zero_of_le hle, Nat.cast_zero]

omit [Fintype ι] in
/-- A truncated nonself distance-level count is bounded by the valuation
excess.  No upper cutoff on distance valuations is required. -/
theorem distance_levelCount_le (a : ι → ℕ) (p M : ℕ) (i j : ι)
    (hp : p.Prime) (hi : 0 < a i) (hj : 0 < a j) (hij : a i ≠ a j) :
    levelCount p (Nat.dist (a i) (a j)) (2 * a i) M ≤
      ((Nat.dist (a i) (a j)).factorization p : ℝ) - primeBaseline a p i j := by
  exact (levelCount_le p (Nat.dist (a i) (a j)) (2 * a i) M hp
    (Nat.dist_pos_of_ne hij).ne' (by omega)).trans_eq
      (distance_double_excess_eq a p i j hp hi hj hij)

/-- The complete retained same-side kernel is bounded off the diagonal
by the distance valuation minus the common baseline. -/
theorem diagSum_le_distance_excess (a : ι → ℕ) (S : Finset ℕ) (M : ℕ)
    (ha : ∀ i, 0 < a i) (hS : ∀ p ∈ S, p.Prime) (i j : ι) (hij : a i ≠ a j) :
    Paired.diagSum (nodeBlock a S M) i j ≤
      (∑ p ∈ S, Real.log (p : ℝ) * ((Nat.dist (a i) (a j)).factorization p : ℝ)) -
        primeBaselineSum a S i j := by
  rw [diagSum_eq_levels]
  calc
    _ ≤ ∑ p : ↥S, Real.log (p : ℝ) * levelCount (p : ℕ)
        (Nat.dist (a i) (a j)) (2 * a i) M := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        _ ≤ ∑ k : Fin (M + 1),
            if (p : ℕ) ^ (k : ℕ) ∣ Nat.dist (a i) (a j) ∧ ¬(p : ℕ) ^ (k : ℕ) ∣ 2 * a i
            then Real.log (p : ℝ) else 0 :=
          Finset.sum_le_sum (fun k hk => diagLevel_le a (p : ℕ) (k : ℕ) i j)
        _ = Real.log (p : ℝ) * levelCount (p : ℕ)
            (Nat.dist (a i) (a j)) (2 * a i) M := by
          rw [Fin.sum_univ_eq_sum_range
            (fun k : ℕ => if (p : ℕ) ^ k ∣ Nat.dist (a i) (a j) ∧ ¬(p : ℕ) ^ k ∣ 2 * a i
              then Real.log (p : ℝ) else 0) (M + 1)]
          unfold levelCount
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          split_ifs <;> simp
    _ ≤ ∑ p : ↥S, Real.log (p : ℝ) *
        (((Nat.dist (a i) (a j)).factorization (p : ℕ) : ℝ) - primeBaseline a (p : ℕ) i j) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (distance_levelCount_le a (p : ℕ) M i j (hS p p.property) (ha i) (ha j) hij)
        (Real.log_natCast_nonneg p)
    _ = _ := by
      rw [Finset.sum_coe_sort S (fun p : ℕ => Real.log (p : ℝ) *
        (((Nat.dist (a i) (a j)).factorization p : ℝ) - primeBaseline a p i j))]
      unfold primeBaselineSum
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end Erdos126Aux.ResidueBlocks
