import Submission.FactorialMinusOneLcmBound

/-!
A weighted-norm / shift-length trade-off for integer row annihilators.
This is auxiliary arithmetic, not a proof or disproof of Spec.lean.
-/
namespace AnnihilatorWeightedHeight

open Finset

noncomputable def weightedMass {ι : Type*} (s : Finset ι)
    (z : ι → ℤ) (offset : ι → ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, |(z i : ℝ)| / x ^ offset i

lemma weightedMass_nonneg {ι : Type*} (s : Finset ι)
    (z : ι → ℤ) (offset : ι → ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ weightedMass s z offset x := by
  apply sum_nonneg
  intro i _
  exact div_nonneg (abs_nonneg _) (pow_nonneg hx _)

/-- Bounding the weighted mass by one does not permit an arbitrarily large
retained coefficient at short shift length. -/
theorem retained_coefficient_bound {ι : Type*} (s : Finset ι)
    (z : ι → ℤ) (offset : ι → ℕ) (x : ℝ) (L : ℕ)
    (hx : 1 ≤ x) (hL : ∀ i ∈ s, offset i ≤ L) :
    |((∑ i ∈ s, z i : ℤ) : ℝ)| ≤ x ^ L * weightedMass s z offset x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  calc
    _ = |∑ i ∈ s, (z i : ℝ)| := by simp
    _ ≤ ∑ i ∈ s, |(z i : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, x ^ L * (|(z i : ℝ)| / x ^ offset i) := by
      apply sum_le_sum
      intro i hi
      have hp : 0 < x ^ offset i := pow_pos hx0 _
      calc
        _ = (|(z i : ℝ)| / x ^ offset i) * x ^ offset i :=
          (div_mul_cancel₀ _ hp.ne').symm
        _ ≤ (|(z i : ℝ)| / x ^ offset i) * x ^ L :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (hL i hi))
            (div_nonneg (abs_nonneg _) hp.le)
        _ = _ := mul_comm _ _
    _ = _ := by simp only [weightedMass, mul_sum]

/-- The offsets control the weighted norm; the actual sample indices may
include any common starting index or may be otherwise unrelated. -/
theorem annihilator_weighted_height {ι : Type*} (s : Finset ι)
    (z : ι → ℤ) (index offset : ι → ℕ) (m L : ℕ) (x : ℝ)
    (hm : 5 ≤ m) (hx : 1 ≤ x) (hL : ∀ i ∈ s, offset i ≤ L)
    (hA : (∑ i ∈ s, z i) ≠ 0)
    (hz : ∀ j < m, ∑ i ∈ s, (z i : ℚ) /
      ((((4*m^2+j).factorial : ℚ) ^ (index i / (4*m^2+j))) *
        ((4*m^2+j).factorial-1)) = 0) :
    (m : ℝ) ^ (m^3) ≤ x ^ L * weightedMass s z offset x := by
  have h := FactorialMinusOneLcmBound.annihilator_coefficient_height
    s z index m hm hA hz
  have hc : (m : ℝ) ^ (m^3) ≤ |((∑ i ∈ s, z i : ℤ) : ℝ)| := by
    have hh : ((m^(m^3) : ℕ) : ℝ) ≤ ((∑ i ∈ s, z i).natAbs : ℝ) := by
      exact_mod_cast h
    simpa only [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] using hh
  exact hc.trans (retained_coefficient_bound s z offset x L hx hL)

/-- A unit weighted-norm budget forces a quantitative shift-length lower
bound. In particular, low-degree row interpolation cannot ignore its
coefficient cost. This remains conditional on a nonzero retained sum. -/
theorem annihilator_length_bound {ι : Type*} (s : Finset ι)
    (z : ι → ℤ) (index offset : ι → ℕ) (m L a : ℕ) (x : ℝ)
    (hm : 5 ≤ m) (hx : 1 ≤ x) (hxm : x ≤ (m : ℝ)^a)
    (hL : ∀ i ∈ s, offset i ≤ L)
    (hA : (∑ i ∈ s, z i) ≠ 0)
    (hW : weightedMass s z offset x ≤ 1)
    (hz : ∀ j < m, ∑ i ∈ s, (z i : ℚ) /
      ((((4*m^2+j).factorial : ℚ) ^ (index i / (4*m^2+j))) *
        ((4*m^2+j).factorial-1)) = 0) :
    m^3 ≤ a*L := by
  have hb := annihilator_weighted_height s z index offset m L x hm hx hL hA hz
  have hpow : (m : ℝ)^(m^3) ≤ (m : ℝ)^(a*L) := by
    calc
      _ ≤ x^L * weightedMass s z offset x := hb
      _ ≤ x^L * 1 := mul_le_mul_of_nonneg_left hW (pow_nonneg (by linarith) _)
      _ = x^L := mul_one _
      _ ≤ ((m : ℝ)^a)^L := pow_le_pow_left₀ (by linarith) hxm _
      _ = _ := (pow_mul _ _ _).symm
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  exact (pow_le_pow_iff_right₀ hmR).mp hpow

end AnnihilatorWeightedHeight

#print axioms AnnihilatorWeightedHeight.retained_coefficient_bound
#print axioms AnnihilatorWeightedHeight.annihilator_weighted_height
#print axioms AnnihilatorWeightedHeight.annihilator_length_bound
