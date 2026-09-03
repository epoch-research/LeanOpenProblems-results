import Submission.MixedSieveDenominator

/-!
# A local-factor comparison for truncated sieve denominators

Changing the root multiplicity at one prime gains its exact local Euler
factor, after a fixed multiplicative reduction in the reference cutoff.
-/
open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

noncomputable def truncatedProductMass (P : Finset ℕ) (w : ℕ → ℝ) (z : ℕ) : ℝ :=
  ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z, ∏ p ∈ S, w p

lemma truncatedProductMass_nonneg (P : Finset ℕ) (w : ℕ → ℝ) (z : ℕ)
    (hw : ∀ p ∈ P, 0 ≤ w p) : 0 ≤ truncatedProductMass P w z :=
  sum_nonneg (fun _S hS => prod_nonneg (fun p hp => hw p ((mem_powerset.mp (mem_filter.mp hS).1) hp)))

lemma truncatedProductMass_mono_cutoff (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) {x y : ℕ} (hxy : x ≤ y) :
    truncatedProductMass P w x ≤ truncatedProductMass P w y := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro S hS
    exact mem_filter.mpr ⟨(mem_filter.mp hS).1,((mem_filter.mp hS).2).trans hxy⟩
  · intro S hS _
    exact prod_nonneg (fun p hp => hw p ((mem_powerset.mp (mem_filter.mp hS).1) hp))

lemma truncatedProductMass_mono_pool (P Q : Finset ℕ) (w : ℕ → ℝ) (z : ℕ)
    (hw : ∀ p ∈ Q, 0 ≤ w p) (hPQ : P ⊆ Q) :
    truncatedProductMass P w z ≤ truncatedProductMass Q w z := by
  apply sum_le_sum_of_subset_of_nonneg
  · intro S hS
    exact mem_filter.mpr ⟨mem_powerset.mpr ((mem_powerset.mp (mem_filter.mp hS).1).trans hPQ),
      (mem_filter.mp hS).2⟩
  · intro S hS _
    exact prod_nonneg (fun p hp => hw p ((mem_powerset.mp (mem_filter.mp hS).1) hp))

lemma truncatedProductMass_congr (P : Finset ℕ) (u v : ℕ → ℝ) (z : ℕ)
    (huv : ∀ p ∈ P, u p=v p) :
    truncatedProductMass P u z = truncatedProductMass P v z := by
  apply sum_congr rfl
  intro S hS
  apply prod_congr rfl
  exact fun p hp => huv p ((mem_powerset.mp (mem_filter.mp hS).1) hp)

lemma truncatedProductMass_insert (P : Finset ℕ) (w : ℕ → ℝ) (q z : ℕ)
    (hq : 0 < q) (hqP : q ∉ P) :
    truncatedProductMass (insert q P) w z =
      truncatedProductMass P w z+w q*truncatedProductMass P w (z/q) := by
  unfold truncatedProductMass
  simp only [sum_filter]
  rw [sum_powerset_insert hqP,mul_sum]
  congr 1
  apply sum_congr rfl
  intro S hS
  have hqS : q ∉ S := fun h => hqP ((mem_powerset.mp hS) h)
  rw [prod_insert hqS,prod_insert hqS]
  have he : q*(∏ p ∈ S, p) ≤ z ↔ (∏ p ∈ S, p) ≤ z/q := by
    rw [Nat.le_div_iff_mul_le hq,mul_comm]
  simp only [he, mul_ite, mul_zero]

lemma truncatedProductMass_insert_upper (P : Finset ℕ) (w : ℕ → ℝ) (q z : ℕ)
    (hq : 0 < q) (hqP : q ∉ P) (hw : ∀ p ∈ insert q P, 0 ≤ w p) :
    truncatedProductMass (insert q P) w z ≤ (1+w q)*truncatedProductMass P w z := by
  rw [truncatedProductMass_insert P w q z hq hqP]
  have hh := mul_le_mul_of_nonneg_left
    (truncatedProductMass_mono_cutoff P w (fun p hp => hw p (mem_insert_of_mem hp)) (Nat.div_le_self z q))
    (hw q (mem_insert_self _ _))
  linarith only [hh]

lemma truncatedProductMass_insert_lower (P : Finset ℕ) (w : ℕ → ℝ) (q z Z : ℕ)
    (hq : 0 < q) (hqP : q ∉ P) (hw : ∀ p ∈ insert q P, 0 ≤ w p) (hz : q*z ≤ Z) :
    (1+w q)*truncatedProductMass P w z ≤ truncatedProductMass (insert q P) w Z := by
  rw [truncatedProductMass_insert P w q Z hq hqP]
  have hmono {x y : ℕ} (hxy : x ≤ y) :=
    truncatedProductMass_mono_cutoff P w (fun p hp => hw p (mem_insert_of_mem hp)) hxy
  have hlow := hmono ((Nat.le_mul_of_pos_left z hq).trans hz)
  have hquot : z ≤ Z/q := (Nat.le_div_iff_mul_le hq).mpr (by simpa only [mul_comm] using hz)
  have hhigh := mul_le_mul_of_nonneg_left (hmono hquot) (hw q (mem_insert_self _ _))
  linarith only [hlow,hhigh]

lemma truncatedProductMass_local_comparison (P : Finset ℕ) (u v : ℕ → ℝ)
    (q z Z : ℕ) (hq : 0 < q) (hqP : q ∈ P)
    (hu : ∀ p ∈ P, 0 ≤ u p) (hv : ∀ p ∈ P, 0 ≤ v p)
    (he : ∀ p ∈ P.erase q, u p=v p) (K : ℝ) (hK : 0 ≤ K)
    (hfactor : 1+u q=K*(1+v q)) (hz : q*z ≤ Z) :
    K*truncatedProductMass P v z ≤ truncatedProductMass P u Z := by
  have hlo := truncatedProductMass_insert_lower (P.erase q) u q z Z hq (notMem_erase _ _) (by
    simpa only [insert_erase hqP] using hu) hz
  have hup := truncatedProductMass_insert_upper (P.erase q) v q z hq (notMem_erase _ _) (by
    simpa only [insert_erase hqP] using hv)
  rw [insert_erase hqP] at hlo hup
  rw [hfactor,truncatedProductMass_congr (P.erase q) u v z he] at hlo
  exact (mul_le_mul_of_nonneg_left hup hK).trans (by simpa only [mul_assoc] using hlo)

noncomputable def pairLocalWeight (a p : ℕ) : ℝ :=
  (pairRootMultiplicity a p : ℝ)/((p : ℝ)-pairRootMultiplicity a p)

lemma pairLocalWeight_nonneg (a p : ℕ) (ha : 2 ∣ a) (hp : p.Prime) :
    0 ≤ pairLocalWeight a p := by
  have hh := (pairRootMultiplicity_properties a p ha hp).2.2
  unfold pairLocalWeight
  exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hh.le))

lemma mixedPairDenominator_eq_truncated (a z : ℕ) (P : Finset ℕ) :
    mixedPairDenominator a z P = truncatedProductMass P (pairLocalWeight a) z := by
  unfold mixedPairDenominator truncatedProductMass
  apply sum_congr rfl
  intro S hS
  rw [← prod_inv_distrib]
  simp only [mixed_root_weight_eq,pairLocalWeight]

lemma mixedPairDenominator_mono_pool (a z : ℕ) (P Q : Finset ℕ)
    (ha : 2 ∣ a) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : P ⊆ Q) :
    mixedPairDenominator a z P ≤ mixedPairDenominator a z Q := by
  simp only [mixedPairDenominator_eq_truncated]
  exact truncatedProductMass_mono_pool P Q _ z (fun p hp => pairLocalWeight_nonneg a p ha (hQ p hp)) hPQ

/-- The local factor at three doubles the denominator for coefficient 3*a,
at a reference cutoff reduced by a factor three. -/
lemma mixedPairDenominator_three_comparison (a z Z : ℕ) (P : Finset ℕ)
    (ha : 2 ∣ a) (h3a : ¬3 ∣ a) (hP : ∀ p ∈ P, p.Prime) (h3P : 3 ∈ P)
    (hz : 3*z ≤ Z) :
    2*mixedPairDenominator (3*a) z P ≤ mixedPairDenominator a Z P := by
  simp only [mixedPairDenominator_eq_truncated]
  apply truncatedProductMass_local_comparison P _ _ 3 z Z (by decide) h3P
    (fun p hp => pairLocalWeight_nonneg a p ha (hP p hp))
    (fun p hp => pairLocalWeight_nonneg (3*a) p (dvd_mul_of_dvd_right ha 3) (hP p hp)) ?_ 2 (by norm_num) ?_ hz
  · intro p hp
    have hp3 : p ≠ 3 := (mem_erase.mp hp).1
    have hpr := hP p (mem_erase.mp hp).2
    have he : p ∣ 3*a ↔ p ∣ a := by
      rw [hpr.dvd_mul]
      have hnot : ¬p ∣ 3 := by
        intro h
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_three).mp h)
      simp [hnot]
    simp [pairLocalWeight,pairRootMultiplicity,he]
  · norm_num [pairLocalWeight,pairRootMultiplicity,h3a]

noncomputable def threeCorrection (a : ℕ) : ℝ := if 3 ∣ a then 1 else 3/4

lemma threeCorrection_bounds (a : ℕ) : (3/4 : ℝ) ≤ threeCorrection a ∧ threeCorrection a ≤ 1 := by
  unfold threeCorrection
  split_ifs <;> norm_num

/-- The effective logarithmic length is L-2; the local gain is retained exactly. -/
theorem mixedPairDenominator_three_dyadic_lower (a L : ℕ)
    (ha : 0 < a) (h2a : 2 ∣ a) (hL : 2 ≤ L) :
    ((a.totient : ℝ)/(a : ℝ))*(((L-2 : ℕ) : ℝ)*Real.log 2)^2/2 ≤
      threeCorrection a*mixedPairDenominator a (2^L) (2^L+1).primesBelow := by
  have hbase := mixedPairDenominator_dyadic_lower a L ha h2a
  by_cases h3a : 3 ∣ a
  · simp only [threeCorrection,if_pos h3a,one_mul]
    apply le_trans _ hbase
    gcongr
    exact_mod_cast Nat.sub_le L 2
  · let z := 2^(L-2)
    let Z := 2^L
    let P := (Z+1).primesBelow
    have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
    have hZ : 4 ≤ Z := by
      change 2^2 ≤ 2^L
      exact Nat.pow_le_pow_right (by decide) hL
    have h3P : 3 ∈ P := Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_three⟩
    have hlen : 3*z ≤ Z := by
      have he : Z=z*4 := by
        dsimp [z,Z]
        rw [← Nat.sub_add_cancel hL,pow_add]
        norm_num
      rw [he]
      omega
    have hzZ : z ≤ Z := (Nat.le_mul_of_pos_left z (by decide)).trans hlen
    have hpool : (z+1).primesBelow ⊆ P := by
      intro p hp
      obtain ⟨hpz,hpr⟩ := Nat.mem_primesBelow.mp hp
      exact Nat.mem_primesBelow.mpr ⟨by omega,hpr⟩
    have hcomp := mixedPairDenominator_three_comparison a z Z P h2a h3a hP h3P hlen
    have hmono := mixedPairDenominator_mono_pool (3*a) z (z+1).primesBelow P
      (dvd_mul_of_dvd_right h2a 3) hP hpool
    have hlower := mixedPairDenominator_dyadic_lower (3*a) (L-2) (by omega)
      (dvd_mul_of_dvd_right h2a 3)
    have hphi : ((3*a).totient : ℝ)/(3*a : ℕ) = (2/3 : ℝ)*((a.totient : ℝ)/(a : ℝ)) := by
      rw [Nat.totient_mul (Nat.prime_three.coprime_iff_not_dvd.mpr h3a)]
      rw [Nat.totient_prime Nat.prime_three]
      norm_num [Nat.cast_mul]
      ring
    rw [hphi] at hlower
    change _ ≤ threeCorrection a*mixedPairDenominator a Z P
    simp only [threeCorrection,if_neg h3a]
    change _ ≤ mixedPairDenominator (3*a) z (z+1).primesBelow at hlower
    nlinarith only [hlower,hmono,hcomp]

end Erdos821.Sieve
