import Submission.BuchstabOrderedCost
import Submission.SelbergPrimes

/-! Sharper depth-uniform costs using uniqueness of prime subset products.
The resulting zeta factor has only a simple pole as the exponent tends to one.
This does not assert the quadratic Jacobsthal conjecture. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real
set_option maxHeartbeats 0

lemma orderedPrimeProduct_le_zeta (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (a : ℝ) (ha : 1 < a) (k : ℕ) :
    orderedPowerProduct (fun i => 1/(p i : ℝ)) a k ≤ reciprocalPowerConstant a := by
  let P : Fin k → ℕ := fun i => p i.val
  have hP : ∀ i, (P i).Prime := fun i => hp i.val
  have hPi : Function.Injective P := hinj.comp Fin.val_injective
  have hprod : orderedPowerProduct (fun i => 1/(p i : ℝ)) a k =
      ∏ i : Fin k, (1+(1/(P i : ℝ))^a) := by
    exact (Fin.prod_univ_eq_prod_range (fun i => 1+(1/(p i : ℝ))^a) k).symm
  rw [hprod, prod_one_add]
  have he (T : Finset (Fin k)) :
      (∏ i ∈ T, (1/(P i : ℝ))^a) = (((∏ i ∈ T, P i : ℕ) : ℝ)^a)⁻¹ := by
    simp only [one_div, inv_rpow (Nat.cast_nonneg _)]
    rw [prod_inv_distrib, finset_prod_rpow T (fun i => (P i : ℝ))
      (fun i hi => Nat.cast_nonneg _), Nat.cast_prod]
  simp_rw [he]
  rw [← sum_image (f := fun n : ℕ => ((n : ℝ)^a)⁻¹)
    (FiniteSelberg.prime_subset_product_injective P hP hPi).injOn]
  exact Summable.sum_le_tsum _ (fun j _ => inv_nonneg.mpr (rpow_nonneg (Nat.cast_nonneg j) a))
    (summable_nat_rpow_inv.mpr ha)

/-- Elementary integral comparison gives an explicit bound on the pole. -/
lemma reciprocalPowerConstant_le (a : ℝ) (ha : 1 < a) :
    reciprocalPowerConstant a ≤ 1+1/(a-1) := by
  have ha0 : a ≠ 0 := by linarith
  have hsum : Summable (fun n : ℕ => ((n : ℝ)^a)⁻¹) := summable_nat_rpow_inv.mpr ha
  have htail : (∑' n : ℕ, (((n+2 : ℕ) : ℝ)^a)⁻¹) ≤ 1/(a-1) := by
    apply (hsum.comp_injective (fun i j h => Nat.add_right_cancel h)).tsum_le_of_sum_range_le
    intro N
    have hmono : AntitoneOn (fun x : ℝ => x^(-a)) (Set.Icc (1 : ℝ) (1+N)) := by
      intro x hx y hy hxy
      exact rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    have hh := hmono.sum_le_integral
    have he : (∫ x : ℝ in (1 : ℝ)..1+N, x^(-a)) =
        ((1+(N : ℝ))^(1-a)-1)/(1-a) := by
      have hn : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1+N) := by
        rw [Set.uIcc_of_le (by have := Nat.cast_nonneg (α := ℝ) N; linarith)]
        intro hz
        linarith [hz.1]
      rw [integral_rpow (Or.inr ⟨by linarith, hn⟩)]
      simp only [show -a+1 = 1-a by ring, one_rpow]
    rw [he] at hh
    have hid : (∑ i ∈ range N, (1+((i+1 : ℕ) : ℝ))^(-a)) =
        ∑ i ∈ range N, (((i+2 : ℕ) : ℝ)^a)⁻¹ := by
      apply sum_congr rfl
      intro i hi
      rw [rpow_neg (by positivity)]
      congr 2
      push_cast
      ring
    rw [hid] at hh
    have hpos : 0 ≤ (1+(N : ℝ))^(1-a) := rpow_nonneg (by positivity) _
    have hden : 0 < a-1 := by linarith
    have hratio : ((1+(N : ℝ))^(1-a)-1)/(1-a) ≤ 1/(a-1) := by
      have hid : ((1+(N : ℝ))^(1-a)-1)/(1-a) =
          (1-(1+(N : ℝ))^(1-a))/(a-1) := by
        field_simp [hden.ne', show (1 : ℝ)-a ≠ 0 by linarith]
        ring
      rw [hid]
      apply (div_le_div_iff_of_pos_right hden).mpr
      linarith only [hpos]
    exact hh.trans hratio
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hfirst : (∑ i ∈ range 2, ((i : ℝ)^a)⁻¹) = 1 := by
    simp [sum_range_succ, zero_rpow ha0]
  rw [hfirst] at hsplit
  unfold reciprocalPowerConstant
  linarith only [hsplit, htail]

/-- No depth factor and no exponential of the zeta pole is needed. -/
theorem prime_refined_lowerError_le_zeta_mul
    (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (cost : ℕ → ℝ → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hcost : ∀ k D, 1 ≤ D → cost k D ≤ C*D)
    (a : ℝ) (ha : 1 < a) (n k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) cost n) k D ≤
        C*(1+1/(a-1))*D^a := by
  have hC0 : 0 ≤ C := by linarith
  have hh := refined_lowerError_le_ordered_product
    (fun i => 1/(p i : ℝ)) (primeKeep p) cost a C
    (by linarith) hC (fun i => by positivity) (primeKeep_levels p hp hmono)
    (fun j E hE => (hcost j E hE).trans (mul_le_mul_of_nonneg_left (by
      simpa using rpow_le_rpow_of_exponent_le hE ha.le) hC0)) n k D hD
  have hz := (orderedPrimeProduct_le_zeta p hp hmono.injective a ha k).trans
    (reciprocalPowerConstant_le a ha)
  have hm := mul_le_mul_of_nonneg_left hz (mul_nonneg hC0 (rpow_nonneg hD a))
  exact hh.trans (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hm)

theorem prime_refined_lowerError_le_zeta
    (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (cost : ℕ → ℝ → ℝ) (hcost : ∀ k D, 1 ≤ D → cost k D ≤ D)
    (a : ℝ) (ha : 1 < a) (n k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) cost n) k D ≤
        (1+1/(a-1))*D^a := by
  simpa only [one_mul] using prime_refined_lowerError_le_zeta_mul p hp hmono cost 1 le_rfl
    (fun j E hE => by simpa only [one_mul] using hcost j E hE) a ha n k D hD

/-- Choosing the exponent after fixing the level yields a genuinely
all-depth O(D log D) bound, with an absolute explicit constant. -/
theorem prime_refined_lowerError_le_log_mul
    (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (cost : ℕ → ℝ → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hcost : ∀ k D, 1 ≤ D → cost k D ≤ C*D)
    (n k : ℕ) (D : ℝ) (hD : 1 < D) :
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) cost n) k D ≤
        C*exp 1*D*(1+log D) := by
  have hD0 : 0 < D := by linarith
  have hlog : 0 < log D := log_pos hD
  let a : ℝ := 1+(log D)⁻¹
  have ha : 1 < a := by dsimp only [a]; linarith [inv_pos.mpr hlog]
  have hh := prime_refined_lowerError_le_zeta_mul p hp hmono cost C hC hcost a ha n k D hD0.le
  have hc : 1+1/(a-1) = 1+log D := by simp [a]
  have he : D^a = D*exp 1 := by
    dsimp only [a]
    rw [rpow_add hD0, rpow_one, rpow_def_of_pos hD0, mul_inv_cancel₀ hlog.ne']
  rw [hc, he] at hh
  exact hh.trans_eq (by ring)

theorem prime_refined_lowerError_le_log_uniform
    (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (hmono : StrictMono p)
    (cost : ℕ → ℝ → ℝ) (hcost : ∀ k D, 1 ≤ D → cost k D ≤ D)
    (n k : ℕ) (D : ℝ) (hD : 1 < D) :
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) cost n) k D ≤
        exp 1*D*(1+log D) := by
  simpa only [one_mul] using prime_refined_lowerError_le_log_mul p hp hmono cost 1 le_rfl
    (fun j E hE => by simpa only [one_mul] using hcost j E hE) n k D hD

#print axioms prime_refined_lowerError_le_log_uniform
#print axioms orderedPrimeProduct_le_zeta
#print axioms reciprocalPowerConstant_le
#print axioms prime_refined_lowerError_le_zeta
end Erdos970.RecursiveSieve.Buchstab
