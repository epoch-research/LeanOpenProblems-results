import Submission.SharpLargeChild
import Submission.GrowingSmoothPrimeChains

/-!
# Near-endpoint growing depths for sparse prime-factor ancestor sets

At X_L = 2^(R*k^L*(L+1)^3), the Lth layer still has every fixed logarithmic
saving. Applications to the conjecture retain its negation as a hypothesis.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 2000000

def sharpDepthScale (k R L : ℕ) : ℕ := R*k^L*(L+1)^3
def sharpDepthCutoff (k R L : ℕ) : ℕ := 2^(sharpDepthScale k R L)

lemma sharpDepth_compensation (k R L : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R) :
    (2 : ℝ)^((L+1)^3) * (sharpDepthCutoff k R L : ℝ)^
      (1-1/((R*k^L : ℕ) : ℝ)) = (sharpDepthCutoff k R L : ℝ) := by
  let U : ℕ := (L+1)^3
  let V : ℕ := R*k^L
  let T : ℕ := sharpDepthScale k R L
  have hV : 0 < V := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hVR : (V : ℝ) ≠ 0 := by exact_mod_cast hV.ne'
  have hUV : V*U = T := rfl
  have hUVR : (V : ℝ)*(U : ℝ) = (T : ℝ) := by exact_mod_cast hUV
  have he : (U : ℝ)+(T : ℝ)*(1-1/(V : ℝ)) = (T : ℝ) := by
    field_simp
    nlinarith only [hUVR]
  change (2 : ℝ)^U * ((2^T : ℕ) : ℝ)^(1-1/(V : ℝ)) = ((2^T : ℕ) : ℝ)
  push_cast
  calc
    (2 : ℝ)^U * ((2 : ℝ)^T)^(1-1/(V : ℝ)) =
        (2 : ℝ)^(U : ℝ) * (2 : ℝ)^((T : ℝ)*(1-1/(V : ℝ))) := by
      rw [Real.rpow_natCast, Real.rpow_natCast_mul (by norm_num)]
    _ = (2 : ℝ)^((U : ℝ)+(T : ℝ)*(1-1/(V : ℝ))) :=
      (Real.rpow_add (by norm_num) _ _).symm
    _ = (2 : ℝ)^T := by rw [he, Real.rpow_natCast]

lemma eventually_cubic_depth_budget (C a k J : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      C*a^L*k^(L^2+J*L)*(L+1)^(3*J) ≤ 2^((L+1)^3) := by
  let B := C+a+k*(J+1)+3*J
  filter_upwards [eventually_ge_atTop B] with L hL
  have hL1 : L ≤ (L+1)^2 := by nlinarith
  have hL2 : L^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (Nat.le_succ L) 2
  have h1 : 1 ≤ (L+1)^2 := one_le_pow₀ (by omega)
  have hLL : L+1 ≤ (L+1)^2 := by nlinarith
  have hinner : L^2+J*L ≤ (J+1)*(L+1)^2 := by
    have h := _root_.add_le_add hL2 (Nat.mul_le_mul_left J hL1)
    nlinarith only [h]
  have hexp : C+a*L+k*(L^2+J*L)+(L+1)*(3*J) ≤ (L+1)^3 := by
    have hC := Nat.mul_le_mul_left C h1
    have ha := Nat.mul_le_mul_left a hL1
    have hk := Nat.mul_le_mul_left k hinner
    have hJ := Nat.mul_le_mul_right (3*J) hLL
    have hBL : B*(L+1)^2 ≤ (L+1)^3 := by
      calc
        _ ≤ (L+1)*(L+1)^2 := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    dsimp [B] at hBL
    nlinarith only [hC, ha, hk, hJ, hBL]
  calc
    _ ≤ (2^C)*(2^a)^L*(2^k)^(L^2+J*L)*(2^(L+1))^(3*J) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left Nat.lt_two_pow_self.le L))
          (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _))
        (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
    _ = 2^(C+a*L+k*(L^2+J*L)+(L+1)*(3*J)) := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

lemma sharpDepth_budget_identity (k R M J L : ℕ) :
    M*sharpLargeChildMassFactor k R L*(sharpDepthScale k R L)^J =
      (M*R^J)*(1+R)^L*k^(L^2+J*L)*(L+1)^(3*J) := by
  unfold sharpLargeChildMassFactor sharpDepthScale
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]
  rw [show L*J = J*L by ring]
  ring

lemma sharp_largeChildLayer_count_compensated (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ) (hA : 0 ∉ A)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) (L : ℕ) :
    (2 : ℝ)^((L+1)^3) *
        (largeChildLayerCount k A L (sharpDepthCutoff k R L) : ℝ) ≤
      (sharpDepthCutoff k R L : ℝ) *
        (setPowerMass A (1-1/(R : ℝ)) * (sharpLargeChildMassFactor k R L : ℝ)) := by
  have hT : 1 ≤ R*k^L := Nat.mul_le_mul hR (one_le_pow₀ hk)
  have hcard := card_set_le_rpow_mass (largeChildLayer k A L)
    (zero_not_mem_largeChildLayer k A hA L) (1-1/((R*k^L : ℕ) : ℝ))
    (reciprocal_exponent_bounds _ hT).1
    (summable_largeChildLayer_reciprocal_sharp k R hk hR A H L)
    (sharpDepthCutoff k R L) (one_le_pow₀ (by decide))
  have hmass := setPowerMass_largeChildLayer_sharp_le k R hk hR A hA H L
  have h := hcard.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
  have hm := mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((L+1)^3))
  calc
    _ ≤ (2 : ℝ)^((L+1)^3) *
        ((sharpDepthCutoff k R L : ℝ)^(1-1/((R*k^L : ℕ) : ℝ)) *
          (setPowerMass A (1-1/(R : ℝ)) * (sharpLargeChildMassFactor k R L : ℝ))) := hm
    _ = _ := by rw [← mul_assoc, sharpDepth_compensation k R L hk hR]
/-- Every fixed power of log_2(X_L) can be saved while the ancestor depth is L. -/
theorem eventually_sharp_growing_largeChildLayer_count_small (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ) (hA : 0 ∉ A)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) (J : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      (sharpDepthScale k R L)^J *
        largeChildLayerCount k A L (sharpDepthCutoff k R L) ≤
          sharpDepthCutoff k R L := by
  obtain ⟨M, hM⟩ := exists_nat_ge (setPowerMass A (1-1/(R : ℝ)))
  filter_upwards [eventually_cubic_depth_budget (M*R^J) (1+R) k J]
    with L hbudget
  rw [← sharpDepth_budget_identity k R M J L] at hbudget
  have hbudgetR : (setPowerMass A (1-1/(R : ℝ)) * (sharpLargeChildMassFactor k R L : ℝ)) *
      ((sharpDepthScale k R L)^J : ℕ) ≤ (2 : ℝ)^((L+1)^3) := by
    calc
      _ ≤ ((M : ℝ)*(sharpLargeChildMassFactor k R L : ℝ)) *
          ((sharpDepthScale k R L)^J : ℕ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      _ ≤ _ := by exact_mod_cast hbudget
  have hc := sharp_largeChildLayer_count_compensated k R hk hR A hA H L
  have hsave : (0 : ℝ) < (2 : ℝ)^((L+1)^3) := pow_pos (by norm_num) _
  have hresult : (((sharpDepthScale k R L)^J *
      largeChildLayerCount k A L (sharpDepthCutoff k R L) : ℕ) : ℝ) ≤
        (sharpDepthCutoff k R L : ℝ) := by
    apply (mul_le_mul_iff_right₀ hsave).mp
    push_cast only [Nat.cast_mul]
    calc
      _ = ((sharpDepthScale k R L)^J : ℕ) *
          ((2 : ℝ)^((L+1)^3) *
            (largeChildLayerCount k A L (sharpDepthCutoff k R L) : ℝ)) := by ring
      _ ≤ ((sharpDepthScale k R L)^J : ℕ) *
          ((sharpDepthCutoff k R L : ℝ) *
            (setPowerMass A (1-1/(R : ℝ)) * (sharpLargeChildMassFactor k R L : ℝ))) :=
        mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)
      _ = (sharpDepthCutoff k R L : ℝ) *
          ((setPowerMass A (1-1/(R : ℝ)) * (sharpLargeChildMassFactor k R L : ℝ)) *
            ((sharpDepthScale k R L)^J : ℕ)) := by ring
      _ ≤ (sharpDepthCutoff k R L : ℝ) * (2 : ℝ)^((L+1)^3) :=
        mul_le_mul_of_nonneg_left hbudgetR (Nat.cast_nonneg _)
      _ = _ := mul_comm _ _
  exact_mod_cast hresult

/-- At least half of the primes up to X_L avoid the Lth ancestor layer,
for every sufficiently large L. -/
theorem eventually_sharp_growing_prime_complement_large (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ) (hA : 0 ∉ A)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) :
    ∀ᶠ L : ℕ in atTop,
      (sharpDepthCutoff k R L + 1).primesBelow.card ≤
        2 * (((sharpDepthCutoff k R L + 1).primesBelow).filter
          (fun p => p ∉ largeChildLayer k A L)).card := by
  filter_upwards [eventually_sharp_growing_largeChildLayer_count_small k R hk hR A hA H 2,
    eventually_ge_atTop 1] with L hbad hL
  let t := sharpDepthScale k R L
  let N := sharpDepthCutoff k R L
  let P := (N+1).primesBelow
  let C := largeChildLayerCount k A L N
  have ht4 : 4 ≤ t := by
    have hc : 4 ≤ (L+1)^3 := by
      calc
        4 ≤ 2^3 := by decide
        _ ≤ _ := Nat.pow_le_pow_left (by omega) 3
    have hT : 1 ≤ R*k^L := Nat.mul_le_mul hR (one_le_pow₀ hk)
    exact hc.trans (Nat.le_mul_of_pos_left _ (by omega : 0 < R*k^L))
  have hN2 : 2 ≤ N := by
    change 2 ≤ 2^t
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
      (by omega : 1 ≤ t)
  have hP : 1 ≤ P.card := by
    apply card_pos.mpr
    refine ⟨2, Nat.mem_primesBelow.mpr ⟨?_, Nat.prime_two⟩⟩
    omega
  have hcheb : N ≤ t*(P.card+1) := by
    have h := Sieve.dyadic_prime_count_lower (t-1)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using h
  have hsmall : t*C ≤ P.card+1 := by
    exact Nat.le_of_mul_le_mul_left
      (by simpa only [pow_two, mul_assoc] using hbad.trans hcheb)
      (by omega : 0 < t)
  have hC : 2*C ≤ P.card := by nlinarith only [hsmall, hP, Nat.mul_le_mul_right C ht4]
  have hsubset : P.filter (fun p => p ∈ largeChildLayer k A L) ⊆
      (range (N+1)).filter (fun p => p ∈ largeChildLayer k A L) := by
    intro p hp
    obtain ⟨hpP, hpL⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mem_primesBelow.mp hpP).1, hpL⟩
  have hCp : (P.filter (fun p => p ∈ largeChildLayer k A L)).card ≤ C := card_le_card hsubset
  have hsplit := card_filter_add_card_filter_not (s := P) (p := fun p => p ∈ largeChildLayer k A L)
  change P.card ≤ 2*(P.filter (fun p => p ∉ largeChildLayer k A L)).card
  omega

/-- This stronger depth consequence still assumes the exact negation. -/
theorem negation_forces_sharp_growing_many_avoiding_trees
    (Hneg : ¬ (∀ ε > (0 : ℝ),
      {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite)) :
    ∃ k R : ℕ, 3 ≤ k ∧ 1 ≤ R ∧ ∀ᶠ L : ℕ in atTop,
      (sharpDepthCutoff k R L + 1).primesBelow.card ≤
        2 * (((sharpDepthCutoff k R L + 1).primesBelow).filter
          (fun p => largeChildAvoidingTree k (rootSmoothPrimeSet k) L p)).card := by
  obtain ⟨k, R, hk, hR, Hsum⟩ :=
    exists_sparse_reciprocal_rootSmoothPrimeSet_of_negation Hneg
  refine ⟨k, R, hk, hR, ?_⟩
  filter_upwards [eventually_sharp_growing_prime_complement_large k R (by omega) hR
    (rootSmoothPrimeSet k) (zero_not_mem_rootSmoothPrimeSet k) Hsum] with L hL
  refine hL.trans (Nat.mul_le_mul_left 2 (card_le_card ?_))
  intro p hp
  obtain ⟨hpP, hpL⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨hpP, (largeChildAvoidingTree_iff k (rootSmoothPrimeSet k) L p).mpr
    ⟨(Nat.mem_primesBelow.mp hpP).2, hpL⟩⟩

end Erdos821
