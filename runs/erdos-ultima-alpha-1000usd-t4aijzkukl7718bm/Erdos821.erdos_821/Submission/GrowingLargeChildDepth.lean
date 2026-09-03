import Submission.LargeChildMass
import Submission.ProgressionScales

/-!
# Growing-depth bounds for power-sparse ancestor layers

At X_L = 2^(R*(2k)^(2L)), the Lth layer has every fixed logarithmic saving.
These bounds assume a power-sparse initial set. They do not resolve Erdos 821.
-/

open Nat Finset Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 4000000

def largeChildDepthScale (k R L : ℕ) : ℕ := R*(2*k)^(2*L)
def largeChildDepthCutoff (k R L : ℕ) : ℕ := 2^(largeChildDepthScale k R L)
noncomputable def largeChildLayerCount (k : ℕ) (A : Set ℕ) (L N : ℕ) : ℕ :=
  ((range (N+1)).filter (fun n => n ∈ largeChildLayer k A L)).card

lemma largeChildDepthScale_pos (k R L : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R) :
    0 < largeChildDepthScale k R L := by
  unfold largeChildDepthScale
  exact Nat.mul_pos (by omega) (pow_pos (by omega) _)

lemma largeChildDepth_compensation (k R L : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R) :
    (2 : ℝ)^((2*k)^L) * (largeChildDepthCutoff k R L : ℝ)^
      (1-1/((R*(2*k)^L : ℕ) : ℝ)) = (largeChildDepthCutoff k R L : ℝ) := by
  let U : ℕ := (2*k)^L
  let V : ℕ := R*(2*k)^L
  let T : ℕ := largeChildDepthScale k R L
  have hV : 0 < V := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  have hVR : (V : ℝ) ≠ 0 := by exact_mod_cast hV.ne'
  have hUV : V*U = T := by
    dsimp [V, U, T, largeChildDepthScale]
    rw [show 2*L = L+L by omega, pow_add]
    ring
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

lemma eventually_depth_factor_budget (C a B c : ℕ) (hB : 2 ≤ B) :
    ∀ᶠ L : ℕ in atTop, C*a^L*B^(L^2+c*L) ≤ 2^(B^L) := by
  filter_upwards [AnalyticSieve.eventually_nat_poly_le_two_pow 1 (C+a+B*(c+1)) 2]
    with L hpoly
  simp only [one_mul] at hpoly
  have hL : L ≤ (L+1)^2 := by nlinarith
  have hL2 : L^2 ≤ (L+1)^2 := Nat.pow_le_pow_left (Nat.le_succ L) 2
  have h1 : 1 ≤ (L+1)^2 := one_le_pow₀ (by omega)
  have hC : C ≤ C*(L+1)^2 := by simpa using Nat.mul_le_mul_left C h1
  have ha : a*L ≤ a*(L+1)^2 := Nat.mul_le_mul_left a hL
  have hinner : L^2+c*L ≤ (c+1)*(L+1)^2 := by
    have h := _root_.add_le_add hL2 (Nat.mul_le_mul_left c hL)
    nlinarith only [h]
  have hexp : C+a*L+B*(L^2+c*L) ≤ (C+a+B*(c+1))*(L+1)^2 := by
    have h := _root_.add_le_add (_root_.add_le_add hC ha) (Nat.mul_le_mul_left B hinner)
    nlinarith only [h]
  calc
    C*a^L*B^(L^2+c*L) ≤ (2^C)*(2^a)^L*(2^B)^(L^2+c*L) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.lt_two_pow_self.le) (Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) L))
        (Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _)
    _ = 2^(C+a*L+B*(L^2+c*L)) := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    _ ≤ 2^((C+a+B*(c+1))*(L+1)^2) := Nat.pow_le_pow_right (by decide) hexp
    _ ≤ 2^(2^L) := Nat.pow_le_pow_right (by decide) hpoly
    _ ≤ 2^(B^L) := Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left hB L)

lemma largeChildDepth_budget_identity (k R M J L : ℕ) :
    M * largeChildMassFactor k R L * (largeChildDepthScale k R L)^J =
      (M*R^J)*(1+2*R)^L*(2*k)^(L^2+(2*J)*L) := by
  unfold largeChildMassFactor largeChildDepthScale
  rw [mul_pow R ((2*k)^(2*L)) J, ← pow_mul, pow_add,
    show (2*L)*J = (2*J)*L by ring]
  ring

lemma largeChildLayer_count_compensated (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ) (hA : 0 ∉ A)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) (L : ℕ) :
    (2 : ℝ)^((2*k)^L) *
        (largeChildLayerCount k A L (largeChildDepthCutoff k R L) : ℝ) ≤
      (largeChildDepthCutoff k R L : ℝ) *
        (setPowerMass A (1-1/(R : ℝ)) * (largeChildMassFactor k R L : ℝ)) := by
  have hN : 1 ≤ largeChildDepthCutoff k R L := one_le_pow₀ (by decide)
  have h := largeChildLayer_card_le k R hk hR A hA H L (largeChildDepthCutoff k R L) hN
  have hm := mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((2*k)^L))
  calc
    _ ≤ (2 : ℝ)^((2*k)^L) *
        ((largeChildDepthCutoff k R L : ℝ)^(1-1/((R*(2*k)^L : ℕ) : ℝ)) *
          (setPowerMass A (1-1/(R : ℝ)) * (largeChildMassFactor k R L : ℝ))) := hm
    _ = _ := by rw [← mul_assoc, largeChildDepth_compensation k R L hk hR]

/-- Every fixed power of log_2(X_L) can be saved while the ancestor depth is L. -/
theorem eventually_growing_largeChildLayer_count_small (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ) (hA : 0 ∉ A)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) (J : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      (largeChildDepthScale k R L)^J *
        largeChildLayerCount k A L (largeChildDepthCutoff k R L) ≤
          largeChildDepthCutoff k R L := by
  obtain ⟨M, hM⟩ := exists_nat_ge (setPowerMass A (1-1/(R : ℝ)))
  filter_upwards [eventually_depth_factor_budget (M*R^J) (1+2*R) (2*k) (2*J) (by omega)]
    with L hbudget
  rw [← largeChildDepth_budget_identity k R M J L] at hbudget
  have hbudgetR : (setPowerMass A (1-1/(R : ℝ)) * (largeChildMassFactor k R L : ℝ)) *
      ((largeChildDepthScale k R L)^J : ℕ) ≤ (2 : ℝ)^((2*k)^L) := by
    calc
      _ ≤ ((M : ℝ)*(largeChildMassFactor k R L : ℝ)) *
          ((largeChildDepthScale k R L)^J : ℕ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      _ ≤ _ := by exact_mod_cast hbudget
  have hc := largeChildLayer_count_compensated k R hk hR A hA H L
  have hsave : (0 : ℝ) < (2 : ℝ)^((2*k)^L) := pow_pos (by norm_num) _
  have hresult : (((largeChildDepthScale k R L)^J *
      largeChildLayerCount k A L (largeChildDepthCutoff k R L) : ℕ) : ℝ) ≤
        (largeChildDepthCutoff k R L : ℝ) := by
    apply (mul_le_mul_iff_right₀ hsave).mp
    push_cast only [Nat.cast_mul]
    calc
      _ = ((largeChildDepthScale k R L)^J : ℕ) *
          ((2 : ℝ)^((2*k)^L) *
            (largeChildLayerCount k A L (largeChildDepthCutoff k R L) : ℝ)) := by ring
      _ ≤ ((largeChildDepthScale k R L)^J : ℕ) *
          ((largeChildDepthCutoff k R L : ℝ) *
            (setPowerMass A (1-1/(R : ℝ)) * (largeChildMassFactor k R L : ℝ))) :=
        mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)
      _ = (largeChildDepthCutoff k R L : ℝ) *
          ((setPowerMass A (1-1/(R : ℝ)) * (largeChildMassFactor k R L : ℝ)) *
            ((largeChildDepthScale k R L)^J : ℕ)) := by ring
      _ ≤ (largeChildDepthCutoff k R L : ℝ) * (2 : ℝ)^((2*k)^L) :=
        mul_le_mul_of_nonneg_left hbudgetR (Nat.cast_nonneg _)
      _ = _ := mul_comm _ _
  exact_mod_cast hresult

/-- At least half of the primes up to X_L avoid the Lth ancestor layer,
for every sufficiently large L. -/
theorem eventually_growing_prime_complement_large (k R : ℕ) (hk : 1 ≤ k) (hR : 1 ≤ R)
    (A : Set ℕ) (hA : 0 ∉ A)
    (H : Summable (A.indicator (fun n : ℕ => (n : ℝ)^(-(1-1/(R : ℝ)))))) :
    ∀ᶠ L : ℕ in atTop,
      (largeChildDepthCutoff k R L + 1).primesBelow.card ≤
        2 * (((largeChildDepthCutoff k R L + 1).primesBelow).filter
          (fun p => p ∉ largeChildLayer k A L)).card := by
  filter_upwards [eventually_growing_largeChildLayer_count_small k R hk hR A hA H 2,
    eventually_ge_atTop 1] with L hbad hL
  let t := largeChildDepthScale k R L
  let N := largeChildDepthCutoff k R L
  let P := (N+1).primesBelow
  let C := largeChildLayerCount k A L N
  have hB : 2 ≤ 2*k := by omega
  have hpow : 4 ≤ (2*k)^(2*L) := by
    calc
      4 = 2^2 := by decide
      _ ≤ (2*k)^2 := Nat.pow_le_pow_left hB 2
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have ht4 : 4 ≤ t := by
    exact hpow.trans (Nat.le_mul_of_pos_left _ (by omega : 0 < R))
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

end Erdos821
