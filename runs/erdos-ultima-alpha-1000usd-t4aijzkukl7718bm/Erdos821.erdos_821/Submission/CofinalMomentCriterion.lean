import Submission.MomentSmoothTransfer

/-!
# A cofinal-order geometric-loss moment criterion

The lower moment hypothesis is not proved here. These results relax a
sufficient arithmetic input without asserting the original conjecture.
-/

open Nat Filter ArithmeticFunction
open scoped Classical BigOperators Topology
namespace Erdos821.HigherDivisors
open AnalyticSieve
set_option maxHeartbeats 3000000

theorem eventually_order_eventually_rough_geometric (t : ℕ) (ht : 2 ≤ t)
    (θ : ℝ) (hθ : 1-1/(2*(t : ℝ)) < θ) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ L : ℕ in atTop,
      roughPrimeMoment k (momentScaleX t L) (momentScaleY L) ≤
        θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*(k.factorial : ℝ)) := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  let ρ : ℝ := 1 - 1/(2*(t : ℝ))
  let κ : ℝ := 1/(128*(t : ℝ))
  have hρ : 0 ≤ ρ := by
    have h := (div_le_one (show (0 : ℝ) < 2*(t : ℝ) by positivity)).mpr
      (show (1 : ℝ) ≤ 2*(t : ℝ) by linarith)
    dsimp [ρ]
    linarith
  have hρ1 : ρ < 1 := by
    have h : (0 : ℝ) < 1/(2*(t : ℝ)) := by positivity
    dsimp [ρ]
    linarith
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hθ0 : 0 < θ := lt_of_le_of_lt hρ hθ
  have hq0 : 0 ≤ ρ/θ := div_nonneg hρ hθ0.le
  have hq1 : ρ/θ < 1 := (div_lt_one hθ0).mpr hθ
  have hlim := (tendsto_factorial_rough_coefficient (ρ/θ) hq0 hq1).const_mul (64/κ^2)
  simp only [mul_zero] at hlim
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 2] with k hcoef0 hk
  have hθk : 0 < θ^k := pow_pos hθ0 _
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hcoef : (64/κ^2)*(k : ℝ)*(Real.exp 1/(k : ℝ))^k*eulerCost k*ρ^k < θ^k/(k.factorial : ℝ) := by
    apply (lt_div_iff₀ hfact).mpr
    have hh : ((64/κ^2)*(k : ℝ)*(Real.exp 1/(k : ℝ))^k*eulerCost k*ρ^k*(k.factorial : ℝ))/θ^k < 1 := by
      convert hcoef0 using 1
      rw [div_pow]
      ring_nf
    exact (div_lt_one hθk).mp hh
  let A : ℝ := 16/κ^2*(k : ℝ)*(Real.exp 1/(k : ℝ))^k*eulerCost k*ρ^k
  have hA : A ≤ θ^k/(4*(k.factorial : ℝ)) := by
    have h4 : 4*A < θ^k/(k.factorial : ℝ) := by
      convert hcoef using 1
      dsimp [A]
      ring_nf
    have he : θ^k/(4*(k.factorial : ℝ)) = (θ^k/(k.factorial : ℝ))/4 := by ring_nf
    rw [he]
    linarith

  filter_upwards [eventually_ge_atTop k,
    eventually_momentSieveError_le k t (by omega) (θ^k/(4*(k.factorial : ℝ))) (by positivity)] with L hkL herror
  have hL : 1 ≤ L := by omega
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hkLR : (k : ℝ) ≤ L := by exact_mod_cast hkL
  have hX : 0 < momentScaleX t L := by unfold momentScaleX; positivity
  have hK : 1 < momentScaleK t L := by
    unfold momentScaleK
    have he : 0 < 128*(t-1)*L := Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) hL
    exact Nat.one_lt_pow he.ne' (by decide)
  have hlog := one_le_log_momentScaleX t L (by omega) hL
  have hcofactor : Real.log (momentScaleK t L) + k ≤ ρ*Real.log (momentScaleX t L) := by
    rw [log_momentScaleK t L (by omega), log_momentScaleX]
    have hid : ρ*(128*(t : ℝ)*(L : ℝ)*Real.log 2) -
        128*((t : ℝ)-1)*(L : ℝ)*Real.log 2 = 64*(L : ℝ)*Real.log 2 := by
      dsimp [ρ]
      field_simp
      ring_nf
    have hb := mul_le_mul_of_nonneg_left (show (1/2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
      (show (0 : ℝ) ≤ 64*(L : ℝ) by positivity)
    nlinarith
  have hsieve : κ*Real.log (momentScaleX t L) ≤ (L : ℝ)*Real.log 2 := by
    rw [log_momentScaleX]
    apply le_of_eq
    dsimp [κ]
    field_simp
  have hmain := rough_sieve_main_le_normalized k (momentScaleX t L) (momentScaleK t L) L
    hk hK (Real.log (momentScaleX t L)) ρ κ (by linarith) hκ hcofactor hsieve
  have hmain' : (k : ℝ)*(16*(momentScaleX t L : ℝ)/((L : ℝ)*Real.log 2)^2)*
      (eulerCost k*harmonicMoment k (momentScaleK t L)) ≤
      θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(4*(k.factorial : ℝ)) := by
    apply hmain.trans
    have h := mul_le_mul_of_nonneg_right hA
      (show 0 ≤ (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2) by positivity)
    convert h using 1 <;> dsimp [A] <;> ring_nf
  have hpower : (1 : ℝ) ≤ (Real.log (momentScaleX t L))^(k-2) := one_le_pow₀ hlog
  have herror' : momentSieveError k t L ≤
      θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(4*(k.factorial : ℝ)) := by
    apply herror.trans
    have h := mul_le_mul_of_nonneg_left hpower
      (show 0 ≤ θ^k*(momentScaleX t L : ℝ)/(4*(k.factorial : ℝ)) by positivity)
    convert h using 1 <;> ring_nf
  have hs := roughPrimeMoment_sieve_bound (k-1) (momentScaleX t L) (momentScaleK t L)
    (momentScaleY L) L (momentScaleX_eq t L (by omega)).le (momentScaleK_le_X t L) hL
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hs
  have hsplit : (k : ℝ)*
      ((16*(momentScaleX t L : ℝ)/((L : ℝ)*Real.log 2)^2)*
        (eulerCost k*harmonicMoment k (momentScaleK t L)) +
        ((2 : ℝ)^(64*L)+(2 : ℝ)^(16*L)+1)*(momentScaleK t L : ℝ)*
          (harmonic (momentScaleK t L) : ℝ)^(k-1)) =
      (k : ℝ)*(16*(momentScaleX t L : ℝ)/((L : ℝ)*Real.log 2)^2)*
        (eulerCost k*harmonicMoment k (momentScaleK t L)) + momentSieveError k t L := by
    unfold momentSieveError
    ring_nf
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one, sub_add_cancel, hsplit] at hs
  have he : θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*(k.factorial : ℝ)) =
      2*(θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(4*(k.factorial : ℝ))) := by ring_nf
  rw [he]
  linarith

theorem eventually_smooth_count_of_moment_denominator (k t : ℕ) (hk : 2 ≤ k) (ht : 2 ≤ t) (D : ℝ) (hD : 0 < D)
    (Hrough : ∀ᶠ L : ℕ in atTop,
      roughPrimeMoment k (momentScaleX t L) (momentScaleY L) ≤
        (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*D)) :
    ∀ᶠ L : ℕ in atTop,
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/D ≤
        shiftedPrimeMoment k (momentScaleX t L) →
      momentScaleK t L ≤ (smoothPrimePool (momentScaleX t L) (momentScaleY L)).card := by
  obtain ⟨C, hC, hweight⟩ := exists_moment_weight_bound k t (by omega) (by omega)
  have hgrowth : ∀ᶠ L : ℕ in atTop, 2*C*D < (2 : ℝ)^L :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
      (eventually_gt_atTop (2*C*D))
  filter_upwards [Hrough, hgrowth, eventually_ge_atTop 1] with L hrough hgrowth hL hlower
  have hlog := one_le_log_momentScaleX t L (by omega) hL
  have hX : (0 : ℝ) < momentScaleX t L := by unfold momentScaleX; positivity
  have hK : (0 : ℝ) < momentScaleK t L := by unfold momentScaleK; positivity
  have hC0 : 0 ≤ C := by linarith
  have hbound : ∀ p ∈ (momentScaleX t L+1).primesBelow,
      (tau k (p-1) : ℝ) ≤ C*(2 : ℝ)^(64*L) := by
    intro p hp
    apply hweight L (p-1)
    have h := (Nat.mem_primesBelow.mp hp).1
    omega
  have htotal := moment_le_rough_add_pool_card k (momentScaleX t L) (momentScaleY L)
    (C*(2 : ℝ)^(64*L)) hbound
  have hlarge : 2*C*D < (2 : ℝ)^(64*L) :=
    hgrowth.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))
  have hXeq : (momentScaleX t L : ℝ) = (momentScaleK t L : ℝ)*((2 : ℝ)^(64*L))^2 := by
    rw [momentScaleX_eq t L (by omega), momentScaleY_eq_square]
    push_cast
    rfl
  have hsmall : (C*(2 : ℝ)^(64*L))*(momentScaleK t L : ℝ) <
      (momentScaleX t L : ℝ)/(2*D) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2*D)).mpr
    have h := mul_lt_mul_of_pos_right hlarge
      (show 0 < (2 : ℝ)^(64*L)*(momentScaleK t L : ℝ) by positivity)
    rw [hXeq]
    convert h using 1 <;> ring_nf
  have hhalf : (momentScaleX t L : ℝ)/(2*D) ≤
      (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*D) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hlog (n := k-2)) hX.le
  by_contra hnot
  have hc : ((smoothPrimePool (momentScaleX t L) (momentScaleY L)).card : ℝ) ≤ momentScaleK t L := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hnot))
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ C*(2 : ℝ)^(64*L) by positivity)
  have he : (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/D =
      2*((momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*D)) := by ring_nf
  rw [he] at hlower
  linarith

/-- Still-unproved lower information: arbitrarily high orders, with any
fixed geometric loss. The scale is allowed to depend on the order. -/
def CofinalGeometricMomentLower : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ t : ℕ, 2 ≤ t → ∀ B : ℕ,
    ∃ k : ℕ, B ≤ k ∧ 2 ≤ k ∧ ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧
      θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(k.factorial : ℝ) ≤
        shiftedPrimeMoment k (momentScaleX t L)

lemma sharp_moments_imply_cofinal_geometric (H : SharpDyadicMomentLower) :
    CofinalGeometricMomentLower := by
  intro θ hθ0 hθ1 t ht B
  let k := max B 2
  refine ⟨k,le_max_left _ _,le_max_right _ _,?_⟩
  intro M
  obtain ⟨L,hL,hbound⟩ := H k (le_max_right _ _) t ht M
  refine ⟨L,hL,le_trans ?_ hbound⟩
  have hθk : θ^k ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
  have hnonneg : 0 ≤ (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2) := by
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.log_natCast_nonneg _) _)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [mul_assoc,one_mul] using mul_le_mul_of_nonneg_right hθk hnonneg

/-- The arithmetic lower bound, if proved, only has to hold at cofinal orders. -/
theorem dyadic_smooth_density_of_cofinal_geometric_moments (H : CofinalGeometricMomentLower)
    (t : ℕ) (ht : 5 ≤ t) (M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ ∃ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ 2^(t*L) ∧ p-1 ∈ Nat.smoothNumbers (2^L)) ∧
      2^((t-1)*L) ≤ P.card := by
  let θ : ℝ := 1-1/(4*(t : ℝ))
  have htR : (5 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hi : 0 < 1/(4*(t : ℝ)) := by positivity
  have hi1 : 1/(4*(t : ℝ)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hθ0 : 0 < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  have hθρ : 1-1/(2*(t : ℝ)) < θ := by
    have he : 1/(2*(t : ℝ)) = 2*(1/(4*(t : ℝ))) := by ring_nf
    dsimp [θ]
    rw [he]
    linarith
  obtain ⟨B,hB⟩ := eventually_atTop.mp (eventually_order_eventually_rough_geometric t (by omega) θ hθρ)
  obtain ⟨k,hkB,hk,Hlower⟩ := H θ hθ0 hθ1 t (by omega) B
  have hrough := hB k hkB
  let D : ℝ := (k.factorial : ℝ)/θ^k
  have hD : 0 < D := by dsimp [D]; positivity
  have hroughD : ∀ᶠ L : ℕ in atTop,
      roughPrimeMoment k (momentScaleX t L) (momentScaleY L) ≤
        (momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(2*D) := by
    filter_upwards [hrough] with L hL
    convert hL using 1
    dsimp [D]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring_nf
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_smooth_count_of_moment_denominator k t hk (by omega) D hD hroughD)
  obtain ⟨L,hL,hlower⟩ := Hlower (max M N)
  have hML : M ≤ L := (le_max_left _ _).trans hL
  have hNL : N ≤ L := (le_max_right _ _).trans hL
  have hcount := hN L hNL (by
    convert hlower using 1
    dsimp [D]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring_nf)
  refine ⟨128*L, (hML.trans (by omega)), smoothPrimePool (momentScaleX t L) (momentScaleY L), ?_, ?_⟩
  · intro p hp
    obtain ⟨hp,hps⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpX,hpr⟩ := Nat.mem_primesBelow.mp hp
    have he : momentScaleX t L = 2^(t*(128*L)) := by unfold momentScaleX; congr 1; ring_nf
    refine ⟨hpr,?_,hps⟩
    rw [← he]
    omega
  · convert hcount using 1
    unfold momentScaleK
    congr 1
    ring_nf

/-- This remains conditional: the geometric-loss moment input is not established. -/
theorem erdos_821_of_cofinal_geometric_moments (H : CofinalGeometricMomentLower) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  erdos_821_of_dyadic_smooth_prime_density (dyadic_smooth_density_of_cofinal_geometric_moments H)

/-- A necessary consequence of a failure of the original conjecture.
It is not an assertion of that failure. -/
theorem negation_forces_geometric_moment_upper
    (Hneg : ¬ (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ t : ℕ, 2 ≤ t ∧ ∃ B : ℕ,
      ∀ k : ℕ, B ≤ k → 2 ≤ k → ∃ M : ℕ, ∀ L : ℕ, M ≤ L →
        shiftedPrimeMoment k (momentScaleX t L) <
          θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(k.factorial : ℝ) := by
  have H : ¬ CofinalGeometricMomentLower := fun h => Hneg (erdos_821_of_cofinal_geometric_moments h)
  unfold CofinalGeometricMomentLower at H
  push_neg at H
  exact H

end Erdos821.HigherDivisors
