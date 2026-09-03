import Submission.LargeDivisorBlockMoment

/-! An explicit, nonempty large-divisor block below the input cutoff.
This instantiates an upper dispersion estimate, not a prime-pair lower bound. -/
namespace Erdos972ExplicitLargeDivisorBlock

open Finset Filter ArithmeticFunction
open Erdos972PrimePowerError Erdos972PrimeRoughOutputs Erdos972SelbergLowerTest
open Erdos972PolynomialRowScales Erdos972LargeDivisorBlockMoment
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] root64

noncomputable def blockStart (α : ℝ) (N v : ℕ) : ℕ := floorMul α N/v+1

lemma blockStart_bounds {α : ℝ} (hα : 1 ≤ α) {N v : ℕ}
    (hv : 0 < v) (hNv : v ≤ N) (hN : v^2+2 ≤ N) (hαv : α+1 < (v:ℝ)) :
    0 < blockStart α N v ∧ blockStart α N v < N ∧
      floorMul α N ≤ blockStart α N v*v ∧ N ≤ blockStart α N v*v ∧
      α*(v:ℝ) < blockStart α N v ∧
      (blockStart α N v:ℝ)*v ≤ (α+1)*(N:ℝ) := by
  let D := blockStart α N v
  have hD0 : 0 < D := Nat.succ_pos _
  have hfloor : floorMul α N < D*v := by
    simpa only [D, blockStart, mul_comm] using Nat.lt_mul_div_succ (floorMul α N) hv
  have hND : N ≤ D*v := (self_le_floorMul hα N).trans hfloor.le
  have hdup : D*v ≤ floorMul α N+v := by
    have hh := Nat.div_mul_le_self (floorMul α N) v
    dsimp [D, blockStart]
    nlinarith only [hh]
  have hflR : (floorMul α N:ℝ) ≤ α*N := Nat.floor_le (by positivity : 0 ≤ α*(N:ℝ))
  have hdupR : (D:ℝ)*v ≤ α*N+v := by
    have hh : (D:ℝ)*v ≤ (floorMul α N:ℝ)+v := by exact_mod_cast hdup
    linarith only [hh, hflR]
  have hvR : (0:ℝ) < v := Nat.cast_pos.mpr hv
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr (hv.trans_le hNv)
  have hNvR : (v:ℝ) ≤ N := Nat.cast_le.mpr hNv
  have hDN : D < N := by
    have hh := mul_lt_mul_of_pos_right hαv hNR
    have hm : (D:ℝ)*v < (N:ℝ)*v := by nlinarith only [hh, hdupR, hNvR]
    have hhDN : (D:ℝ) < N := by nlinarith only [hm, hvR]
    exact_mod_cast hhDN
  have hDα : α*(v:ℝ) < D := by
    have hN2 : (v:ℝ)^2+2 ≤ N := by exact_mod_cast hN
    have hgap := mul_le_mul_of_nonneg_left hN2 (by linarith : 0 ≤ α)
    have hfloorR : α*N < (D:ℝ)*v+1 := by
      have hh := Nat.lt_floor_add_one (α*(N:ℝ))
      have hf : (floorMul α N:ℝ) ≤ (D:ℝ)*v := by exact_mod_cast hfloor.le
      change α*N < (floorMul α N:ℝ)+1 at hh
      linarith only [hh, hf]
    by_contra hnot
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hvR.le
    nlinarith only [hgap, hfloorR, hm, hα]
  refine ⟨hD0, hDN, hfloor.le, hND, hDα, ?_⟩
  nlinarith only [hdupR, hNvR]

lemma root64_square_add_two_le_sixth {u : ℕ} (hu : 0 < u) (hv : 2 ≤ root64 u) :
    (root64 u)^2+2 ≤ u^6 := by
  have hv0 : 0 < root64 u := (root64_bounds hu).1
  have hv2 : 4 ≤ (root64 u)^2 := by nlinarith only [hv]
  have h24 : (root64 u)^2+2 ≤ (root64 u)^4 := by nlinarith only [hv2, sq_nonneg ((root64 u:ℤ)^2-2)]
  have h464 : (root64 u)^4 ≤ (root64 u)^64 := Nat.pow_le_pow_right hv0 (by decide)
  exact ((h24.trans h464).trans (root64_bounds hu).2.1).trans (Nat.le_self_pow (by decide) u)

/-- The block is explicit and lies strictly below N=u^6. Its centered energy
is bounded by N*root64(u) times a logarithmic factor, on arbitrarily large
actual irrational scales. This is not an o(N) signed-error estimate. -/
theorem exists_explicit_large_block_dispersion {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u D : ℕ, B < u ∧ 0 < u ∧ D = blockStart α (u^6) (root64 u) ∧
      0 < D ∧ D < u^6 ∧ u^6 ≤ D*root64 u ∧
      (D:ℝ)*root64 u ≤ (α+1)*(u:ℝ)^6 ∧
      (∑ d ∈ Ioc D (2*D), (row (Ioc 0 (u^6)) primeWeight (floorMul α) d-
        Chebyshev.psi (u^6 : ℕ)/(d:ℝ))^2) ≤
          (u:ℝ)^6*(root64 u:ℝ)*((14*α+15)*Real.log (u^6 : ℕ)+49) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (root64_tendsto.eventually_ge_atTop (⌈α⌉₊+3))
  obtain ⟨u, hBu, hu, hb⟩ := exists_large_block_dispersion_scale hα hI (max B T)
  have hvcut := hT u ((le_max_right B T).trans hBu.le)
  have hv0 := (root64_bounds hu).1
  have hv2 : 2 ≤ root64 u := by omega
  have hNv : root64 u ≤ u^6 := by
    exact ((Nat.le_self_pow (by decide : 64 ≠ 0) (root64 u)).trans
      (root64_bounds hu).2.1).trans (Nat.le_self_pow (by decide) u)
  have hαv : α+1 < (root64 u:ℝ) := by
    have hc := Nat.le_ceil α
    have hvR : (⌈α⌉₊:ℝ)+3 ≤ root64 u := by exact_mod_cast hvcut
    linarith only [hc, hvR]
  let D := blockStart α (u^6) (root64 u)
  obtain ⟨hD0, hDN, hfloor, hND, hDα, hDv⟩ :=
    blockStart_bounds hα.le hv0 hNv (root64_square_add_two_le_sixth hu hv2) hαv
  change 0 < D at hD0
  change D < u^6 at hDN
  change floorMul α (u^6) ≤ D*root64 u at hfloor
  change u^6 ≤ D*root64 u at hND
  change α*(root64 u:ℝ) < D at hDα
  change (D:ℝ)*root64 u ≤ (α+1)*((u^6:ℕ):ℝ) at hDv
  rw [Nat.cast_pow] at hDv
  refine ⟨u, D, (le_max_left B T).trans_lt hBu, hu, rfl, hD0, hDN, hND, hDv, ?_⟩
  have hh := hb D (root64 u) (root64 u) hD0 hv0 le_rfl hfloor hDα hND
  have hmain : 14*(D:ℝ)*root64 u+(u:ℝ)^6 ≤ (14*α+15)*(u:ℝ)^6 := by
    nlinarith only [hDv]
  have hlog : 0 ≤ (root64 u:ℝ)*Real.log (u^6 : ℕ) := by
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have htail : 49*((u^6:ℕ):ℝ)^2/D ≤ 49*(u:ℝ)^6*(root64 u:ℝ) := by
    have hdR : (0:ℝ) < D := Nat.cast_pos.mpr hD0
    have hnR : ((u^6:ℕ):ℝ) ≤ (D:ℝ)*root64 u := by exact_mod_cast hND
    rw [Nat.cast_pow] at hnR ⊢
    apply (div_le_iff₀ hdR).mpr
    have hm := mul_le_mul_of_nonneg_left hnR (show 0 ≤ 49*(u:ℝ)^6 by positivity)
    nlinarith only [hm]
  apply hh.trans
  calc
    _ ≤ ((root64 u:ℝ)*Real.log (u^6 : ℕ))*((14*α+15)*(u:ℝ)^6)+
        49*(u:ℝ)^6*(root64 u:ℝ) := add_le_add (mul_le_mul_of_nonneg_left hmain hlog) htail
    _ = _ := by ring

#print axioms blockStart_bounds
#print axioms root64_square_add_two_le_sixth
#print axioms exists_explicit_large_block_dispersion
end Erdos972ExplicitLargeDivisorBlock
