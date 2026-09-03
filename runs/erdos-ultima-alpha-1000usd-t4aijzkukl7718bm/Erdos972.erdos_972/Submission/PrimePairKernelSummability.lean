import FormalConjecturesUtil

/-! A summable reciprocal-square kernel on pairs of primes. This uses
only the ordinary Chebyshev upper bound, not a prime-pair correlation
estimate along a prescribed slope. -/
namespace Erdos972PrimePairKernelSummability

open Finset Filter
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 2000000

abbrev PrimeIndex := {p : ℕ // p.Prime}

noncomputable def pairKernel (x : PrimeIndex × PrimeIndex) : ℝ :=
  (((max x.1.val x.2.val : ℕ):ℝ)^2)⁻¹

def pairBlock (x : PrimeIndex × PrimeIndex) : ℕ := Nat.log 2 (max x.1.val x.2.val)

noncomputable def blockBudget (k : ℕ) : ℝ :=
  ((2^(k+1):ℕ).primeCounting : ℝ)^2 / ((2:ℝ)^k)^2

lemma blockBudget_nonneg (k : ℕ) : 0 ≤ blockBudget k := by
  unfold blockBudget
  positivity

lemma summable_blockBudget : Summable blockBudget := by
  let C : ℝ := Real.log 4+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : Summable (fun k : ℕ => (((k+1:ℕ):ℝ)^2)⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2))
  have hmajor := hbase.mul_left (4*C^2/(Real.log 2)^2)
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  have hpow : Tendsto (fun k : ℕ => ((2^(k+1):ℕ):ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      ((tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ))).comp (tendsto_add_atTop_nat 1))
  filter_upwards [hpow.eventually (Chebyshev.eventually_primeCounting_le
    (by norm_num : (0:ℝ) < 1))] with k hk
  rw [Nat.floor_natCast] at hk
  have hlog : Real.log ((2^(k+1):ℕ):ℝ) = ((k+1:ℕ):ℝ)*Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hlog] at hk
  have hpc0 : (0:ℝ) ≤ (2^(k+1):ℕ).primeCounting := Nat.cast_nonneg _
  have hs := pow_le_pow_left₀ hpc0 hk 2
  rw [Real.norm_eq_abs, abs_of_nonneg (blockBudget_nonneg k)]
  change ((2^(k+1):ℕ).primeCounting : ℝ)^2 / ((2:ℝ)^k)^2 ≤ _
  apply (div_le_div_of_nonneg_right hs (sq_nonneg ((2:ℝ)^k))).trans_eq
  change ((C*((2^(k+1):ℕ):ℝ)/(((k+1:ℕ):ℝ)*Real.log 2))^2 / ((2:ℝ)^k)^2) = _
  rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  have hk0 : ((k+1:ℕ):ℝ) ≠ 0 := by positivity
  have hp0 : (2:ℝ)^k ≠ 0 := by positivity
  field_simp
  ring

lemma pairBlock_bounds (x : PrimeIndex × PrimeIndex) :
    2^(pairBlock x) ≤ max x.1.val x.2.val ∧
      max x.1.val x.2.val < 2^(pairBlock x+1) := by
  refine ⟨Nat.pow_log_le_self 2 ?_, Nat.lt_pow_succ_log_self (by decide) _⟩
  exact Nat.ne_of_gt (x.1.property.pos.trans_le (le_max_left _ _))

lemma fiber_card_bound (S : Finset (PrimeIndex × PrimeIndex)) (k : ℕ) :
    (S.filter (fun x => pairBlock x = k)).card ≤ ((2^(k+1):ℕ).primeCounting)^2 := by
  classical
  let M := 2^(k+1)
  let T := (M+1).primesBelow ×ˢ (M+1).primesBelow
  have hc : (S.filter (fun x => pairBlock x = k)).card ≤ T.card := by
    apply card_le_card_of_injOn (fun x : PrimeIndex × PrimeIndex => (x.1.val, x.2.val))
    · intro x hx
      have hxb := (pairBlock_bounds x).2
      rw [(mem_filter.mp hx).2] at hxb
      apply mem_product.mpr
      constructor
      · exact Nat.mem_primesBelow.mpr ⟨by dsimp [M]; omega, x.1.property⟩
      · exact Nat.mem_primesBelow.mpr ⟨by dsimp [M]; omega, x.2.property⟩
    · intro x hx y hy hxy
      exact Prod.ext (Subtype.ext (congrArg Prod.fst hxy))
        (Subtype.ext (congrArg Prod.snd hxy))
  simpa only [T, card_product, Nat.primesBelow_card_eq_primeCounting',
    Nat.primeCounting, pow_two, M] using hc

lemma fiber_kernel_bound (S : Finset (PrimeIndex × PrimeIndex)) (k : ℕ) :
    (∑ x ∈ S.filter (fun x => pairBlock x = k), pairKernel x) ≤ blockBudget k := by
  classical
  have hbound (x : PrimeIndex × PrimeIndex) (hx : x ∈ S.filter (fun x => pairBlock x = k)) :
      pairKernel x ≤ (((2:ℝ)^k)^2)⁻¹ := by
    have hxb := (pairBlock_bounds x).1
    rw [(mem_filter.mp hx).2] at hxb
    have hcast : (2:ℝ)^k ≤ ((max x.1.val x.2.val : ℕ):ℝ) := by exact_mod_cast hxb
    unfold pairKernel
    simpa only [one_div] using one_div_le_one_div_of_le
      (sq_pos_of_pos (pow_pos (by norm_num : (0:ℝ) < 2) k))
      (pow_le_pow_left₀ (by positivity) hcast 2)
  calc
    _ ≤ ∑ x ∈ S.filter (fun x => pairBlock x = k), (((2:ℝ)^k)^2)⁻¹ :=
      sum_le_sum hbound
    _ = ((S.filter (fun x => pairBlock x = k)).card:ℝ)*(((2:ℝ)^k)^2)⁻¹ := by simp
    _ ≤ (((2^(k+1):ℕ).primeCounting)^2:ℕ)*(((2:ℝ)^k)^2)⁻¹ :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (fiber_card_bound S k)) (by positivity)
    _ = _ := by simp only [blockBudget, Nat.cast_pow, div_eq_mul_inv]

/-- The dyadic prime-pair mass is O(1/k^2), hence summable. No assertion
about simultaneous primality in an irrational floor strip is used. -/
theorem summable_pairKernel : Summable pairKernel := by
  classical
  apply summable_of_sum_le (c := ∑' k : ℕ, blockBudget k)
  · intro x
    unfold pairKernel
    positivity
  · intro S
    rw [← sum_fiberwise_of_maps_to (s := S) (t := S.image pairBlock) (g := pairBlock)
      (fun x hx => mem_image.mpr ⟨x, hx, rfl⟩) pairKernel]
    exact (sum_le_sum (fun k hk => fiber_kernel_bound S k)).trans
      (summable_blockBudget.sum_le_tsum (S.image pairBlock) (fun k _ => blockBudget_nonneg k))

#print axioms summable_blockBudget
#print axioms summable_pairKernel

end Erdos972PrimePairKernelSummability
