import Submission.RealWeightedCharacterEnergyExplore
import Submission.RandomConstantProfileExplore
import Submission.AffineRootAggregateExplore

/-! The shifted fractional profile has only logarithmically many squared
weight units. A character translation therefore has at most O(log^2 h)
large signed-mean fibers. This is not yet a binary rounding or repair. -/
namespace Erdos66WeightedProfileCharacter
open Erdos66ConstantProfile Erdos66ShiftedProfile Erdos66RealWeightedCharacterEnergy
  Erdos66AffineRootAggregate Erdos66SharedParameterKernel
open scoped Classical
set_option maxHeartbeats 1800000

noncomputable def profileWeight (μ : ℝ) (s i : ℕ) : ℝ := Real.sqrt μ*b (i+s)

lemma profileWeight_bounds (μ : ℝ) (s : ℕ) (hμ : 0 ≤ μ) (hs : μ ≤ (s : ℝ)+1)
    (i : ℕ) : 0 ≤ profileWeight μ s i ∧ profileWeight μ s i ≤ 1 := by
  exact Erdos66RandomConstantProfile.probability_bounds μ s i hμ hs ⟨i,Nat.lt_succ_self i⟩

lemma profileWeight_sq_mass (μ : ℝ) (s h : ℕ) (hμ : 0 ≤ μ) :
    (∑ i∈Finset.range h, (profileWeight μ s i)^2) ≤ μ*(harmonic h : ℝ) := by
  have hterm (i : ℕ) : (profileWeight μ s i)^2 ≤ μ/((i : ℝ)+1) := by
    have hbi : (b i)^2 ≤ 1/((i : ℝ)+1) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ)<(i : ℝ)+1)).mpr
      nlinarith [b_square_bound i]
    have hshift := pow_le_pow_left₀ (b_pos (i+s)).le (b_antitone (by omega : i ≤ i+s)) 2
    have hm := mul_le_mul_of_nonneg_left (hshift.trans hbi) hμ
    simpa only [profileWeight,mul_pow,Real.sq_sqrt hμ,mul_one_div] using hm
  calc
    _ ≤ ∑ i∈Finset.range h, μ/((i : ℝ)+1) := Finset.sum_le_sum (fun i _ ↦ hterm i)
    _ = _ := by simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_add,Rat.cast_one,Rat.cast_natCast,Nat.cast_add,
        Nat.cast_one,Finset.mul_sum,div_eq_mul_inv]

lemma profileWeight_sq_mass_log (μ : ℝ) (s h : ℕ) (hμ : 0 ≤ μ) :
    (∑ i∈Finset.range h, (profileWeight μ s i)^2) ≤ μ*(1+Real.log (h : ℝ)) :=
  (profileWeight_sq_mass μ s h hμ).trans (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log h) hμ)

lemma profileWeight_fiber (μ : ℝ) (s h q : ℕ) (hμ : 0 ≤ μ) (hq : q<h) :
    labelFiber h (profileWeight μ s) q = μ*tailConv s q := by
  rw [labelFiber,diagonal_sum h q hq,tailConv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [profileWeight]
  rw [show Real.sqrt μ*b (i+s)*(Real.sqrt μ*b (q-i+s)) =
    (Real.sqrt μ)^2*(b (i+s)*b (q-i+s)) by ring,Real.sq_sqrt hμ]

/-- A single admissible translation works for every error threshold. The
exceptional coarse-target count is independent of both mu and the prime. -/
theorem exists_profile_translation (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (s h : ℕ) (hh : 4*h<p) (μ : ℝ) (hμ : 0<μ) :
    ∃ a : ZMod p, (∀ i<h, a+(i : ZMod p) ≠ 0) ∧
      (∀ q<2*h, 2*a+(q : ZMod p) ≠ 0) ∧
      ∀ ε : ℝ, 0<ε →
        ((badTargets h (profileWeight μ s) a (ε*μ)).card : ℝ) ≤
          8*(1+Real.log (h : ℝ))^2/ε^2 := by
  obtain ⟨a,ha,hop,henergy,hbad⟩ := exists_admissible_weighted_translate p hp h hh (profileWeight μ s)
  refine ⟨a,ha,hop,fun ε hε ↦ ?_⟩
  have hmass := profileWeight_sq_mass_log μ s h hμ.le
  have hmass0 : 0 ≤ ∑ i∈Finset.range h, (profileWeight μ s i)^2 :=
    Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hsq := pow_le_pow_left₀ hmass0 hmass 2
  have hb := hbad (ε*μ) (by positivity)
  have hmain : ((badTargets h (profileWeight μ s) a (ε*μ)).card : ℝ)*ε^2 ≤
      8*(1+Real.log (h : ℝ))^2 := by
    have hmul : (((badTargets h (profileWeight μ s) a (ε*μ)).card : ℝ)*ε^2)*μ^2 ≤
        (8*(1+Real.log (h : ℝ))^2)*μ^2 := by nlinarith
    exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hμ)).mp hmul
  exact (le_div_iff₀ (sq_pos_of_pos hε)).mpr hmain

/-- A fractional root profile is uniformly accurate off the explicitly
bounded set of coarse exceptions. All fine field-plane targets are covered. -/
theorem exists_fractional_root_profile (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (s h : ℕ) (hh : 4*h<p) (μ ε : ℝ) (hμ : 0<μ) (hε : 0<ε) :
    ∃ (a : ZMod p) (T : Finset ℕ),
      (∀ i<h, a+(i : ZMod p) ≠ 0) ∧
      (∀ q<2*h, 2*a+(q : ZMod p) ≠ 0) ∧
      (T.card : ℝ) ≤ 8*(1+Real.log (h : ℝ))^2/ε^2 ∧
      ∀ q<h, q∉T → ∀ t u : ZMod p,
        |rootAggregate h a (profileWeight μ s) q t u-μ*tailConv s q| ≤ ε*μ := by
  obtain ⟨a,ha,hop,hbad⟩ := exists_profile_translation p hp s h hh μ hμ
  let T := badTargets h (profileWeight μ s) a (ε*μ)
  refine ⟨a,T,ha,hop,hbad ε hε,?_⟩
  intro q hq hqT t u
  have hq2 : q<2*h := by omega
  have hs : |signedFiber h (profileWeight μ s) a q| ≤ ε*μ := by
    by_contra hnot
    apply hqT
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq2,lt_of_not_ge hnot⟩
  rw [←profileWeight_fiber μ s h q hμ.le hq]
  exact (rootAggregate_error h a (profileWeight μ s) q
    (by simpa only [ZMod.ringChar_zmod_n] using hp) ha (hop q hq2) t u).trans hs

end Erdos66WeightedProfileCharacter
