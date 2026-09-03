import Submission.VariableBernoulliBoundsExplore

/-! Finite Bernoulli selection using a sum of target-dependent tails. -/
namespace Erdos66SummedBernoulliBounds
open Erdos66FiniteBernoulli Erdos66VariableBernoulliBounds
open scoped Classical
variable {ι κ : Type*} [Fintype ι]
set_option maxHeartbeats 1000000

/-- Sum the individual tail estimates, without a common worst-case scale. -/
theorem exists_summed_bound (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset κ) (F : κ → (ι → Bool) → ℝ) (m V : κ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : ∀ k∈S, m k ≤ V k)
    (hmgf : ∀ k∈S, ∀ t : ℝ, |t| ≤ 1/2 →
      expect p (fun ω ↦ Real.exp (t*(F k ω-m k))) ≤ Real.exp (2*t^2*m k))
    (hsmall : (∑ k∈S, 2*Real.exp (-ε^2*V k/8)) < 1) :
    ∃ ω, 0 < weight p ω ∧ ∀ k∈S, |F k ω-m k| < ε*V k := by
  let t := ε/4
  have ht : 0 < t := by dsimp [t]; positivity
  have htbound : |t| ≤ 1/2 := by rw [abs_of_pos ht]; dsimp [t]; linarith
  have hntbound : |-t| ≤ 1/2 := by simpa only [abs_neg] using htbound
  let P (ω : ι → Bool) := ∑ k∈S,
    (Real.exp (t*(F k ω-m k-ε*V k)) + Real.exp (-t*(F k ω-m k+ε*V k)))
  have hterm (k : κ) (hk : k∈S) :
      expect p (fun ω ↦ Real.exp (t*(F k ω-m k-ε*V k)) +
        Real.exp (-t*(F k ω-m k+ε*V k))) ≤ 2*Real.exp (-ε^2*V k/8) := by
    have he₁ (ω : ι → Bool) : Real.exp (t*(F k ω-m k-ε*V k)) =
        Real.exp (-t*ε*V k)*Real.exp (t*(F k ω-m k)) := by
      rw [←Real.exp_add]; congr 1; ring
    have he₂ (ω : ι → Bool) : Real.exp (-t*(F k ω-m k+ε*V k)) =
        Real.exp (-t*ε*V k)*Real.exp (-t*(F k ω-m k)) := by
      rw [←Real.exp_add]; congr 1; ring
    rw [expect_add]
    simp_rw [he₁,he₂]
    rw [expect_const_mul,expect_const_mul]
    have h₁ := hmgf k hk t htbound
    have h₂ := hmgf k hk (-t) hntbound
    have hb : Real.exp (2*t^2*m k) ≤ Real.exp (2*t^2*V k) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hm k hk) (by positivity))
    have h₁' := mul_le_mul_of_nonneg_left (h₁.trans hb) (Real.exp_pos (-t*ε*V k)).le
    have h₂' := mul_le_mul_of_nonneg_left
      (show expect p (fun ω ↦ Real.exp (-t*(F k ω-m k))) ≤ Real.exp (2*t^2*V k) by
        simpa only [neg_sq] using h₂.trans (by simpa only [neg_sq] using hb))
      (Real.exp_pos (-t*ε*V k)).le
    have he : Real.exp (-t*ε*V k)*Real.exp (2*t^2*V k) = Real.exp (-ε^2*V k/8) := by
      rw [←Real.exp_add]; congr 1; dsimp [t]; ring
    rw [he] at h₁' h₂'
    linarith
  have hP : expect p P < 1 := by
    change expect p (fun ω ↦ ∑ k∈S, _) < 1
    rw [expect_sum]
    exact (Finset.sum_le_sum hterm).trans_lt hsmall
  obtain ⟨ω,hw,hω⟩ := exists_positive_weight_lt p hp P 1 hP
  refine ⟨ω,hw,fun k hk ↦ ?_⟩
  have hle : Real.exp (t*(F k ω-m k-ε*V k)) +
      Real.exp (-t*(F k ω-m k+ε*V k)) ≤ P ω := by
    exact Finset.single_le_sum (f := fun j ↦
      Real.exp (t*(F j ω-m j-ε*V j)) + Real.exp (-t*(F j ω-m j+ε*V j)))
      (fun j hj ↦ by positivity) hk
  have h₁ : Real.exp (t*(F k ω-m k-ε*V k)) < 1 := by
    linarith [Real.exp_pos (-t*(F k ω-m k+ε*V k))]
  have h₂ : Real.exp (-t*(F k ω-m k+ε*V k)) < 1 := by
    linarith [Real.exp_pos (t*(F k ω-m k-ε*V k))]
  have he₁ := Real.exp_lt_one_iff.mp h₁
  have he₂ := Real.exp_lt_one_iff.mp h₂
  rw [abs_lt]
  constructor <;> nlinarith

end Erdos66SummedBernoulliBounds
