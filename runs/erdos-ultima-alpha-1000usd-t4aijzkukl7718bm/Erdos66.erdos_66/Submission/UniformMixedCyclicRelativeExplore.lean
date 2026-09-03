import Submission.EveryPrimeRelativeFamilyExplore
import Submission.MixedCyclicThickeningExplore
import Submission.OuterCarryProfileExplore

/-! A mixed, nested, every-prime cyclic family with freely variable sufficiently
large coordinate thickness. -/
namespace Erdos66UniformMixedCyclicRelative
open Erdos66EveryPrimeRelativeFamily Erdos66CyclicThickening
  Erdos66MixedCyclicThickening Erdos66OuterCarryProfile
open scoped Classical
set_option maxHeartbeats 1500000

theorem every_prime_mixed_cyclic_family (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (H : ℕ) :
    ∃ D K₀ : ℕ, 0 < D ∧ 0 < K₀ ∧ ∀ p : ℕ, ∀ hp : p.Prime,
      max (8*(D*H)+2) (2*(D*H)^2) < p → ∀ K : ℕ, K₀ ≤ K →
      ∃ C : ℕ → Finset (ZMod ((p*K)^2)), C 0=∅ ∧ Monotone C ∧
        ∀ i ≤ H, ∀ j ≤ H, ∀ z,
          |(cyclicCount ((p*K)^2) (C i) (C j) z : ℝ)-4*(D : ℝ)^2*K^2*i*j| ≤
            η*(4*(D : ℝ)^2*K^2*i*j) := by
  obtain ⟨D,hD,hfamily⟩ := every_prime_relative_family (η/2) (by positivity) H
  obtain ⟨K₀,hK₀big⟩ := exists_nat_gt (max (1 : ℝ) (8/η))
  have hK₀ : 0 < K₀ := by
    have hh := lt_of_le_of_lt (le_max_left _ _) hK₀big
    exact_mod_cast (show (0 : ℝ) < K₀ by linarith)
  have hηK₀ : 8 < η*K₀ := by
    have hh := (div_lt_iff₀ hη).mp (lt_of_le_of_lt (le_max_right _ _) hK₀big)
    linarith
  refine ⟨D,K₀,hD,hK₀,fun p hp hprime K hK ↦ ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hKpos : 0 < K := hK₀.trans_le hK
  letI : NeZero K := ⟨hKpos.ne'⟩
  obtain ⟨B,hB0,hBmono,hB⟩ := hfamily p hp hprime
  let C : ℕ → Finset (ZMod ((p*K)^2)) := fun i ↦ thickenedSet p K (B i)
  refine ⟨C,?_,fun i j hij ↦ thickenedSet_mono p K (hBmono hij),?_⟩
  · simp [C,hB0,thickenedSet]
  · intro i hi j hj z
    have hf : ∀ t s : ZMod p,
        |((mixedFiber p (B i) (B j) t s).card : ℝ)-4*(D : ℝ)^2*i*j| ≤
          (η/2)*(4*(D : ℝ)^2*i*j) := by
      intro t s
      exact (hB i hi j hj).1 (t,s)
    have hh := thickenedSet_error p K (B i) (B j) (4*(D : ℝ)^2*i*j)
      ((η/2)*(4*(D : ℝ)^2*i*j)) hf z
    have hKr : (K₀ : ℝ) ≤ K := by exact_mod_cast hK
    have hηK : 8 ≤ η*K := by nlinarith
    have hμ : 0 ≤ 4*(D : ℝ)^2*i*j := by positivity
    have hbudget : (K : ℝ)^2*(η/2)+2*K*(1+η/2) ≤ η*K^2 := by
      have h₁ := mul_le_mul_of_nonneg_right hηK (Nat.cast_nonneg (α := ℝ) K)
      have h₂ := mul_le_mul_of_nonneg_right hη1 (Nat.cast_nonneg (α := ℝ) K)
      nlinarith
    have he : (K : ℝ)^2*(4*(D : ℝ)^2*i*j)=4*(D : ℝ)^2*K^2*i*j := by ring
    rw [he] at hh
    apply hh.trans
    convert mul_le_mul_of_nonneg_right hbudget hμ using 1 <;> dsimp only [C,cyclicCount] <;> ring

end Erdos66UniformMixedCyclicRelative
