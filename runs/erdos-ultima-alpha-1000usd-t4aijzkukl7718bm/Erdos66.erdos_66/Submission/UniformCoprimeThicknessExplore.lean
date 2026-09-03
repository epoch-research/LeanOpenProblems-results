import Submission.CoprimeThicknessGeometryExplore
import Submission.EveryPrimeRelativeFamilyExplore

/-! One plane family supports every later pair of coprime coordinate
thicknesses over the same prime, with controlled mixed counts. -/
namespace Erdos66UniformCoprimeThickness
open Erdos66EveryPrimeRelativeFamily Erdos66CoprimeThickness
  Erdos66MixedCyclicThickening Erdos66OuterCarryProfile
open scoped Classical
set_option maxHeartbeats 1800000

lemma rectangle_relative_budget (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (K L : ℕ) (hbig : 4≤η*(max K L:ℕ)) :
    (K:ℝ)*L*(η/2)+(min K L:ℕ)*(1+η/2) ≤ η*K*L := by
  by_cases hKL : K≤L
  · rw [min_eq_left hKL]
    rw [max_eq_right hKL] at hbig
    have hh := mul_le_mul_of_nonneg_right hbig (Nat.cast_nonneg (α:=ℝ) K)
    have hηK := mul_le_mul_of_nonneg_right hη1 (Nat.cast_nonneg (α:=ℝ) K)
    nlinarith
  · have hLK : L≤K := by omega
    rw [min_eq_right hLK]
    rw [max_eq_left hLK] at hbig
    have hh := mul_le_mul_of_nonneg_right hbig (Nat.cast_nonneg (α:=ℝ) L)
    have hηL := mul_le_mul_of_nonneg_right hη1 (Nat.cast_nonneg (α:=ℝ) L)
    nlinarith

/-- The underlying plane family is selected before K and L. This is
same-prime compatibility, not compatibility between different fields. -/
theorem every_prime_coprime_thickness_family (η : ℝ) (hη : 0<η) (hη1 : η≤1) (H : ℕ) :
    ∃ D K₀ : ℕ, 0<D ∧ 0<K₀ ∧ ∀ p : ℕ, ∀ hprime : p.Prime,
      max (8*(D*H)+2) (2*(D*H)^2)<p →
      letI : Fact p.Prime := ⟨hprime⟩
      ∃ B : ℕ → Finset (ZMod p × ZMod p), B 0=∅ ∧ Monotone B ∧
        ∀ K L : ℕ, ∀ hK : NeZero K, ∀ hL : NeZero L,
        ∀ hp : p.Coprime (K*L), ∀ hKL : K.Coprime L, K₀ ≤ max K L →
        ∀ i≤H, ∀ j≤H, ∀ z : ZMod (p*(p*(K*L))),
          |(cyclicCount _ (leftSet p K L hp hKL (B i)) (rightSet p K L hp hKL (B j)) z:ℝ)-
            4*(D:ℝ)^2*K*L*i*j| ≤ η*(4*(D:ℝ)^2*K*L*i*j) := by
  obtain ⟨D,hD,hfamily⟩ := every_prime_relative_family (η/2) (by positivity) H
  obtain ⟨K₀,hK₀big⟩ := exists_nat_gt (max (1:ℝ) (4/η))
  have hK₀ : 0<K₀ := by
    have hh := (le_max_left (1:ℝ) (4/η)).trans_lt hK₀big
    exact_mod_cast (show (0:ℝ)<K₀ by linarith)
  have hηK₀ : 4<η*K₀ := by
    have hh := (div_lt_iff₀ hη).mp ((le_max_right (1:ℝ) (4/η)).trans_lt hK₀big)
    nlinarith
  refine ⟨D,K₀,hD,hK₀,fun p hprime hpbound ↦ ?_⟩
  letI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨B,hB0,hBmono,hB⟩ := hfamily p hprime hpbound
  refine ⟨B,hB0,hBmono,fun K L hK hL hp hKL hbig i hi j hj z ↦ ?_⟩
  letI := hK
  letI := hL
  have hflat : ∀ t s : ZMod p,
      |((mixedFiber p (B i) (B j) t s).card:ℝ)-4*(D:ℝ)^2*i*j| ≤
        (η/2)*(4*(D:ℝ)^2*i*j) := fun t s ↦ (hB i hi j hj).1 (t,s)
  have hh := mixed_thickness_error p K L hp hKL (B i) (B j)
    (4*(D:ℝ)^2*i*j) ((η/2)*(4*(D:ℝ)^2*i*j)) hflat z
  have hreal : (K₀:ℝ)≤(max K L:ℕ) := by exact_mod_cast hbig
  have hbudget := rectangle_relative_budget η hη hη1 K L (by nlinarith)
  have hμ : 0≤4*(D:ℝ)^2*i*j := by positivity
  have hbudget' := mul_le_mul_of_nonneg_right hbudget hμ
  have he : (K:ℝ)*L*(4*(D:ℝ)^2*i*j)=4*(D:ℝ)^2*K*L*i*j := by ring
  rw [he] at hh
  exact hh.trans (by nlinarith only [hbudget'])

end Erdos66UniformCoprimeThickness
