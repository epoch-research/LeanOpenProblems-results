import Submission.UniformJointCoprimeThicknessExplore
import Submission.OuterMixedPrefixExplore

/-! Endpoint-prefix control for the joint coprime-thickness palette after one
common outer repetition. This remains a finite-period statement. -/
namespace Erdos66JointThicknessPrefix
open Erdos66JointCoprimeThickness Erdos66UniformJointCoprimeThickness
  Erdos66CoprimeThickness Erdos66OuterCarryProfile Erdos66OuterMixedPrefix
  Erdos66SaturatingCyclicFamily Erdos66CyclicThickening
open scoped Classical
set_option maxHeartbeats 1800000

variable (p K L : ℕ) [NeZero p] [NeZero K] [NeZero L]
variable (hp : p.Coprime (K*L)) (hKL : K.Coprime L)

lemma twoSet_actualMean (a b : Bool) (B C : Finset (ZMod p × ZMod p)) :
    actualMean _ (twoSet p K L hp hKL a B) (twoSet p K L hp hKL b C) =
      (K:ℝ)*L*((B.card:ℝ)*C.card/(p:ℝ)^2) := by
  simp only [actualMean, twoSet_card, Nat.cast_mul]
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hK0 : (K:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  have hL0 : (L:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  field_simp

variable (R : ℕ) [NeZero R]

noncomputable def outerTwoSet (a : Bool) (B : Finset (ZMod p × ZMod p)) :
    Finset (ZMod ((p*(p*(K*L)))*R)) :=
  outerLift _ R (twoSet p K L hp hKL a B)

lemma outerTwoSet_card (a : Bool) (B : Finset (ZMod p × ZMod p)) :
    (outerTwoSet p K L hp hKL R a B).card = R*(K*L*B.card) := by
  rw [outerTwoSet, outerLift_card, twoSet_card]

/-- The original joint cyclic error controls every endpoint prefix after the
outer lift; no same-side or cross-side pair is omitted. -/
theorem outerTwoSet_prefix_error (B C : Finset (ZMod p × ZMod p))
    (μ σ η : ℝ) (hμ : 0≤μ) (hσ : 0≤σ) (hη : 0≤η)
    (hση : σ≤η/4) (hR : 2≤η*(R:ℝ))
    (hflat : ∀ a b : Bool, ∀ z,
      |(cyclicCount _ (twoSet p K L hp hKL a B) (twoSet p K L hp hKL b C) z:ℝ)-μ|
        ≤ σ*μ) (a b : Bool) (z : ZMod ((p*(p*(K*L)))*R))
    (u : ℕ) (hu : u≤(p*(p*(K*L)))*R) :
    |(prefixCount _ (outerTwoSet p K L hp hKL R a B)
      (outerTwoSet p K L hp hKL R b C) z u:ℝ)-
      ((u:ℝ)/((p:ℝ)*(p*(K*L))*R))*(R*μ)| ≤ η*(R*μ) := by
  have hh := outer_prefix_error (p*(p*(K*L))) R
    (twoSet p K L hp hKL a B) (twoSet p K L hp hKL b C) z u hu
    μ σ hμ hσ (hflat a b _)
  have hR1 : (1:ℝ)≤R := by exact_mod_cast NeZero.pos R
  have hbound : ((R:ℝ)+1)*σ+1 ≤ η*R := by
    have h1 := mul_le_mul_of_nonneg_left hση (show (0:ℝ)≤R+1 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hR1 hη
    nlinarith
  have hfinal := hh.trans (mul_le_mul_of_nonneg_right hbound hμ)
  simpa only [outerTwoSet, Nat.cast_mul, mul_assoc] using hfinal

/-- A single plane family, chosen before all thicknesses and outer repetitions,
gives the joint flatness and endpoint-prefix estimates in each later period. -/
theorem every_prime_joint_prefix_family (η : ℝ) (hη : 0<η) (hη1 : η≤1) (H : ℕ) :
    ∃ D K₀ : ℕ, 0<D ∧ 0<K₀ ∧ ∀ p : ℕ, ∀ hprime : p.Prime,
      max (8*(D*H)+2) (2*(D*H)^2)<p →
      letI : Fact p.Prime := ⟨hprime⟩
      ∃ B : ℕ → Finset (ZMod p × ZMod p), B 0=∅ ∧ Monotone B ∧
        ∀ K L R : ℕ, ∀ hK : NeZero K, ∀ hL : NeZero L, ∀ hR : NeZero R,
        ∀ hp : p.Coprime (K*L), ∀ hKL : K.Coprime L,
        K₀ ≤ min K L → 2≤η*(R:ℝ) →
        ∀ i≤H, ∀ j≤H, ∀ a b : Bool,
          (∀ z,
            |(cyclicCount _ (outerTwoSet p K L hp hKL R a (B i))
              (outerTwoSet p K L hp hKL R b (B j)) z:ℝ)-
              R*(4*(D:ℝ)^2*K*L*i*j)| ≤ η*(R*(4*(D:ℝ)^2*K*L*i*j))) ∧
          (∀ z u, u≤(p*(p*(K*L)))*R →
            |(prefixCount _ (outerTwoSet p K L hp hKL R a (B i))
              (outerTwoSet p K L hp hKL R b (B j)) z u:ℝ)-
              ((u:ℝ)/((p:ℝ)*(p*(K*L))*R))*(R*(4*(D:ℝ)^2*K*L*i*j))| ≤
                η*(R*(4*(D:ℝ)^2*K*L*i*j))) := by
  obtain ⟨D,K₀,hD,hK₀,hfamily⟩ :=
    every_prime_joint_coprime_thickness_family (η/4) (by positivity) (by linarith) H
  refine ⟨D,K₀,hD,hK₀,fun p hprime hpbound ↦ ?_⟩
  letI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨B,hB0,hBmono,hB⟩ := hfamily p hprime hpbound
  refine ⟨B,hB0,hBmono,fun K L R hK hL hR hp hKL hbig hRbig i hi j hj a b ↦ ?_⟩
  letI := hK
  letI := hL
  letI := hR
  have hflat := hB K L hK hL hp hKL hbig i hi j hj
  have hμ : 0≤4*(D:ℝ)^2*K*L*i*j := by positivity
  constructor
  · intro z
    simp only [outerTwoSet, outer_cyclicCount, Nat.cast_mul, ← mul_sub,
      abs_mul, abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) R)]
    have hh := mul_le_mul_of_nonneg_left (hflat a b (reduceDigit _ R z))
      (Nat.cast_nonneg (α:=ℝ) R)
    have hnonneg := mul_nonneg (mul_nonneg hη.le (Nat.cast_nonneg (α:=ℝ) R)) hμ
    nlinarith only [hh,hnonneg]
  · intro z u hu
    exact outerTwoSet_prefix_error p K L hp hKL R (B i) (B j)
      (4*(D:ℝ)^2*K*L*i*j) (η/4) η hμ (by positivity) hη.le le_rfl hRbig
      hflat a b z u hu

end Erdos66JointThicknessPrefix
