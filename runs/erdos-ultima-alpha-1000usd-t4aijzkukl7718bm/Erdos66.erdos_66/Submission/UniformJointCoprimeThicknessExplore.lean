import Submission.JointCoprimeThicknessExplore
import Submission.EveryPrimeRelativeFamilyExplore

/-! One plane family supports every later admissible pair of large coprime
thicknesses, including all four mixed pair types. -/
namespace Erdos66UniformJointCoprimeThickness
open Erdos66EveryPrimeRelativeFamily Erdos66JointCoprimeThickness
  Erdos66MixedCyclicThickening Erdos66OuterCarryProfile
open scoped Classical
set_option maxHeartbeats 1800000

lemma joint_relative_budget (η : ℝ) (hη1 : η≤1)
    (K L : ℕ) (hbig : 8≤η*(min K L:ℕ)) :
    (K:ℝ)*L*(η/2)+2*(max K L:ℕ)*(1+η/2) ≤ η*K*L := by
  by_cases hKL : K≤L
  · rw [max_eq_right hKL]
    rw [min_eq_left hKL] at hbig
    have hh := mul_le_mul_of_nonneg_right hbig (Nat.cast_nonneg (α:=ℝ) L)
    have hηL := mul_le_mul_of_nonneg_right hη1 (Nat.cast_nonneg (α:=ℝ) L)
    nlinarith
  · have hLK : L≤K := by omega
    rw [max_eq_left hLK]
    rw [min_eq_right hLK] at hbig
    have hh := mul_le_mul_of_nonneg_right hbig (Nat.cast_nonneg (α:=ℝ) K)
    have hηK := mul_le_mul_of_nonneg_right hη1 (Nat.cast_nonneg (α:=ℝ) K)
    nlinarith

/-- No prime change is asserted. Both thicknesses must be large; large maximum
alone suffices for cross-types but not for the self-type transfer. -/
theorem every_prime_joint_coprime_thickness_family
    (η : ℝ) (hη : 0<η) (hη1 : η≤1) (H : ℕ) :
    ∃ D K₀ : ℕ, 0<D ∧ 0<K₀ ∧ ∀ p : ℕ, ∀ hprime : p.Prime,
      max (8*(D*H)+2) (2*(D*H)^2)<p →
      letI : Fact p.Prime := ⟨hprime⟩
      ∃ B : ℕ → Finset (ZMod p × ZMod p), B 0=∅ ∧ Monotone B ∧
        ∀ K L : ℕ, ∀ hK : NeZero K, ∀ hL : NeZero L,
        ∀ hp : p.Coprime (K*L), ∀ hKL : K.Coprime L, K₀ ≤ min K L →
        ∀ i≤H, ∀ j≤H, ∀ a b : Bool, ∀ z : ZMod (p*(p*(K*L))),
          |(cyclicCount _ (twoSet p K L hp hKL a (B i))
            (twoSet p K L hp hKL b (B j)) z:ℝ)-
            4*(D:ℝ)^2*K*L*i*j| ≤ η*(4*(D:ℝ)^2*K*L*i*j) := by
  obtain ⟨D,hD,hfamily⟩ := every_prime_relative_family (η/2) (by positivity) H
  obtain ⟨K₀,hK₀big⟩ := exists_nat_gt (max (1:ℝ) (8/η))
  have hK₀ : 0<K₀ := by
    have hh := (le_max_left (1:ℝ) (8/η)).trans_lt hK₀big
    exact_mod_cast (show (0:ℝ)<K₀ by linarith)
  have hηK₀ : 8<η*K₀ := by
    have hh := (div_lt_iff₀ hη).mp ((le_max_right (1:ℝ) (8/η)).trans_lt hK₀big)
    nlinarith
  refine ⟨D,K₀,hD,hK₀,fun p hprime hpbound ↦ ?_⟩
  letI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨B,hB0,hBmono,hB⟩ := hfamily p hprime hpbound
  refine ⟨B,hB0,hBmono,fun K L hK hL hp hKL hbig i hi j hj a b z ↦ ?_⟩
  letI := hK
  letI := hL
  have hflat : ∀ t s : ZMod p,
      |((mixedFiber p (B i) (B j) t s).card:ℝ)-4*(D:ℝ)^2*i*j| ≤
        (η/2)*(4*(D:ℝ)^2*i*j) := fun t s ↦ (hB i hi j hj).1 (t,s)
  have hh := twoSet_error p K L hp hKL (B i) (B j)
    (4*(D:ℝ)^2*i*j) ((η/2)*(4*(D:ℝ)^2*i*j)) (by positivity) (by positivity)
    hflat a b z
  have hreal : (K₀:ℝ)≤(min K L:ℕ) := by exact_mod_cast hbig
  have hbudget := joint_relative_budget η hη1 K L (by nlinarith)
  have hμ : 0≤4*(D:ℝ)^2*i*j := by positivity
  have hbudget' := mul_le_mul_of_nonneg_right hbudget hμ
  have he : (K:ℝ)*L*(4*(D:ℝ)^2*i*j)=4*(D:ℝ)^2*K*L*i*j := by ring
  rw [he] at hh
  exact hh.trans (by nlinarith only [hbudget'])

end Erdos66UniformJointCoprimeThickness
