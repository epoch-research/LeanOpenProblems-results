import Submission.RelativeCyclicFamilyExplore
import Submission.RepeatCarryExplore

/-! Relative control of both integer carry fibers, with the coefficient
chosen before an arbitrarily large common period. -/
namespace Erdos66RelativeFiberFamily
open Erdos66RelativeCyclicFamily Erdos66RepeatCarry Erdos66IntegerBlock
open scoped Classical
set_option maxHeartbeats 1000000

/-- These families can be used with arbitrary integer block levels: their
error scales with the product of the levels, including at level zero. -/
theorem exists_relative_fiber_family (η : ℝ) (hη : 0 < η) (H : ℕ) :
    ∃ β : ℝ, 0 < β ∧ ∀ N₀ : ℕ, ∃ M : ℕ, N₀ < M ∧ ∃ hM : NeZero M,
      ∃ C : ℕ → Finset (ZMod M), C 0 = ∅ ∧ Monotone C ∧
        ∀ i ≤ H, ∀ j ≤ H, ∀ t : ℕ, t < M →
          |(lower M (C i) (C j) t : ℝ) - (t : ℝ) / M * (β * i * j)| ≤ η * (β * i * j) ∧
          |(upper M (C i) (C j) t : ℝ) - (1 - (t : ℝ) / M) * (β * i * j)| ≤ η * (β * i * j) := by
  let η' : ℝ := min (η / 8) (1 / 8)
  have hη' : 0 < η' := lt_min (by positivity) (by norm_num)
  have hη'η : η' ≤ η / 8 := min_le_left _ _
  have hη'1 : η' ≤ 1 / 8 := min_le_right _ _
  obtain ⟨J, hJbig⟩ := exists_nat_gt (max (1 : ℝ) (8 / η))
  have hJreal : (1 : ℝ) < J := lt_of_le_of_lt (le_max_left _ _) hJbig
  have hJ : 1 ≤ J := by exact_mod_cast hJreal.le
  have hJη : 8 < η * J := by
    have hh := (div_lt_iff₀ hη).mp (lt_of_le_of_lt (le_max_right _ _) hJbig)
    linarith
  have hfac : (J : ℝ) * η' + 1 + η' ≤ η * J := by
    have hh := mul_le_mul_of_nonneg_left hη'η (Nat.cast_nonneg (α := ℝ) J)
    nlinarith
  letI : NeZero J := ⟨by omega⟩
  obtain ⟨β₀, hβ₀, hfam⟩ := exists_relative_cyclic_family η' hη' H
  refine ⟨J * β₀, by positivity, fun N₀ ↦ ?_⟩
  obtain ⟨M₀, hM₀N, hM₀, C, hC0, hCmono, hC⟩ := hfam N₀
  letI := hM₀
  let M := M₀ * J
  let C' : ℕ → Finset (ZMod M) := fun i ↦ repeatPattern M₀ J (C i)
  have hMge : M₀ ≤ M := by dsimp [M]; nlinarith
  refine ⟨M, by omega, inferInstance, C', ?_, ?_, ?_⟩
  · simp [C', hC0, repeatPattern]
  · intro i j hij a ha
    exact (mem_repeatPattern M₀ J (C j) a).mpr (hCmono hij ((mem_repeatPattern M₀ J (C i) a).mp ha))
  · intro i hi j hj n hn
    let q := n / M₀
    let t := n % M₀
    have ht : t < M₀ := Nat.mod_lt _ (NeZero.pos _)
    have heq : q * M₀ + t = n := Nat.div_add_mod' _ _
    have hq : q < J := by
      have hh := (Nat.div_lt_iff_lt_mul (NeZero.pos M₀)).mpr (show n < J * M₀ by dsimp [M] at hn; nlinarith)
      exact hh
    have hμ : 0 ≤ β₀ * i * j := by positivity
    have herr := repeat_fiber_error M₀ J (C i) (C j) (β₀ * i * j) (η' * (β₀ * i * j))
      hμ (mul_nonneg hη'.le hμ) (hC i hi j hj) q t hq ht
    rw [heq] at herr
    have hmainlow : ((q : ℝ) + (t : ℝ) / M₀) * (β₀ * i * j) =
        (n : ℝ) / M * ((J : ℝ) * β₀ * i * j) := by
      have heq' : (q : ℝ) * M₀ + t = n := by exact_mod_cast heq
      have hM₀real : (M₀ : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M₀
      have hJreal0 : (J : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne J
      dsimp [M]
      push_cast
      field_simp
      nlinarith
    have hmainupper : ((J : ℝ) - q - (t : ℝ) / M₀) * (β₀ * i * j) =
        (1 - (n : ℝ) / M) * ((J : ℝ) * β₀ * i * j) := by
      nlinarith
    have hbound : (J : ℝ) * (η' * (β₀ * i * j)) + β₀ * i * j + η' * (β₀ * i * j) ≤
        η * ((J : ℝ) * β₀ * i * j) := by
      have hh := mul_le_mul_of_nonneg_right hfac hμ
      nlinarith
    change |(lower (M₀ * J) (repeatPattern M₀ J (C i)) (repeatPattern M₀ J (C j)) n : ℝ) - _| ≤ _ ∧
      |(upper (M₀ * J) (repeatPattern M₀ J (C i)) (repeatPattern M₀ J (C j)) n : ℝ) - _| ≤ _
    rw [← hmainlow, ← hmainupper]
    exact ⟨herr.1.trans hbound, herr.2.trans hbound⟩

end Erdos66RelativeFiberFamily
