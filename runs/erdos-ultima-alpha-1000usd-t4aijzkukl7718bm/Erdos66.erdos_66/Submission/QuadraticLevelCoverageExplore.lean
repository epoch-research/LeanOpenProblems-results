import Submission.QuadraticLevelSelectionExplore

/-! The quadratically spaced levels have arbitrarily fine multiplicative
coverage after a fixed initial index, independently of the final index. -/
namespace Erdos66QuadraticLevelCoverage
open Erdos66QuadraticLevelSelection
open scoped Classical
set_option maxHeartbeats 1800000

lemma level_step_bound (D j : ℕ) (ε : ℝ) (hscale : 3 ≤ ε*((j:ℝ)+1)) :
    (level D (j+1):ℝ) ≤ (1+ε)*(level D j:ℝ) := by
  have hJ : (1:ℝ) ≤ (j:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hh := mul_le_mul_of_nonneg_right hscale (show (0:ℝ) ≤ (j:ℝ)+1 by positivity)
  have hstep : ((j:ℝ)+2)^2 ≤ (1+ε)*((j:ℝ)+1)^2 := by nlinarith only [hh,hJ]
  have hm := mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg (α := ℝ) D)
  simp only [level,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  nlinarith only [hm]

 theorem exists_level_coverage_threshold (ε : ℝ) (hε : 0<ε) :
    ∃ I : ℕ, ∀ D J : ℕ, I ≤ J → ∀ x : ℝ,
      (level D I:ℝ) ≤ x → x ≤ level D J →
      ∃ j : ℕ, I ≤ j ∧ j ≤ J ∧ x ≤ level D j ∧ (level D j:ℝ) ≤ (1+ε)*x := by
  let I : ℕ := ⌈3/ε⌉₊
  have hI : 3 ≤ ε*(I:ℝ) := by
    have hh := (div_le_iff₀ hε).mp (Nat.le_ceil (3/ε))
    linarith
  have hstep (D j : ℕ) (hj : I ≤ j) : (level D (j+1):ℝ) ≤ (1+ε)*(level D j:ℝ) := by
    apply level_step_bound
    have hij : (I:ℝ) ≤ j := by exact_mod_cast hj
    nlinarith only [hI,hij,hε]
  refine ⟨I,?_⟩
  intro D J hIJ x hxI hxJ
  let S := (Finset.Icc I J).filter (fun j ↦ x ≤ (level D j:ℝ))
  have hS : S.Nonempty := ⟨J,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hIJ,le_rfl⟩,hxJ⟩⟩
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image S id hS
  obtain ⟨hjI,hjJ⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1
  have hxj := (Finset.mem_filter.mp hj).2
  have hx0 : 0 ≤ x := (Nat.cast_nonneg (level D I)).trans hxI
  refine ⟨j,hjI,hjJ,hxj,?_⟩
  by_cases he : j=I
  · subst j
    nlinarith only [hxI,hx0,hε]
  · have hjpos : 0<j := by omega
    have hprev : (level D (j-1):ℝ)<x := by
      by_contra hh
      have hm : j-1∈S := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,le_of_not_gt hh⟩
      have hbad := hmin (j-1) hm
      change j ≤ j-1 at hbad
      omega
    have hh := hstep D (j-1) (by omega)
    rw [Nat.sub_add_cancel hjpos] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hprev.le (by linarith))

end Erdos66QuadraticLevelCoverage
