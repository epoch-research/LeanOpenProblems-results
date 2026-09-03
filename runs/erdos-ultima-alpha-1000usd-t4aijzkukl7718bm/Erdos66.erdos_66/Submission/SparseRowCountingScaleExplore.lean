import Submission.InfiniteIntervalRowsExplore

/-! Transfer of negligible original counting scale to the finite row budgets
used by simultaneous interval-row rounding. -/
namespace Erdos66SparseRowCountingScale
open Filter Erdos66Counting Erdos66SparseRowMeanDecay
open scoped Classical Topology
set_option maxHeartbeats 2800000

lemma row_count_scale_bound (n : ℕ) :
    Real.sqrt (((2*(n+1)+1 : ℕ) : ℝ)*Real.log ((2*(n+1)+1 : ℕ) : ℝ)) ≤
      4*Real.sqrt (((n : ℝ)+1)*Real.log ((n : ℝ)+2)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log ((n : ℝ)+2) := Real.log_nonneg (by linarith)
  have hlogK : 0 ≤ Real.log ((2*(n+1)+1 : ℕ) : ℝ) := Real.log_nonneg (by push_cast; linarith)
  have hKpos : (0 : ℝ)<((2*(n+1)+1 : ℕ) : ℝ) := by positivity
  have harg : ((2*(n+1)+1 : ℕ) : ℝ) ≤ ((n : ℝ)+2)^2 := by push_cast; nlinarith
  have hh := Real.log_le_log hKpos harg
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hK : ((2*(n+1)+1 : ℕ) : ℝ) ≤ 4*((n : ℝ)+1) := by push_cast; linarith
  have hprod := mul_le_mul hK hh hlogK (by positivity : 0 ≤ 4*((n : ℝ)+1))
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  nlinarith only [hprod,show 0 ≤ ((n : ℝ)+1)*Real.log ((n : ℝ)+2) by positivity]

lemma sparse_row_count_decay (D E : Set ℕ) (hED : E ⊆ D)
    (hD : Tendsto (fun n : ℕ ↦ (count D n : ℝ)/Real.sqrt ((n : ℝ)*Real.log n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (count E (2*(n+1)+1) : ℝ)/
      Real.sqrt (((n : ℝ)+1)*Real.log ((n : ℝ)+2))) atTop (𝓝 0) := by
  have hK : Tendsto (fun n : ℕ ↦ 2*(n+1)+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ show n ≤ 2*(n+1)+1 by omega) tendsto_id
  have hh := (hD.comp hK).const_mul 4
  simp only [mul_zero,Function.comp_apply] at hh
  apply squeeze_zero (fun n ↦ div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) ?_ hh
  intro n
  let K := 2*(n+1)+1
  have hsub : count E K ≤ count D K := Finset.card_le_card (by
    intro i hi
    exact mem_cutoff.mpr ⟨(mem_cutoff.mp hi).1,hED (mem_cutoff.mp hi).2⟩)
  have hNpos : 0<Real.sqrt (((n : ℝ)+1)*Real.log ((n : ℝ)+2)) :=
    Real.sqrt_pos.mpr (mul_pos (by positivity) (Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)))
  have hKpos : 0<Real.sqrt ((K : ℝ)*Real.log K) := by
    apply Real.sqrt_pos.mpr
    apply mul_pos
    · dsimp only [K]; positivity
    · apply Real.log_pos
      exact_mod_cast (show 1<K by dsimp only [K]; omega)
  have hb := row_count_scale_bound n
  change Real.sqrt ((K : ℝ)*Real.log K) ≤ 4*Real.sqrt (((n : ℝ)+1)*Real.log ((n : ℝ)+2)) at hb
  have hsub' : (count E K : ℝ) ≤ count D K := by exact_mod_cast hsub
  change (count E K : ℝ)/Real.sqrt (((n : ℝ)+1)*Real.log ((n : ℝ)+2)) ≤
    4*((count D K : ℝ)/Real.sqrt ((K : ℝ)*Real.log K))
  apply (div_le_iff₀ hNpos).mpr
  have hmul := mul_le_mul_of_nonneg_right hb
    (div_nonneg (Nat.cast_nonneg (count D K)) hKpos.le)
  have he : Real.sqrt ((K : ℝ)*Real.log K)*((count D K : ℝ)/Real.sqrt ((K : ℝ)*Real.log K))=count D K := by field_simp
  rw [he] at hmul
  nlinarith only [hsub',hmul]

end Erdos66SparseRowCountingScale
