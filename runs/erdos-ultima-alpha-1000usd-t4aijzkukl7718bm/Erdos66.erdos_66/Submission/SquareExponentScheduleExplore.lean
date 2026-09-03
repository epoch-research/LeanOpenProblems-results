import Submission.DyadicDeletionExplore

/-! Square-separated dyadic exponents have sublogarithmically many active
centers, uniformly at every natural cutoff. -/
namespace Erdos66SquareExponentSchedule
open Filter
open scoped Topology
set_option maxHeartbeats 2000000

def activeBound (n : ℕ) : ℕ := (Nat.log 2 (2*(n+1))).sqrt+1

lemma index_lt_activeBound (k : ℕ → ℕ) (hk : ∀ j, (j+1)^2 ≤ k j)
    (j n : ℕ) (hjn : 2^(k j) ≤ 2*(n+1)) : j<activeBound n := by
  have hlog := Nat.le_log_of_pow_le (by norm_num : 1<2) hjn
  have hsq : (j+1)*(j+1) ≤ Nat.log 2 (2*(n+1)) := by
    simpa only [pow_two] using (hk j).trans hlog
  have hj := Nat.le_sqrt.mpr hsq
  dsimp only [activeBound]
  omega

lemma activeBound_square_le (n : ℕ) :
    (activeBound n : ℝ)^2 ≤ (4/Real.log 2)*Real.log ((n : ℝ)+2)+2 := by
  have hl2 : 0<Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let m := Nat.log 2 (2*(n+1))
  have hp := Nat.pow_log_le_self 2 (show 2*(n+1)≠0 by omega)
  have hp' : (2 : ℝ)^m ≤ 2*((n : ℝ)+1) := by exact_mod_cast hp
  have hplog := Real.log_le_log (by positivity : (0 : ℝ)<2^m) hp'
  rw [Real.log_pow] at hplog
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have harg : 2*((n : ℝ)+1) ≤ ((n : ℝ)+2)^2 := by nlinarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ)<2*((n : ℝ)+1)) harg
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hm : (m : ℝ) ≤ 2*Real.log ((n : ℝ)+2)/Real.log 2 :=
    (le_div_iff₀ hl2).mpr (by linarith)
  have hs : (m.sqrt : ℝ)^2 ≤ m := by
    have hh : m.sqrt^2 ≤ m := by simpa only [pow_two] using Nat.sqrt_le m
    exact_mod_cast hh
  have hm' : 2*(m : ℝ) ≤ (4/Real.log 2)*Real.log ((n : ℝ)+2) := by
    calc
      _ ≤ 2*(2*Real.log ((n : ℝ)+2)/Real.log 2) := mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by ring
  have hs0 : 0 ≤ (m.sqrt : ℝ) := Nat.cast_nonneg _
  have hb : (activeBound n : ℝ)=(m.sqrt : ℝ)+1 := by simp [activeBound,m]
  rw [hb]
  nlinarith [sq_nonneg ((m.sqrt : ℝ)-1)]

lemma activeBound_log_limit :
    Tendsto (fun n : ℕ ↦ (activeBound n : ℝ)/Real.log ((n : ℝ)+2)) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ ↦ (n : ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith) tendsto_natCast_atTop_atTop
  have hl := Real.tendsto_log_atTop.comp hx
  have hinv := hl.const_div_atTop 1
  have hb := (hinv.const_mul (4/Real.log 2)).add ((hinv.pow 2).const_mul 2)
  simp only [mul_zero,zero_pow (by decide : 2≠0),add_zero,Function.comp_apply] at hb
  have hs : Tendsto (fun n : ℕ ↦ ((activeBound n : ℝ)/Real.log ((n : ℝ)+2))^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ sq_nonneg _) ?_ hb
    intro n
    have hlog : 0<Real.log ((n : ℝ)+2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hh := div_le_div_of_nonneg_right (activeBound_square_le n) (sq_nonneg (Real.log ((n : ℝ)+2)))
    rw [div_pow]
    convert hh using 1
    field_simp [hlog.ne']
  have hh := hs.sqrt
  simp only [Real.sqrt_zero,Real.sqrt_sq_eq_abs] at hh
  convert hh using 1
  funext n
  rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)))]

/-- Arbitrary per-center thresholds can be met without losing square
separation of the dyadic exponents. -/
theorem exists_dominating_schedule (T : ℕ → ℕ) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ j, (j+1)^2 ≤ k j ∧ T j ≤ 2^(k j) := by
  let k : ℕ → ℕ := fun j ↦ (j+1)^2+∑ i∈Finset.range (j+1), T i
  have hsum (j : ℕ) : T j ≤ ∑ i∈Finset.range (j+1), T i :=
    Finset.single_le_sum (fun i _ ↦ Nat.zero_le (T i)) (Finset.mem_range.mpr (by omega))
  refine ⟨k,?_,?_⟩
  · apply strictMono_nat_of_lt_succ
    intro j
    dsimp only [k]
    simp only [Finset.sum_range_succ]
    apply Nat.add_lt_add_of_lt_of_le
    · exact Nat.pow_lt_pow_left (by omega) (by decide)
    · omega
  · intro j
    have hT : T j ≤ k j := (hsum j).trans (Nat.le_add_left _ _)
    exact ⟨Nat.le_add_right _ _,Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by norm_num) hT)⟩

end Erdos66SquareExponentSchedule
