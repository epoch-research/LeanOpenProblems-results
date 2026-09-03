import Submission.IntegerBlockExplore
import Submission.ResidueSeriesExplore

/-!
# Fixed-block replication and logarithmic representation limits

Replacing each a in A by the entire block [Ma,M(a+1)) preserves existence
of a logarithmic limit, and multiplies its coefficient by M. In particular,
this operation is not a way to obtain convergence by averaging a sequence
that did not already converge. This does not settle Erdős Problem 66.
-/

namespace Erdos66BlockReplicationLimit
open Filter AdditiveCombinatorics Erdos66IntegerBlock Erdos66ResidueSeries
open scoped Classical Topology
set_option maxHeartbeats 1800000

variable (M : ℕ) [NeZero M]

def replicate (A : Set ℕ) : Set ℕ := {n | n / M ∈ A}

noncomputable def palette (A : Set ℕ) (k : ℕ) : Finset (ZMod M) :=
  if k ∈ A then Finset.univ else ∅

lemma replicate_eq_blockSet (A : Set ℕ) :
    replicate M A = blockSet M (palette M A) := by
  ext n
  simp only [replicate, blockSet, palette, Set.mem_setOf_eq]
  split_ifs <;> simp_all

lemma lower_full (t : ℕ) (ht : t < M) :
    lower M Finset.univ Finset.univ t = t + 1 := by
  have he : (Finset.range M).filter (fun x ↦ x ≤ t) = Finset.range (t+1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp only [lower, Finset.mem_univ, and_true]
  rw [Finset.sum_boole, he, Finset.card_range]
  rfl

lemma upper_full (t : ℕ) (ht : t < M) :
    upper M Finset.univ Finset.univ t = M - (t+1) := by
  have hh := lower_add_upper M Finset.univ Finset.univ t
  simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ, ZMod.card] at hh
  rw [lower_full M t ht] at hh
  omega

lemma lower_palette (A : Set ℕ) (i j t : ℕ) (ht : t < M) :
    lower M (palette M A i) (palette M A j) t =
      (if i ∈ A ∧ j ∈ A then 1 else 0) * (t+1) := by
  by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
  · simpa only [palette, if_pos hi, if_pos hj, if_pos (And.intro hi hj), one_mul] using
      lower_full M t ht
  all_goals simp [palette, hi, hj, lower]

lemma upper_palette (A : Set ℕ) (i j t : ℕ) (ht : t < M) :
    upper M (palette M A i) (palette M A j) t =
      (if i ∈ A ∧ j ∈ A then 1 else 0) * (M-(t+1)) := by
  by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
  · simpa only [palette, if_pos hi, if_pos hj, if_pos (And.intro hi hj), one_mul] using
      upper_full M t ht
  all_goals simp [palette, hi, hj, upper]

/-- The exact natural carry formula, not a cyclic representation count. -/
theorem replicate_rep_succ (A : Set ℕ) (q t : ℕ) (ht : t < M) :
    sumRep (replicate M A) ((q+1)*M+t) =
      (t+1) * sumRep A (q+1) + (M-(t+1)) * sumRep A q := by
  rw [replicate_eq_blockSet, block_formula M _ (q+1) t ht]
  simp_rw [lower_palette M A _ _ t ht, upper_palette M A _ _ t ht]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have he : (∑ k ∈ Finset.range (q+1), if k ∈ A ∧ q+1-k-1 ∈ A then 1 else 0) =
      sumRep A q := by
    rw [sumRep_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hkq : k ≤ q := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    rw [show q+1-k-1=q-k by omega]
  rw [← sumRep_range, he]
  ring

/-- At the last digit in each block there is no averaging at all. -/
theorem replicate_rep_last (A : Set ℕ) (q : ℕ) :
    sumRep (replicate M A) (q*M+(M-1)) = M * sumRep A q := by
  have hM : 0 < M := NeZero.pos M
  rw [replicate_eq_blockSet, block_formula M _ q (M-1) (by omega)]
  simp_rw [lower_palette M A _ _ (M-1) (by omega),
    upper_palette M A _ _ (M-1) (by omega)]
  simp only [show M-1+1=M by omega, Nat.sub_self, mul_zero, Finset.sum_const_zero,
    add_zero]
  rw [← Finset.sum_mul, ← sumRep_range, Nat.mul_comm]

/-- A finite collection of affine subsequence limits controls the full sequence. -/
lemma tendsto_of_all_residues {f : ℕ → ℝ} {c : ℝ}
    (h : ∀ t : Fin M, Tendsto (fun q ↦ f (q*M+t.val)) atTop (𝓝 c)) :
    Tendsto f atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : ∀ t : Fin M, ∀ᶠ q : ℕ in atTop, dist (f (q*M+t.val)) c < ε :=
    fun t ↦ (h t).eventually (Metric.ball_mem_nhds c hε)
  have hall : ∀ᶠ q : ℕ in atTop, ∀ t : Fin M, dist (f (q*M+t.val)) c < ε :=
    Filter.eventually_all.mpr he
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp hall
  refine ⟨Q*M, fun n hn ↦ ?_⟩
  have hnq : Q ≤ n/M := (Nat.le_div_iff_mul_le (NeZero.pos M)).mpr hn
  have hh := hQ (n/M) hnq ⟨n%M, Nat.mod_lt _ (NeZero.pos M)⟩
  simpa only [Nat.mul_comm (n/M) M, Nat.div_add_mod] using hh

/-- Fixed-block replication multiplies the limit coefficient. -/
theorem replicate_log_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ (sumRep (replicate M A) n : ℝ)/Real.log n)
      atTop (𝓝 ((M : ℝ)*c)) := by
  apply tendsto_of_all_residues M
  intro t
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hs := affine_log_limit 1 h 1
  simp only [mul_one] at hs
  have hsum := (hs.const_mul ((t.val+1 : ℕ) : ℝ)).add
    (h.const_mul ((M-(t.val+1) : ℕ) : ℝ))
  have hcoef : ((t.val+1 : ℕ) : ℝ)*c + ((M-(t.val+1) : ℕ) : ℝ)*c = (M : ℝ)*c := by
    rw [← add_mul, ← Nat.cast_add, Nat.add_sub_of_le (by omega : t.val+1 ≤ M)]
  rw [hcoef] at hsum
  have hratio := log_affine_ratio M (M+t.val)
  have hlim := hsum.div hratio (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with q hq
  have hlog : Real.log (q : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hq))
  rw [replicate_rep_succ M A q t.val t.isLt]
  push_cast
  simp only [Pi.div_apply]
  rw [show ((q : ℝ)+1)*M+t.val=(q : ℝ)*M+(M+t.val) by ring]
  field_simp

/-- Conversely, the last-digit subsequence recovers the original limit. -/
theorem log_limit_of_replicate {A : Set ℕ} {d : ℝ}
    (h : Tendsto (fun n ↦ (sumRep (replicate M A) n : ℝ)/Real.log n) atTop (𝓝 d)) :
    Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 (d/(M : ℝ))) := by
  have hh := (affine_log_limit M h (M-1)).div_const (M : ℝ)
  apply hh.congr
  intro q
  rw [replicate_rep_last, Nat.cast_mul]
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  field_simp

/-- Replication cannot create a logarithmic limit from a nonconvergent input. -/
theorem replicate_log_limit_iff (A : Set ℕ) (c : ℝ) :
    Tendsto (fun n ↦ (sumRep (replicate M A) n : ℝ)/Real.log n)
      atTop (𝓝 ((M : ℝ)*c)) ↔
    Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  constructor
  · intro h
    have hh := log_limit_of_replicate M h
    have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
    simpa only [mul_div_cancel_left₀ c hM] using hh
  · exact replicate_log_limit M

end Erdos66BlockReplicationLimit
