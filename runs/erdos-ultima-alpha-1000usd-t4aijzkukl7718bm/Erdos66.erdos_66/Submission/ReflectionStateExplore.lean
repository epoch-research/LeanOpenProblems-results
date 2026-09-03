import Submission.LargeReflectionPatchExplore
import Submission.CompactnessExplore
import Submission.Explore

/-! A reflection-peak extension preserving a frozen prefix and exact base
tail counts. The bound 11 does not grow under repeated extensions. -/
namespace Erdos66ReflectionState
open Filter AdditiveCombinatorics Erdos66Fractional Erdos66Generating Erdos66Rounding
  Erdos66Counting Erdos66ReflectionRoundingPatch Erdos66SetIntervalReplacement
  Erdos66LargeReflectionPatch Erdos66Compactness
open scoped Topology Classical
set_option maxHeartbeats 1500000

structure State where
  A : Set ℕ
  T : ℕ
  discrepancy : ∀ N, |(count A N : ℝ)-cumulative profile N| ≤ 11
  tail_mem : ∀ i, T ≤ i → (i ∈ A ↔ i ∈ base)
  tail_count : ∀ N, T ≤ N → count A N = count base N

noncomputable def initial : State := ⟨base,0,fun N ↦
  (base_count_discrepancy N).trans (by norm_num),fun _ _ ↦ Iff.rfl,fun _ _ ↦ rfl⟩

def Extension (s : State) (M : ℕ) (q : State × ℕ) : Prop :=
  s.T < q.1.T ∧ s.T ≤ q.2 ∧ q.2 < q.1.T ∧
    (∀ i, i < s.T → (i ∈ q.1.A ↔ i ∈ s.A)) ∧
    (M : ℝ) ≤ (sumRep q.1.A q.2 : ℝ)/Real.log q.2

theorem exists_extension (s : State) (M : ℕ) : ∃ q, Extension s M q := by
  obtain ⟨L,W,G,hL,hW,hG,hGc,hGp,ht2,hpeak⟩ := exists_large_patch (s.T+2) M
  let t := 2*L+2*W-1
  let A' := replace s.A (L+W) (L+2*W) G
  have hright : intervalPart s.A (L+W) (L+2*W) = intervalPart base (L+W) (L+2*W) := by
    apply intervalPart_congr
    intro i hi
    exact s.tail_mem i (by have hh := hi.1; omega)
  have hleft : intervalPart s.A L (L+W) = intervalPart base L (L+W) := by
    apply intervalPart_congr
    intro i hi
    exact s.tail_mem i (by have hh := hi.1; omega)
  have hGc' : G.card = (intervalPart s.A (L+W) (L+2*W)).card := by rwa [hright]
  have hdisc : ∀ N, |(count A' N : ℝ)-cumulative profile N| ≤ 11 := by
    intro N
    by_cases hN : N ≤ L+W
    · rw [replacement_count_before s.A (L+W) (L+2*W) G hG N hN]
      exact s.discrepancy N
    · have hc := replacement_count_difference s.A (L+W) (L+2*W) G hG N
      rw [hright] at hc
      have hclose : |(count A' N : ℝ)-count s.A N| ≤ 10 := by rw [hc]; exact hGp N
      have hbase := s.tail_count N (by omega)
      rw [hbase] at hclose
      calc
        _ = |((count A' N : ℝ)-count base N)+((count base N : ℝ)-cumulative profile N)| := by ring_nf
        _ ≤ |(count A' N : ℝ)-count base N|+|(count base N : ℝ)-cumulative profile N| := abs_add_le _ _
        _ ≤ 11 := by linarith [base_count_discrepancy N]
  have htend : L+2*W ≤ t+1 := by dsimp [t]; omega
  have hTt : s.T ≤ t := by dsimp [t]; omega
  let s' : State := {
    A := A'
    T := t+1
    discrepancy := hdisc
    tail_mem := by
      intro i hi
      have hi' : t+1 ≤ i := hi
      exact (mem_replace_outside s.A (L+W) (L+2*W) G hG i
        (by simp only [Set.mem_Ico]; omega)).trans (s.tail_mem i (by omega))
    tail_count := by
      intro N hN
      have hN' : t+1 ≤ N := hN
      exact (replacement_count_after s.A (L+W) (L+2*W) G hG hGc' N (by omega)).trans
        (s.tail_count N (by omega)) }
  refine ⟨(s',t),?_,hTt,by dsimp [s']; omega,?_,?_⟩
  · change s.T < t+1
    omega
  · intro i hi
    exact mem_replace_outside s.A (L+W) (L+2*W) G hG i
      (by simp only [Set.mem_Ico]; omega)
  · have hsub := intervalPart_sub_replace s.A L W G
    rw [hleft] at hsub
    have hh := Erdos66Explore.sumRep_mono hsub t
    have hlog : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ t by omega))
    exact hpeak.trans (div_le_div_of_nonneg_right (by exact_mod_cast hh) hlog)

noncomputable def step (s : State) (M : ℕ) : State × ℕ :=
  Classical.choose (exists_extension s M)

lemma step_spec (s : State) (M : ℕ) : Extension s M (step s M) :=
  Classical.choose_spec (exists_extension s M)

end Erdos66ReflectionState
