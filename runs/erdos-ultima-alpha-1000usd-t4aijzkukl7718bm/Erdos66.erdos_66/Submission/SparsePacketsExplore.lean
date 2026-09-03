import Submission.WindowPerturbationExplore
import Submission.Explore

/-! Sparse interval packets create unbounded normalized peaks while meeting
the quartic counting bound used for stability of window averages. -/
namespace Erdos66SparsePackets
open AdditiveCombinatorics Erdos66Fractional Erdos66Rounding Erdos66Generating
  Erdos66MovingWindowRounding Erdos66MovingWindowLimit Erdos66Counting
  Erdos66WindowPerturbation Erdos66Explore Filter
open scoped Topology Classical
set_option maxHeartbeats 1500000

noncomputable def packet (k : ℕ) : Finset ℕ :=
  Finset.Ico ((k+1)^8) ((k+1)^8+k+1)

def sparsePackets : Set ℕ := {a | ∃ k, a∈packet k}

def packetCenter (k : ℕ) : ℕ := 2*(k+1)^8+k

lemma packet_card (k : ℕ) : (packet k).card=k+1 := by
  simp only [packet,Nat.card_Ico]
  omega

lemma packet_index_le {k a : ℕ} (ha : a∈packet k) : k+1 ≤ a := by
  have hh := (Finset.mem_Ico.mp ha).1
  exact (Nat.le_self_pow (by decide : 8≠0) (k+1)).trans hh

lemma packet_mass_bound (K : ℕ) :
    (∑ k∈Finset.range (K+1), (packet k).card) ≤ (K+1)^2 := by
  simp only [packet_card]
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ]
    nlinarith

/-- This bound holds at every cutoff, not only at packet endpoints. -/
theorem sparsePackets_quartic_count (N : ℕ) : count sparsePackets N ^4 ≤ N := by
  let T := (Finset.range N).filter (fun k ↦ (k+1)^8<N)
  have hactive {a k : ℕ} (ha : a<N) (hk : a∈packet k) : k∈T := by
    have hi := packet_index_le hk
    have hs := (Finset.mem_Ico.mp hk).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩
  by_cases hT : T.Nonempty
  · obtain ⟨K,hK,hmax⟩ := Finset.exists_max_image T (fun k ↦ k) hT
    have hKN : (K+1)^8<N := (Finset.mem_filter.mp hK).2
    have hsub : cutoff sparsePackets N ⊆ (Finset.range (K+1)).biUnion packet := by
      intro a ha
      obtain ⟨haN,k,hk⟩ := mem_cutoff.mp ha
      have hi := hmax k (hactive haN hk)
      exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_range.mpr (by omega),hk⟩
    have hcount : count sparsePackets N ≤ (K+1)^2 :=
      (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (packet_mass_bound K))
    have hh := Nat.pow_le_pow_left hcount 4
    rw [← pow_mul] at hh
    exact hh.trans hKN.le
  · have he : cutoff sparsePackets N=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨haN,k,hk⟩ := mem_cutoff.mp ha
      exact hT ⟨k,hactive haN hk⟩
    simp only [count,he,Finset.card_empty,zero_pow (by decide : 4≠0)]
    exact Nat.zero_le N

lemma packet_reflection (k : ℕ) {a : ℕ} (ha : a∈packet k) :
    a ≤ packetCenter k ∧ packetCenter k-a∈packet k := by
  have hh := Finset.mem_Ico.mp ha
  constructor
  · dsimp [packetCenter]
    omega
  · apply Finset.mem_Ico.mpr
    dsimp only [packetCenter]
    constructor <;> omega

lemma packet_peak {A : Set ℕ} (hA : sparsePackets⊆A) (k : ℕ) :
    k+1 ≤ sumRep A (packetCenter k) := by
  let f : ℕ → ℕ × ℕ := fun a ↦ (a,packetCenter k-a)
  have hf : Function.Injective f := fun a b h ↦ congrArg Prod.fst h
  have hs : (packet k).image f ⊆ (Finset.antidiagonal (packetCenter k)).filter
      (fun p : ℕ×ℕ ↦ p.1∈A ∧ p.2∈A) := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hle,hm⟩ := packet_reflection k ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr (by dsimp [f]; omega),
      hA ⟨k,ha⟩,hA ⟨k,hm⟩⟩
  rw [← packet_card k,← Finset.card_image_of_injective (packet k) hf]
  exact (Finset.card_le_card hs).trans_eq (sumRep_def A (packetCenter k)).symm

lemma packetCenter_bounds (k : ℕ) :
    k+1 ≤ packetCenter k ∧ packetCenter k ≤ 3*(k+1)^8 := by
  have hh := Nat.le_self_pow (by decide : 8≠0) (k+1)
  dsimp only [packetCenter]
  constructor <;> omega

lemma packetCenter_atTop : Tendsto packetCenter atTop atTop := by
  apply tendsto_atTop_mono (fun k ↦ (Nat.le_succ k).trans (packetCenter_bounds k).1) tendsto_id

lemma log_packetCenter_div_index :
    Tendsto (fun k : ℕ ↦ Real.log (packetCenter k)/(k+1)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun k : ℕ ↦ (k : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by linarith) tendsto_natCast_atTop_atTop
  have hlogratio : Tendsto (fun k : ℕ ↦ Real.log ((k : ℝ)+1)/((k : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp hcast
  have hbound := (hcast.const_div_atTop (Real.log 3)).add (hlogratio.const_mul 8)
  simp only [mul_zero,add_zero] at hbound
  apply squeeze_zero' (Eventually.of_forall (fun k ↦ by
    exact div_nonneg (Real.log_natCast_nonneg _) (by positivity))) _ hbound
  filter_upwards [] with k
  have hlog : Real.log (packetCenter k : ℝ) ≤ Real.log 3+8*Real.log ((k : ℝ)+1) := by
    have hpos : (0 : ℝ)<packetCenter k := by
      exact_mod_cast (show 0<packetCenter k by have := (packetCenter_bounds k).1; omega)
    have h := Real.log_le_log hpos
      (show (packetCenter k : ℝ) ≤ 3*((k : ℝ)+1)^8 by exact_mod_cast (packetCenter_bounds k).2)
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hh := div_le_div_of_nonneg_right hlog (by positivity : (0 : ℝ) ≤ k+1)
  simpa only [add_div,mul_div_assoc] using hh

/-- The peaks are genuinely unbounded after logarithmic normalization. -/
theorem packets_peaks_atTop {A : Set ℕ} (hA : sparsePackets⊆A) :
    Tendsto (fun k ↦ (sumRep A (packetCenter k) : ℝ)/Real.log (packetCenter k))
      atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  let B := max b 0
  have hB : 0 ≤ B := le_max_right _ _
  have hBp : 0 < B+1 := by linarith
  have hsmall := log_packetCenter_div_index.eventually_lt_const (one_div_pos.mpr hBp)
  filter_upwards [eventually_ge_atTop 1,hsmall] with k hk hsmall
  have hlog : 0 < Real.log (packetCenter k : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1<packetCenter k by have := (packetCenter_bounds k).1; omega))
  have hidx : (0 : ℝ)<k+1 := by positivity
  have hh := (div_lt_div_iff₀ hidx hBp).mp hsmall
  have hpeak : (k : ℝ)+1 ≤ sumRep A (packetCenter k) := by
    exact_mod_cast packet_peak hA k
  have hb : b ≤ B := le_max_left _ _
  apply (le_div_iff₀ hlog).mpr
  nlinarith [mul_le_mul_of_nonneg_right hb hlog.le]

/-- An arbitrary superset of the sparse packets has no finite pointwise
normalized limit, despite the packets' small counting function. -/
theorem packets_exclude_finite_limit {A : Set ℕ} (hA : sparsePackets⊆A) (c : ℝ) :
    ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro h
  have hh := (h.comp packetCenter_atTop).mul log_packetCenter_div_index
  simp only [mul_zero] at hh
  have hzero : Tendsto (fun k : ℕ ↦ (sumRep A (packetCenter k) : ℝ)/((k : ℝ)+1))
      atTop (𝓝 0) := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hlog : Real.log (packetCenter k : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by
      exact_mod_cast (show 1<packetCenter k by have := (packetCenter_bounds k).1; omega)))
    dsimp only [Function.comp_def]
    field_simp
  have hge : ∀ k : ℕ, (1 : ℝ) ≤ (sumRep A (packetCenter k) : ℝ)/((k : ℝ)+1) := by
    intro k
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<k+1)).mpr
    simpa only [one_mul,Nat.cast_add,Nat.cast_one] using
      (show ((k+1 : ℕ) : ℝ) ≤ sumRep A (packetCenter k) by exact_mod_cast packet_peak hA k)
  have hcontra := ge_of_tendsto hzero (Eventually.of_forall hge)
  norm_num at hcontra

/-- A concrete averaged example that is not a pointwise witness. -/
theorem spiky_averaged_example :
    (∀ w : ℕ → ℕ, (∀ᶠ n in atTop, w n ≤ n ∧ n ≤ (w n)^2) →
      Tendsto (fun n : ℕ ↦ (∑ k∈movingWindow n (w n),
        (sumRep (roundedSet profile∪sparsePackets) k : ℝ))/
          ((w n : ℝ)*Real.log n)) atTop (𝓝 1)) ∧
    ∀ c : ℝ, ¬ Tendsto (fun n ↦ (sumRep (roundedSet profile∪sparsePackets) n : ℝ)/Real.log n)
      atTop (𝓝 c) := by
  constructor
  · intro w hw
    exact rounded_union_window_limit sparsePackets
      (fun N ↦ by exact_mod_cast sparsePackets_quartic_count N) w hw
  · exact packets_exclude_finite_limit Set.subset_union_right

/-- The same set has the full shorter-window averaged property and a
subsequence of normalized representation counts tending to infinity. -/
theorem spiky_averaged_example_of_width :
    (∀ w : ℕ → ℕ, (∀ᶠ n in atTop, 0<w n ∧ w n ≤ n) →
      Tendsto (fun n : ℕ ↦ (n : ℝ)/((w n : ℝ)^2*Real.log n)) atTop (𝓝 0) →
      Tendsto (fun n : ℕ ↦ (∑ k∈movingWindow n (w n),
        (sumRep (roundedSet profile∪sparsePackets) k : ℝ))/
          ((w n : ℝ)*Real.log n)) atTop (𝓝 1)) ∧
    Tendsto (fun k ↦ (sumRep (roundedSet profile∪sparsePackets) (packetCenter k) : ℝ)/
      Real.log (packetCenter k)) atTop atTop := by
  constructor
  · intro w hw hscale
    exact rounded_union_window_limit_of_width sparsePackets
      (fun N ↦ by exact_mod_cast sparsePackets_quartic_count N) w hw hscale
  · exact packets_peaks_atTop Set.subset_union_right

end Erdos66SparsePackets
