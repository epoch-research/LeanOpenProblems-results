import Submission.TauberianProfileExplore

/-! Counting constraints on copying a prefix into an adjacent block.
These exclude iterated full-prefix repetition at arbitrary scales, not
arbitrary constructions for the original conjecture. -/
namespace Erdos66PrefixCopy
open Erdos66Counting Erdos66TauberianProfile Erdos66Explore
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma count_pos_eventually {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ N in atTop, 0 < count A N := by
  obtain ⟨a,ha⟩ := (witness_infinite hc ht).nonempty
  filter_upwards [eventually_ge_atTop (a+1)] with N hN
  exact Finset.card_pos.mpr ⟨a,mem_cutoff.mpr ⟨by omega,ha⟩⟩

lemma log_multiple_ratio (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N : ℕ ↦ Real.log (m*N : ℕ)/Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := (hlog.const_div_atTop (Real.log m)).add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn0 : (N:ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
  have hln : Real.log (N:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1<N by omega)))
  rw [Nat.cast_mul,Real.log_mul hm0 hn0,add_div,div_self hln]

/-- Regular variation of the counting function at every fixed integer
multiple of the cutoff. -/
theorem count_multiple_ratio {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N ↦ (count A (m*N) : ℝ)/count A N) atTop (𝓝 (Real.sqrt m)) := by
  have hp := witness_counting_square_profile hc ht
  have hmTop : Tendsto (fun N : ℕ ↦ m*N) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ by change N ≤ m*N; nlinarith) tendsto_id
  have hcpos := limit_pos hc ht
  have hq : 4*c/Real.pi ≠ 0 := ne_of_gt (by positivity)
  have hrat := (hp.comp hmTop).div hp hq
  rw [div_self hq] at hrat
  have hprod := (hrat.mul (log_multiple_ratio m hm)).mul_const (m:ℝ)
  simp only [one_mul] at hprod
  have hs : Tendsto (fun N ↦ ((count A (m*N) : ℝ)/count A N)^2) atTop (𝓝 (m:ℝ)) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 2, count_pos_eventually hc ht] with N hN hC
    have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have hn0 : (N:ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
    have hmn : 1 < m*N := by nlinarith
    have hln : Real.log (N:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1<N by omega)))
    have hlmn : Real.log ((m:ℝ)*N) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hmn))
    have hcount : (count A N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
    simp only [Pi.div_apply, Function.comp_def, Nat.cast_mul]
    field_simp
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply hh.congr
  intro N
  exact Real.sqrt_sq (by positivity)

noncomputable def copiedPrefix (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (cutoff A N).filter (fun a ↦ a+N ∈ A)

lemma copiedPrefix_bound (A : Set ℕ) (N : ℕ) :
    count A N + (copiedPrefix A N).card ≤ count A (2*N) := by
  let S := (copiedPrefix A N).image (fun a ↦ a+N)
  have hcard : S.card=(copiedPrefix A N).card :=
    Finset.card_image_of_injective _ (fun a b h ↦ Nat.add_right_cancel h)
  have hdis : Disjoint (cutoff A N) S := by
    apply Finset.disjoint_left.mpr
    intro x hx hs
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hs
    have hx' := (mem_cutoff.mp hx).1
    omega
  have hsub : cutoff A N ∪ S ⊆ cutoff A (2*N) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨hx,ha⟩ := mem_cutoff.mp hx
      exact mem_cutoff.mpr ⟨by omega,ha⟩
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨ha,hmem⟩ := Finset.mem_filter.mp ha
      exact mem_cutoff.mpr ⟨by have hh := (mem_cutoff.mp ha).1; omega,hmem⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,hcard] at hh
  exact hh

/-- Only a proportion at most sqrt(2)-1 of the old prefix may be copied
into the next block, up to an arbitrarily small eventual error. -/
theorem eventual_copy_fraction_bound {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      ((copiedPrefix A N).card : ℝ)/count A N < Real.sqrt 2-1+ε := by
  have hlim := count_multiple_ratio hc ht 2 (by decide)
  have hu := hlim.eventually_lt_const (show Real.sqrt 2 < Real.sqrt 2+ε by linarith)
  filter_upwards [hu,count_pos_eventually hc ht] with N hN hpos
  have hp : (0:ℝ) < count A N := by exact_mod_cast hpos
  have hc' : (count A N:ℝ)+(copiedPrefix A N).card ≤ count A (2*N) :=
    by exact_mod_cast copiedPrefix_bound A N
  have hh := (div_lt_iff₀ hp).mp hN
  apply (div_lt_iff₀ hp).mpr
  nlinarith

/-- Arbitrary scales are allowed: full-prefix repetition is eventually
impossible for any hypothetical witness. -/
theorem eventually_no_full_prefix_copy {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ N in atTop, ¬ (∀ a < N, a∈A → a+N∈A) := by
  have hroot : Real.sqrt 2 < 2 := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hb := eventual_copy_fraction_bound hc ht (2-Real.sqrt 2) (by linarith)
  filter_upwards [hb,count_pos_eventually hc ht] with N hN hpos
  intro hcopy
  have he : copiedPrefix A N=cutoff A N := by
    apply Finset.filter_true_of_mem
    intro a ha
    exact hcopy a (mem_cutoff.mp ha).1 (mem_cutoff.mp ha).2
  rw [he] at hN
  change (count A N : ℝ)/count A N < _ at hN
  rw [div_self (by exact_mod_cast (Nat.ne_of_gt hpos))] at hN
  linarith

/-- Infinitely late full-prefix copies exclude the conjectured limit. -/
theorem no_log_limit_of_frequent_prefix_copies (A : Set ℕ)
    (hcopy : ∀ K : ℕ, ∃ N ≥ K, ∀ a < N, a∈A → a+N∈A)
    (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro ht
  obtain ⟨K,hK⟩ := eventually_atTop.mp (eventually_no_full_prefix_copy hc ht)
  obtain ⟨N,hN,hcopyN⟩ := hcopy K
  exact hK N hN hcopyN

end Erdos66PrefixCopy
