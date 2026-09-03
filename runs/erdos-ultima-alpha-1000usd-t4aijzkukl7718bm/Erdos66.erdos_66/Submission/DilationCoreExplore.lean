import Submission.PrefixCopyExplore
import Submission.ResidueCountingExplore

/-! Any fixed-dilation-invariant core has negligible counting mass inside
a hypothetical witness. This includes infinite-memory multiplicative cores;
it is not a disproof for arbitrary sets. -/
namespace Erdos66DilationCore
open Erdos66Counting Erdos66PrefixCopy Erdos66ResidueCounting
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 1500000

lemma image_residue_count_bound (A B : Set ℕ) (m N : ℕ) (hm : 0 < m)
    (himage : ∀ a ∈ B, m*a ∈ A) :
    count B N ≤ count (residueSet m A 0) (m*N) := by
  apply Finset.card_le_card_of_injOn (fun a ↦ m*a)
  · intro a ha
    obtain ⟨ha,hB⟩ := mem_cutoff.mp ha
    apply mem_cutoff.mpr
    refine ⟨Nat.mul_lt_mul_of_pos_left ha hm, himage a hB, ?_⟩
    simp
  · intro a ha b hb he
    exact Nat.eq_of_mul_eq_mul_left hm he

lemma multiple_residue_ratio {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun N ↦ (count (residueSet m A 0) (m*N) : ℝ)/count A N)
      atTop (𝓝 (Real.sqrt m/m)) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hmTop : Tendsto (fun N : ℕ ↦ m*N) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ by change N ≤ m*N; nlinarith) tendsto_id
  have hh := ((witness_ordinary_residue_equidistribution m hc ht 0).comp hmTop).mul
    (count_multiple_ratio hc ht m hm)
  have he : (1/(m:ℝ))*Real.sqrt m=Real.sqrt m/m := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [hmTop.eventually (count_pos_eventually hc ht)] with N hN
  have hpos : (count A (m*N) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  dsimp only [Function.comp_def]
  field_simp

/-- The fraction of an old set whose dilation can lie inside a witness
is at most 1/sqrt(m), in the eventual-envelope sense. -/
theorem eventual_dilation_fraction_bound {A B : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (m : ℕ) (hm : 0 < m) (himage : ∀ a ∈ B, m*a ∈ A)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, (count B N : ℝ)/count A N < Real.sqrt m/m+ε := by
  have hu := (multiple_residue_ratio hc ht m hm).eventually_lt_const
    (show Real.sqrt m/m < Real.sqrt m/m+ε by linarith)
  filter_upwards [hu] with N hN
  exact (div_le_div_of_nonneg_right
    (by exact_mod_cast image_residue_count_bound A B m N hm himage)
    (Nat.cast_nonneg _)).trans_lt hN

lemma dilation_iterate (B : Set ℕ) (m : ℕ) (hB : ∀ a ∈ B, m*a ∈ B)
    (k a : ℕ) (ha : a ∈ B) : m^k*a ∈ B := by
  induction k with
  | zero => simpa using ha
  | succ k ih => simpa only [pow_succ', mul_assoc] using hB (m^k*a) ih

/-- Iterated dilations force an invariant core to have zero relative mass
inside any hypothetical witness. No automaticity assumption is made. -/
theorem dilation_core_negligible {A B : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (m : ℕ) (hm : 1 < m) (hBA : B ⊆ A) (hB : ∀ a ∈ B, m*a ∈ B) :
    Tendsto (fun N ↦ (count B N : ℝ)/count A N) atTop (𝓝 0) := by
  have hmR : (1:ℝ) < m := by exact_mod_cast hm
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0:ℝ) ≤ 1/m by positivity)
    (show (1:ℝ)/m < 1 by rw [div_lt_one (by positivity)]; exact hmR)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun N ↦ ha.trans_le (by positivity))
  · intro ε hε
    obtain ⟨k,hk⟩ := (hpow.eventually_lt_const hε).exists
    have he : Real.sqrt (m^(2*k):ℕ)/(m^(2*k):ℕ) = (1/(m:ℝ))^k := by
      rw [Nat.cast_pow, show 2*k=k*2 by omega, pow_mul,Real.sqrt_sq (by positivity)]
      rw [one_div_pow]
      field_simp
    have hlim := multiple_residue_ratio hc ht (m^(2*k)) (pow_pos (by omega) _)
    rw [he] at hlim
    have hu := hlim.eventually_lt_const hk
    filter_upwards [hu] with N hN
    have hcount := image_residue_count_bound A B (m^(2*k)) N (pow_pos (by omega) _)
      (fun a ha ↦ hBA (dilation_iterate B m hB (2*k) a ha))
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hcount)
      (Nat.cast_nonneg _)).trans_lt hN

/-- Adding a negligible correction to a dilation-invariant core cannot
supply a witness: the added set must carry asymptotically all its mass. -/
theorem dilation_union_repair_full (B D : Set ℕ) (m : ℕ) (hm : 1 < m)
    (hB : ∀ a ∈ B, m*a ∈ B) (c : ℝ) (hc : c ≠ 0)
    (ht : Tendsto (fun n ↦ (sumRep (B ∪ D) n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count D N : ℝ)/count (B ∪ D) N) atTop (𝓝 1) := by
  have hcore := dilation_core_negligible hc ht m hm Set.subset_union_left hB
  have hlo := hcore.const_sub 1
  simp only [sub_zero] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [count_pos_eventually hc ht] with N hN
    have hpos : (0:ℝ) < count (B ∪ D) N := by exact_mod_cast hN
    have he : cutoff (B ∪ D) N=cutoff B N ∪ cutoff D N := by
      ext a
      simp only [mem_cutoff,Finset.mem_union,Set.mem_union]
      tauto
    have hh : count (B ∪ D) N ≤ count B N+count D N := by
      unfold count
      rw [he]
      exact Finset.card_union_le _ _
    have hr : (count (B ∪ D) N:ℝ) ≤ count B N+count D N := by exact_mod_cast hh
    have hb := div_le_div_of_nonneg_right hr hpos.le
    rw [div_self hpos.ne',add_div] at hb
    linarith
  · filter_upwards [count_pos_eventually hc ht] with N hN
    apply (div_le_iff₀ (by exact_mod_cast hN : (0:ℝ)<count (B ∪ D) N)).mpr
    rw [one_mul]
    exact_mod_cast (show count D N ≤ count (B ∪ D) N from
      Finset.card_le_card (fun a ha ↦ mem_cutoff.mpr
        ⟨(mem_cutoff.mp ha).1,Or.inr (mem_cutoff.mp ha).2⟩))

/-- No repair of zero relative counting mass can fix such a core. -/
theorem no_negligible_dilation_repair (B D : Set ℕ) (m : ℕ) (hm : 1 < m)
    (hB : ∀ a ∈ B, m*a ∈ B)
    (hD : Tendsto (fun N ↦ (count D N : ℝ)/count (B ∪ D) N) atTop (𝓝 0))
    (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n ↦ (sumRep (B ∪ D) n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro ht
  have := tendsto_nhds_unique hD (dilation_union_repair_full B D m hm hB c hc ht)
  norm_num at this

/-- In particular a whole set closed under a dilation greater than one
cannot have the logarithmic limit in the conjecture. -/
theorem no_nonzero_log_limit_of_dilation_closed (A : Set ℕ) (m : ℕ) (hm : 1 < m)
    (hA : ∀ a ∈ A, m*a ∈ A) (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro ht
  have hz := dilation_core_negligible hc ht m hm (fun _ ha ↦ ha) hA
  have ho : Tendsto (fun N ↦ (count A N : ℝ)/count A N) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [count_pos_eventually hc ht] with N hN
    exact (div_self (by exact_mod_cast (Nat.ne_of_gt hN))).symm
  have := tendsto_nhds_unique hz ho
  norm_num at this

/-- Square-multiple closure, even with an arbitrary set of allowed kernels,
is an instance of the obstruction. -/
theorem no_nonzero_log_limit_of_square_closed (A : Set ℕ)
    (hA : ∀ a ∈ A, ∀ k : ℕ, k^2*a ∈ A) (c : ℝ) (hc : c ≠ 0) :
    ¬ Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c) := by
  apply no_nonzero_log_limit_of_dilation_closed A 4 (by decide) _ c hc
  intro a ha
  simpa using hA a ha 2

end Erdos66DilationCore
