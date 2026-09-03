import Submission.DigitBlockingExplore

/-! A fixed-width nondeterministic digit program may depend on the entire
word length and on the digit position. Even this nonuniform recognition
cannot supply positive relative counting mass in a hypothetical witness.
No bounded-width hypothesis is asserted for arbitrary subsets of N. -/
namespace Erdos66NonuniformDigitCore
open Filter AdditiveCombinatorics Erdos66Counting Erdos66AutomaticCore
  Erdos66LayeredDigitAsymptotic Erdos66LayeredDigitProgram Erdos66LayeredPath
  Erdos66DigitBlocking Erdos66DfaCounting
open scoped Topology Classical
set_option maxHeartbeats 2600000
variable {b : ℕ} {σ : Type*} [Fintype σ]

/-- There is no compatibility requirement between the programs for
different word lengths. Zero-padded words are recognized. -/
def Recognizes (hb : 1 < b) (E : ℕ → ℕ → σ → Fin b → σ → Prop)
    (initial : ℕ → σ) (accepting : ℕ → Set σ) (B : Set ℕ) : Prop :=
  ∀ k n, n<b^k → (n∈B ↔ ∃ z∈accepting k,
    Erdos66LayeredPath.Path (E k) 0 (finWord hb k n) (initial k) z)

lemma grouped_recognition (hb : 1 < b) (E : ℕ → ℕ → σ → Fin b → σ → Prop)
    (initial : ℕ → σ) (T : ℕ → Set σ) (B : Set ℕ)
    (hrec : Recognizes hb E initial T B) {d : ℕ} (hbd : 1 < b^d) (k : ℕ) :
    accepted (fromEdge (blockEdge hb d (E (d*k))) k (initial (d*k)) (T (d*k)))=
      cutoff B ((b^d)^k) := by
  ext n
  constructor
  · intro hn
    have hnlt := accepted_lt hbd _ hn
    refine mem_cutoff.mpr ⟨hnlt,?_⟩
    apply (hrec (d*k) n (by simpa only [pow_mul] using hnlt)).mpr
    exact (mem_block_program hb hbd (E (d*k)) k n (initial (d*k)) (T (d*k)) hnlt).mp hn
  · intro hn
    obtain ⟨hnlt,hnB⟩ := mem_cutoff.mp hn
    apply (mem_block_program hb hbd (E (d*k)) k n (initial (d*k)) (T (d*k)) hnlt).mpr
    exact (hrec (d*k) n (by simpa only [pow_mul] using hnlt)).mp hnB

/-- Fixed width forces square-root-negligible counting mass under a
logarithmic representation cap, without stationarity or determinism. -/
theorem nonuniform_subset_sq_negligible (hb : 1 < b)
    (E : ℕ → ℕ → σ → Fin b → σ → Prop) (initial : ℕ → σ) (T : ℕ → Set σ)
    (A B : Set ℕ) (hBA : B⊆A) (hrec : Recognizes hb E initial T B)
    {K C : ℝ} (hK : 0≤K) (hC : 0≤C)
    (hu : ∀ n, (sumRep A n:ℝ)≤K+C*Real.log ((n:ℝ)+2)) :
    Tendsto (fun N : ℕ ↦ (count B N:ℝ)^2/N) atTop (𝓝 0) := by
  obtain ⟨d,hd⟩ := pow_unbounded_of_one_lt (max ((Fintype.card σ)^2) 1) hb
  have hbd : 1 < b^d := (le_max_right _ _).trans_lt hd
  have hwidth : (Fintype.card σ)^2<b^d := (le_max_left _ _).trans_lt hd
  exact recognized_subset_sq_negligible hbd hwidth
    (fun k ↦ fromEdge (blockEdge hb d (E (d*k))) k (initial (d*k)) (T (d*k)))
    A B hBA (grouped_recognition hb E initial T B hrec hbd) hK hC hu

/-- A nonuniform bounded-width digit core supplies none of the asymptotic
counting mass of a hypothetical logarithmic-representation witness. -/
theorem nonuniform_subset_negligible (hb : 1 < b)
    (E : ℕ → ℕ → σ → Fin b → σ → Prop) (initial : ℕ → σ) (T : ℕ → Set σ)
    (A B : Set ℕ) (hBA : B⊆A) (hrec : Recognizes hb E initial T B)
    (c : ℝ) (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N ↦ (count B N:ℝ)/count A N) atTop (𝓝 0) := by
  obtain ⟨K,C,hK,hC,hu⟩ := global_log_upper_bound ht
  have hB := nonuniform_subset_sq_negligible hb E initial T A B hBA hrec hK hC.le hu
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((Erdos66Explore.sumRep_tendsto_atTop hc ht).eventually_ge_atTop 1)
  exact negligible_relative_to_basis A B hB M hM

/-- A complete witness cannot have such a nonuniform bounded-width digit
description. This is a restricted-class theorem, not the conjecture's negation. -/
theorem no_nonzero_log_limit (hb : 1 < b)
    (E : ℕ → ℕ → σ → Fin b → σ → Prop) (initial : ℕ → σ) (T : ℕ → Set σ)
    (A : Set ℕ) (hrec : Recognizes hb E initial T A) (c : ℝ) (hc : c≠0) :
    ¬ Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c) := by
  intro ht
  have hzero := nonuniform_subset_negligible hb E initial T A A Set.Subset.rfl hrec c hc ht
  have hone : Tendsto (fun N ↦ (count A N:ℝ)/count A N) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [count_positive_eventually hc ht] with N hN
    exact (div_self (by exact_mod_cast (Nat.ne_of_gt hN))).symm
  have he := tendsto_nhds_unique hzero hone
  norm_num at he

end Erdos66NonuniformDigitCore
