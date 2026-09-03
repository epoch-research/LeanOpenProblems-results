import Submission.Compactness

/-!
A density-sensitive completion criterion for the ordinary increasing greedy
cube-Sidon construction. The uniform arithmetic boundary estimate is an
assumption, not proved here.
-/
namespace Erdos1206.EntropyBoundaryCriterion
open Finset
open scoped Classical

noncomputable def greedy : ℕ → Finset ℕ
  | 0 => ∅
  | n+1 => if IsSidon ((fun a : ℕ => a^3) '' ((insert n (greedy n) : Finset ℕ) : Set ℕ))
      then insert n (greedy n) else greedy n

lemma greedy_sidon (n : ℕ) :
    IsSidon ((fun a : ℕ => a^3) '' (greedy n : Set ℕ)) := by
  induction n with
  | zero => simp [greedy, IsSidon]
  | succ n ih =>
    rw [greedy]
    split_ifs with h
    · exact h
    · exact ih

lemma greedy_subset_range (n : ℕ) : greedy n ⊆ range n := by
  induction n with
  | zero => simp [greedy]
  | succ n ih =>
    rw [greedy]
    split_ifs <;> intro x hx
    · rcases mem_insert.mp hx with rfl | hx
      · simp
      · exact mem_range.mpr (lt_trans (mem_range.mp (ih hx)) (Nat.lt_succ_self _))
    · exact mem_range.mpr (lt_trans (mem_range.mp (ih hx)) (Nat.lt_succ_self _))

lemma greedy_mono_step (n : ℕ) : greedy n ⊆ greedy (n+1) := by
  rw [greedy]
  split_ifs
  · exact subset_insert _ _
  · exact subset_rfl

lemma greedy_mono {m n : ℕ} (h : m ≤ n) : greedy m ⊆ greedy n := by
  induction n, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ n h ih => exact ih.trans (greedy_mono_step n)

lemma cube_sidon_mono {S T : Finset ℕ}
    (hT : IsSidon ((fun a : ℕ => a^3) '' (T : Set ℕ))) (hST : S ⊆ T) :
    IsSidon ((fun a : ℕ => a^3) '' (S : Set ℕ)) := by
  apply Set.IsSidon.subset hT
  exact Set.image_mono (by exact hST)

/-- Roots in the prefix which cannot be adjoined to `S`. -/
noncomputable def boundary (S : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (range N).filter (fun n =>
    ¬ IsSidon ((fun a : ℕ => a^3) '' ((insert n S : Finset ℕ) : Set ℕ)))

lemma greedy_rejected {n N : ℕ} (hn : n < N) (hnot : n ∉ greedy N) :
    n ∈ boundary (greedy N) N := by
  refine mem_filter.mpr ⟨mem_range.mpr hn, ?_⟩
  intro hs
  have hsmall : IsSidon ((fun a : ℕ => a^3) '' ((insert n (greedy n) : Finset ℕ) : Set ℕ)) :=
    cube_sidon_mono hs (insert_subset_insert n (greedy_mono hn.le))
  have hin : n ∈ greedy (n+1) := by rw [greedy, if_pos hsmall]; simp
  exact hnot (greedy_mono hn hin)

lemma boundary_disjoint {S : Finset ℕ} (N : ℕ)
    (hs : IsSidon ((fun a : ℕ => a^3) '' (S : Set ℕ))) :
    Disjoint S (boundary S N) := by
  apply disjoint_left.mpr
  intro n hn hb
  have hh := (mem_filter.mp hb).2
  rw [insert_eq_of_mem hn] at hh
  exact hh hs

lemma greedy_partition (N : ℕ) :
    (greedy N).card + (boundary (greedy N) N).card = N := by
  have he : greedy N ∪ boundary (greedy N) N = range N := by
    ext n
    constructor
    · intro hn
      rcases mem_union.mp hn with hn | hn
      · exact greedy_subset_range N hn
      · exact (mem_filter.mp hn).1
    · intro hn
      by_cases hh : n ∈ greedy N
      · exact mem_union_left _ hh
      · exact mem_union_right _ (greedy_rejected (mem_range.mp hn) hh)
  have hh := card_union_of_disjoint (boundary_disjoint N (greedy_sidon N))
  rw [he, card_range] at hh
  exact hh.symm

lemma greedy_prefix {n N : ℕ} (hn : n ≤ N) :
    (greedy N).filter (fun a => a < n) = greedy n := by
  induction N, hn using Nat.le_induction with
  | base =>
    apply filter_eq_self.mpr
    intro a ha
    exact mem_range.mp (greedy_subset_range _ ha)
  | succ N hN ih =>
    rw [greedy]
    split_ifs
    · rw [filter_insert]
      simp only [show ¬N < n by omega, if_false]
      exact ih
    · exact ih

/-- A uniform small-set completion estimate suffices. The boundary bound
must hold for all prefixes and all finite cube-Sidon sets in the prefix. -/
theorem small_set_boundary_suffices {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, ∀ S : Finset ℕ, S ⊆ range N →
      IsSidon ((fun a : ℕ => a^3) '' (S : Set ℕ)) →
      (S.card : ℝ) ≤ δ*N →
      (boundary S N).card ≤ (1-2*δ)*N+C) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a^3) '' A) := by
  have hpre (n : ℕ) : δ*n ≤ ((greedy n).card : ℝ)+C := by
    by_cases hsmall : ((greedy n).card : ℝ) ≤ δ*n
    · have hb := hbound n (greedy n) (greedy_subset_range n) (greedy_sidon n) hsmall
      have he : ((greedy n).card : ℝ)+(boundary (greedy n) n).card = n := by
        exact_mod_cast greedy_partition n
      have hc : (0 : ℝ) ≤ (greedy n).card := by positivity
      nlinarith
    · linarith
  apply existence_of_finite_prefix_construction hδ (C := C)
  intro N
  refine ⟨greedy N, greedy_sidon N, ?_⟩
  intro n hn
  rw [greedy_prefix hn]
  exact hpre n

/-- More generally, any uniform completion modulus that tends to zero
with the selected proportion gives a positive-density greedy construction. -/
theorem continuous_boundary_modulus_suffices (F : ℝ → ℝ) {C : ℝ}
    (hC : 0 ≤ C)
    (hlim : Filter.Tendsto F (nhds 0) (nhds 0))
    (hbound : ∀ N : ℕ, ∀ S : Finset ℕ, S ⊆ range N →
      IsSidon ((fun a : ℕ => a^3) '' (S : Set ℕ)) →
      (boundary S N).card ≤ (N : ℝ)*F (S.card/N)+C) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a^3) '' A) := by
  have hev : ∀ᶠ x : ℝ in nhds 0, F x < 1/2 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hev
  let δ : ℝ := min (ε/2) (1/4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε/2 := min_le_left _ _
  have hδ4 : δ ≤ 1/4 := min_le_right _ _
  apply small_set_boundary_suffices hδ hC
  intro N S hSN hs hsmall
  have hb := hbound N S hSN hs
  by_cases hN : N=0
  · subst N
    simpa only [Nat.cast_zero, zero_mul, mul_zero, zero_add] using hb
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hx0 : (0:ℝ) ≤ S.card/N := div_nonneg (Nat.cast_nonneg _) hNpos.le
  have hxδ : (S.card:ℝ)/N ≤ δ := (div_le_iff₀ hNpos).mpr hsmall
  have hdist : dist ((S.card:ℝ)/N) 0 < ε := by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hx0]
    linarith
  have hf : F ((S.card:ℝ)/N) < 1/2 := hball hdist
  nlinarith

/-- In particular, the density-sensitive logarithmic boundary estimate
would settle the conjecture. Unlike `O(|S| log N)`, this uses `log(N/|S|)`.
No such arithmetic estimate is asserted without the explicit hypothesis. -/
theorem logarithmic_boundary_suffices (K : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, ∀ S : Finset ℕ, S ⊆ range N →
      IsSidon ((fun a : ℕ => a^3) '' (S : Set ℕ)) →
      (boundary S N).card ≤ K*S.card*(1+Real.log ((N:ℝ)/S.card))+C) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a^3) '' A) := by
  let F : ℝ → ℝ := fun x => K*(x-x*Real.log x)
  have hcont : Continuous F :=
    continuous_const.mul (continuous_id.sub Real.continuous_mul_log)
  have hlim : Filter.Tendsto F (nhds 0) (nhds 0) := by
    simpa [F] using (hcont.tendsto 0)
  apply continuous_boundary_modulus_suffices F hC hlim
  intro N S hSN hs
  have hb := hbound N S hSN hs
  by_cases hN : N=0
  · have hS : S=∅ := subset_empty.mp (by simpa [hN] using hSN)
    simpa [hN,hS,F] using hb
  by_cases hS : S.card=0
  · simpa [hS,F] using hb
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN
  have hm : (S.card:ℝ) ≠ 0 := by exact_mod_cast hS
  have he : (N:ℝ)*F (S.card/N) = K*S.card*(1+Real.log ((N:ℝ)/S.card)) := by
    dsimp only [F]
    rw [Real.log_div hm hn, Real.log_div hn hm]
    field_simp
    ring
  rw [he]
  exact hb

#print axioms logarithmic_boundary_suffices
#print axioms small_set_boundary_suffices
#print axioms continuous_boundary_modulus_suffices
end Erdos1206.EntropyBoundaryCriterion
