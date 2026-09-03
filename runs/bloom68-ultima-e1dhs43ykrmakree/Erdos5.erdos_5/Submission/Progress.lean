import FormalConjecturesUtil

/-!
# Verified reductions for the normalized consecutive-prime-gap problem

These lemmas do not assume either theorem in `Spec.lean`. They isolate the
arithmetic assertion that remains to be proved, without claiming that assertion.
-/


open Filter Real Set
open scoped Topology

namespace PrimeGapProgress

/-- The target property, stated for an arbitrary real sequence. -/
def FullNonnegativeCluster (u : ℕ → ℝ) : Prop :=
  ∀ C : ℝ, 0 ≤ C →
    ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => u (n i)) atTop (𝓝 C)

/-- The exact arithmetic density condition required for the target. -/
def PositiveIntervalHits (u : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧ a < u n ∧ u n < b

theorem subsequence_iff_cluster (u : ℕ → ℝ) (C : ℝ) :
    (∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => u (n i)) atTop (𝓝 C)) ↔
      MapClusterPt C atTop u := by
  constructor
  · rintro ⟨n, hn, ht⟩
    exact ht.mapClusterPt.of_comp hn.tendsto_atTop
  · exact TopologicalSpace.FirstCountableTopology.tendsto_subseq

theorem cluster_iff_tail_approximation (u : ℕ → ℝ) (C : ℝ) :
    MapClusterPt C atTop u ↔
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ |u n - C| < ε := by
  rw [Metric.nhds_basis_ball.mapClusterPt_iff_frequently]
  simp only [Metric.mem_ball, Real.dist_eq, frequently_atTop]

theorem full_iff_interval_hits (u : ℕ → ℝ) :
    FullNonnegativeCluster u ↔ PositiveIntervalHits u := by
  constructor
  · intro h a b ha hab N
    have hc := (subsequence_iff_cluster u ((a + b) / 2)).mp
      (h ((a + b) / 2) (by linarith))
    obtain ⟨n, hn, hdist⟩ := (cluster_iff_tail_approximation u ((a + b) / 2)).mp hc
      ((b - a) / 2) (by linarith) N
    rw [abs_lt] at hdist
    exact ⟨n, hn, by linarith [hdist.1], by linarith [hdist.2]⟩
  · intro h C hC
    apply (subsequence_iff_cluster u C).mpr
    apply (cluster_iff_tail_approximation u C).mpr
    intro ε hε N
    obtain ⟨n, hn, hlo, hhi⟩ := h (max (C - ε / 2) (ε / 4))
      (C + ε / 2) (lt_of_lt_of_le (by linarith) (le_max_right _ _))
      (max_lt (by linarith) (by linarith)) N
    refine ⟨n, hn, abs_lt.mpr ⟨?_, ?_⟩⟩
    · have : C - ε / 2 < u n := lt_of_le_of_lt (le_max_left _ _) hlo
      linarith
    · linarith

theorem not_full_iff_forbidden_interval (u : ℕ → ℝ) :
    ¬ FullNonnegativeCluster u ↔
      ∃ a b : ℝ, 0 < a ∧ a < b ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → u n ≤ a ∨ b ≤ u n := by
  rw [full_iff_interval_hits]
  simp only [PositiveIntervalHits, not_forall, not_exists, not_and, not_lt]
  constructor
  · rintro ⟨a, b, ha, hab, N, hN⟩
    refine ⟨a, b, ha, hab, N, ?_⟩
    intro n hn
    by_cases h : u n ≤ a
    · exact Or.inl h
    · exact Or.inr (hN n hn (lt_of_not_ge h))
  · rintro ⟨a, b, ha, hab, N, hN⟩
    refine ⟨a, b, ha, hab, N, ?_⟩
    intro n hn hlo
    rcases hN n hn with h | h
    · exact False.elim ((not_lt_of_ge h) hlo)
    · exact h

theorem interval_hits_iff_rational (u : ℕ → ℝ) :
    PositiveIntervalHits u ↔
      ∀ a b : ℚ, 0 < a → a < b → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ (a : ℝ) < u n ∧ u n < (b : ℝ) := by
  constructor
  · intro h a b ha hab N
    exact h (a : ℝ) (b : ℝ) (by exact_mod_cast ha) (by exact_mod_cast hab) N
  · intro h a b ha hab N
    obtain ⟨a', haa', ha'b⟩ := exists_rat_btwn hab
    obtain ⟨b', ha'b', hb'b⟩ := exists_rat_btwn ha'b
    have ha' : (0 : ℚ) < a' := by exact_mod_cast ha.trans haa'
    have hab' : a' < b' := by exact_mod_cast ha'b'
    obtain ⟨n, hn, hlo, hhi⟩ := h a' b' ha' hab' N
    exact ⟨n, hn, haa'.trans hlo, hhi.trans hb'b⟩

noncomputable def normalizedGap (n : ℕ) : ℝ := primeGap n / log n

theorem normalizedGap_nonnegative (n : ℕ) : 0 ≤ normalizedGap n := by
  exact div_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)

theorem normalized_gap_target_iff :
    (∀ C : ℝ, 0 ≤ C →
      ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => normalizedGap (n i)) atTop (𝓝 C)) ↔
    (∀ a b : ℝ, 0 < a → a < b → ∀ N : ℕ,
      ∃ n : ℕ, N ≤ n ∧ a < normalizedGap n ∧ normalizedGap n < b) :=
  full_iff_interval_hits normalizedGap

theorem target_iff_rational_gap_intervals :
    FullNonnegativeCluster normalizedGap ↔
      ∀ a b : ℚ, 0 < a → a < b → ∀ N : ℕ,
        ∃ n : ℕ, max N 2 ≤ n ∧
          (a : ℝ) * log n < (primeGap n : ℝ) ∧
          (primeGap n : ℝ) < (b : ℝ) * log n := by
  rw [full_iff_interval_hits, interval_hits_iff_rational]
  constructor
  · intro h a b ha hab N
    obtain ⟨n, hn, hlo, hhi⟩ := h a b ha hab (max N 2)
    have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
    have hlog : 0 < log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    exact ⟨n, hn, (lt_div_iff₀ hlog).mp hlo, (div_lt_iff₀ hlog).mp hhi⟩
  · intro h a b ha hab N
    obtain ⟨n, hn, hlo, hhi⟩ := h a b ha hab N
    have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
    have hlog : 0 < log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    exact ⟨n, (le_max_left N 2).trans hn,
      (lt_div_iff₀ hlog).mpr hlo, (div_lt_iff₀ hlog).mpr hhi⟩

/-- A common-weight second-moment criterion for simultaneous occupancy. -/
theorem two_island_overlap {ι : Type*} (s : Finset ι) (w x y : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hmass : ∑ i ∈ s, w i = 1)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i)
    (hmoment : (∑ i ∈ s, w i * (x i + y i)) ^ 2 >
      ∑ i ∈ s, w i * (x i ^ 2 + y i ^ 2)) :
    ∃ i ∈ s, 0 < x i ∧ 0 < y i := by
  classical
  let μ : ℝ := ∑ i ∈ s, w i * (x i + y i)
  have hvariance : 0 ≤ ∑ i ∈ s, w i * ((x i + y i) - μ) ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hexpand : (∑ i ∈ s, w i * ((x i + y i) - μ) ^ 2) =
      (∑ i ∈ s, w i * (x i + y i) ^ 2) - μ ^ 2 := by
    calc
      (∑ i ∈ s, w i * ((x i + y i) - μ) ^ 2) =
          ∑ i ∈ s, (w i * (x i + y i) ^ 2 -
            2 * μ * (w i * (x i + y i)) + μ ^ 2 * w i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i ∈ s, w i * (x i + y i) ^ 2) -
          2 * μ * (∑ i ∈ s, w i * (x i + y i)) + μ ^ 2 * (∑ i ∈ s, w i) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (∑ i ∈ s, w i * (x i + y i) ^ 2) - μ ^ 2 := by
        rw [hmass]
        change _ - 2 * μ * μ + μ ^ 2 * 1 = _
        ring
  by_contra h
  push_neg at h
  have hxy : ∀ i ∈ s, x i * y i = 0 := by
    intro i hi
    rcases (hx i hi).eq_or_lt with hxi | hxi
    · rw [← hxi, zero_mul]
    · have hyi : y i = 0 := le_antisymm (h i hi hxi) (hy i hi)
      rw [hyi, mul_zero]
  have heq : (∑ i ∈ s, w i * (x i + y i) ^ 2) =
      ∑ i ∈ s, w i * (x i ^ 2 + y i ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [add_sq, mul_assoc, hxy i hi, mul_zero, add_zero]
  rw [hexpand, heq] at hvariance
  change (∑ i ∈ s, w i * (x i ^ 2 + y i ^ 2)) < μ ^ 2 at hmoment
  linarith

/-- Deleting one vertex can destroy at most two edges of an ordered sequence. -/
theorem targeted_edges_le_twice_bad_vertices (edges bad : Finset ℕ)
    (hcover : ∀ i ∈ edges, i ∈ bad ∨ i + 1 ∈ bad) :
    edges.card ≤ 2 * bad.card := by
  have hsub : edges ⊆ bad ∪ bad.image (fun n => n - 1) := by
    intro i hi
    rcases hcover i hi with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i + 1, h, by omega⟩)
  calc
    edges.card ≤ (bad ∪ bad.image (fun n => n - 1)).card := Finset.card_le_card hsub
    _ ≤ bad.card + (bad.image (fun n => n - 1)).card := Finset.card_union_le _ _
    _ ≤ bad.card + bad.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * bad.card := by omega

/-- A strict excess over the deletion budget leaves a targeted edge with both vertices intact. -/
theorem exists_intact_targeted_edge (edges bad : Finset ℕ)
    (hcount : 2 * bad.card < edges.card) :
    ∃ i ∈ edges, i ∉ bad ∧ i + 1 ∉ bad := by
  by_contra h
  push_neg at h
  have hcover : ∀ i ∈ edges, i ∈ bad ∨ i + 1 ∈ bad := by
    intro i hi
    by_cases hb : i ∈ bad
    · exact Or.inl hb
    · exact Or.inr (h i hi hb)
  exact (not_lt_of_ge (targeted_edges_le_twice_bad_vertices edges bad hcover)) hcount

#print axioms targeted_edges_le_twice_bad_vertices
#print axioms exists_intact_targeted_edge
#print axioms target_iff_rational_gap_intervals
#print axioms two_island_overlap
#print axioms subsequence_iff_cluster
#print axioms cluster_iff_tail_approximation
#print axioms full_iff_interval_hits
#print axioms not_full_iff_forbidden_interval
#print axioms normalized_gap_target_iff

end PrimeGapProgress
