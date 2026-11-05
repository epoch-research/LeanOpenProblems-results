import Submission.ArithmeticProgression
import Submission.BlockGluing
import Submission.ReciprocalComparison

/-!
# An exact finite-extremal criterion for reciprocal summability

For a fixed length `k ≥ 3`, let `r k N` be the largest cardinality of a
positive-step `k`-AP-free subset of `{1, …, N}`. Reciprocal summability of
every `k`-AP-free set is equivalent to summability of `r k (4 ^ j) / 4 ^ j`.

The maximum is taken over a finite powerset. The necessary direction glues
translated extremizers in the separated blocks `(3 * 4 ^ j, 4 * 4 ^ j]`;
the sufficient direction uses the reciprocal shell criterion.

The final propositions are conditional reductions only: no theorem asserting
the original Erdős statement is imported or used.
-/

namespace Erdos3Aux

open scoped BigOperators

/-- Containment of progressions is monotone in the ambient set. -/
theorem ContainsProgression.mono_set {A B : Set ℕ} {k : ℕ}
    (h : ContainsProgression A k) (hAB : A ⊆ B) : ContainsProgression B k := by
  rcases h with ⟨a, d, hd, hmem⟩
  exact ⟨a, d, hd, fun n hn ↦ hAB (hmem n hn)⟩

/-- The empty set has no positive-length progression. -/
theorem not_containsProgression_empty {k : ℕ} (hk : 0 < k) :
    ¬ ContainsProgression (∅ : Set ℕ) k := by
  rintro ⟨a, d, hd, hmem⟩
  exact hmem 0 hk

/-- Translation in `ℕ` preserves and reflects positive-length progressions.
In the reverse direction, the zeroth term supplies the unshifted initial term. -/
theorem containsProgression_translate_iff (A : Set ℕ) (m : ℕ) {k : ℕ}
    (hk : 0 < k) :
    ContainsProgression ((fun n : ℕ ↦ m + n) '' A) k ↔ ContainsProgression A k := by
  constructor
  · rintro ⟨a, d, hd, hmem⟩
    have hzero : a ∈ (fun n : ℕ ↦ m + n) '' A := by simpa using hmem 0 hk
    obtain ⟨a₀, ha₀, hstart⟩ := hzero
    refine ⟨a₀, d, hd, ?_⟩
    intro n hn
    obtain ⟨x, hx, heq⟩ := hmem n hn
    rw [← hstart, Nat.add_assoc] at heq
    have hxEq : x = a₀ + n * d := Nat.add_left_cancel heq
    simpa [hxEq] using hx
  · rintro ⟨a, d, hd, hmem⟩
    refine ⟨m + a, d, hd, ?_⟩
    intro n hn
    exact ⟨a + n * d, hmem n hn, (Nat.add_assoc m a (n * d)).symm⟩

/-- All admissible finite sets for the extremal problem on `[1, N]`. -/
noncomputable def progressionFreeSubsets (k N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter
    (fun s ↦ ¬ ContainsProgression (s : Set ℕ) k)

@[simp] theorem mem_progressionFreeSubsets {k N : ℕ} {s : Finset ℕ} :
    s ∈ progressionFreeSubsets k N ↔
      s ⊆ Finset.Icc 1 N ∧ ¬ ContainsProgression (s : Set ℕ) k := by
  classical
  simp [progressionFreeSubsets]

/-- The finite extremal function `r_k(N)`, for positive-step progressions. -/
noncomputable def r (k N : ℕ) : ℕ :=
  (progressionFreeSubsets k N).sup Finset.card

/-- Every admissible finite set has cardinality at most the extremal value. -/
theorem card_le_r {k N : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.Icc 1 N) (hfree : ¬ ContainsProgression (s : Set ℕ) k) :
    s.card ≤ r k N :=
  Finset.le_sup (mem_progressionFreeSubsets.mpr ⟨hs, hfree⟩)

/-- The extremal value cannot exceed the interval length. -/
theorem r_le (k N : ℕ) : r k N ≤ N := by
  apply Finset.sup_le
  intro s hs
  have hsub := (mem_progressionFreeSubsets.mp hs).1
  simpa [Nat.card_Icc] using Finset.card_le_card hsub

/-- Positive length makes the family of admissible sets nonempty. -/
theorem progressionFreeSubsets_nonempty {k : ℕ} (hk : 0 < k) (N : ℕ) :
    (progressionFreeSubsets k N).Nonempty := by
  refine ⟨∅, mem_progressionFreeSubsets.mpr ⟨Finset.empty_subset _, ?_⟩⟩
  simpa using not_containsProgression_empty hk

/-- The finite extremal value is attained, including when `N = 0`. -/
theorem exists_extremizer {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∃ s : Finset ℕ, s ⊆ Finset.Icc 1 N ∧
      ¬ ContainsProgression (s : Set ℕ) k ∧ s.card = r k N := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_mem_eq_sup
    (progressionFreeSubsets k N) (progressionFreeSubsets_nonempty hk N) Finset.card
  exact ⟨s, (mem_progressionFreeSubsets.mp hs).1,
    (mem_progressionFreeSubsets.mp hs).2, hcard.symm⟩

/-- The base-four extremal density at scale `j`. -/
noncomputable def extremalDensity (k j : ℕ) : ℝ :=
  (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j

theorem extremalDensity_nonneg (k j : ℕ) : 0 ≤ extremalDensity k j := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

/-- An AP-free shell is already an admissible subset of the full next interval;
no splitting or translation of the shell is required. -/
theorem fourShellIn_card_le_r {A : Set ℕ} {k : ℕ}
    (hfree : ¬ ContainsProgression A k) (j : ℕ) :
    (fourShellIn A j).card ≤ r k (4 ^ (j + 1)) := by
  apply card_le_r
  · intro n hn
    have h := mem_fourShellIn.mp hn
    exact Finset.mem_Icc.mpr ⟨fourShell_pos (mem_fourShell.mpr h.2), h.2.2.le⟩
  · intro h
    apply hfree
    exact h.mono_set (fun n hn ↦ (mem_fourShellIn.mp hn).1)

/-- The shell reciprocal sum is bounded by four times the next extremal density. -/
theorem reciprocalShellSum_le_shifted_extremalDensity {A : Set ℕ} {k : ℕ}
    (hfree : ¬ ContainsProgression A k) (j : ℕ) :
    reciprocalShellSum A j ≤ 4 * extremalDensity k (j + 1) := by
  calc
    reciprocalShellSum A j ≤ ((fourShellIn A j).card : ℝ) / (4 : ℝ) ^ j :=
      reciprocalShellSum_le_card_div A j
    _ ≤ (r k (4 ^ (j + 1)) : ℝ) / (4 : ℝ) ^ j :=
      div_le_div_of_nonneg_right (by exact_mod_cast fourShellIn_card_le_r hfree j)
        (pow_nonneg (by norm_num) _)
    _ = 4 * extremalDensity k (j + 1) := by
      simp only [extremalDensity, pow_succ]
      field_simp

/-- Summability of extremal densities implies reciprocal summability of every
set excluding progressions of the fixed length. This direction needs no lower
bound on that length. -/
theorem summable_reciprocal_of_extremalDensity {k : ℕ}
    (hs : Summable (extremalDensity k)) {A : Set ℕ}
    (hfree : ¬ ContainsProgression A k) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  have hshift : Summable (fun j : ℕ ↦ extremalDensity k (j + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  exact summable_reciprocal_of_shell_bound
    (fun j ↦ mul_nonneg (by norm_num) (extremalDensity_nonneg k (j + 1)))
    (hshift.mul_left 4) (reciprocalShellSum_le_shifted_extremalDensity hfree)

/-- Choose an attained extremizer at a positive length. -/
noncomputable def extremizer (k N : ℕ) (hk : 0 < k) : Finset ℕ :=
  Classical.choose (exists_extremizer hk N)

theorem extremizer_subset (k N : ℕ) (hk : 0 < k) :
    extremizer k N hk ⊆ Finset.Icc 1 N :=
  (Classical.choose_spec (exists_extremizer hk N)).1

theorem extremizer_free (k N : ℕ) (hk : 0 < k) :
    ¬ ContainsProgression (extremizer k N hk : Set ℕ) k :=
  (Classical.choose_spec (exists_extremizer hk N)).2.1

theorem extremizer_card (k N : ℕ) (hk : 0 < k) :
    (extremizer k N hk).card = r k N :=
  (Classical.choose_spec (exists_extremizer hk N)).2.2

/-- Shift the scale-`j` extremizer by `3 * 4 ^ j`. -/
noncomputable def shiftedExtremizer (k j : ℕ) (hk : 0 < k) : Finset ℕ :=
  (extremizer k (4 ^ j) hk).image (fun n ↦ 3 * 4 ^ j + n)

@[simp] theorem coe_shiftedExtremizer (k j : ℕ) (hk : 0 < k) :
    (shiftedExtremizer k j hk : Set ℕ) =
      (fun n : ℕ ↦ 3 * 4 ^ j + n) '' (extremizer k (4 ^ j) hk : Set ℕ) := by
  simp only [shiftedExtremizer, Finset.coe_image]

/-- The translated extremizer lies in the separated block, including its right endpoint. -/
theorem shiftedExtremizer_subset_fourBlock (k j : ℕ) (hk : 0 < k) :
    (shiftedExtremizer k j hk : Set ℕ) ⊆ fourBlock j := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have h := Finset.mem_Icc.mp (extremizer_subset k (4 ^ j) hk hn)
  exact mem_fourBlock.mpr (by omega)

theorem shiftedExtremizer_card (k j : ℕ) (hk : 0 < k) :
    (shiftedExtremizer k j hk).card = r k (4 ^ j) := by
  rw [shiftedExtremizer, Finset.card_image_of_injective _
    (fun a b h ↦ Nat.add_left_cancel h)]
  exact extremizer_card k (4 ^ j) hk

theorem shiftedExtremizer_free (k j : ℕ) (hk : 0 < k) :
    ¬ ContainsProgression (shiftedExtremizer k j hk : Set ℕ) k := by
  rw [coe_shiftedExtremizer, containsProgression_translate_iff _ _ hk]
  exact extremizer_free k (4 ^ j) hk

/-- Distinct shifted extremizers are disjoint, by uniqueness of the block index. -/
theorem shiftedExtremizer_disjoint {k i j : ℕ} (hk : 0 < k) (hij : i ≠ j) :
    Disjoint (shiftedExtremizer k i hk) (shiftedExtremizer k j hk) := by
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  exact hij (fourBlock_index_unique
    (shiftedExtremizer_subset_fourBlock k i hk hni)
    (shiftedExtremizer_subset_fourBlock k j hk hnj))

/-- The union of the separated translated extremizers. -/
noncomputable def extremalBlockUnion (k : ℕ) (hk : 0 < k) : Set ℕ :=
  ⋃ j : ℕ, (shiftedExtremizer k j hk : Set ℕ)

/-- No crossing AP can appear in the union when the fixed length is at least three. -/
theorem extremalBlockUnion_free {k : ℕ} (hk : 3 ≤ k) (hpos : 0 < k) :
    ¬ ContainsProgression (extremalBlockUnion k hpos) k := by
  exact block_union_progressionFree
    (shiftedExtremizer_subset_fourBlock k · hpos) hk
    (shiftedExtremizer_free k · hpos)

/-- A finite subset of a set with a summable reciprocal series has reciprocal sum
at most the subtype `tsum`. Zero membership is allowed. -/
theorem finite_reciprocal_sum_le_tsum {A : Set ℕ}
    (hA : Summable (fun a : A ↦ 1 / (a : ℝ))) {s : Finset ℕ}
    (hs : (s : Set ℕ) ⊆ A) :
    (∑ n ∈ s, 1 / (n : ℝ)) ≤ ∑' a : A, 1 / (a : ℝ) := by
  classical
  rw [← Finset.sum_subtype_of_mem (fun n : ℕ ↦ 1 / (n : ℝ)) hs]
  exact hA.sum_le_tsum (s.subtype (fun n ↦ n ∈ A))
    (fun a _ ↦ one_div_nonneg.mpr (Nat.cast_nonneg (a : ℕ)))

/-- A uniform bound for the sum of harmonics on any finitely many blocks.
Disjointness is used explicitly to turn the double sum into a finite `biUnion`. -/
theorem sum_block_reciprocals_le_tsum {k : ℕ} {hk : 0 < k}
    (hU : Summable (fun a : extremalBlockUnion k hk ↦ 1 / (a : ℝ)))
    (s : Finset ℕ) :
    (∑ j ∈ s, ∑ n ∈ shiftedExtremizer k j hk, 1 / (n : ℝ)) ≤
      ∑' a : extremalBlockUnion k hk, 1 / (a : ℝ) := by
  classical
  have hdisj : (s : Set ℕ).PairwiseDisjoint (fun j ↦ shiftedExtremizer k j hk) := by
    intro i hi j hj hij
    exact shiftedExtremizer_disjoint hk hij
  rw [← Finset.sum_biUnion hdisj]
  apply finite_reciprocal_sum_le_tsum hU
  intro n hn
  obtain ⟨j, hj, hnj⟩ := Finset.mem_biUnion.mp hn
  exact Set.mem_iUnion.mpr ⟨j, hnj⟩

/-- Each element of a shifted scale-`j` extremizer is at most `4 * 4 ^ j`,
so its harmonic sum is at least one quarter of the extremal density. -/
theorem extremalDensity_le_four_mul_block_reciprocal (k j : ℕ) (hk : 0 < k) :
    extremalDensity k j ≤ 4 * (∑ n ∈ shiftedExtremizer k j hk, 1 / (n : ℝ)) := by
  have hbound : extremalDensity k j / 4 ≤
      ∑ n ∈ shiftedExtremizer k j hk, 1 / (n : ℝ) := by
    calc
      extremalDensity k j / 4 =
          ((shiftedExtremizer k j hk).card : ℝ) / (4 * (4 : ℝ) ^ j) := by
        rw [shiftedExtremizer_card]
        simp only [extremalDensity]
        ring
      _ = ∑ n ∈ shiftedExtremizer k j hk, 1 / (4 * (4 : ℝ) ^ j) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ ∑ n ∈ shiftedExtremizer k j hk, 1 / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have h := mem_fourBlock.mp (shiftedExtremizer_subset_fourBlock k j hk hn)
        have hnpos : (0 : ℝ) < (n : ℝ) := by
          exact_mod_cast (show 0 < n by omega)
        apply one_div_le_one_div_of_le hnpos
        exact_mod_cast h.2
  simpa only [mul_comm] using (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp hbound

/-- Every finite extremal-density subsum is at most four times the reciprocal
`tsum` of the glued extremizers, if that reciprocal series is summable. -/
theorem sum_extremalDensity_le_four_tsum {k : ℕ} {hk : 0 < k}
    (hU : Summable (fun a : extremalBlockUnion k hk ↦ 1 / (a : ℝ)))
    (s : Finset ℕ) :
    (∑ j ∈ s, extremalDensity k j) ≤
      4 * (∑' a : extremalBlockUnion k hk, 1 / (a : ℝ)) := by
  calc
    (∑ j ∈ s, extremalDensity k j) ≤
        ∑ j ∈ s, 4 * (∑ n ∈ shiftedExtremizer k j hk, 1 / (n : ℝ)) :=
      Finset.sum_le_sum (fun j _ ↦ extremalDensity_le_four_mul_block_reciprocal k j hk)
    _ = 4 * (∑ j ∈ s, ∑ n ∈ shiftedExtremizer k j hk, 1 / (n : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 4 * (∑' a : extremalBlockUnion k hk, 1 / (a : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_block_reciprocals_le_tsum hU s) (by norm_num)

/-- Summability of the single glued example already forces summability of
all the fixed-length extremal densities. -/
theorem summable_extremalDensity_of_block_union_summable {k : ℕ} {hk : 0 < k}
    (hU : Summable (fun a : extremalBlockUnion k hk ↦ 1 / (a : ℝ))) :
    Summable (extremalDensity k) :=
  summable_of_sum_le (extremalDensity_nonneg k) (sum_extremalDensity_le_four_tsum hU)

/-- Necessity of the extremal series criterion for a fixed length at least three. -/
theorem summable_extremalDensity_of_reciprocal {k : ℕ} (hk : 3 ≤ k)
    (h : ∀ A : Set ℕ, ¬ ContainsProgression A k →
      Summable (fun a : A ↦ 1 / (a : ℝ))) :
    Summable (extremalDensity k) := by
  have hpos : 0 < k := by omega
  exact summable_extremalDensity_of_block_union_summable
    (h (extremalBlockUnion k hpos) (extremalBlockUnion_free hk hpos))

/-- Exact fixed-length finite-extremal criterion. -/
theorem fixed_length_extremal_criterion {k : ℕ} (hk : 3 ≤ k) :
    (∀ A : Set ℕ, ¬ ContainsProgression A k →
      Summable (fun a : A ↦ 1 / (a : ℝ))) ↔
    Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) := by
  exact ⟨summable_extremalDensity_of_reciprocal hk,
    fun hs A hfree ↦ summable_reciprocal_of_extremalDensity hs hfree⟩

/-- If the fixed-length extremal series fails to converge, the separated
extremizer union is a progression-free set with a nonsummable reciprocal series. -/
theorem exists_progressionFree_not_summable_of_not_extremalDensity {k : ℕ}
    (hk : 3 ≤ k) (hs : ¬ Summable (extremalDensity k)) :
    ∃ A : Set ℕ, ¬ ContainsProgression A k ∧
      ¬ Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  have hpos : 0 < k := by omega
  exact ⟨extremalBlockUnion k hpos, extremalBlockUnion_free hk hpos,
    fun hU ↦ hs (summable_extremalDensity_of_block_union_summable hU)⟩

/-- The original reciprocal-divergence-to-arbitrarily-long-AP statement,
expressed as a proposition rather than assumed as a theorem. -/
def OriginalStatement : Prop :=
  ∀ A : Set ℕ, (¬ Summable (fun a : A ↦ 1 / (a : ℝ))) →
    ∃ᶠ k : ℕ in Filter.atTop, ∃ S ⊆ A, S.IsAPOfLength (k : ℕ∞)

/-- Convergence of all the fixed-length extremal series would prove the original
statement. Lengths below three are obtained by taking prefixes. -/
theorem originalStatement_of_all_extremal_summable
    (hs : ∀ k : ℕ, 3 ≤ k →
      Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j)) :
    OriginalStatement := by
  intro A hA
  apply (frequently_isAPOfLength_iff A).mpr
  intro k
  have hk : 3 ≤ max 3 k := le_max_left _ _
  have hlong : ContainsProgression A (max 3 k) := by
    by_contra hfree
    exact hA (summable_reciprocal_of_extremalDensity (hs (max 3 k) hk) hfree)
  exact hlong.mono_length (le_max_right _ _)

/-- Conversely, the original statement would imply convergence of every
fixed-length extremal series at length at least three. -/
theorem all_extremal_summable_of_originalStatement (h : OriginalStatement) :
    ∀ k : ℕ, 3 ≤ k →
      Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) := by
  intro k hk
  apply (fixed_length_extremal_criterion hk).mp
  intro A hfree
  by_contra hA
  exact hfree ((frequently_isAPOfLength_iff A).mp (h A hA) k)

/-- Conditional reduction of the original statement to precisely the remaining
finite-extremal series convergence obligation. -/
theorem originalStatement_iff_all_extremal_summable :
    OriginalStatement ↔ ∀ k : ℕ, 3 ≤ k →
      Summable (fun j : ℕ ↦ (r k (4 ^ j) : ℝ) / (4 : ℝ) ^ j) :=
  ⟨all_extremal_summable_of_originalStatement, originalStatement_of_all_extremal_summable⟩

/-- A single nonsummable fixed-length extremal series would disprove the
original statement, without assuming or using the original conjecture. -/
theorem not_originalStatement_of_not_extremalDensity {k : ℕ}
    (hk : 3 ≤ k) (hs : ¬ Summable (extremalDensity k)) :
    ¬ OriginalStatement := by
  intro h
  exact hs (all_extremal_summable_of_originalStatement h k hk)

/-- Exact disproof criterion: failure of the original statement is equivalent
to nonsummability of the actual extremal series for one fixed length. -/
theorem not_originalStatement_iff_exists_not_extremalDensity :
    (¬ OriginalStatement) ↔
      ∃ k : ℕ, 3 ≤ k ∧ ¬ Summable (extremalDensity k) := by
  classical
  rw [originalStatement_iff_all_extremal_summable]
  push_neg
  rfl

/-- Increasing the forbidden length can only increase the extremal value. -/
theorem r_mono_length {k l N : ℕ} (hkl : k ≤ l) : r k N ≤ r l N := by
  apply Finset.sup_le
  intro s hs
  obtain ⟨hsub, hfree⟩ := mem_progressionFreeSubsets.mp hs
  exact card_le_r hsub (fun h ↦ hfree (h.mono_length hkl))

/-- Extremal densities are monotone in the forbidden progression length. -/
theorem extremalDensity_mono_length {k l : ℕ} (hkl : k ≤ l) (j : ℕ) :
    extremalDensity k j ≤ extremalDensity l j := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast r_mono_length (N := 4 ^ j) hkl
  · exact pow_nonneg (by norm_num) j

/-- A summability bound for a longer forbidden length also controls every
shorter length; the converse direction is not asserted. -/
theorem summable_extremalDensity_of_length_le {k l : ℕ} (hkl : k ≤ l)
    (hs : Summable (extremalDensity l)) : Summable (extremalDensity k) := by
  exact Summable.of_nonneg_of_le (extremalDensity_nonneg k)
    (extremalDensity_mono_length hkl) hs

/-- It is equivalent to establish extremal summability for an unbounded
collection of forbidden lengths. Monotonicity fills all shorter lengths. -/
theorem originalStatement_iff_frequently_extremalDensity_summable :
    OriginalStatement ↔
      ∃ᶠ k : ℕ in Filter.atTop, Summable (extremalDensity k) := by
  constructor
  · intro h
    apply Filter.frequently_atTop.mpr
    intro n
    exact ⟨max 3 n, le_max_right 3 n,
      all_extremal_summable_of_originalStatement h (max 3 n) (le_max_left 3 n)⟩
  · intro h
    apply originalStatement_of_all_extremal_summable
    intro k hk
    obtain ⟨l, hkl, hs⟩ := Filter.frequently_atTop.mp h k
    exact summable_extremalDensity_of_length_le hkl hs

end Erdos3Aux
