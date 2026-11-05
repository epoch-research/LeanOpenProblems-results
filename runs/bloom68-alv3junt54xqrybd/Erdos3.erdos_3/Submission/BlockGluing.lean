import FormalConjecturesUtil

/-!
# Gluing progression-free subsets of separated base-four blocks

The blocks are `I_j = (3 * 4 ^ j, 4 * 4 ^ j]` in `ℕ`. A strictly increasing
three-term arithmetic progression whose terms lie in these blocks cannot
cross between blocks. Overlapping triples give the same conclusion for every
positive-step progression of length at least three. Consequently, an arbitrary
union of subsets of the blocks is free of progressions of a fixed length
`k ≥ 3` whenever each subset is free of progressions of that length.

This file is independent of the AP/set-cardinality equivalence: the local
predicate `BlockContainsProgression` uses positive-step witnesses directly.
-/

namespace Erdos3Aux

/-- The separated block `I_j = (3 * 4 ^ j, 4 * 4 ^ j]` of natural numbers. -/
def fourBlock (j : ℕ) : Set ℕ :=
  Set.Ioc (3 * 4 ^ j) (4 * 4 ^ j)

@[simp] theorem mem_fourBlock {j x : ℕ} :
    x ∈ fourBlock j ↔ 3 * 4 ^ j < x ∧ x ≤ 4 * 4 ^ j := by
  rfl

/-- Every earlier block ends at or before the scale of a later block. -/
theorem fourBlock_earlier_max {i j : ℕ} (hij : i < j) :
    4 * 4 ^ i ≤ 4 ^ j := by
  calc
    4 * 4 ^ i = 4 ^ (i + 1) := by rw [pow_succ']
    _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- A later block starts strictly above at least twelve times the current scale. -/
theorem fourBlock_later_min {j l : ℕ} (hjl : j < l) :
    12 * 4 ^ j ≤ 3 * 4 ^ l := by
  have hpow := fourBlock_earlier_max hjl
  omega

/-- The block indices are nondecreasing with the elements. -/
theorem fourBlock_index_mono {i j x y : ℕ}
    (hx : x ∈ fourBlock i) (hy : y ∈ fourBlock j) (hxy : x ≤ y) :
    i ≤ j := by
  by_contra h
  have hji : j < i := by omega
  have hpow := fourBlock_earlier_max hji
  rcases mem_fourBlock.mp hx with ⟨hxlo, hxhi⟩
  rcases mem_fourBlock.mp hy with ⟨hylo, hyhi⟩
  omega

/-- An element belongs to at most one of the separated blocks. -/
theorem fourBlock_index_unique {i j x : ℕ}
    (hi : x ∈ fourBlock i) (hj : x ∈ fourBlock j) : i = j := by
  exact le_antisymm (fourBlock_index_mono hi hj le_rfl)
    (fourBlock_index_mono hj hi le_rfl)

/-- A strictly increasing three-term AP in the union of the blocks cannot cross blocks. -/
theorem no_crossing3AP {i j l x y z : ℕ}
    (hx : x ∈ fourBlock i) (hy : y ∈ fourBlock j) (hz : z ∈ fourBlock l)
    (hxy : x < y) (hyz : y < z) (hAP : x + z = 2 * y) :
    i = j ∧ j = l := by
  have hij : i ≤ j := fourBlock_index_mono hx hy hxy.le
  have hjl : j ≤ l := fourBlock_index_mono hy hz hyz.le
  rcases mem_fourBlock.mp hx with ⟨hxlo, hxhi⟩
  rcases mem_fourBlock.mp hy with ⟨hylo, hyhi⟩
  rcases mem_fourBlock.mp hz with ⟨hzlo, hzhi⟩
  -- Write N = 4 ^ j. Since x > 0 and y ≤ 4N, we have z < 8N.
  have hzbound : z < 8 * 4 ^ j := by omega
  have hlj : l = j := by
    by_contra hne
    have hjl' : j < l := by omega
    have hpow := fourBlock_later_min hjl'
    -- Any later block starts above 12N, contradicting z < 8N.
    omega
  subst l
  -- Now z ≤ 4N and y > 3N, so x = 2y - z > 2N.
  have hxbound : 2 * 4 ^ j < x := by omega
  have hij' : i = j := by
    by_contra hne
    have hijlt : i < j := by omega
    have hpow := fourBlock_earlier_max hijlt
    -- Any earlier block ends at or before N, contradicting x > 2N.
    omega
  exact ⟨hij', rfl⟩

/-- The no-crossing lemma applied to any consecutive triple of a positive-step AP. -/
theorem no_crossing3AP_terms {a d n i j l : ℕ} (hd : 0 < d)
    (hzero : a + n * d ∈ fourBlock i)
    (hone : a + (n + 1) * d ∈ fourBlock j)
    (htwo : a + (n + 2) * d ∈ fourBlock l) :
    i = j ∧ j = l := by
  apply no_crossing3AP hzero hone htwo
  · simp only [add_mul, one_mul]
    omega
  · simp only [add_mul, one_mul]
    omega
  · ring

/-- Every positive-step AP of length at least three in the union of the blocks
lies wholly in a single block. -/
theorem progression_in_single_fourBlock {a d k : ℕ}
    (hk : 3 ≤ k) (hd : 0 < d)
    (hmem : ∀ n < k, a + n * d ∈ ⋃ j : ℕ, fourBlock j) :
    ∃ j : ℕ, ∀ n < k, a + n * d ∈ fourBlock j := by
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hmem 0 (by omega))
  refine ⟨j, Nat.twoStepInduction ?_ ?_ ?_⟩
  · intro _
    exact hj
  · intro _
    obtain ⟨j₁, hj₁⟩ := Set.mem_iUnion.mp (hmem 1 (by omega))
    obtain ⟨j₂, hj₂⟩ := Set.mem_iUnion.mp (hmem 2 (by omega))
    have hindices := no_crossing3AP_terms (a := a) (n := 0) hd hj hj₁ hj₂
    simpa [← hindices.1] using hj₁
  · intro n ihzero ihone hn
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hmem (n + 2) hn)
    have hzero := ihzero (by omega)
    have hone := ihone (by omega)
    have hindices := no_crossing3AP_terms (a := a) (n := n) hd hzero hone hl
    simpa [← hindices.2] using hl

/-- For arbitrary pieces `C_j ⊆ I_j`, a positive-step AP of length at least
three in their union lies wholly in a single piece, not merely a single block. -/
theorem progression_in_single_block_piece {C : ℕ → Set ℕ} {a d k : ℕ}
    (hC : ∀ j, C j ⊆ fourBlock j) (hk : 3 ≤ k) (hd : 0 < d)
    (hmem : ∀ n < k, a + n * d ∈ ⋃ j : ℕ, C j) :
    ∃ j : ℕ, ∀ n < k, a + n * d ∈ C j := by
  have hblocks : ∀ n < k, a + n * d ∈ ⋃ j : ℕ, fourBlock j := by
    intro n hn
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hmem n hn)
    exact Set.mem_iUnion.mpr ⟨j, hC j hj⟩
  obtain ⟨j, hj⟩ := progression_in_single_fourBlock hk hd hblocks
  refine ⟨j, ?_⟩
  intro n hn
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (hmem n hn)
  have hlj : l = j := fourBlock_index_unique (hC l hl) (hj n hn)
  simpa [hlj] using hl

/-- A conventional witness-based AP predicate, kept independent of other files.
The common difference is strictly positive. -/
def BlockContainsProgression (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ n < k, a + n * d ∈ A

/-- For lengths at least three, the union contains a progression if and only if
one of its block pieces contains a progression of that same length. -/
theorem block_union_containsProgression_iff {C : ℕ → Set ℕ} {k : ℕ}
    (hC : ∀ j, C j ⊆ fourBlock j) (hk : 3 ≤ k) :
    BlockContainsProgression (⋃ j : ℕ, C j) k ↔
      ∃ j : ℕ, BlockContainsProgression (C j) k := by
  constructor
  · rintro ⟨a, d, hd, hmem⟩
    obtain ⟨j, hj⟩ := progression_in_single_block_piece hC hk hd hmem
    exact ⟨j, a, d, hd, hj⟩
  · rintro ⟨j, a, d, hd, hmem⟩
    exact ⟨a, d, hd, fun n hn => Set.mem_iUnion.mpr ⟨j, hmem n hn⟩⟩

/-- Gluing subsets of the separated blocks preserves the exclusion of
positive-step progressions of any fixed length `k ≥ 3`. -/
theorem block_union_progressionFree {C : ℕ → Set ℕ} {k : ℕ}
    (hC : ∀ j, C j ⊆ fourBlock j) (hk : 3 ≤ k)
    (hfree : ∀ j, ¬ BlockContainsProgression (C j) k) :
    ¬ BlockContainsProgression (⋃ j : ℕ, C j) k := by
  intro h
  obtain ⟨j, hj⟩ := (block_union_containsProgression_iff hC hk).mp h
  exact hfree j hj

end Erdos3Aux
