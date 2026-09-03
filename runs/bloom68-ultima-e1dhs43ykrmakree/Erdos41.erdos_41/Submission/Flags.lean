import Submission.Work

/-!
# Compactness for cubic-bounded flags

For a fixed natural constant `K`, flags of every finite length exist if and only
if an infinite flag exists. The reverse implication uses compactness of the
product of the finite coordinate bounds. No positivity hypothesis is imposed.
-/

namespace Work

def FiniteCubicFlag (K n : ℕ) : Prop := ∃ f : Fin n → ℕ, StrictMono f ∧ (∀ i, f i ≤ K * (i.val + 1)^3) ∧ NtupleCondition (Set.range f) 3

def InfiniteCubicFlag (K : ℕ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ (∀ i, f i ≤ K * (i + 1)^3) ∧ NtupleCondition (Set.range f) 3

/-- Restrict an infinite flag to its first `n` entries. -/
theorem InfiniteCubicFlag.finiteCubicFlag {K : ℕ} (h : InfiniteCubicFlag K)
    (n : ℕ) : FiniteCubicFlag K n := by
  rcases h with ⟨f, hf, hbound, htriple⟩
  refine ⟨fun i => f i.val, ?_, fun i => hbound i.val, ?_⟩
  · intro i j hij
    exact hf hij
  · apply htriple.mono
    rintro a ⟨i, rfl⟩
    exact ⟨i.val, rfl⟩

/-- The ambient compact space encodes the bound in each coordinate. -/
private abbrev CubicFlagSpace (K : ℕ) := ∀ i : ℕ, Fin (K * (i + 1)^3 + 1)

private def cubicFlagPrefix {K : ℕ} (n : ℕ) (x : CubicFlagSpace K) : Fin n → ℕ :=
  fun i => (x i.val).val

/-- This cylinder imposes only the conditions on the first `n` coordinates. -/
private def cubicFlagCylinder (K n : ℕ) : Set (CubicFlagSpace K) :=
  {x | StrictMono (cubicFlagPrefix n x) ∧
    NtupleCondition (Set.range (cubicFlagPrefix n x)) 3}

private theorem continuous_cubicFlagPrefix (K n : ℕ) :
    Continuous (cubicFlagPrefix (K := K) n) := by
  apply continuous_pi
  intro i
  exact continuous_of_discreteTopology.comp (continuous_apply i.val)

private theorem isClosed_cubicFlagCylinder (K n : ℕ) :
    IsClosed (cubicFlagCylinder K n) := by
  change IsClosed ((cubicFlagPrefix (K := K) n) ⁻¹'
    {g | StrictMono g ∧ NtupleCondition (Set.range g) 3})
  exact (isClosed_discrete _).preimage (continuous_cubicFlagPrefix K n)

private theorem cubicFlagCylinder_decreasing (K n : ℕ) :
    cubicFlagCylinder K (n + 1) ⊆ cubicFlagCylinder K n := by
  intro x hx
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact hx.1 (Fin.strictMono_castSucc hij)
  · apply hx.2.mono
    rintro a ⟨i, rfl⟩
    exact ⟨i.castSucc, rfl⟩

private theorem cubicFlagCylinder_nonempty {K n : ℕ} (h : FiniteCubicFlag K n) :
    (cubicFlagCylinder K n).Nonempty := by
  classical
  rcases h with ⟨f, hf, hbound, htriple⟩
  let x : CubicFlagSpace K := fun i =>
    if hi : i < n then
      ⟨f ⟨i, hi⟩, Nat.lt_succ_of_le (hbound ⟨i, hi⟩)⟩
    else
      ⟨0, Nat.zero_lt_succ _⟩
  have hx : cubicFlagPrefix n x = f := by
    funext i
    simp [cubicFlagPrefix, x, i.isLt]
  refine ⟨x, ?_⟩
  change StrictMono (cubicFlagPrefix n x) ∧
    NtupleCondition (Set.range (cubicFlagPrefix n x)) 3
  rw [hx]
  exact ⟨hf, htriple⟩

/-- Any finite subset of a sequence's range is contained in a single prefix. -/
private theorem finset_subset_range_prefix (f : ℕ → ℕ) (S : Finset ℕ)
    (hS : (↑S : Set ℕ) ⊆ Set.range f) :
    ∃ n, (↑S : Set ℕ) ⊆ Set.range (fun i : Fin n => f i.val) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨n, hn⟩ := ih (fun b hb => hS (Finset.mem_insert_of_mem hb))
    obtain ⟨i, hi⟩ := hS (Finset.mem_insert_self a S)
    refine ⟨max n (i + 1), ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact ⟨⟨i, lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_right _ _)⟩, hi⟩
    · obtain ⟨j, hj⟩ := hn hb
      exact ⟨⟨j.val, lt_of_lt_of_le j.isLt (le_max_left _ _)⟩, hj⟩

/-- Compactness turns flags of every finite length into one infinite flag. -/
theorem infiniteCubicFlag_of_forall_finiteCubicFlag {K : ℕ}
    (h : ∀ n, FiniteCubicFlag K n) : InfiniteCubicFlag K := by
  classical
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (cubicFlagCylinder K) (cubicFlagCylinder_decreasing K)
      (fun n => cubicFlagCylinder_nonempty (h n))
      (isClosed_cubicFlagCylinder K 0).isCompact (isClosed_cubicFlagCylinder K)
  have hprefix : ∀ n, StrictMono (cubicFlagPrefix n x) ∧
      NtupleCondition (Set.range (cubicFlagPrefix n x)) 3 := Set.mem_iInter.mp hx
  let f : ℕ → ℕ := fun i => (x i).val
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j hij
    exact (hprefix (j + 1)).1
      (show (⟨i, lt_of_lt_of_le hij (Nat.le_succ j)⟩ : Fin (j + 1)) <
        ⟨j, Nat.lt_succ_self j⟩ from hij)
  · intro i
    exact Nat.le_of_lt_succ (x i).isLt
  · intro I J hIJ
    rcases hIJ with ⟨hI, hJ, hIcard, hJcard, hsum⟩
    have hUnion : (↑(I ∪ J) : Set ℕ) ⊆ Set.range f := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hI ha
      · exact hJ ha
    obtain ⟨n, hn⟩ := finset_subset_range_prefix f (I ∪ J) hUnion
    apply (hprefix n).2 I J
    exact ⟨fun a ha => hn (Finset.mem_union_left J ha),
      fun a ha => hn (Finset.mem_union_right I ha), hIcard, hJcard, hsum⟩

/-- Finite-flag compactness, including `K = 0` and empty finite flags. -/
theorem infiniteCubicFlag_iff (K : ℕ) :
    InfiniteCubicFlag K ↔ ∀ n, FiniteCubicFlag K n := by
  constructor
  · exact fun h n => h.finiteCubicFlag n
  · exact infiniteCubicFlag_of_forall_finiteCubicFlag

end Work
