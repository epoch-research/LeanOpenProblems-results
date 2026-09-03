import Submission.SparseRankTransversalExplore

/-! One replacement menu for every later subset of a negligible deletion set.
A sufficiently remote part of this same menu has arbitrarily small global
logarithmic insertion cost, without choosing replacements anew. -/
namespace Erdos66UniformSparseRestorationMenu
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Generating Erdos66Fractional
  Erdos66ClampedPrefixContinuation Erdos66RankProfileGap Erdos66BracketRankMove
  Erdos66RankCellExchange Erdos66InfiniteRankSwap Erdos66SparseRankTransversal
  Erdos66InsertionIncrementComparison Erdos66Explore Erdos66Compactness
open scoped Classical Topology
set_option maxHeartbeats 3600000

noncomputable def assignment (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) (u : ℕ) : ℕ :=
  rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)

def selectedFrom (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) (F E : Set ℕ) : Set ℕ :=
  {u | u∈F ∧ assignment A hbr u∈E}

def restoredFrom (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) (F E : Set ℕ) : Set ℕ :=
  (A\E)∪selectedFrom A hbr F E

lemma selectedFrom_subset (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) (F E : Set ℕ) :
    selectedFrom A hbr F E ⊆ F := fun _ h ↦ h.1

lemma selectedFrom_image (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) (F E : Set ℕ)
    (hE : E ⊆ assignment A hbr '' F) :
    assignment A hbr '' selectedFrom A hbr F E=E := by
  apply Set.Subset.antisymm
  · rintro d ⟨u,hu,rfl⟩
    exact hu.2
  · intro d hd
    obtain ⟨u,hu,he⟩ := hE hd
    exact ⟨u,⟨hu,he ▸ hd⟩,he⟩

lemma restoredFrom_brackets (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) (F E : Set ℕ)
    (hFA : Disjoint F A) (hE : E ⊆ assignment A hbr '' F)
    (hinj : Set.InjOn (assignment A hbr) F)
    (hloc : ∀ u∈F, u ≤ 2*assignment A hbr u) :
    ∀ L, PrefixBrackets profile (restoredFrom A hbr F E) L := by
  exact infinite_rank_swap_brackets A hbr E (selectedFrom A hbr F E)
    (hFA.mono_left (selectedFrom_subset A hbr F E)) (selectedFrom_image A hbr F E hE)
    (hinj.mono (selectedFrom_subset A hbr F E)) (fun u hu ↦ hloc u hu.1)

lemma restoredFrom_increment (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L) (F E : Set ℕ)
    (hFA : Disjoint F A) (n : ℕ) :
    0 ≤ (sumRep (restoredFrom A hbr F E) n : ℝ)-(sumRep (A\E) n : ℝ) ∧
      (sumRep (restoredFrom A hbr F E) n : ℝ)-(sumRep (A\E) n : ℝ) ≤
        (sumRep (A∪F) n : ℝ)-(sumRep A n : ℝ) := by
  have hG := selectedFrom_subset A hbr F E
  have hFA' : Disjoint (selectedFrom A hbr F E) A := hFA.mono_left hG
  have hl := sumRep_mono (show A\E ⊆ restoredFrom A hbr F E from fun _ h ↦ Or.inl h) n
  have hu := insertion_increment_mono (A\E) A (selectedFrom A hbr F E) Set.diff_subset hFA' n
  have hm := sumRep_mono (show A∪selectedFrom A hbr F E ⊆ A∪F from Set.union_subset_union_right A hG) n
  have hl' : (sumRep (A\E) n : ℝ) ≤ sumRep (restoredFrom A hbr F E) n := by exact_mod_cast hl
  have hm' : (sumRep (A∪selectedFrom A hbr F E) n : ℝ) ≤ sumRep (A∪F) n := by exact_mod_cast hm
  change (sumRep (restoredFrom A hbr F E) n : ℝ)-(sumRep (A\E) n : ℝ) ≤ _ at hu
  constructor <;> linarith

lemma restoredFrom_increment_zero_below (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (F E : Set ℕ) (M n : ℕ) (hn : n<M)
    (hloc : ∀ u∈F, assignment A hbr u ≤ 2*u) (hE : ∀ d∈E, 2*M ≤ d) :
    sumRep (restoredFrom A hbr F E) n=sumRep (A\E) n := by
  apply sumRep_congr_below
  intro i hi
  have hnot : i∉selectedFrom A hbr F E := by
    rintro ⟨hiF,hiE⟩
    have hlo := hloc i hiF
    have hhi := hE _ hiE
    omega
  simp only [restoredFrom,Set.mem_union,hnot,or_false]

/-- The replacement set F is selected before every tolerance and every
later subset E. Only a lower cutoff depends on the tolerance. -/
theorem exists_uniform_sparse_restoration_menu
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (D : Set ℕ) (hDA : D ⊆ A)
    (hdec : Tendsto (fun n : ℕ ↦ (count D n : ℝ)/Real.sqrt ((n : ℝ)*Real.log n)) atTop (𝓝 0)) :
    ∃ F : Set ℕ, Disjoint F A ∧ ∀ ε : ℝ, 0<ε → ∃ N : ℕ,
      ∀ E : Set ℕ, E ⊆ D → (∀ d∈E, N ≤ d) →
        (A\E ⊆ restoredFrom A hbr F E) ∧
        (∀ L, PrefixBrackets profile (restoredFrom A hbr F E) L) ∧
        (∀ n : ℕ, 0 ≤ (sumRep (restoredFrom A hbr F E) n : ℝ)-(sumRep (A\E) n : ℝ) ∧
          (sumRep (restoredFrom A hbr F E) n : ℝ)-(sumRep (A\E) n : ℝ) ≤ ε*Real.log ((n : ℝ)+2)) ∧
        Tendsto (fun n : ℕ ↦ ((sumRep (restoredFrom A hbr F E) n : ℝ)-(sumRep (A\E) n : ℝ))/
          Real.log n) atTop (𝓝 0) := by
  obtain ⟨N₀,F,hFA,himage,hinj,hloc,hFlim⟩ := exists_sparse_rank_transversal A hbr D hDA hdec
  change assignment A hbr '' F={d | d∈D ∧ N₀ ≤ d} at himage
  change Set.InjOn (assignment A hbr) F at hinj
  change ∀ u∈F, assignment A hbr u ≤ 2*u ∧ u ≤ 2*assignment A hbr u at hloc
  refine ⟨F,hFA,?_⟩
  intro ε hε
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hFlim.eventually_lt_const hε)
  let N := max N₀ (2*M)
  refine ⟨N,?_⟩
  intro E hED hEN
  have hEimage : E ⊆ assignment A hbr '' F := by
    intro d hd
    rw [himage]
    exact ⟨hED hd,(le_max_left _ _).trans (hEN d hd)⟩
  have hEremote (d : ℕ) (hd : d∈E) : 2*M ≤ d := (le_max_right _ _).trans (hEN d hd)
  have hcore : A\E ⊆ restoredFrom A hbr F E := fun _ h ↦ Or.inl h
  have hinc := restoredFrom_increment A hbr F E hFA
  refine ⟨hcore,restoredFrom_brackets A hbr F E hFA hEimage hinj (fun u hu ↦ (hloc u hu).2),?_,?_⟩
  · intro n
    refine ⟨(hinc n).1,?_⟩
    have hlog : 0<Real.log ((n : ℝ)+2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    by_cases hn : M ≤ n
    · exact (hinc n).2.trans ((div_le_iff₀ hlog).mp (hM n hn).le)
    · rw [restoredFrom_increment_zero_below A hbr F E M n (by omega)
        (fun u hu ↦ (hloc u hu).1) hEremote,sub_self]
      exact mul_nonneg hε.le hlog.le
  · have hshift : Tendsto (fun n : ℕ ↦
        ((sumRep (restoredFrom A hbr F E) n : ℝ)-(sumRep (A\E) n : ℝ))/Real.log ((n : ℝ)+2))
        atTop (𝓝 0) := by
      apply squeeze_zero (fun n ↦ div_nonneg (hinc n).1
        (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith))) ?_ hFlim
      intro n
      exact div_le_div_of_nonneg_right (hinc n).2
        (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
    exact log_zero_unshift _ (fun n ↦ (hinc n).1) hshift

end Erdos66UniformSparseRestorationMenu
