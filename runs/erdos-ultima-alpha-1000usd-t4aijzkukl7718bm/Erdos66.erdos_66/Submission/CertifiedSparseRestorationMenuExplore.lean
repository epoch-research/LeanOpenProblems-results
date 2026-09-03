import Submission.SublogPatternInvariantsExplore
import Submission.UniformSparseRestorationMenuExplore

/-! One sparse restoration menu preserving qualitative boundary and central
triple estimates for every later deletion choice. This is conditional on
negligible deletion mass and is not an all-target correction theorem. -/
namespace Erdos66CertifiedSparseRestorationMenu
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Generating Erdos66Fractional
  Erdos66ClampedPrefixContinuation Erdos66RankProfileGap Erdos66BracketRankMove
  Erdos66RankCellExchange Erdos66InfiniteRankSwap Erdos66SparseRankTransversal
  Erdos66InsertionIncrementComparison Erdos66Explore Erdos66Compactness
  Erdos66UniformSparseRestorationMenu Erdos66SublogPatternInvariants
open scoped Classical Topology
set_option maxHeartbeats 3600000

theorem exists_certified_sparse_restoration_menu
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (hB : SmallBoundary A) (hT : SublogCentral A)
    (D : Set ℕ) (hDA : D ⊆ A)
    (hdec : Tendsto (fun n : ℕ ↦ (count D n : ℝ)/Real.sqrt ((n : ℝ)*Real.log n)) atTop (𝓝 0)) :
    ∃ F : Set ℕ, Disjoint F A ∧
      (∀ E : Set ℕ, SmallBoundary (restoredFrom A hbr F E) ∧
        SublogCentral (restoredFrom A hbr F E)) ∧
      ∀ ε : ℝ, 0<ε → ∃ N : ℕ,
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
  have hAU : A ⊆ A∪F := Set.subset_union_left
  have hBU := smallBoundary_insert A (A∪F) hAU hB hFlim
  have hTU := sublogCentral_insert A (A∪F) hAU hT hFlim
  refine ⟨F,hFA,?_,?_⟩
  · intro E
    have hsub : restoredFrom A hbr F E ⊆ A∪F := by
      intro u hu
      rcases hu with hu | hu
      · exact Or.inl hu.1
      · exact Or.inr hu.1
    exact ⟨smallBoundary_mono hsub hBU,sublogCentral_mono hsub hTU⟩
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


end Erdos66CertifiedSparseRestorationMenu
