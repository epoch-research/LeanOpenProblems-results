import Submission.SimultaneousIntervalRowSelectionExplore
import Submission.InfiniteRankWindowExplore
import Submission.InfiniteRankSwapExplore
import Submission.InsertionIncrementComparisonExplore

/-! One sparse rank transversal, selected before all later subsets of the
prescribed deletions. Its full representation increment is sublogarithmic. -/
namespace Erdos66SparseRankTransversal
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Generating Erdos66Fractional
  Erdos66ClampedPrefixContinuation Erdos66RankProfileGap Erdos66RankCellWindow
  Erdos66BracketRankMove Erdos66RankCellExchange Erdos66InfiniteRankWindow
  Erdos66InfiniteRankSwap Erdos66SimultaneousIntervalRowSelection
  Erdos66ReflectionRoundingPatch Erdos66InsertionIncrementComparison
  Erdos66PredecessorCutoffTransfer Erdos66Explore Erdos66SparseRowMeanDecay
open scoped Classical Topology
set_option maxHeartbeats 5000000

 theorem exists_sparse_rank_transversal
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (D : Set ℕ) (hDA : D ⊆ A)
    (hdec : Tendsto (fun n : ℕ ↦ (count D n : ℝ)/Real.sqrt ((n : ℝ)*Real.log n)) atTop (𝓝 0)) :
    ∃ (N₀ : ℕ) (F : Set ℕ), Disjoint F A ∧
      (fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)) '' F=
        {d | d∈D ∧ N₀ ≤ d} ∧
      Set.InjOn (fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)) F ∧
      (∀ u∈F, rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u) ≤ 2*u ∧
        u ≤ 2*rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)) ∧
      Tendsto (fun n : ℕ ↦ ((sumRep (A∪F) n : ℝ)-(sumRep A n : ℝ))/
        Real.log ((n : ℝ)+2)) atTop (𝓝 0) := by
  obtain ⟨N₀,hN₀⟩ := exists_uniform_rank_probability_rows
  let E : Set ℕ := {d | d∈D ∧ N₀ ≤ d}
  have hED : E ⊆ D := fun _ h ↦ h.1
  have hEA : E ⊆ A := hED.trans hDA
  have hrows (d : ℕ) : ∃ (L U : ℕ) (S : Finset ℕ), d∈E → S.Nonempty ∧ S ⊆ Finset.Ico L U ∧
      (∀ i∈S, i∉A) ∧
      (∀ i∈Finset.Ico L U, d ≤ 2*i ∧ i ≤ 2*d ∧ cell profile i=count A d) ∧
      (∀ i∈Finset.Ico L U, ((S.card : ℝ)⁻¹ ≤ 256*profile i)) ∧
      (S.card : ℝ)⁻¹*(U-L : ℕ) ≤ 2 := by
    by_cases hd : d∈E
    · obtain ⟨L,U,S,hs⟩ := hN₀ A hbr d hd.2 (hEA hd)
      exact ⟨L,U,S,fun _ ↦ hs⟩
    · exact ⟨0,0,∅,fun h ↦ (hd h).elim⟩
  choose L U S hrows using hrows
  have hne (d : ℕ) (hd : d∈E) : (S d).Nonempty := (hrows d hd).1
  have hsub (d : ℕ) (hd : d∈E) : S d ⊆ Finset.Ico (L d) (U d) := (hrows d hd).2.1
  have hfresh (d : ℕ) (hd : d∈E) : ∀ i∈S d, i∉A := (hrows d hd).2.2.1
  have hrow (d : ℕ) (hd : d∈E) : ∀ i∈Finset.Ico (L d) (U d),
      d ≤ 2*i ∧ i ≤ 2*d ∧ cell profile i=count A d := (hrows d hd).2.2.2.1
  have hmaj (d : ℕ) (hd : d∈E) : ∀ i∈Finset.Ico (L d) (U d),
      ((S d).card : ℝ)⁻¹ ≤ 256*profile i := (hrows d hd).2.2.2.2.1
  have hfill (d : ℕ) (hd : d∈E) : ((S d).card : ℝ)⁻¹*(U d-L d : ℕ) ≤ 2 := (hrows d hd).2.2.2.2.2
  have hLU (d : ℕ) (hd : d∈E) : L d<U d := by
    obtain ⟨i,hi⟩ := hne d hd
    have hh := Finset.mem_Ico.mp (hsub d hd hi)
    omega
  have hord (d : ℕ) (hd : d∈E) (e : ℕ) (he : e∈E) (hde : d<e) : U d ≤ L e := by
    by_contra hn
    have hdlu := hLU d hd
    have helu := hLU e he
    have hdi : U d-1∈Finset.Ico (L d) (U d) := Finset.mem_Ico.mpr ⟨by omega,by omega⟩
    have hei : L e∈Finset.Ico (L e) (U e) := Finset.mem_Ico.mpr ⟨le_rfl,helu⟩
    have hh := cell_mono profile profile_nonneg (show L e ≤ U d-1 by omega)
    rw [(hrow d hd _ hdi).2.2,(hrow e he _ hei).2.2] at hh
    have hc := count_strict_of_mem A d e (hEA hd) hde
    omega
  have hEdec : Tendsto (fun n : ℕ ↦ (count E n : ℝ)/Real.sqrt ((n : ℝ)*Real.log n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) ?_ hdec
    intro n
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact_mod_cast (Finset.card_le_card (show cutoff E n ⊆ cutoff D n from by
      intro i hi
      exact mem_cutoff.mpr ⟨(mem_cutoff.mp hi).1,hED (mem_cutoff.mp hi).2⟩))
  obtain ⟨F,hFA,hFsupport,hFone,hFlim⟩ := exists_sparse_interval_transversal A hbr E S L U
    hne hsub hfresh hord (fun d hd i hi ↦ (hrow d hd i hi).1) 256 (by norm_num) hmaj hfill hEdec
  let assign (u : ℕ) := rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)
  have hassigned (d : ℕ) (hd : d∈E) (u : ℕ) (hu : u∈Finset.Ico (L d) (U d)) : assign u=d := by
    dsimp only [assign]
    rw [(hrow d hd u hu).2.2]
    exact rankPoint_at_mem A (harmonic_brackets_unbounded A hbr) d (hEA hd)
  have himage : assign '' F=E := by
    apply Set.Subset.antisymm
    · rintro d ⟨u,hu,rfl⟩
      obtain ⟨e,he,hue⟩ := hFsupport u hu
      rw [hassigned e he u (hsub e he hue)]
      exact he
    · intro d hd
      have hnon : (intervalPart F (L d) (U d)).Nonempty := Finset.card_pos.mp (by rw [hFone d hd]; norm_num)
      obtain ⟨u,hu⟩ := hnon
      obtain ⟨hur,huF⟩ := Finset.mem_filter.mp hu
      exact ⟨u,huF,hassigned d hd u hur⟩
  have hinj : Set.InjOn assign F := by
    intro u hu v hv he
    obtain ⟨d,hd,hud⟩ := hFsupport u hu
    obtain ⟨e,heE,hve⟩ := hFsupport v hv
    have hurow := hsub d hd hud
    have hvrow := hsub e heE hve
    rw [hassigned d hd u hurow,hassigned e heE v hvrow] at he
    subst e
    have hh := Finset.card_le_one.mp (hFone d hd).le
    exact hh u (Finset.mem_filter.mpr ⟨hurow,hu⟩) v (Finset.mem_filter.mpr ⟨hvrow,hv⟩)
  have hloc : ∀ u∈F, assign u ≤ 2*u ∧ u ≤ 2*assign u := by
    intro u hu
    obtain ⟨d,hd,hud⟩ := hFsupport u hu
    have hurow := hsub d hd hud
    rw [hassigned d hd u hurow]
    exact ⟨(hrow d hd u hurow).1,(hrow d hd u hurow).2.1⟩
  exact ⟨N₀,F,hFA,himage,hinj,hloc,hFlim⟩

end Erdos66SparseRankTransversal
