import Submission.BracketWindowOccupancyExplore
import Submission.RankRestorationAlgebraExplore
import Submission.WideRankRestorationBudgetExplore
import Submission.AggregatedRankRestorationSelectionExplore
import Submission.LogCellWindowBudgetExplore
import Submission.ShortSupportSwapTailExplore
import Submission.CentralTripleDeletionExplore

/-! Global rank restoration from exact brackets alone. No representation
envelope is assumed, either globally or on the finite test horizon. -/
namespace Erdos66WideBracketOnlyRestoration
open Filter AdditiveCombinatorics Erdos66Counting Erdos66NatPairAlgebra
  Erdos66FiniteSwapAlgebra Erdos66OrderedPartialReplacement
  Erdos66CentralTripleCounts Erdos66CentralTripleDeletion
  Erdos66RankRestorationSelection Erdos66RankRestorationAlgebra
  Erdos66WideRankRestorationBudget Erdos66WideRankCellBudget
  Erdos66AggregatedRankRestorationSelection Erdos66AdaptiveSingletonAlgebra
  Erdos66LogCellWindowBudget Erdos66RankCellWindow Erdos66RankProfileGap
  Erdos66BracketRankMove Erdos66RankCellExchange Erdos66ClampedPrefixContinuation
  Erdos66Fractional Erdos66PredecessorScaleBudget Erdos66PredecessorCutoffTransfer
  Erdos66PredecessorCandidateDegree Erdos66IntervalPredecessorRepair
  Erdos66ShortSupportSwapTail Erdos66Compactness Erdos66Explore Erdos66BracketWindowOccupancy
open scoped Classical Topology
set_option maxHeartbeats 6000000
set_option linter.style.existsImplication false

/-- The restoration cost is measured from the deleted core, not the original
host. The deletion loss can be estimated separately for an entire batch. -/
theorem uniformly_eventually_rank_restoration
    (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N*(Real.log N)^2/Real.sqrt N) atTop (𝓝 0))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Set ℕ,
      (∀ L, PrefixBrackets profile A L) →
      ∀ D : Finset ℕ, (D : Set ℕ) ⊆ A →
      (∀ d∈D, 2*N ≤ d ∧ d ≤ 5*N) → (D.card : ℝ) ≤ S N →
      ∃ F : Finset ℕ, F.card=D.card ∧ Disjoint (F : Set ℕ) A ∧
        (∀ u∈D∪F, N ≤ u ∧ u ≤ 6*N) ∧
        (∀ L, PrefixBrackets profile (swap A D F) L) ∧
        ∀ z, sumRep (A\(D : Set ℕ)) z ≤ sumRep (swap A D F) z ∧
          (sumRep (swap A D F) z : ℝ)-sumRep (A\(D : Set ℕ)) z ≤ ε*Real.log ((z : ℝ)+2) := by
  obtain ⟨ht,hparams⟩ := eventually_wide_rank_budget S hS hdec ε hε 33
  let t : ℝ := 20*((33 : ℕ)+1)/ε
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 32,hlog.eventually_ge_atTop 1,eventually_wide_window,
    hparams,eventually_harmonic_short_support_tail,hlog.eventually_ge_atTop (6/ε)]
    with N hN hl hwm hp htail hl6
  intro A hbr D hDA hDloc hm
  let w := wideWindow N
  let m := D.card
  let e : Fin m ↪o ℕ := D.orderEmbOfFin rfl
  let d : ℕ → ℕ := fun k ↦ if hk : k < m then e ⟨k,hk⟩ else 0
  let X := N^33+1
  let A₀ := cutoff A X
  have hNp : 0<N := by omega
  have hNr : (0 : ℝ)<N := by exact_mod_cast hNp
  have hXX : 6*N<X := by
    have hp' := Nat.pow_le_pow_right hNp (show 2 ≤ 33 by norm_num)
    have hh : 6*N ≤ N^2 := by nlinarith
    dsimp only [X]
    omega
  have hw : 0<w := hwm.1
  have hwN : w ≤ N := hwm.2.1
  have hwp : (0 : ℝ)<w := by exact_mod_cast hw
  have hdmem (k : ℕ) (hk : k < m) : d k∈D := by
    dsimp only [d]
    rw [dif_pos hk]
    exact Finset.orderEmbOfFin_mem D rfl _
  have hdimage : (Finset.range m).image d=D := by
    apply Finset.Subset.antisymm
    · intro u hu
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hu
      exact hdmem k (Finset.mem_range.mp hk)
    · intro u hu
      have he : Finset.univ.image e=D := Finset.image_orderEmbOfFin_univ _ _
      rw [←he] at hu
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
      refine Finset.mem_image.mpr ⟨i.val,Finset.mem_range.mpr i.isLt,?_⟩
      simp [d,i.isLt]
  have hdinj : Set.InjOn d (Finset.range m : Set ℕ) := by
    intro i hi j hj he
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    simp only [d,dif_pos hi',dif_pos hj'] at he
    exact congrArg Fin.val (e.injective he)
  have hdloc (u : ℕ) (hu : u∈D) : 2*N ≤ u ∧ u ≤ 5*N ∧ w ≤ u := by
    have hh := hDloc u hu
    omega
  have hwin (k : ℕ) : ∃ L : ℕ, k < m →
      ∀ i : Fin w, N ≤ L+i.val ∧ L+i.val ≤ 6*N ∧ 0<2*(L+i.val) ∧
        rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile (L+i.val))=d k := by
    by_cases hk : k < m
    · have hdk := hdmem k hk
      have hdl := hdloc (d k) hdk
      have hmass : (w : ℝ)*profile (d k-w) ≤ 1/4 :=
        (mul_le_mul_of_nonneg_left (profile_antitone (show N ≤ d k-w by omega)) (Nat.cast_nonneg w)).trans hwm.2.2.1
      obtain ⟨L,hLlo,hLhi,hLi⟩ := exists_rank_cell_window profile A profile_nonneg profile_antitone hbr
        (harmonic_brackets_unbounded A hbr) (d k) w (hDA hdk) hdl.2.2 hmass
      refine ⟨L,fun _ i ↦ ?_⟩
      have hb := hLi i
      exact ⟨by omega,by omega,by omega,hb.2.2.2.2⟩
    · exact ⟨0,fun h ↦ (hk h).elim⟩
  choose L hL using hwin
  let f (k : ℕ) (i : Fin w) := L k+i.val
  have hfinj (k : ℕ) (_hk : k < m) : Function.Injective (f k) := by
    intro i j he
    apply Fin.ext
    dsimp only [f] at he
    omega
  have hcut (k : ℕ) (hk : k < m) (i : Fin w) : f k i∈A ↔ f k i∈A₀ := by
    have hb := (hL k hk i).2.1
    simp only [A₀,mem_cutoff,show f k i<X by dsimp only [f]; omega,true_and]
  have hwindow (k : ℕ) (i : Fin w) : L k ≤ f k i ∧ f k i<L k+w := by
    have hi := i.isLt
    dsimp only [f]
    omega
  have hB (k : ℕ) (hk : k < m) : ((Finset.univ.filter (fun a ↦ f k a∈A₀)).card : ℝ) ≤ 3 := by
    have hsel : Finset.univ.filter (fun i : Fin w ↦ f k i∈A₀) ⊆
        Finset.univ.filter (fun i : Fin w ↦ f k i∈A) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_cutoff.mp (Finset.mem_filter.mp hi).2).2⟩
    have hh : ((Finset.univ.filter (fun a ↦ f k a∈A₀)).card : ℝ) ≤
        (Erdos66ReflectionRoundingPatch.intervalPart A (L k) (L k+w)).card := by
      exact_mod_cast (Finset.card_le_card hsel).trans
        (interval_old_card A (f k) (hfinj k hk) (L k) w (hwindow k))
    have hNL : N ≤ L k := by simpa using (hL k hk ⟨0,hw⟩).1
    have hc := antitone_window_count profile A 1 profile_antitone
      (brackets_count_discrepancy profile A hbr) (L k) w
    have hm := mul_le_mul_of_nonneg_left (profile_antitone hNL) (Nat.cast_nonneg w)
    have hmass : (w : ℝ)*profile N ≤ 1/4 := hwm.2.2.1
    linarith
  obtain ⟨hbudget,hsmall⟩ := hp m hm
  have hsmall' : (∑ _z∈Finset.range X,
      Real.exp (Real.exp t*((∑ i∈Finset.range (m*w), profile i)+5*m)/((w : ℝ)/2)-
        t*(ε*Real.log N/10)))<1 := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,X,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    exact hsmall
  obtain ⟨F,hFc,hAF₀,hFA,hpoints,hbr',hload⟩ := exists_aggregated_rank_restoration A hbr A₀ D
    (fun u hu ↦ (mem_cutoff.mp hu).2) w m d L hdimage hdinj
    (fun k hk a ↦ (hL k hk a).2.2.2) hcut 3 hB (Finset.range X) ((w : ℝ)/2) t
    (fun _ ↦ ε*Real.log N/10) (by positivity) ht hbudget hsmall'
  have hs (u : ℕ) (hu : u∈D∪F) : N ≤ u ∧ u ≤ 6*N := by
    rcases Finset.mem_union.mp hu with hu | hu
    · have hh := hdloc u hu
      omega
    · obtain ⟨k,hk,a,rfl⟩ := hpoints u hu
      exact ⟨(hL k hk a).1,(hL k hk a).2.1⟩
  refine ⟨F,hFc,hFA,hs,hbr',?_⟩
  intro z
  have hmon : sumRep (A\(D : Set ℕ)) z ≤ sumRep (swap A D F) z :=
    sumRep_mono (show A\(D : Set ℕ) ⊆ swap A D F from Set.subset_union_left) z
  refine ⟨hmon,?_⟩
  by_cases hzlo : z<N
  · have he : sumRep (swap A D F) z=sumRep (A\(D : Set ℕ)) z := by
      apply sumRep_congr_below
      intro i hi
      have hFi : i∉F := fun hh ↦ by have := (hs i (Finset.mem_union_right _ hh)).1; omega
      simp only [swap,Set.mem_union,Finset.mem_coe,hFi,or_false]
    rw [he,sub_self]
    exact mul_nonneg hε.le (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) z; linarith))
  · have hlz : Real.log (N : ℝ) ≤ Real.log ((z : ℝ)+2) :=
      Real.log_le_log hNr (by exact_mod_cast (show N ≤ z+2 by omega))
    have hεlog := mul_le_mul_of_nonneg_left hlz hε.le
    by_cases hz : z<X
    · have hh := (swapped_insertion_bound A₀ D F hAF₀ z).trans_lt
        (hload z (Finset.mem_range.mpr hz))
      have hcore : sumRep ((A₀\D : Finset ℕ) : Set ℕ) z=sumRep (A\(D : Set ℕ)) z := by
        simpa only [swapped,Finset.union_empty,swap,Finset.coe_empty,Set.union_empty] using
          (cutoff_swap_rep A D ∅ hz)
      rw [cutoff_swap_rep A D F hz,hcore] at hh
      have hpos : 0 ≤ ε*Real.log N := mul_nonneg hε.le (by linarith)
      linarith
    · have htail' := htail A hbr ∅ F (by simp) hFA
        (fun u hu ↦ by
          have huF : u∈F := by simpa only [Finset.empty_union] using hu
          have := (hs u (Finset.mem_union_right _ huF)).2
          omega) z (by dsimp only [X] at hz; omega)
      simp only [swap,Finset.coe_empty,Set.diff_empty] at htail'
      have hcomp := swap_insertion_compare A D F hFA z
      have hcompR : (sumRep (swap A D F) z : ℝ)+sumRep A z ≤
          sumRep (A\(D : Set ℕ)) z+sumRep (A∪(F : Set ℕ)) z := by exact_mod_cast hcomp
      have h6 : 6 ≤ ε*Real.log N := by
        have hh := (div_le_iff₀ hε).mp hl6
        nlinarith
      have hb := (abs_le.mp htail').2
      linarith

/-- In particular, every prescribed deletion demand `N^a` with `a<1/2`
can be restored with a uniform sublogarithmic insertion budget. -/
theorem eventually_power_rank_restoration (a ε : ℝ) (ha : a<1/2) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Set ℕ,
      (∀ L, PrefixBrackets profile A L) →
      ∀ D : Finset ℕ, (D : Set ℕ) ⊆ A →
      (∀ d∈D, 2*N ≤ d ∧ d ≤ 5*N) → (D.card : ℝ) ≤ (N : ℝ)^a →
      ∃ F : Finset ℕ, F.card=D.card ∧ Disjoint (F : Set ℕ) A ∧
        (∀ u∈D∪F, N ≤ u ∧ u ≤ 6*N) ∧
        (∀ L, PrefixBrackets profile (swap A D F) L) ∧
        ∀ z, sumRep (A\(D : Set ℕ)) z ≤ sumRep (swap A D F) z ∧
          (sumRep (swap A D F) z : ℝ)-sumRep (A\(D : Set ℕ)) z ≤ ε*Real.log ((z : ℝ)+2) :=
  uniformly_eventually_rank_restoration (fun N ↦ (N : ℝ)^a)
    (Filter.Eventually.of_forall (fun N ↦ Real.rpow_nonneg (Nat.cast_nonneg N) a))
    (Erdos66WideRankRestorationBudget.power_demand_decay a ha) ε hε

end Erdos66WideBracketOnlyRestoration
