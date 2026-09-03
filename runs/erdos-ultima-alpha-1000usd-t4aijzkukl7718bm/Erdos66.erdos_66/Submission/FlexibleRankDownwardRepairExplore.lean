import Submission.PrescribedRankRelocationExplore
import Submission.LogCellWindowBudgetExplore
import Submission.ShortSupportSwapTailExplore
import Submission.CentralTripleDeletionExplore

/-! Exact-bracket downward repairs with an explicit central-triple certificate.
The central boundary cutoff is independent of the relocation scale. -/
namespace Erdos66FlexibleRankDownwardRepair
open Filter AdditiveCombinatorics Erdos66Counting Erdos66NatPairAlgebra
  Erdos66FiniteSwapAlgebra Erdos66OrderedPartialReplacement
  Erdos66CentralTripleCounts Erdos66CentralTripleDeletion
  Erdos66PrescribedRankRelocation Erdos66AdaptiveSingletonAlgebra
  Erdos66LogCellWindowBudget Erdos66RankCellWindow Erdos66RankProfileGap
  Erdos66BracketRankMove Erdos66RankCellExchange Erdos66ClampedPrefixContinuation
  Erdos66Fractional Erdos66PredecessorScaleBudget Erdos66PredecessorCutoffTransfer
  Erdos66PredecessorCandidateDegree Erdos66IntervalPredecessorRepair
  Erdos66ShortSupportSwapTail Erdos66Compactness Erdos66Explore
open scoped Classical Topology
set_option maxHeartbeats 6000000
set_option linter.style.existsImplication false

/-- The threshold is uniform over all hosts with the indicated envelope and
brackets. The triple bound is checked for the actual current host and center. -/
theorem uniformly_eventually_downward_rank_repair
    (K C M ε : ℝ) (R : ℕ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hM : 0 ≤ M) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Set ℕ,
      (∀ L, PrefixBrackets profile A L) →
      (∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2)) →
      ∀ T n : ℕ, 4*N ≤ n → n ≤ 5*N →
      (∀ z, z ≤ N^33 → n≠z → (fiber A T n z).card ≤ R) →
      ∀ D : Finset ℕ, D ⊆ endpoints A T n → (D.card : ℝ) ≤ M*Real.log N →
      (∀ d∈D, n+2*windowSize N<2*d) →
      ∃ F : Finset ℕ, F.card=D.card ∧ Disjoint (F : Set ℕ) A ∧
        (∀ u∈D∪F, N ≤ u ∧ u ≤ 6*N) ∧
        (∀ L, PrefixBrackets profile (swap A D F) L) ∧
        sumRep A n=sumRep (swap A D F) n+2*D.card ∧
        ∀ z, z≠n → |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  let B : ℝ := K+C*((33 : ℕ)+6)+1
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  obtain ⟨ht,hparams⟩ := eventually_singleton_window_budget M B ε hM hB hε 33
  let t : ℝ := 20*((33 : ℕ)+1)/ε
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 32,hlog.eventually_ge_atTop 1,eventually_window_mass,
    hparams,eventually_harmonic_short_support_tail,hlog.eventually_ge_atTop ((4*(R : ℝ)+6)/ε)]
    with N hN hl hwm hp htail hlR
  intro A hbr henv T n hnlo hnhi htr D hDE hm hmargin
  let w := windowSize N
  let m := D.card
  let e : Fin m ↪o ℕ := D.orderEmbOfFin rfl
  let d : ℕ → ℕ := fun k ↦ if hk : k < m then e ⟨k,hk⟩ else 0
  let X := N^33+1
  let A₀ := cutoff A X
  let V : ℝ := B*Real.log (N : ℝ)
  let Q : ℝ := 2*B*(Real.log N)^5
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
    have he := mem_endpoints.mp (hDE hu)
    have hh := hmargin u hu
    omega
  have hD₀ : D ⊆ A₀ := by
    intro u hu
    have he := mem_endpoints.mp (hDE hu)
    exact mem_cutoff.mpr ⟨by omega,he.2.2.2.1⟩
  have hpartner : pairs D A₀ n=D.card := by
    apply pairs_eq_card_of_partner
    intro u hu
    have he := mem_endpoints.mp (hDE hu)
    exact ⟨he.1,mem_cutoff.mpr ⟨by omega,he.2.2.2.2⟩⟩
  have hwin (k : ℕ) : ∃ L : ℕ, k < m →
      ∀ i : Fin w, N ≤ L+i.val ∧ L+i.val ≤ 6*N ∧ n<2*(L+i.val) ∧
        rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile (L+i.val))=d k := by
    by_cases hk : k < m
    · have hdk := hdmem k hk
      have hdl := hdloc (d k) hdk
      have hde := mem_endpoints.mp (hDE hdk)
      have hmar := hmargin (d k) hdk
      have hmass : (w : ℝ)*profile (d k-w) ≤ 1/4 :=
        (mul_le_mul_of_nonneg_left (profile_antitone (show N ≤ d k-w by omega)) (Nat.cast_nonneg w)).trans hwm.2.2
      obtain ⟨L,hLlo,hLhi,hLi⟩ := exists_rank_cell_window profile A profile_nonneg profile_antitone hbr
        (harmonic_brackets_unbounded A hbr) (d k) w hde.2.2.2.1 hdl.2.2 hmass
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
  have hAcap : ∀ z, (sumRep (A₀ : Set ℕ) z : ℝ) ≤ V :=
    finite_profile_envelope A K C hK hC henv N 33 (by omega) hl
  have hQ : Real.sqrt (2*(w : ℝ)*V) ≤ Q := window_degree_bound N B hB hl
  have hlocal (a : ℕ) :
      ((Erdos66ReflectionRoundingPatch.intervalPart (A₀ : Set ℕ) a (a+w)).card : ℝ) ≤ Q :=
    (natural_window_bound A₀ V hAcap a w).trans hQ
  have hwindow (k : ℕ) (i : Fin w) : L k ≤ f k i ∧ f k i<L k+w := by
    have hi := i.isLt
    dsimp only [f]
    omega
  have hB₀ (k : ℕ) (hk : k < m) : ((Finset.univ.filter (fun a ↦ f k a∈A₀)).card : ℝ) ≤ Q := by
    have hh : ((Finset.univ.filter (fun a ↦ f k a∈A₀)).card : ℝ) ≤
        (Erdos66ReflectionRoundingPatch.intervalPart (A₀ : Set ℕ) (L k) (L k+w)).card := by
      exact_mod_cast interval_old_card (A₀ : Set ℕ) (f k) (hfinj k hk) (L k) w (hwindow k)
    exact hh.trans (hlocal _)
  have hKz (k : ℕ) (hk : k < m) (z : ℕ) : ((partnerChoices A₀ (f k) z).card : ℝ) ≤ Q := by
    have hh : ((partnerChoices A₀ (f k) z).card : ℝ) ≤
        (Erdos66ReflectionRoundingPatch.intervalPart (A₀ : Set ℕ) (z+1-(L k+w)) (z+1-(L k+w)+w)).card := by
      exact_mod_cast interval_hit_card (A₀ : Set ℕ) (f k) (hfinj k hk) (L k) w z (hwindow k)
    exact hh.trans (hlocal _)
  obtain ⟨hbudget,hsmall⟩ := hp m hm
  have hbudget' : (w : ℝ)/2+Q+Q ≤ Fintype.card (Fin w) := by
    rw [Fintype.card_fin]
    dsimp only [Q,w]
    linarith
  have hsmall' : (∑ _z∈Finset.range X,
      Real.exp ((m : ℝ)*(Real.exp t*(Q+m+1)/((w : ℝ)/2))-t*(ε*Real.log N/10)))<1 := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,X,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    exact hsmall
  obtain ⟨F,hFc,hAF₀,hFA,hpoints,hbr',htarget,hcol⟩ := exists_prescribed_rank_relocation A hbr A₀ D n m d f
    hdimage hdinj hD₀ (fun u hu ↦ by have := hmargin u hu; omega) hpartner hfinj
    (fun k hk a ↦ (hL k hk a).2.2.1) (fun k hk a ↦ (hL k hk a).2.2.2)
    hcut Q Q hB₀ (fun k hk ↦ hKz k hk n) (Finset.range X) ((w : ℝ)/2) t (fun _ ↦ Q)
    (fun _ ↦ ε*Real.log N/10) (by positivity) ht (fun k hk z _ ↦ hKz k hk z) hbudget' hsmall'
  have hDA : (D : Set ℕ) ⊆ A := fun u hu ↦ (mem_endpoints.mp (hDE hu)).2.2.2.1
  have hs (u : ℕ) (hu : u∈D∪F) : N ≤ u ∧ u ≤ 6*N := by
    rcases Finset.mem_union.mp hu with hu | hu
    · have hh := hdloc u hu
      omega
    · obtain ⟨k,hk,a,rfl⟩ := hpoints u hu
      exact ⟨(hL k hk a).1,(hL k hk a).2.1⟩
  refine ⟨F,hFc,hFA,hs,hbr',?_,?_⟩
  · rw [cutoff_rep A (by omega),cutoff_swap_rep A D F (by omega)] at htarget
    exact htarget
  · intro z hzn
    by_cases hzlo : z<N
    · have he : sumRep (swap A D F) z=sumRep A z := by
        apply sumRep_congr_below
        intro i hi
        apply swap_mem_outside
        intro hh
        have hh' := (hs i hh).1
        omega
      rw [he,sub_self,abs_zero]
      exact mul_nonneg hε.le (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) z; linarith))
    · have hlz : Real.log (N : ℝ) ≤ Real.log ((z : ℝ)+2) :=
        Real.log_le_log hNr (by exact_mod_cast (show N ≤ z+2 by omega))
      have hεlog := mul_le_mul_of_nonneg_left hlz hε.le
      have hlarge : 4*(R : ℝ)+6 ≤ ε*Real.log N := by
        have hh := (div_le_iff₀ hε).mp hlR
        nlinarith
      by_cases hz : z<X
      · have hpair : pairs D A₀ z ≤ (fiber A T n z).card := by
          rw [pairs_eq_filter]
          apply Finset.card_le_card
          intro u hu
          obtain ⟨hu,huz,huA⟩ := Finset.mem_filter.mp hu
          have he := mem_endpoints.mp (hDE hu)
          exact mem_fiber.mpr ⟨he.1,he.2.1,he.2.2.1,huz,he.2.2.2.1,he.2.2.2.2,(mem_cutoff.mp huA).2⟩
        have hbound := hpair.trans (htr z (by dsimp only [X] at hz; omega) (Ne.symm hzn))
        have hr : (pairs D A₀ z : ℝ) ≤ R := by exact_mod_cast hbound
        have hh := hcol z (Finset.mem_range.mpr hz)
        rw [cutoff_swap_rep A D F hz,cutoff_rep A hz] at hh
        nlinarith
      · have hh := htail A hbr D F hDA hFA (fun u hu ↦ by have := (hs u hu).2; omega) z
          (by dsimp only [X] at hz; omega)
        linarith

end Erdos66FlexibleRankDownwardRepair
