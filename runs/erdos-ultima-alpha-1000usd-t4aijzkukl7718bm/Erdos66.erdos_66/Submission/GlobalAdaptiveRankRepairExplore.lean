import Submission.AdaptiveAssignedRepairExplore
import Submission.AdaptiveRepairBudgetExplore
import Submission.ShortSupportSwapTailExplore

/-! Coordinated exact-bracket repairs at many comparable centers. The total
packet demand may be o(sqrt(N)/log(N)); all natural targets are controlled. -/
namespace Erdos66GlobalAdaptiveRankRepair
open Filter AdditiveCombinatorics Erdos66Counting Erdos66FiniteSwapAlgebra
  Erdos66OrderedPartialReplacement Erdos66PredecessorCutoffTransfer
  Erdos66PredecessorScaleBudget Erdos66AssignedIntervalRepair
  Erdos66PredecessorPacketRepair Erdos66PredecessorCandidateDegree
  Erdos66AssignedPacketDegree Erdos66IntervalPredecessorRepair
  Erdos66AdaptiveAssignedRepair Erdos66AdaptivePacketAlgebra Erdos66AdaptiveRepairBudget
  Erdos66GlobalRankPacketRepair Erdos66ShortSupportSwapTail
  Erdos66RankProfileGap Erdos66RankCellExchange Erdos66BracketRankMove
  Erdos66ClampedPrefixContinuation Erdos66Fractional Erdos66ProfileLowerGap
  Erdos66Compactness Erdos66Explore
open scoped Classical Topology
set_option maxHeartbeats 5000000

lemma harmonic_rank_gap_thirteen (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (N H u : ℕ) (hH : H ≤ N) (hu : u ≤ 13*N)
    (hlen : 2*Real.sqrt ((16*N+1 : ℕ) : ℝ)<H) :
    u<rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)+2*H ∧
      rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)<u+2*H := by
  have hHp : 0<H := by
    have hn := Real.sqrt_nonneg ((16*N+1 : ℕ) : ℝ)
    have hh : (0 : ℝ)<H := by linarith
    exact_mod_cast hh
  apply rank_assignment_gap profile A profile_nonneg profile_antitone hbr
    (harmonic_brackets_unbounded A hbr) u H hHp
  have hs := Real.sqrt_le_sqrt (show (u+H : ℝ)+1 ≤ ((16*N+1 : ℕ) : ℝ) by
    exact_mod_cast (show u+H+1 ≤ 16*N+1 by omega))
  have hsn := Real.sqrt_nonneg ((16*N+1 : ℕ) : ℝ)
  have hlen' : Real.sqrt ((u+H : ℕ)+1 : ℝ)<H := by push_cast; linarith
  have hh := mul_lt_mul_of_pos_right hlen' (profile_pos (u+H))
  have hl := sqrt_mul_profile_lower (u+H)
  push_cast at hh hl
  exact hl.trans_lt hh

/-- Every prescribed list of centers in [16N,17N] is handled jointly. Repeated
centers specify multiplicities. This remains below square-root total demand;
it does not assume the probabilistic exceptional sets satisfy that bound. -/
theorem uniformly_eventually_global_adaptive_rank_repair
    (K C ε : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hε : 0<ε)
    (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N*Real.log N/Real.sqrt N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Set ℕ,
      (∀ L, PrefixBrackets profile A L) →
      (∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2)) →
      ∀ m : ℕ, (m : ℝ) ≤ S N → ∀ n : ℕ → ℕ,
      (∀ k < m, 16*N ≤ n k ∧ n k ≤ 17*N) →
      ∃ D F : Finset ℕ, (D : Set ℕ) ⊆ A ∧ Disjoint (F : Set ℕ) A ∧
        D.card=2*m ∧ F.card=2*m ∧
        (∀ u∈D∪F, 2*N ≤ u ∧ u ≤ 15*N) ∧
        (∀ L, PrefixBrackets profile (swap A D F) L) ∧
        (∀ z∈(Finset.range m).image n,
          sumRep (swap A D F) z=sumRep A z+2*occurrences n m z) ∧
        ∀ z, z∉(Finset.range m).image n →
          |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  let G : ℝ := 100
  let B₀ : ℝ := K+C*((33 : ℕ)+6)+1
  let B : ℝ := (4+2*G)*B₀
  have hG : 0 ≤ G := by norm_num [G]
  have hB₀ : 1 ≤ B₀ := by dsimp [B₀]; nlinarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨ht,hparams⟩ := eventually_adaptive_budget S hS hdec B G ε hB hG hε 33
  let t : ℝ := 56*((33 : ℕ)+1)/ε
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 32,eventually_gap_bounds 1 (by norm_num),hparams,
    eventually_harmonic_short_support_tail,hlog.eventually_ge_atTop (6/ε)] with N hN hgap hp htail hlε
  obtain ⟨hN16,hl,hHN,hHG,hlen⟩ := hgap
  intro A hbr henv m hm n hn
  let H := gapSize 1 N
  let assign := fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)
  let X := N^33+1
  let A₀ := cutoff A X
  let V : ℝ := B₀*Real.log (N : ℝ)
  let Q : ℝ := B*Real.sqrt (N : ℝ)*Real.log N
  let Cs := (Finset.range m).image n
  let x : Fin N → ℕ := fun i ↦ 4*N+i.val
  have hNp : 0<N := by omega
  have hNreal : (0 : ℝ)<N := by exact_mod_cast hNp
  have hXX : 17*N<X := by
    have hh := Nat.pow_le_pow_right hNp (show 2 ≤ 33 by norm_num)
    have hs : 17*N ≤ N^2 := by nlinarith
    dsimp only [X]
    omega
  have hHG4 : ((4*H : ℕ) : ℝ) ≤ G*Real.sqrt (N : ℝ) := by
    dsimp only [G,H]
    push_cast
    nlinarith
  have hAcap : ∀ z, (sumRep (A₀ : Set ℕ) z : ℝ) ≤ V :=
    finite_profile_envelope A K C hK hC henv N 33 (by omega) hl
  have hb : 2*Real.sqrt (2*(N : ℝ)*V)+8*H*V ≤ Q := by
    have hh := degree_budget N (4*H) G B₀ V hNreal.le hG hB₀ hl hHG4 rfl
    push_cast at hh
    dsimp only [Q,B]
    nlinarith only [hh]
  have hx : Function.Injective x := by
    intro i j he
    apply Fin.ext
    dsimp only [x] at he
    omega
  have hepoints (k : ℕ) (hk : k < m) (b : Bool) (i : Fin N) :
      4*N ≤ endpoint (n k) x b i ∧ endpoint (n k) x b i ≤ 13*N := by
    have hi := i.isLt
    have hnk := hn k hk
    cases b <;> simp only [endpoint,x,Bool.false_eq_true,if_false,if_true] <;> omega
  have hhalf (k : ℕ) (hk : k < m) (i : Fin N) : 2*x i<n k := by
    have hi := i.isLt
    have hnk := hn k hk
    dsimp only [x]
    omega
  have hinj (k : ℕ) (hk : k < m) (b : Bool) : Function.Injective (endpoint (n k) x b) :=
    endpoint_injective (n k) x hx (fun i ↦ by have := hhalf k hk i; omega) b
  have hgap' (k : ℕ) (hk : k < m) (b : Bool) (i : Fin N) :
      endpoint (n k) x b i<assign (endpoint (n k) x b i)+2*H ∧
        assign (endpoint (n k) x b i)<endpoint (n k) x b i+2*H := by
    apply harmonic_rank_gap_thirteen A hbr N H _ hHN (hepoints k hk b i).2
    simpa using hlen
  have hmem (k : ℕ) (hk : k < m) (b : Bool) (i : Fin N) : assign (endpoint (n k) x b i)∈A₀ := by
    have hu := (hepoints k hk b i).2
    have hg := (hgap' k hk b i).2
    exact mem_cutoff.mpr ⟨by dsimp only [H] at hg; omega,rankPoint_mem A _ _⟩
  have hsep (k : ℕ) (hk : k < m) (i : Fin N) :
      Function.Injective (fun b ↦ assign (endpoint (n k) x b i)) := by
    apply assigned_endpoints_separated assign (n k) x (2*H) _ (hgap' k hk) i
    intro a
    have ha := a.isLt
    have hn' := hn k hk
    dsimp only [x,H]
    omega
  have hfiber (k : ℕ) (hk : k < m) (b : Bool) (r : ℕ) :
      (Finset.univ.filter (fun a ↦ assign (endpoint (n k) x b a)=r)).card ≤ 4*H := by
    have hh := nearby_assignment_fiber assign (endpoint (n k) x b) (hinj k hk b) (2*H) (hgap' k hk b) r
    omega
  have hdeg (k : ℕ) (hk : k < m) :
      ((Erdos66AssignedPacketRepair.badChoices A₀ assign (n k) x).card : ℝ) ≤ Q ∧
      ∀ z, ((Erdos66AssignedPacketRepair.swapHits A₀ assign (n k) x z).card : ℝ) ≤ Q := by
    let start : Bool → ℕ := fun b ↦ if b then n k+1-(4*N+N) else 4*N
    have hwindow (b : Bool) (i : Fin N) : start b ≤ endpoint (n k) x b i ∧ endpoint (n k) x b i<start b+N := by
      have hi := i.isLt
      have hn' := hn k hk
      cases b <;> simp only [start,endpoint,x,Bool.false_eq_true,if_false,if_true] <;> omega
    have hh := assigned_candidate_degrees A₀ assign (n k) x (4*H) N start (Real.sqrt (2*N*V))
      (hinj k hk) hwindow (fun L ↦ natural_window_bound A₀ V hAcap L N) (hmem k hk) (hfiber k hk)
    have hd (z : ℕ) : 2*Real.sqrt (2*(N : ℝ)*V)+2*(4*H : ℕ)*sumRep (A₀ : Set ℕ) z ≤ Q := by
      have hc := mul_le_mul_of_nonneg_left (hAcap z) (show (0 : ℝ) ≤ 8*H by positivity)
      push_cast
      linarith
    exact ⟨hh.1.trans (hd (n k)),fun z ↦ (hh.2 z).trans (hd z)⟩
  have hCs : Cs.card ≤ m := (Finset.card_image_le).trans_eq (Finset.card_range m)
  have hcent (k : ℕ) (hk : k < m) : n k∈Cs := Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr hk,rfl⟩
  obtain ⟨hav,hsmall⟩ := hp m (4*H) Cs.card hm hHG4 hCs
  have hsmall' : (∑ _z∈Finset.range X,
      Real.exp ((m : ℝ)*(Real.exp t*(Q+4*m+2)/((N : ℝ)/2))-t*(ε*Real.log N/28)))<1 := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,X,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    convert hsmall using 1
    congr 1
    congr 1
    dsimp only [t,Q]
    ring
  obtain ⟨D,F,hD,hF,hDc,hFc,hshape,hiF,hpoints,hcenter,hcol⟩ :=
    exists_adaptive_assigned_repair A₀ Cs assign n (fun _ ↦ x) m (4*H) hcent
      hinj hhalf hmem hsep hfiber Q Q (fun _ ↦ Q) (fun k hk ↦ (hdeg k hk).1)
      (fun k hk _ _ ↦ (hdeg k hk).2 _) (Finset.range X) ((N : ℝ)/2) t
      (fun _ ↦ ε*Real.log N/28) (by positivity) ht (fun k hk _ _ ↦ (hdeg k hk).2 _) (by simpa only [Fintype.card_fin] using hav) hsmall'
  have hFp (u : ℕ) (hu : u∈F) : 4*N ≤ u ∧ u ≤ 13*N := by
    obtain ⟨k,hk,a,ha⟩ := hpoints u hu
    obtain ⟨b,rfl⟩ := (mem_packet_iff (n k) x a u).mp ha
    exact hepoints k hk b a
  have hs (u : ℕ) (hu : u∈D∪F) : 2*N ≤ u ∧ u ≤ 15*N := by
    rcases Finset.mem_union.mp hu with hu | hu
    · rw [hshape] at hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      have hvb := hFp v hv
      obtain ⟨k,hk,a,ha⟩ := hpoints v hv
      obtain ⟨b,rfl⟩ := (mem_packet_iff (n k) x a v).mp ha
      have hg := hgap' k hk b a
      dsimp only [H] at hg
      omega
    · have hh := hFp u hu
      omega
  have hDA : (D : Set ℕ) ⊆ A := fun u hu ↦ (mem_cutoff.mp (hD hu)).2
  have hFA : Disjoint (F : Set ℕ) A := by
    apply Set.disjoint_left.mpr
    intro u hu ha
    have hb' := (hFp u hu).2
    exact Finset.disjoint_left.mp hF (mem_cutoff.mpr ⟨by omega,ha⟩) hu
  refine ⟨D,F,hDA,hFA,hDc,hFc,hs,rank_assigned_swap_brackets A hbr D F hFA hshape hiF,?_,?_⟩
  · intro z hz
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hz
    have hn' := (hn k (Finset.mem_range.mp hk)).2
    have hc := hcenter (n k) (hcent k (Finset.mem_range.mp hk))
    rw [cutoff_swap_rep A D F (by omega),cutoff_rep A (by omega)] at hc
    exact hc
  · intro z hzC
    by_cases hzlo : z<2*N
    · have he : sumRep (swap A D F) z=sumRep A z := by
        apply sumRep_congr_below
        intro i hi
        apply swap_mem_outside
        intro hm'
        have hh := (hs i hm').1
        omega
      rw [he,sub_self,abs_zero]
      exact mul_nonneg hε.le (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) z; linarith))
    · have hlz : Real.log (N : ℝ) ≤ Real.log ((z : ℝ)+2) :=
        Real.log_le_log hNreal (by exact_mod_cast (show N ≤ z+2 by omega))
      have hεlog := mul_le_mul_of_nonneg_left hlz hε.le
      by_cases hz : z<X
      · have hh := hcol z (Finset.mem_range.mpr hz) hzC
        rw [cutoff_swap_rep A D F hz,cutoff_rep A hz] at hh
        nlinarith
      · have hh := htail A hbr D F hDA hFA (fun u hu ↦ (hs u hu).2) z (by dsimp only [X] at hz; omega)
        have h6 : 6 ≤ ε*Real.log (N : ℝ) := by have := (div_le_iff₀ hε).mp hlε; nlinarith
        linarith

/-- The fixed-host version of the uniform coordinated repair theorem. -/
theorem eventually_global_adaptive_rank_repair
    (A : Set ℕ) (K C ε : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hε : 0<ε)
    (hbr : ∀ L, PrefixBrackets profile A L)
    (henv : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2))
    (S : ℕ → ℝ) (hS : ∀ᶠ N in atTop, 0 ≤ S N)
    (hdec : Tendsto (fun N : ℕ ↦ S N*Real.log N/Real.sqrt N) atTop (𝓝 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ S N → ∀ n : ℕ → ℕ,
      (∀ k < m, 16*N ≤ n k ∧ n k ≤ 17*N) →
      ∃ D F : Finset ℕ, (D : Set ℕ) ⊆ A ∧ Disjoint (F : Set ℕ) A ∧
        D.card=2*m ∧ F.card=2*m ∧
        (∀ u∈D∪F, 2*N ≤ u ∧ u ≤ 15*N) ∧
        (∀ L, PrefixBrackets profile (swap A D F) L) ∧
        (∀ z∈(Finset.range m).image n,
          sumRep (swap A D F) z=sumRep A z+2*occurrences n m z) ∧
        ∀ z, z∉(Finset.range m).image n →
          |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  filter_upwards [uniformly_eventually_global_adaptive_rank_repair K C ε hK hC hε S hS hdec] with N hN
  exact hN A hbr henv

/-- In particular, any fixed sub-square-root power of packet requests is
admissible. The list and its repeated centers may be chosen after N. -/
theorem eventually_global_adaptive_rank_power
    (A : Set ℕ) (K C ε a : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hε : 0<ε) (ha : a<1/2)
    (hbr : ∀ L, PrefixBrackets profile A L)
    (henv : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ (N : ℝ)^a → ∀ n : ℕ → ℕ,
      (∀ k < m, 16*N ≤ n k ∧ n k ≤ 17*N) →
      ∃ D F : Finset ℕ, (D : Set ℕ) ⊆ A ∧ Disjoint (F : Set ℕ) A ∧
        D.card=2*m ∧ F.card=2*m ∧
        (∀ u∈D∪F, 2*N ≤ u ∧ u ≤ 15*N) ∧
        (∀ L, PrefixBrackets profile (swap A D F) L) ∧
        (∀ z∈(Finset.range m).image n,
          sumRep (swap A D F) z=sumRep A z+2*occurrences n m z) ∧
        ∀ z, z∉(Finset.range m).image n →
          |(sumRep (swap A D F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  exact eventually_global_adaptive_rank_repair A K C ε hK hC hε hbr henv
    (fun N ↦ (N : ℝ)^a) (Eventually.of_forall (fun N ↦ Real.rpow_nonneg (Nat.cast_nonneg N) a))
    (power_demand_decay a ha)

end Erdos66GlobalAdaptiveRankRepair
