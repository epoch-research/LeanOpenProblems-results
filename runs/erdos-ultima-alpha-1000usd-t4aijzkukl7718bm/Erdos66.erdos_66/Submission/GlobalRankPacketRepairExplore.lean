import Submission.PredecessorScaleBudgetExplore
import Submission.AssignedIntervalRepairExplore
import Submission.RankProfileGapExplore

/-! A one-target repair of an infinite balanced host, with uniform logarithmic
collateral at every other natural target and with bounded spatial support. -/
namespace Erdos66GlobalRankPacketRepair
open Filter AdditiveCombinatorics Erdos66Counting Erdos66PredecessorCell
  Erdos66OrderedPartialReplacement Erdos66FiniteSwapAlgebra Erdos66Compactness
  Erdos66Explore Erdos66PredecessorCutoffTransfer Erdos66PredecessorScaleBudget
  Erdos66LocatedIntervalPredecessor Erdos66PredecessorRepairParameters
  Erdos66PredecessorPacketRepair Erdos66Fractional Erdos66ReflectionRoundingPatch
  Erdos66Generating Erdos66Rounding Erdos66AssignedIntervalRepair
  Erdos66RankProfileGap Erdos66RankCellExchange Erdos66BracketRankMove
  Erdos66ClampedPrefixContinuation Erdos66BracketOrderedExchange
open scoped Topology Classical
set_option maxHeartbeats 3500000

/-- The finite-set form of the rank-family certificate. -/
lemma rank_assigned_swap_brackets (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (E F : Finset ℕ) (hF : Disjoint (F : Set ℕ) A)
    (hshape : E=F.image (fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)))
    (hinj : Set.InjOn (fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u))
      (F : Set ℕ)) :
    ∀ L, PrefixBrackets profile (swap A E F) L := by
  let assign := fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)
  have hc : Function.Injective (fun u : ↥F ↦ cell profile u.val) := by
    intro u v he
    apply Subtype.ext
    exact hinj u.property v.property (congrArg (rankPoint A (harmonic_brackets_unbounded A hbr)) he)
  have hb := rank_family_brackets profile A profile_nonneg hbr
    (harmonic_brackets_unbounded A hbr) (fun u : ↥F ↦ u.val)
    (fun u ↦ Set.disjoint_left.mp hF u.property)
    (fun u ↦ Erdos66ProfileLowerGap.profile_pos u.val) hc
  have he : Finset.univ.image (fun u : ↥F ↦ assign u.val)=E := by
    rw [hshape]
    ext u
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨v.val,v.property,hv⟩
    · rintro ⟨v,hv,he⟩
      exact ⟨⟨v,hv⟩,he⟩
  have hf : Finset.univ.image (fun u : ↥F ↦ u.val)=F := by
    ext u
    simp
  change ∀ L, PrefixBrackets profile
    (swap A (Finset.univ.image (fun u : ↥F ↦ assign u.val))
      (Finset.univ.image (fun u : ↥F ↦ u.val))) L at hb
  rwa [he,hf] at hb

/-- The target is `16*N`. All modifications are in `[2*N,14*N]`, and all original prefix brackets are retained.
This is one-target feasibility, not simultaneous repair of arbitrary targets. -/
theorem eventually_global_rank_packet_repair (A : Set ℕ) (K C M ε : ℝ)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hM : 0 ≤ M) (hε : 0 < ε)
    (hbr : ∀ L, PrefixBrackets profile A L)
    (henv : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ M*Real.log (N : ℝ) →
      ∃ E F : Finset ℕ, (E : Set ℕ) ⊆ A ∧ Disjoint (F : Set ℕ) A ∧
        E.card = 2*m ∧ F.card = 2*m ∧
        (∀ u ∈ E ∪ F, 2*N ≤ u ∧ u ≤ 14*N) ∧
        (∀ L, PrefixBrackets profile (swap A E F) L) ∧
        sumRep (swap A E F) (16*N) = sumRep A (16*N)+2*m ∧
        ∀ z, z ≠ 16*N →
          |(sumRep (swap A E F) z : ℝ)-sumRep A z| ≤ ε*Real.log ((z : ℝ)+2) := by
  let h : ℕ := ⌈4*M/ε⌉₊+2
  have hh : 2 ≤ h := by dsimp [h]; omega
  have hhscale : 4*M ≤ ε*(h : ℝ) := by
    have hc := Nat.le_ceil (4*M/ε)
    have hc' := (div_le_iff₀ hε).mp hc
    dsimp only [h]
    push_cast
    nlinarith
  let G : ℝ := 100
  let B₀ : ℝ := K+C*((h : ℝ)+6)+1
  let B : ℝ := (4+2*G)*B₀
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hB₀ : 1 ≤ B₀ := by
    dsimp [B₀]
    have hp : 0 ≤ C*((h : ℝ)+6) := by positivity
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨ht,hparams⟩ := eventually_predecessor_selection_small M G B ε hM hG hB hε h
  let t : ℝ := 32*((h : ℝ)+1)/ε
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gap_bounds 1 (by norm_num),hparams,hlog.eventually_ge_atTop (24/ε)]
    with N hgap hp hlε
  obtain ⟨hN,hl,hHN,hHG,hlen⟩ := hgap
  intro m hm
  let H := gapSize 1 N
  let assign := fun u ↦ rankPoint A (harmonic_brackets_unbounded A hbr) (cell profile u)
  have hHG4 : ((4*H : ℕ) : ℝ) ≤ G*Real.sqrt (N : ℝ) := by
    dsimp only [G, H]
    push_cast
    nlinarith
  let X := N^h+1
  let A₀ := cutoff A X
  let V : ℝ := B₀*Real.log (N : ℝ)
  have hNp : 0 < N := by omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNp
  have hXX : 16*N < X := by
    have hpow := Nat.pow_le_pow_right hNp hh
    have hs : 16*N ≤ N^2 := by nlinarith
    dsimp only [X]
    omega
  have hAcap : ∀ z, (sumRep (A₀ : Set ℕ) z : ℝ) ≤ V :=
    finite_profile_envelope A K C hK hC henv N h (by omega) hl
  have hb : 2*Real.sqrt (2*(N : ℝ)*V)+8*H*V ≤ B*Real.sqrt (N : ℝ)*Real.log (N : ℝ) := by
    have hb := degree_budget N (4*H) G B₀ V hNreal.le hG hB₀ hl hHG4 rfl
    push_cast at hb
    dsimp only [B]
    nlinarith only [hb]
  have hepoints (b : Bool) (i : Fin N) :
      4*N ≤ endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i ∧
        endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i ≤ 12*N := by
    have hi := i.isLt
    cases b <;> simp only [endpoint,Bool.false_eq_true,if_false,if_true] <;> omega
  have hgap' (b : Bool) (i : Fin N) :
      endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i <
        assign (endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i)+2*H ∧
      assign (endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i) <
        endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i+2*H := by
    apply harmonic_rank_gap A hbr N H _ hNp hHN (hepoints b i).2
    simpa using hlen
  have hmem (b : Bool) (i : Fin N) :
      assign (endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i) ∈ A₀ := by
    have hu := (hepoints b i).2
    have hg := (hgap' b i).2
    exact mem_cutoff.mpr ⟨by dsimp only [H] at hg; omega,rankPoint_mem A _ _⟩
  have hsmall : ((m : ℝ)^4+16*m^2*H+m*(2*Real.sqrt (2*N*V)+8*H*V))/N +
      ((Finset.range X).card : ℝ)*Real.exp ((m : ℝ)*Real.exp t*(2*Real.sqrt (2*N*V)+8*H*V)/N -
        t*(ε*Real.log (N : ℝ)/16)) < 1 := by
    have hc := hp N m (4*H) (by linarith) hm hHG4
    push_cast at hc
    rw [show 4*(m : ℝ)^2*(4*(H : ℝ))=16*(m : ℝ)^2*(H : ℝ) by ring] at hc
    have hb' := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) m)
    have hfirst := div_le_div_of_nonneg_right (add_le_add_right hb' ((m : ℝ)^4+16*m^2*H)) hNreal.le
    have he := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ (m : ℝ)*Real.exp t by positivity)) hNreal.le
    have he' := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_right he (t*(ε*Real.log (N : ℝ)/16))))
      (show (0 : ℝ) ≤ (N : ℝ)^h+1 by positivity)
    simp only [Finset.card_range,X,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    change _ + ((N : ℝ)^h+1)*Real.exp ((m : ℝ)*Real.exp t*(2*Real.sqrt (2*N*V)+8*H*V)/N -
      t*(ε*Real.log (N : ℝ)/16)) < 1
    dsimp only [t] at *
    linarith
  have hsmall' : ((m : ℝ)^4+8*m^2*(2*H : ℕ)+m*(2*Real.sqrt (2*N*V)+4*(2*H : ℕ)*V))/N +
      ((Finset.range X).card : ℝ)*Real.exp ((m : ℝ)*Real.exp t*(2*Real.sqrt (2*N*V)+4*(2*H : ℕ)*V)/N -
        t*(ε*Real.log (N : ℝ)/16)) < 1 := by
    have he₁ : 8*(m : ℝ)^2*((2*H : ℕ) : ℝ)=16*(m : ℝ)^2*H := by push_cast; ring
    have he₂ : 4*((2*H : ℕ) : ℝ)*V=8*(H : ℝ)*V := by push_cast; ring
    rw [he₁,he₂]
    exact hsmall
  obtain ⟨E,F,hE,hF,hEc,hFc,htarget,hself,hshape,hinjF,hsupp,hcol⟩ :=
    exists_assigned_interval_repair A₀ assign V hAcap (16*N) (4*N) N (2*H) hNp
      (by dsimp only [H]; omega) hmem hgap'
      m (Finset.range X) (ε*Real.log (N : ℝ)/16) t ht hsmall'
  have hs (u : ℕ) (hu : u ∈ E ∪ F) : 2*N ≤ u ∧ u ≤ 14*N := by
    have hp := hsupp u hu
    dsimp only [H] at hp
    omega
  have hEA : (E : Set ℕ) ⊆ A := fun u hu ↦ (mem_cutoff.mp (hE hu)).2
  have hFA : Disjoint (F : Set ℕ) A := by
    apply Set.disjoint_left.mpr
    intro u hu ha
    have hb := (hs u (Finset.mem_union_right E hu)).2
    exact Finset.disjoint_left.mp hF (mem_cutoff.mpr ⟨by omega,ha⟩) hu
  refine ⟨E,F,hEA,hFA,hEc,hFc,hs,?_,?_,?_⟩
  · exact rank_assigned_swap_brackets A hbr E F hFA hshape hinjF
  · rw [cutoff_swap_rep A E F hXX,cutoff_rep A hXX] at htarget
    exact htarget
  · intro z hzn
    by_cases hzlo : z < 2*N
    · have he : sumRep (swap A E F) z = sumRep A z := by
        apply sumRep_congr_below
        intro i hi
        apply swap_mem_outside
        intro hh
        have hh' := (hs i hh).1
        omega
      rw [he,sub_self,abs_zero]
      exact mul_nonneg hε.le (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) z; linarith))
    · by_cases hz : z < X
      · have hc := hcol z (Finset.mem_range.mpr hz) hzn
        rw [cutoff_swap_rep A E F hz,cutoff_rep A hz] at hc
        have hlz : Real.log (N : ℝ) ≤ Real.log ((z : ℝ)+2) :=
          Real.log_le_log hNreal (by exact_mod_cast (show N ≤ z+2 by omega))
        have hlarge : 24 ≤ ε*Real.log (N : ℝ) := by have hh := (div_le_iff₀ hε).mp hlε; nlinarith
        have hmul := mul_le_mul_of_nonneg_left hlz hε.le
        linarith
      · have hc := swap_rep_error A E F (2*m) hEc.le hFc.le z
        have hz' : (N : ℝ)^h ≤ (z : ℝ)+2 := by
          exact_mod_cast (show N^h ≤ z+2 by dsimp only [X] at hz; omega)
        have hlz := Real.log_le_log (pow_pos hNreal h) hz'
        rw [Real.log_pow] at hlz
        have he := mul_le_mul_of_nonneg_left hlz hε.le
        have hh' := mul_le_mul_of_nonneg_right hhscale (show 0 ≤ Real.log (N : ℝ) by linarith)
        push_cast at hc
        nlinarith

end Erdos66GlobalRankPacketRepair
