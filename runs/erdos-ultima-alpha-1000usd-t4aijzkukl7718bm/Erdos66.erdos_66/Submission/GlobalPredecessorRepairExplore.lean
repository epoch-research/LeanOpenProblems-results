import Submission.PredecessorScaleBudgetExplore

/-! A one-target repair of an infinite balanced host, with uniform logarithmic
collateral at every other natural target and with bounded spatial support. -/
namespace Erdos66GlobalPredecessorRepair
open Filter AdditiveCombinatorics Erdos66Counting Erdos66PredecessorCell
  Erdos66OrderedPartialReplacement Erdos66FiniteSwapAlgebra Erdos66Compactness
  Erdos66Explore Erdos66PredecessorCutoffTransfer Erdos66PredecessorScaleBudget
  Erdos66LocatedIntervalPredecessor Erdos66PredecessorRepairParameters
  Erdos66PredecessorPacketRepair Erdos66Fractional Erdos66ReflectionRoundingPatch
  Erdos66Generating Erdos66Rounding
open scoped Topology Classical
set_option maxHeartbeats 3500000

/-- The target is `16*N`. All modifications are in `[3*N,12*N]`.
This is one-target feasibility, not simultaneous repair of arbitrary targets. -/
theorem eventually_global_predecessor_repair (A : Set ℕ) (D K C M ε : ℝ)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hC : 0 ≤ C) (hM : 0 ≤ M) (hε : 0 < ε)
    (hbal : ∀ X, |(count A X : ℝ)-cumulative profile X| ≤ D)
    (henv : ∀ z, (sumRep A z : ℝ) ≤ K+C*Real.log ((z : ℝ)+2)) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, (m : ℝ) ≤ M*Real.log (N : ℝ) →
      ∃ E F : Finset ℕ, (E : Set ℕ) ⊆ A ∧ Disjoint (F : Set ℕ) A ∧
        E.card = 2*m ∧ F.card = 2*m ∧
        (∀ u ∈ E ∪ F, 3*N ≤ u ∧ u ≤ 12*N) ∧
        (∀ X, -1 ≤ (count (swap A E F) X : ℝ)-count A X ∧
          (count (swap A E F) X : ℝ)-count A X ≤ 0) ∧
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
  let G : ℝ := 12*(D+1)+1
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
  filter_upwards [eventually_gap_bounds D hD,hparams,hlog.eventually_ge_atTop (24/ε)]
    with N hgap hp hlε
  obtain ⟨hN,hl,hHN,hHG,hlen⟩ := hgap
  intro m hm
  let H := gapSize D N
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
  have hb : 2*Real.sqrt (2*(N : ℝ)*V)+2*H*V ≤ B*Real.sqrt (N : ℝ)*Real.log (N : ℝ) :=
    degree_budget N H G B₀ V hNreal.le hG hB₀ hl hHG rfl
  have hepoints (b : Bool) (i : Fin N) :
      4*N ≤ endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i ∧
        endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i ≤ 12*N := by
    have hi := i.isLt
    cases b <;> simp only [endpoint,Bool.false_eq_true,if_false,if_true] <;> omega
  have hgap' (b : Bool) (i : Fin N) :
      predecessor (A₀ : Set ℕ) (endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i) ∈ A₀ ∧
      endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i <
        predecessor (A₀ : Set ℕ) (endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i)+H := by
    let u := endpoint (16*N) (fun i : Fin N ↦ 4*N+i.val) b i
    have hu : 4*N ≤ u ∧ u ≤ 12*N := hepoints b i
    have hHX : H ≤ u+1 := by dsimp only [H]; omega
    have hlen' : 2*D*Real.sqrt (((u+1 : ℕ) : ℝ)) < H := by
      have hs := Real.sqrt_le_sqrt (show ((u+1 : ℕ) : ℝ) ≤ ((16*N+1 : ℕ) : ℝ) by exact_mod_cast (show u+1 ≤ 16*N+1 by omega))
      exact (mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2*D)).trans_lt hlen
    obtain ⟨hmem,hclose⟩ := predecessor_gap_of_profile A D hD hbal u H hHX hlen'
    have he : predecessor (A₀ : Set ℕ) u = predecessor A u := predecessor_cutoff A (by omega)
    change predecessor (A₀ : Set ℕ) u ∈ A₀ ∧ u < predecessor (A₀ : Set ℕ) u+H
    rw [he]
    exact ⟨mem_cutoff.mpr ⟨(predecessor_le A u).trans_lt (by omega),hmem⟩,hclose⟩
  have hsmall : ((m : ℝ)^4+4*m^2*H+m*(2*Real.sqrt (2*N*V)+2*H*V))/N +
      ((Finset.range X).card : ℝ)*Real.exp ((m : ℝ)*Real.exp t*(2*Real.sqrt (2*N*V)+2*H*V)/N -
        t*(ε*Real.log (N : ℝ)/16)) < 1 := by
    have hc := hp N m H (by linarith) hm hHG
    have hb' := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) m)
    have hfirst := div_le_div_of_nonneg_right (add_le_add_right hb' ((m : ℝ)^4+4*m^2*H)) hNreal.le
    have he := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ (m : ℝ)*Real.exp t by positivity)) hNreal.le
    have he' := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_right he (t*(ε*Real.log (N : ℝ)/16))))
      (show (0 : ℝ) ≤ (N : ℝ)^h+1 by positivity)
    simp only [Finset.card_range,X,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    change _ + ((N : ℝ)^h+1)*Real.exp ((m : ℝ)*Real.exp t*(2*Real.sqrt (2*N*V)+2*H*V)/N -
      t*(ε*Real.log (N : ℝ)/16)) < 1
    dsimp only [t] at *
    linarith
  obtain ⟨E,F,hE,hF,hEc,hFc,hpref,htarget,hself,hsupp,hcol⟩ :=
    exists_located_interval_predecessor_repair A₀ V hAcap (16*N) (4*N) N H hNp
      (by dsimp only [H]; omega) (fun b i ↦ (hgap' b i).1) (fun b i ↦ (hgap' b i).2)
      m (Finset.range X) (ε*Real.log (N : ℝ)/16) t ht hsmall
  have hs (u : ℕ) (hu : u ∈ E ∪ F) : 3*N ≤ u ∧ u ≤ 12*N := by
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
  · intro Y
    have he₀ : (E : Set ℕ) ⊆ (A₀ : Set ℕ) := hE
    have hf₀ : Disjoint (F : Set ℕ) (A₀ : Set ℕ) := by
      exact Set.disjoint_left.mpr (fun u hu ha ↦ Finset.disjoint_left.mp hF ha hu)
    have he := swap_count_difference A E F hEA hFA Y
    have he' := swap_count_difference (A₀ : Set ℕ) E F he₀ hf₀ Y
    have hpref' := hpref Y
    rw [swapped_coe] at hpref'
    rw [he,← he']
    exact hpref'
  · rw [cutoff_swap_rep A E F hXX,cutoff_rep A hXX] at htarget
    exact htarget
  · intro z hzn
    by_cases hzlo : z < 3*N
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

end Erdos66GlobalPredecessorRepair
