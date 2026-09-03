import Submission.CurveFamilyPacketExplore

/-! Whole-coarse-block repairs assembled into a finite plane profile without
exceptional targets. This does not assert inter-scale compatibility. -/
namespace Erdos66RepairedPlaneProfile
open Filter AdditiveCombinatorics Erdos66TripleDeletionParameters Erdos66ExceptionalLabeledPackets
  Erdos66CurveFamilyPacket Erdos66BalancedRepairParameters Erdos66AffineRootAggregate
  Erdos66RealWeightedCharacterEnergy Erdos66FiniteField Erdos66OriginRepair
open scoped Topology Classical
set_option maxHeartbeats 3000000

/-- Every sufficiently large m works for every sufficiently large odd prime.
The coarse family contains only individual nonzero-parameter curves or empty
sets, not unions of many curves at one label. -/
theorem eventually_repaired_plane_profiles (ε : ℝ) (hε : 0<ε) (hε1 : ε ≤ 1) :
    ∀ᶠ m : ℝ in atTop, ∀ (p : ℕ) [Fact p.Prime], p≠2 → 8*(length m+1)+16<p →
      ∃ B : ℕ → Finset (ZMod p×ZMod p),
        (∀ i, length m < i → B i=∅) ∧
        (∀ i, B i=∅ ∨ ∃ u : ZMod p, u≠0 ∧ B i=parabolaSet {u}) ∧
        (∀ q z, planeFiber B q z ≤ (1+4*ε)*m^3) ∧
        (∀ q, start m ε ≤ q → q ≤ length m → ∀ z, |planeFiber B q z-m^3| < 5*ε*m^3) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_id.const_mul_atTop hε).eventually_ge_atTop 120,
    eventually_deleted_profiles ε hε hε1,eventually_exception_packets ε hε hε1]
    with m hm hlarge hprofile hpackets
  dsimp only [id] at hlarge
  have hm13 : m ≤ m^3 := by simpa only [pow_one] using pow_le_pow_right₀ hm (by norm_num : (1 : ℕ) ≤ 3)
  have hlarge' : 120 ≤ ε*m^3 := by nlinarith
  have hm3 : 0 ≤ m^3 := by positivity
  intro p hp hp2 hpL
  have hF : ringChar (ZMod p)≠2 := by simpa only [ZMod.ringChar_zmod_n] using hp2
  obtain ⟨a,T₀,D,hD,ha,hop,hT₀,hloc,hzero,hu,hl,hsgn⟩ := hprofile p hp2 (by omega)
  let T := T₀.filter (fun q ↦ start m ε ≤ q ∧ q ≤ length m)
  have hTT₀ : T ⊆ T₀ := Finset.filter_subset _ _
  have hTrange : T ⊆ Finset.Icc (start m ε) (length m) := by
    intro q hq
    exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hq).2
  have hT : (T.card : ℝ) ≤ 128*(1+Real.log (((length m+1 : ℕ) : ℝ)))^2/ε^2 := by
    have hh : (T.card : ℝ) ≤ T₀.card := by exact_mod_cast Finset.card_le_card hTT₀
    exact hh.trans hT₀
  obtain ⟨d,hdi,hda,hcenter,hunique,hmixed⟩ := hpackets D T hD hu hTrange hT
  let U := D.image (fun (i : ℕ) ↦ a+(i : ZMod p))
  have hU : U.card ≤ length m+1 := by
    have hh := Finset.card_image_le (s := D) (f := fun i ↦ a+(i : ZMod p))
    have hh' := Finset.card_le_card hD
    simp only [Finset.card_range] at hh'
    dsimp [U]
    omega
  have hsize : 4*(U.card+2)+3<Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  obtain ⟨u,v,x,y,hu0,hv0,hx0,hy0,huv,hxy,hplus,hminus,hparold,hparsum⟩ :=
    exists_balanced_palette hF U hsize
  have hpar0 : ∀ r∈({u,v,x,y} : Finset (ZMod p)), r≠0 := by
    intro r hr
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with he | he | he | he <;> subst r <;> assumption
  have hparold' : ∀ r∈({u,v,x,y} : Finset (ZMod p)), ∀ i∈D, r+(a+(i : ZMod p))≠0 := by
    intro r hr i hi
    exact hparold r hr _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  have haD : ∀ i∈D, a+(i : ZMod p)≠0 := fun i hi ↦ ha i (Finset.mem_range.mp (hD hi))
  let B := extendedCurves D T (multiplicity m) a d u v x y
  let S := D∪Finset.univ.image d
  have hS : S ⊆ Finset.range (length m+1) := by
    apply Finset.union_subset hD
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (by have hh := (hda j).1; omega)
  have hBs : ∀ i, i∉S → B i=∅ := extendedCurves_support D T (multiplicity m) a d u v x y
  have hc (q : ℕ) (z : ZMod p×ZMod p) :
      0 ≤ planeFiber B q z-planeFiber (coloredCurve D a) q z-(if q∈T then 4*(multiplicity m : ℝ) else 0) ∧
      planeFiber B q z-planeFiber (coloredCurve D a) q z-(if q∈T then 4*(multiplicity m : ℝ) else 0) < 116 :=
    extendedCurves_collateral hF D T (multiplicity m) (length m+1) a d hD hdi
      (fun j ↦ by have hh := (hda j).1; omega) (fun j ↦ (hda j).2) hcenter hunique hmixed
      u v x y hpar0 hparsum haD hparold' huv hxy hplus hminus q z
  have hbase (q : ℕ) (hq : q ≤ 2*length m) (z : ZMod p×ZMod p) :
      |planeFiber (coloredCurve D a) q z-(sumRep (D : Set ℕ) q : ℝ)| < 2*ε*m^3 := by
    have hh := coloredCurve_plane_error_all D a (length m+1) q hD hF ha (hop q (by omega)) z
    exact hh.trans_lt (hsgn q hq)
  have hbasezero (q : ℕ) (hq : q∈T) (z : ZMod p×ZMod p) : planeFiber (coloredCurve D a) q z=0 :=
    coloredCurve_plane_zero D a (length m+1) q hD (hzero q (hTT₀ hq)) z
  have hk : 4*(multiplicity m : ℝ) ≤ m^3 := by
    have hh : (multiplicity m : ℝ) ≤ m^3/4 := Nat.floor_le (by positivity)
    linarith
  have hkl : m^3-4 < 4*(multiplicity m : ℝ) := by
    have hh := Nat.lt_floor_add_one (m^3/4)
    change m^3/4 < (multiplicity m : ℝ)+1 at hh
    linarith
  refine ⟨B,?_,?_,?_,?_⟩
  · intro i hi
    apply hBs i
    intro hiS
    have hh := Finset.mem_range.mp (hS hiS)
    omega
  · intro i
    by_cases hi : ∃ j, d j=i
    · obtain ⟨j,rfl⟩ := hi
      right
      refine ⟨repairParameter u v x y j,hpar0 _ (repairParameter_mem u v x y j),?_⟩
      exact extendedCurves_new D T (multiplicity m) a d hdi u v x y j
    · have he : B i=coloredCurve D a i := Function.extend_apply' _ _ i hi
      rw [he]
      by_cases hiD : i∈D
      · right
        exact ⟨a+(i : ZMod p),haD i hiD,by simp [coloredCurve,hiD]⟩
      · left
        simp [coloredCurve,hiD]
  · intro q z
    by_cases hq : q ≤ 2*length m
    · have hcoll := hc q z
      by_cases hqT : q∈T
      · rw [hbasezero q hqT z,if_pos hqT,sub_zero] at hcoll
        nlinarith
      · rw [if_neg hqT,sub_zero] at hcoll
        have hb := (abs_lt.mp (hbase q hq z)).2
        nlinarith [hu q]
    · rw [planeFiber_zero_above_support B S (length m) q hS hBs (by omega)]
      positivity
  · intro q hq₀ hq z
    have hcoll := hc q z
    by_cases hqT : q∈T
    · rw [hbasezero q hqT z,if_pos hqT,sub_zero] at hcoll
      rw [abs_lt]
      constructor <;> nlinarith [hcoll.1,hcoll.2]
    · have hqT₀ : q∉T₀ := fun hh ↦ hqT (Finset.mem_filter.mpr ⟨hh,hq₀,hq⟩)
      rw [if_neg hqT,sub_zero] at hcoll
      have hb := abs_lt.mp (hbase q (by omega) z)
      have hl' := abs_lt.mp (hl q hq₀ hq hqT₀)
      rw [abs_lt]
      constructor <;> nlinarith [hcoll.1,hcoll.2]

end Erdos66RepairedPlaneProfile
