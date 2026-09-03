import Submission.BalancedWeightedPacketExplore
import Submission.BalancedRepairParametersExplore

/-! Actual plane-curve families obtained by attaching the fixed balanced
palette to jointly selected coarse labels. -/
namespace Erdos66CurveFamilyPacket
open Erdos66ExceptionalLabeledPackets Erdos66WeightedPacketAlgebra Erdos66BalancedWeightedPacket
  Erdos66BalancedRepairParameters Erdos66AffineRootAggregate Erdos66FiniteField Erdos66OriginRepair
  Erdos66MultiPacket
open scoped Classical
set_option maxHeartbeats 2600000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def planeFiber (B : ℕ → Finset (F×F)) (q : ℕ) (z : F×F) : ℝ :=
  ∑ i∈Finset.range (q+1), (pairCount (B i) (B (q-i)) z : ℝ)

lemma planeFiber_support (B : ℕ → Finset (F×F)) (D : Finset ℕ) (h q : ℕ)
    (hD : D ⊆ Finset.range h) (hB : ∀ i, i∉D → B i=∅) (z : F×F) :
    planeFiber B q z=fiberSum D D (fun i j ↦ (pairCount (B i) (B j) z : ℝ)) q := by
  let H := h+q+1
  have hDH : D ⊆ Finset.range H := hD.trans (Finset.range_mono (by dsimp [H]; omega))
  unfold planeFiber
  rw [←diagonal_sum H q (by dsimp [H]; omega) (fun i j ↦ (pairCount (B i) (B j) z : ℝ))]
  exact fiberSum_of_support D (Finset.range H) hDH _
    (fun i hi j ↦ by simp [hB i hi,pairCount]) (fun j hj i ↦ by simp [hB j hj,pairCount]) q

lemma planeFiber_zero_above_support (B : ℕ → Finset (F×F)) (D : Finset ℕ) (L q : ℕ)
    (hD : D ⊆ Finset.range (L+1)) (hB : ∀ i, i∉D → B i=∅) (hq : 2*L<q) (z : F×F) :
    planeFiber B q z=0 := by
  rw [planeFiber_support B D (L+1) q hD hB]
  apply fiberSum_zero_of_pairs_zero
  exact Erdos66NaturalLabeledPackets.pairs_zero_above D D L q
    (fun i hi ↦ by have hh := Finset.mem_range.mp (hD hi); omega)
    (fun i hi ↦ by have hh := Finset.mem_range.mp (hD hi); omega) hq

lemma coloredCurve_plane_error_all (D : Finset ℕ) (a : F) (h q : ℕ)
    (hD : D ⊆ Finset.range h) (hF : ringChar F ≠ 2) (ha : ∀ i<h, a+(i : F)≠0)
    (hq : 2*a+(q : F)≠0) (z : F×F) :
    |planeFiber (coloredCurve D a) q z-(AdditiveCombinatorics.sumRep (D : Set ℕ) q : ℝ)| ≤
      |Erdos66SharedParameterKernel.labelFiber h
        (fun i ↦ selectedWeight D i*(quadraticChar F (a+i) : ℝ)) q| := by
  have hs (i : ℕ) (hi : i∉D) : coloredCurve D a i=∅ := by simp [coloredCurve,hi]
  have he := fiberSum_of_support D (Finset.range h) hD
    (fun i j ↦ (pairCount (coloredCurve D a i) (coloredCurve D a j) z : ℝ))
    (fun i hi j ↦ by simp [hs i hi,pairCount]) (fun j hj i ↦ by simp [hs j hj,pairCount]) q
  rw [planeFiber_support (coloredCurve D a) D h q hD hs,←he]
  exact coloredCurve_aggregate_error D a h q hD hF ha hq z.1 z.2

lemma coloredCurve_plane_zero (D : Finset ℕ) (a : F) (h q : ℕ)
    (hD : D ⊆ Finset.range h) (hz : AdditiveCombinatorics.sumRep (D : Set ℕ) q=0) (z : F×F) :
    planeFiber (coloredCurve D a) q z=0 := by
  rw [planeFiber_support (coloredCurve D a) D h q hD (fun i hi ↦ by simp [coloredCurve,hi])]
  exact fiberSum_zero_of_pairs_zero D D _ q (by rwa [Erdos66NatPairAlgebra.pairs_self])

lemma singleton_pairCount_le_two (hF : ringChar F ≠ 2) (u v : F)
    (hu : u≠0) (hv : v≠0) (huv : u+v≠0) (z : F×F) :
    pairCount (parabolaSet {u}) (parabolaSet {v}) z ≤ 2 := by
  obtain ⟨t,s⟩ := z
  have hh := parabola_sum_count hF u v t s hu hv huv
  rw [←map_mul,←map_mul] at hh
  have hc := quadraticChar_abs_le_one (F := F) (u*v*((u+v)*s-t^2))
  have he := singleton_parabola_pair_count u v t s
  have hb : (pairCount (parabolaSet {u}) (parabolaSet {v}) (t,s) : ℤ) ≤ 2 := by
    linarith [(abs_le.mp hc).2]
  exact_mod_cast hb

noncomputable def repairParameter {T : Finset ℕ} {k : ℕ} (u v x y : F) (j : Label T k) : F :=
  if j.1.2 then (if j.2 then y else x) else (if j.2 then v else u)

lemma repairParameter_mem {T : Finset ℕ} {k : ℕ} (u v x y : F) (j : Label T k) :
    repairParameter u v x y j∈({u,v,x,y} : Finset F) := by
  unfold repairParameter
  split_ifs <;> simp

noncomputable def extendedCurves (D T : Finset ℕ) (k : ℕ) (a : F) (d : Label T k → ℕ)
    (u v x y : F) : ℕ → Finset (F×F) :=
  Function.extend d (fun j ↦ parabolaSet {repairParameter u v x y j}) (coloredCurve D a)

lemma extendedCurves_new (D T : Finset ℕ) (k : ℕ) (a : F) (d : Label T k → ℕ)
    (hd : Function.Injective d) (u v x y : F) (j : Label T k) :
    extendedCurves D T k a d u v x y (d j)=parabolaSet {repairParameter u v x y j} :=
  hd.extend_apply _ _ j

lemma extendedCurves_old (D T : Finset ℕ) (k : ℕ) (a : F) (d : Label T k → ℕ)
    (havoid : ∀ j, d j∉D) (u v x y : F) (i : ℕ) (hi : i∈D) :
    extendedCurves D T k a d u v x y i=coloredCurve D a i := by
  apply Function.extend_apply'
  rintro ⟨j,hj⟩
  exact havoid j (hj.symm ▸ hi)

lemma extendedCurves_support (D T : Finset ℕ) (k : ℕ) (a : F) (d : Label T k → ℕ)
    (u v x y : F) (i : ℕ) (hi : i∉D∪Finset.univ.image d) :
    extendedCurves D T k a d u v x y i=∅ := by
  have hD : i∉D := fun hh ↦ hi (Finset.mem_union_left _ hh)
  have hn : ¬∃ j, d j=i := by
    rintro ⟨j,hj⟩
    exact hi (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩))
  rw [extendedCurves,Function.extend_apply' _ _ _ hn]
  simp [coloredCurve,hD]

/-- The scalar collateral estimate is now an estimate for actual counts of
pairs of plane curves, with no exceptional fine target. -/
theorem extendedCurves_collateral (hF : ringChar F ≠ 2) (D T : Finset ℕ) (k h : ℕ)
    (a : F) (d : Label T k → ℕ) (hD : D ⊆ Finset.range h)
    (hd : Function.Injective d) (hdh : ∀ j, d j<h) (havoid : ∀ j, d j∉D)
    (hcenter : ∀ g : Group T k, ∀ s : Bool, d ((g,s),false)+d ((g,s),true)=g.1.val)
    (hunique : ∀ u v w s : Label T k, ¬Designated u v → ¬Designated w s →
      d u+d v=d w+d s → (u=w ∧ v=s) ∨ (u=s ∧ v=w))
    (hmixed : ∀ q, (Erdos66NatPairAlgebra.pairs (Finset.univ.image d) D q : ℝ) < 28)
    (u v x y : F) (hpar0 : ∀ r∈({u,v,x,y} : Finset F), r≠0)
    (hparsum : ∀ r∈({u,v,x,y} : Finset F), ∀ s∈({u,v,x,y} : Finset F), r+s≠0)
    (ha : ∀ i∈D, a+(i : F)≠0)
    (hparold : ∀ r∈({u,v,x,y} : Finset F), ∀ i∈D, r+(a+(i : F))≠0)
    (huv : u+v=1) (hxy : x+y=1) (hplus : quadraticChar F (u*v)=1)
    (hminus : quadraticChar F (x*y)= -1) (q : ℕ) (z : F×F) :
    0 ≤ planeFiber (extendedCurves D T k a d u v x y) q z-planeFiber (coloredCurve D a) q z-
      (if q∈T then 4*(k : ℝ) else 0) ∧
    planeFiber (extendedCurves D T k a d u v x y) q z-planeFiber (coloredCurve D a) q z-
      (if q∈T then 4*(k : ℝ) else 0) < 116 := by
  let B := extendedCurves D T k a d u v x y
  let w : ℕ → ℕ → ℝ := fun i j ↦ (pairCount (B i) (B j) z : ℝ)
  have hsym (i j : ℕ) : w i j=w j i := by dsimp [w]; rw [pairCount_comm]
  have hzero (i j : ℕ) : 0 ≤ w i j := Nat.cast_nonneg _
  have hn (j : Label T k) : B (d j)=parabolaSet {repairParameter u v x y j} :=
    extendedCurves_new D T k a d hd u v x y j
  have ho (i : ℕ) (hi : i∈D) : B i=parabolaSet {a+(i : F)} := by
    dsimp only [B]
    rw [extendedCurves_old D T k a d havoid u v x y i hi]
    simp only [coloredCurve,if_pos hi]
  have hnew (j l : Label T k) : w (d j) (d l) ≤ 2 := by
    dsimp [w]
    rw [hn,hn]
    exact_mod_cast singleton_pairCount_le_two hF _ _
      (hpar0 _ (repairParameter_mem u v x y j)) (hpar0 _ (repairParameter_mem u v x y l))
      (hparsum _ (repairParameter_mem u v x y j) _ (repairParameter_mem u v x y l)) z
  have hmix (j : Label T k) (i : ℕ) (hi : i∈D) : w (d j) i ≤ 2 := by
    dsimp [w]
    rw [hn,ho i hi]
    exact_mod_cast singleton_pairCount_le_two hF _ _ (hpar0 _ (repairParameter_mem u v x y j))
      (ha i hi) (hparold _ (repairParameter_mem u v x y j) i hi) z
  have hbal (g : Group T k) :
      w (d ((g,false),false)) (d ((g,false),true))+
        w (d ((g,true),false)) (d ((g,true),true))=2 := by
    dsimp [w]
    rw [hn,hn,hn,hn]
    simp only [repairParameter,Bool.false_eq_true,if_false,if_true]
    exact_mod_cast balanced_pair_count hF u v x y (hpar0 u (by simp)) (hpar0 v (by simp))
      (hpar0 x (by simp)) (hpar0 y (by simp)) huv hxy hplus hminus z.1 z.2
  have hh := balanced_repair_collateral D T k d hd havoid hcenter hunique hmixed w hsym hzero hnew hmix hbal q
  have hS : D∪Finset.univ.image d ⊆ Finset.range h := by
    apply Finset.union_subset hD
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (hdh j)
  have htotal := planeFiber_support B (D∪Finset.univ.image d) h q hS
    (extendedCurves_support D T k a d u v x y) z
  have hbase := planeFiber_support (coloredCurve D a) D h q hD (fun i hi ↦ by simp [coloredCurve,hi]) z
  have he : fiberSum D D w q=fiberSum D D (fun i j ↦ (pairCount (coloredCurve D a i) (coloredCurve D a j) z : ℝ)) q := by
    unfold fiberSum
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [w,B]
    rw [extendedCurves_old D T k a d havoid u v x y i hi,extendedCurves_old D T k a d havoid u v x y j hj]
  rw [he,←hbase,←htotal] at hh
  exact hh

end Erdos66CurveFamilyPacket
