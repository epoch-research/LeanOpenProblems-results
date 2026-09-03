import Submission.RowSparsePrefixExplore
import Submission.CyclicThickeningExplore
import Submission.ParabolaRepairExplore
import Submission.CharacterEnergyExplore

/-! Uniform row bounds for graph families and their thickened integer
realizations. These estimates control mixed counts with a short prefix. -/
namespace Erdos66GraphRowGeometry
open AdditiveCombinatorics Erdos66ParabolaRepair Erdos66OriginRepair
  Erdos66CharacterEnergy Erdos66CyclicThickening Erdos66RowSparsePrefix
  Erdos66WindowPerturbation Erdos66NatPairAlgebra Erdos66Counting
open scoped Classical
set_option maxHeartbeats 1500000

section Field
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def rowCount (B : Finset (F×F)) (s : F) : ℕ :=
  (Finset.univ.filter (fun x : F ↦ (x,s)∈B)).card

lemma rowCount_mono {B C : Finset (F×F)} (hBC : B⊆C) (s : F) :
    rowCount B s ≤ rowCount C s := by
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBC (Finset.mem_filter.mp hx).2⟩

lemma curve_row_bound (u s : F) (hu : u≠0) : rowCount (curve u) s ≤ 2 := by
  apply le_trans _ (square_fiber_card_le_two (s*u))
  apply Finset.card_le_card
  intro x hx
  have hh := (mem_curve u (x,s)).mp (Finset.mem_filter.mp hx).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(div_eq_iff hu).mp hh.symm⟩

lemma parabola_row_bound (U : Finset F) (hU : ∀ u∈U, u≠0) (s : F) :
    rowCount (parabolaSet U) s ≤ 2*U.card := by
  have he : Finset.univ.filter (fun x : F ↦ (x,s)∈parabolaSet U)=
      U.biUnion (fun u ↦ Finset.univ.filter (fun x : F ↦ (x,s)∈curve u)) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,
      parabolaSet_eq_biUnion]
  calc
    _ = (U.biUnion (fun u ↦ Finset.univ.filter (fun x : F ↦ (x,s)∈curve u))).card := by rw [rowCount,he]
    _ ≤ ∑ u∈U, rowCount (curve u) s := Finset.card_biUnion_le
    _ ≤ ∑ _u∈U, 2 := Finset.sum_le_sum (fun u hu ↦ curve_row_bound u s (hU u hu))
    _ = _ := by simp [Nat.mul_comm]

lemma repaired_subset (U : Finset F) (w : F) (T : Finset F) :
    parabolaSet U∪repairPoints w T ⊆ parabolaSet (U∪{w,-w}) := by
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · exact Erdos66RectangleRepair.parabolaSet_mono Finset.subset_union_left hz
  · exact Erdos66RectangleRepair.parabolaSet_mono Finset.subset_union_right (repairPoints_subset w T hz)

lemma repaired_row_bound (U : Finset F) (hU : ∀ u∈U, u≠0)
    (w : F) (hw : w≠0) (T : Finset F) (s : F) :
    rowCount (parabolaSet U∪repairPoints w T) s ≤ 2*(U.card+2) := by
  have hnz : ∀ u∈U∪{w,-w}, u≠0 := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hU u hu
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hw
      · exact neg_ne_zero.mpr hw
  have hcard : (U∪{w,-w}).card ≤ U.card+2 :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_insert_le _ _ |>.trans
      (by simp)) _)
  exact (rowCount_mono (repaired_subset U w T) s).trans
    ((parabola_row_bound (U∪{w,-w}) hnz s).trans (Nat.mul_le_mul_left 2 hcard))

end Field

section Encoded
variable (p K : ℕ) [NeZero p] [NeZero K]

/-- A row-indexed realization. Allowing the plane set to vary with the row
only strengthens the scope of the local occupancy estimate. -/
def graphRowsSet (B : ℕ → Finset (ZMod p×ZMod p)) : Set ℕ :=
  {n | ((n : ZMod p),((n/(p*K) : ℕ) : ZMod p))∈B (n/(p*K))}

lemma row_offset_cast (q r : ℕ) :
    ((q*(p*K)+r : ℕ) : ZMod p)=(r : ZMod p) := by
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,mul_zero,zero_add]

lemma graphRows_local_eq (B : ℕ → Finset (ZMod p×ZMod p)) (q : ℕ) :
    localCount (graphRowsSet p K B) (q*(p*K)) (p*K)=
      (Finset.univ.filter (fun x : ZMod (p*K) ↦ ((x.val : ZMod p),(q : ZMod p))∈B q)).card := by
  unfold localCount
  apply Finset.card_bij (fun n _ ↦ ((n-q*(p*K) : ℕ) : ZMod (p*K)))
  · intro n hn
    obtain ⟨hnI,hnB⟩ := Finset.mem_filter.mp hn
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hnI
    have hdiff : n-q*(p*K)<p*K := by omega
    have hq : n/(p*K)=q := Nat.div_eq_of_lt_le hlo (by nlinarith)
    have he : n=q*(p*K)+(n-q*(p*K)) := by omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [ZMod.val_natCast_of_lt hdiff]
    change ((n : ZMod p),((n/(p*K) : ℕ) : ZMod p))∈B (n/(p*K)) at hnB
    rw [hq] at hnB
    have hc : (n : ZMod p)=((n-q*(p*K) : ℕ) : ZMod p) := by
      conv_lhs => rw [he]
      exact row_offset_cast p K q _
    rwa [hc] at hnB
  · intro n hn m hm he
    have hnI := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1
    have hmI := Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1
    have hh := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (show n-q*(p*K)<p*K by omega),
      ZMod.val_natCast_of_lt (show m-q*(p*K)<p*K by omega)] at hh
    omega
  · intro x hx
    have hxB := (Finset.mem_filter.mp hx).2
    have hxlt := ZMod.val_lt x
    refine ⟨q*(p*K)+x.val,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
      have hq : (q*(p*K)+x.val)/(p*K)=q :=
        Nat.div_eq_of_lt_le (by omega) (by nlinarith)
      change ((((q*(p*K)+x.val : ℕ) : ZMod p),
        (((q*(p*K)+x.val)/(p*K) : ℕ) : ZMod p))∈B ((q*(p*K)+x.val)/(p*K)))
      rwa [hq,row_offset_cast]
    · simpa only [Nat.add_sub_cancel_left] using ZMod.natCast_zmod_val x

lemma lifted_row_card (B : Finset (ZMod p×ZMod p)) (s : ZMod p) :
    (Finset.univ.filter (fun x : ZMod (p*K) ↦ ((x.val : ZMod p),s)∈B)).card=
      K*rowCount B s := by
  rw [Finset.card_filter,← Equiv.sum_comp (blockEquiv p K),Fintype.sum_prod_type]
  simp only [blockEquiv,Equiv.ofBijective_apply,blockDigit_val,Nat.cast_add,Nat.cast_mul,
    ZMod.natCast_self,zero_mul,add_zero,ZMod.natCast_zmod_val]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← Finset.mul_sum,rowCount,Finset.card_filter]
  norm_cast

lemma graphRows_sparse (B : ℕ → Finset (ZMod p×ZMod p)) (H : ℕ)
    (hB : ∀ q s, rowCount (B q) s ≤ H) :
    RowSparse (graphRowsSet p K B) (p*K) (K*H) := by
  intro q
  rw [graphRows_local_eq,lifted_row_card]
  exact Nat.mul_le_mul_left K (hB q _)

/-- Repaired graph families retain a row bound independent of how many
points are used for the origin repair. -/
lemma repaired_graphRows_sparse (U : ℕ → Finset (ZMod p))
    (hU : ∀ q u, u∈U q → u≠0) (w : ℕ → ZMod p) (hw : ∀ q, w q≠0)
    (T : ℕ → Finset (ZMod p)) (H : ℕ) (hcard : ∀ q, (U q).card ≤ H)
    [Fact p.Prime] :
    RowSparse (graphRowsSet p K (fun q ↦ parabolaSet (U q)∪repairPoints (w q) (T q)))
      (p*K) (2*K*(H+2)) := by
  have hh := graphRows_sparse p K (fun q ↦ parabolaSet (U q)∪repairPoints (w q) (T q))
    (2*(H+2)) (fun q s ↦ (repaired_row_bound (U q) (hU q) (w q) (hw q) (T q) s).trans
      (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (hcard q) 2)))
  convert hh using 1 <;> ring

/-- The old prefix may have arbitrarily many points. Only its length must
fit inside one new row; the mixed error is O(K*(number of curves+2)). -/
theorem repaired_graphRows_prefix_bound [Fact p.Prime]
    (U : ℕ → Finset (ZMod p)) (hU : ∀ q u, u∈U q → u≠0)
    (w : ℕ → ZMod p) (hw : ∀ q, w q≠0) (T : ℕ → Finset (ZMod p))
    (H : ℕ) (hcard : ∀ q, (U q).card ≤ H)
    (A : Finset ℕ) (L n : ℕ) (hA : ∀ a∈A, a<L) (hL : L ≤ p*K)
    (hd : Disjoint (A : Set ℕ)
      (graphRowsSet p K (fun q ↦ parabolaSet (U q)∪repairPoints (w q) (T q))))
    (hn : 2*L ≤ n) :
    let B := graphRowsSet p K (fun q ↦ parabolaSet (U q)∪repairPoints (w q) (T q))
    sumRep B n ≤ sumRep ((A : Set ℕ)∪B) n ∧
      sumRep ((A : Set ℕ)∪B) n ≤ sumRep B n+8*K*(H+2) := by
  dsimp only
  have hh := union_short_prefix_bound A _ L (p*K) (2*K*(H+2)) n hA hd
    (Nat.mul_pos (NeZero.pos p) (NeZero.pos K)) hL (repaired_graphRows_sparse p K U hU w hw T H hcard) hn
  convert hh using 1 <;> ring

end Encoded
end Erdos66GraphRowGeometry
