import Submission.AffineLineKernelExplore

/-! Actual finite-set realization of the affine-line kernel. The exact
cardinality calculation preserves the global self-convolution mean. -/
namespace Erdos66AffineLineAssembly
open Erdos66AffineLineKernel Erdos66OriginRepair Erdos66DisjointPaletteAssembly
open scoped Classical
set_option maxHeartbeats 2200000
variable {G F : Type*} [AddCommGroup G] [DecidableEq G]
  [Field F] [Fintype F] [DecidableEq F]

noncomputable def oldSet (A : F → Finset G) : Finset G := Finset.univ.biUnion A
noncomputable def lift (A : F → Finset G) : Finset (G×(F×F)) := assembly A line

/-- The translated lines do not retain the whole old zero slice: only
color zero occurs there. This is not a prefix-preserving construction. -/
lemma mem_lift_zero (A : F → Finset G) (a : G) :
    (a,((0:F),0))∈lift A ↔ a∈A 0 := by
  simp only [lift,assembly,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_product,mem_line,mul_zero,zero_add]
  constructor
  · rintro ⟨u,ha,hu⟩
    have hu' : u=0 := sq_eq_zero_iff.mp hu.symm
    simpa only [hu'] using ha
  · intro ha
    exact ⟨0,ha,by ring⟩

lemma oldSet_card (A : F → Finset G)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) :
    (oldSet A).card=∑ u : F, (A u).card := by
  apply Finset.card_biUnion
  intro u hu v hv huv
  exact hA huv

lemma lift_card (A : F → Finset G)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) :
    (lift A).card=(oldSet A).card*Fintype.card F := by
  rw [lift,assembly,Finset.card_biUnion (assembly_pairwise A hA line)]
  simp_rw [Finset.card_product,line_card]
  rw [←Finset.sum_mul,oldSet_card A hA]

lemma oldSet_pairCount (A : F → Finset G)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) (t : G) :
    pairCount (oldSet A) (oldSet A) t=
      ∑ u : F, ∑ v : F, pairCount (A u) (A v) t := by
  exact pairCount_biUnion_self _ A (fun u _ v _ huv ↦ hA huv) t

lemma lift_pairCount (A : F → Finset G)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) (t : G) (x y : F) :
    (pairCount (lift A) (lift A) (t,(x,y)):ℝ)=
      weightedCount (fun u v ↦ (pairCount (A u) (A v) t:ℝ)) x y := by
  rw [lift,assembly_pairCount A hA]
  simp only [Nat.cast_sum,Nat.cast_mul,weightedCount]

/-- The transfer error needs only self-count bounds for each old color.
No estimate for two different old colors is assumed. -/
theorem lift_error (htwo : (2:F)≠0) (A : F → Finset G)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) (t : G) (g : ℝ)
    (hg : 0≤g) (hcap : ∀ u, (pairCount (A u) (A u) t:ℝ)≤g) (x y : F) :
    |(pairCount (lift A) (lift A) (t,(x,y)):ℝ)-pairCount (oldSet A) (oldSet A) t|≤
      2*Fintype.card F*g := by
  rw [lift_pairCount A hA,oldSet_pairCount A hA]
  push_cast
  exact weighted_error htwo _ g hg (fun u ↦ ⟨Nat.cast_nonneg _,hcap u⟩) x y

/-- There is no hidden multiplicative loss in the *global mean* at the
finite product-group level. This does not assert a natural carry transfer. -/
theorem mean_preserved [Fintype G] (A : F → Finset G)
    (hA : Pairwise (fun i j ↦ Disjoint (A i) (A j))) :
    ((lift A).card:ℝ)^2/Fintype.card (G×(F×F))=
      ((oldSet A).card:ℝ)^2/Fintype.card G := by
  rw [lift_card A hA]
  simp only [Nat.cast_mul,Fintype.card_prod]
  push_cast
  have hF : (Fintype.card F:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  <;> ring

end Erdos66AffineLineAssembly
