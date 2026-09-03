import Submission.IndefiniteUnitOrthogonality
import Submission.FourCycleCommonCover

/-! The signature (3,2) unit orthogonality candidate is countably covered.
The proof first removes antipodal twins, then excludes induced octahedra.
This is an auxiliary candidate exclusion for Erdős 595. -/
set_option autoImplicit false
open SimpleGraph Set
open scoped BigOperators
namespace Erdos595IndefiniteFive
open Erdos595IndefiniteUnit
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {m n : ℕ}

def bilin : LinearMap.BilinForm K (Space K m n) :=
  LinearMap.mk₂ K form
    (by intros; simp only [form,Prod.fst_add,Prod.snd_add,add_dotProduct]; ring)
    (by intros; simp only [form,Prod.smul_fst,Prod.smul_snd,smul_dotProduct,smul_eq_mul]; ring)
    (by intros; simp only [form,Prod.fst_add,Prod.snd_add,dotProduct_add]; ring)
    (by intros; simp only [form,Prod.smul_fst,Prod.smul_snd,dotProduct_smul,smul_eq_mul]; ring)

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] lemma bilin_apply (x y : Space K m n) : bilin x y = form x y := rfl

private lemma dot_nonneg {d : ℕ} (x : Fin d → K) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- After a full positive orthonormal frame, the orthogonal complement
has no nonzero isotropic vectors. -/
lemma complement_anisotropic (x : Fin m → UnitPoint K m n)
    (hx : ∀ i j, i ≠ j → (graph K m n).Adj (x i) (x j))
    (z : Space K m n) (hz : ∀ i, form (x i).val z = 0) (hzz : form z z = 0) : z = 0 := by
  classical
  let b := basisOfPiSpaceOfLinearIndependent (positive_independent x hx)
  let g : Fin m → K := fun i => b.repr z.1 i
  let v : Space K m n := ∑ i, g i • (x i).val
  have hp : v.1 = z.1 := by
    simpa only [v,g,Prod.fst_sum,Prod.smul_fst,coe_basisOfPiSpaceOfLinearIndependent,b]
      using b.sum_repr z.1
  have row (i : Fin m) : form (x i).val v = g i := by
    change bilin (x i).val v = g i
    simp only [v,LinearMap.BilinForm.sum_right,LinearMap.BilinForm.smul_right,
      bilin_apply]
    rw [Finset.sum_eq_single i]
    · rw [(x i).property,mul_one]
    · intro j _ hji
      rw [hx i j hji.symm,mul_zero]
    · simp
  have hvv : form v v = ∑ i, g i * g i := by
    change bilin v v = _
    conv_lhs => arg 1; rw [show v = ∑ i, g i • (x i).val from rfl]
    simp only [LinearMap.BilinForm.sum_left,LinearMap.BilinForm.smul_left,
      bilin_apply,row]
  have hvz : form v z = 0 := by
    change bilin v z = 0
    simp only [v,LinearMap.BilinForm.sum_left,LinearMap.BilinForm.smul_left,
      bilin_apply,hz,mul_zero,Finset.sum_const_zero]
  have hw : form (v - z) (v - z) = ∑ i, g i * g i := by
    change bilin (v - z) (v - z) = _
    simp only [map_sub,LinearMap.sub_apply,bilin_apply,hvv,hvz,form_symm z v,hzz]
    ring
  have hn : -((v - z).2 ⬝ᵥ (v - z).2) = ∑ i, g i * g i := by
    simpa only [form,Prod.fst_sub,hp,sub_self,dotProduct_zero,zero_sub] using hw
  have hg (i : Fin m) : g i = 0 := by
    have hi := Finset.single_le_sum (s := Finset.univ) (f := fun j => g j * g j)
      (fun j _ => mul_self_nonneg (g j)) (Finset.mem_univ i)
    have hneg := dot_nonneg (v - z).2
    have h0 : g i * g i = 0 := by nlinarith
    exact mul_self_eq_zero.mp h0
  have hv : v = 0 := by simp only [v,hg,zero_smul,Finset.sum_const_zero]
  have hzpos : z.1 = 0 := by simpa only [hv,Prod.fst_zero] using hp.symm
  have hzneg : z.2 = 0 := by
    apply dotProduct_self_eq_zero.mp
    have hh := hzz
    simpa only [form,hzpos,dotProduct_zero,zero_sub,neg_eq_zero] using hh
  exact Prod.ext hzpos hzneg

/-- Two non-collinear unit vectors in each of m mutually orthogonal parts
require at least m negative coordinates as well as m positive coordinates. -/
lemma multipartite_bound (x y : Fin m → UnitPoint K m n)
    (hx : ∀ i j, i ≠ j → (graph K m n).Adj (x i) (x j))
    (hy : ∀ i j, i ≠ j → (graph K m n).Adj (y i) (y j))
    (hxy : ∀ i j, i ≠ j → form (x i).val (y j).val = 0)
    (hne : ∀ i (t : K), (y i).val ≠ t • (x i).val) : m ≤ n := by
  classical
  let t (i : Fin m) := form (x i).val (y i).val
  let r (i : Fin m) : Space K m n := (y i).val - t i • (x i).val
  have hxr (i j : Fin m) : form (x i).val (r j) = 0 := by
    change bilin (x i).val ((y j).val - t j • (x j).val) = 0
    simp only [map_sub,LinearMap.BilinForm.smul_right,bilin_apply]
    by_cases hij : i = j
    · subst j
      rw [(x i).property,mul_one]
      exact sub_self _
    · rw [hxy i j hij,hx i j hij,mul_zero,sub_self]
  have hrr (i j : Fin m) (hij : i ≠ j) : form (r i) (r j) = 0 := by
    change bilin ((y i).val - t i • (x i).val) ((y j).val - t j • (x j).val) = 0
    simp only [map_sub,LinearMap.sub_apply,LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right,bilin_apply]
    rw [hx i j hij,hy i j hij,hxy i j hij,form_symm (y i).val (x j).val,
      hxy j i hij.symm]
    ring
  have hr (i : Fin m) : form (r i) (r i) ≠ 0 := by
    intro h
    exact (sub_ne_zero.mpr (hne i (t i))) (complement_anisotropic x hx (r i)
      (fun j => hxr j i) h)
  let v : Fin m ⊕ Fin m → Space K m n := Sum.elim (fun i => (x i).val) r
  have hv : bilin.iIsOrtho v := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hx i j (fun h => hij (congrArg Sum.inl h))
      | inr j => exact hxr i j
    | inr i =>
      cases j with
      | inl j => exact (form_symm (r i) (x j).val).trans (hxr j i)
      | inr j => exact hrr i j (fun h => hij (congrArg Sum.inr h))
  have hn : ∀ i, ¬bilin.IsOrtho (v i) (v i) := by
    intro i
    cases i with
    | inl i => exact (x i).property.trans_ne one_ne_zero
    | inr i => exact hr i
  have hi := (LinearMap.BilinForm.linearIndependent_of_iIsOrtho hv hn).fintype_card_le_finrank
  simp only [Fintype.card_sum,Fintype.card_fin,Space,Module.finrank_prod,
    Module.finrank_pi] at hi
  omega

private def opposite (x : UnitPoint K m n) : UnitPoint K m n :=
  ⟨-x.val,by
    change bilin (-x.val) (-x.val) = 1
    simpa only [map_neg,LinearMap.neg_apply,neg_neg,bilin_apply] using x.property⟩

private lemma opposite_opposite (x : UnitPoint K m n) : opposite (opposite x) = x := by
  apply Subtype.ext
  exact neg_neg _

private lemma adj_opposite_left (x y : UnitPoint K m n) :
    (graph K m n).Adj (opposite x) y ↔ (graph K m n).Adj x y := by
  change bilin (-x.val) y.val = 0 ↔ bilin x.val y.val = 0
  simp only [map_neg,LinearMap.neg_apply,neg_eq_zero]

private lemma adj_opposite_right (x y : UnitPoint K m n) :
    (graph K m n).Adj x (opposite y) ↔ (graph K m n).Adj x y := by
  change bilin x.val (-y.val) = 0 ↔ bilin x.val y.val = 0
  simp only [map_neg,neg_eq_zero]

section Canonical
variable [LinearOrder (UnitPoint K m n)]

private def canon (x : UnitPoint K m n) : UnitPoint K m n := min x (opposite x)

private lemma canon_opposite (x : UnitPoint K m n) : canon (opposite x) = canon x := by
  simp only [canon,opposite_opposite,min_comm]

private lemma canon_idem (x : UnitPoint K m n) : canon (canon x) = canon x := by
  rcases min_choice x (opposite x) with h | h
  · change canon (min x (opposite x)) = min x (opposite x)
    rw [h]
    exact h
  · change canon (min x (opposite x)) = min x (opposite x)
    rw [h,canon_opposite]
    exact h

private abbrev Canonical := {x : UnitPoint K m n | canon x = x}

private def canonHom : graph K m n →g (graph K m n).induce (Canonical (K := K)) where
  toFun x := ⟨canon x,canon_idem x⟩
  map_rel' := by
    intro x y h
    change (graph K m n).Adj (canon x) (canon y)
    rcases min_choice x (opposite x) with hx | hx <;>
      rcases min_choice y (opposite y) with hy | hy <;>
      change canon x = _ at hx <;> change canon y = _ at hy <;>
      rw [hx,hy] <;> simpa only [adj_opposite_left,adj_opposite_right] using h

private lemma canonical_scalar_eq (x y : Canonical (K := K) (m := m) (n := n))
    (t : K) (h : y.val.val = t • x.val.val) : x = y := by
  have ht : t * t = 1 := by
    have hnorm := y.val.property
    change bilin y.val.val y.val.val = 1 at hnorm
    rw [h,LinearMap.BilinForm.smul_left,LinearMap.BilinForm.smul_right,
      bilin_apply,x.val.property,mul_one] at hnorm
    exact hnorm
  rcases mul_self_eq_one_iff.mp ht with ht | ht
  · subst t
    apply Subtype.ext
    apply Subtype.ext
    simpa only [one_smul] using h.symm
  · subst t
    have he : y.val = opposite x.val := by
      apply Subtype.ext
      simpa only [neg_one_smul] using h
    apply Subtype.ext
    calc
      x.val = canon x.val := x.property.symm
      _ = canon (opposite x.val) := (canon_opposite x.val).symm
      _ = canon y.val := congrArg canon he.symm
      _ = y.val := y.property

end Canonical

/-- All signature (3,n) unit orthogonality graphs with n < 3 are covered,
even over arbitrarily large non-Archimedean ordered fields. -/
theorem countable_cover (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) (hn : n < 3) : Erdos595Work.IsCountableUnionOfTriangleFree (graph K 3 n) := by
  classical
  letI : LinearOrder (UnitPoint K 3 n) := IsWellOrder.linearOrder WellOrderingRel
  apply Erdos595Work.countable_union_of_hom (canonHom (K := K) (m := 3) (n := n))
  apply Erdos595FourCycleCommon.cover_of_no_octahedron
  · exact (cliqueFree_four K n).comap (SimpleGraph.Embedding.induce _)
  · rintro ⟨e⟩
    let x : Fin 3 → UnitPoint K 3 n := fun i => (e (i,0)).val
    let y : Fin 3 → UnitPoint K 3 n := fun i => (e (i,1)).val
    have cross (i j : Fin 3) (a b : Fin 2) (hij : i ≠ j) :
        (graph K 3 n).Adj (e (i,a)).val (e (j,b)).val :=
      e.toHom.map_adj (show (completeEquipartiteGraph 3 2).Adj (i,a) (j,b) from hij)
    have hh := multipartite_bound x y (fun i j hij => cross i j 0 0 hij)
      (fun i j hij => cross i j 1 1 hij) (fun i j hij => cross i j 0 1 hij) (by
        intro i t he
        have hEq := canonical_scalar_eq (e (i,0)) (e (i,1)) t he
        have h01 : (0 : Fin 2) = 1 := congrArg Prod.snd (e.injective hEq)
        exact (by decide : (0 : Fin 2) ≠ 1) h01)
    omega

#print axioms complement_anisotropic
#print axioms multipartite_bound
#print axioms countable_cover
end Erdos595IndefiniteFive
