import Submission.RightFiberCover
import Submission.FiniteFiberOddBound
import Submission.MatchingBundleRightCover

/-!
A finite fiber glued across a triangle-free index graph by equality of a
proper label has a countably covered SECOND right adjoint. The first right
adjoint admits a finite rainbow-on-triangles vertex labeling when the label
palette is finite. This excludes the prism candidate at its second stage.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595CrossClassSecondRight
open Erdos595ArcAdjoint Erdos595TriangleFiber Erdos595MatchingBundle
variable {S I C : Type*} (F : SimpleGraph S) (B : SimpleGraph I) (c : S → C)

abbrev H := glue F B c
abbrev Point := Biclique (H F B c)

/-- Both sides of a biclique meet this index fiber. -/
def Internal (p : Point F B c) (i : I) : Prop :=
  (∃ a : S, (a,i) ∈ p.val.1) ∧ ∃ b : S, (b,i) ∈ p.val.2

/-- All within-fiber edges of the biclique carry one unordered label pair. -/
def Uniform (p : Point F B c) : Prop :=
  ∃ t : Sym2 C, ∀ a b : S × I, a ∈ p.val.1 → b ∈ p.val.2 → a.2 = b.2 →
    s(c a.1,c b.1) = t

lemma cross_label {p : Point F B c} {a b : S × I}
    (ha : a ∈ p.val.1) (hb : b ∈ p.val.2) (hne : a.2 ≠ b.2) : c a.1 = c b.1 := by
  rcases p.property a ha b hb with h | h
  · exact (hne h.1).elim
  · exact h.2

/-- Two internal fibers force a uniform pair; this uses only equality of
cross labels, and not the triangle-free hypothesis on the index graph. -/
lemma uniform_of_two {p : Point F B c} {i j : I} (hi : Internal F B c p i)
    (hj : Internal F B c p j) (hne : i ≠ j) : Uniform F B c p := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := hi
  obtain ⟨⟨d,hd⟩,⟨e,he⟩⟩ := hj
  have hae : c a = c e := cross_label F B c ha he hne
  have hdb : c d = c b := cross_label F B c hd hb hne.symm
  refine ⟨s(c a,c b),?_⟩
  intro x y hx hy hxy
  by_cases hxi : x.2 = i
  · have hxj : x.2 ≠ j := fun h => hne (hxi.symm.trans h)
    have hjy : j ≠ y.2 := fun h => hne (hxi.symm.trans (hxy.trans h.symm))
    have hx := cross_label F B c hx he hxj
    have hy := cross_label F B c hd hy hjy
    rw [hx,← hae,← hy,hdb]
  · have hx := cross_label F B c hx hb hxi
    have hy := cross_label F B c ha hy (fun h => hxi (hxy.trans h.symm))
    rw [hx,← hy]
    exact Sym2.eq_swap

lemma internal_unique {p : Point F B c} (hp : ¬Uniform F B c p) {i j : I}
    (hi : Internal F B c p i) (hj : Internal F B c p j) : i = j := by
  by_contra hne
  exact hp (uniform_of_two F B c hi hj hne)

variable [Nonempty C]

lemma nonuniform_internal {p : Point F B c} (hp : ¬Uniform F B c p) :
    ∃ i, Internal F B c p i := by
  classical
  by_contra hn
  apply hp
  refine ⟨s(Classical.choice ‹Nonempty C›,Classical.choice ‹Nonempty C›),?_⟩
  intro a b ha hb he
  exact (hn ⟨a.2,⟨⟨a.1,ha⟩,⟨b.1,by simpa only [he] using hb⟩⟩⟩).elim

noncomputable def index (p : Point F B c) (hp : ¬Uniform F B c p) : I :=
  (nonuniform_internal F B c hp).choose

lemma index_internal (p : Point F B c) (hp : ¬Uniform F B c p) :
    Internal F B c p (index F B c p hp) := (nonuniform_internal F B c hp).choose_spec

/-- Restriction to an index fiber, identified with the original fiber graph. -/
def fiberBiclique (p : Point F B c) (i : I) : Biclique F :=
  ⟨({a | (a,i) ∈ p.val.1},{b | (b,i) ∈ p.val.2}),by
    intro a ha b hb
    exact glue_same_fiber F B c (p := (a,i)) (q := (b,i)) rfl
      (p.property (a,i) ha (b,i) hb)⟩

noncomputable def code (p : Point F B c) : Sym2 C ⊕ Biclique F := by
  classical
  exact if hp : Uniform F B c p then Sum.inl hp.choose
  else Sum.inr (fiberBiclique F B c p (index F B c p hp))

variable (hc : ∀ a b, F.Adj a b → c a ≠ c b) (hB : B.CliqueFree 3)

include hc hB in
lemma triangle_fibers {p q r : Point F B c} (s : Six (H F B c) p q r) :
    (s.x.2 = s.y.2 ∧ s.x.2 = s.z.2) ∧ (s.x'.2 = s.y'.2 ∧ s.x'.2 = s.z'.2) :=
  ⟨glue_triangles F B c hc hB _ _ _ (s.tri _).1 (s.tri _).2.1 (s.tri _).2.2,
    glue_triangles F B c hc hB _ _ _ (s.tri' _).1 (s.tri' _).2.1 (s.tri' _).2.2⟩

include hc hB in
lemma code_ne {p q r : Point F B c} (hpq : (right (H F B c)).Adj p q)
    (hpr : (right (H F B c)).Adj p r) (hqr : (right (H F B c)).Adj q r) :
    code F B c p ≠ code F B c q := by
  classical
  intro he
  let t := six (H F B c) hpq hpr hqr
  have hf := triangle_fibers F B c hc hB t
  have hip : Internal F B c p t.x.2 :=
    ⟨⟨t.z.1,by simpa only [hf.1.2] using t.hz.2⟩,⟨t.x.1,t.hx.1⟩⟩
  have hiq : Internal F B c q t.x.2 :=
    ⟨⟨t.x.1,t.hx.2⟩,⟨t.y.1,by simpa only [hf.1.1] using t.hy.1⟩⟩
  have hjp : Internal F B c p t.x'.2 :=
    ⟨⟨t.x'.1,t.hx'.2⟩,⟨t.z'.1,by simpa only [hf.2.2] using t.hz'.1⟩⟩
  by_cases hp : Uniform F B c p <;> by_cases hq : Uniform F B c q
  · have he' : hp.choose = hq.choose := by simpa only [code,dif_pos hp,dif_pos hq,Sum.inl.injEq] using he
    have hp' := hp.choose_spec t.z t.x t.hz.2 t.hx.1 hf.1.2.symm
    have hq' := hq.choose_spec t.x t.y t.hx.2 t.hy.1 hf.1.1
    have heq : s(c t.z.1,c t.x.1) = s(c t.x.1,c t.y.1) := hp'.trans (he'.trans hq'.symm)
    have hxz : c t.x.1 ≠ c t.z.1 := hc _ _ (glue_same_fiber F B c hf.1.2 (t.tri _).2.1)
    have hyz : c t.y.1 ≠ c t.z.1 := hc _ _
      (glue_same_fiber F B c (hf.1.1.symm.trans hf.1.2) (t.tri _).2.2)
    have hz : c t.z.1 ∈ s(c t.x.1,c t.y.1) := heq ▸ Sym2.mem_mk_left _ _
    rcases Sym2.mem_iff.mp hz with hz | hz
    · exact hxz hz.symm
    · exact hyz hz.symm
  · simp only [code,dif_pos hp,dif_neg hq,Sum.inl_ne_inr] at he
  · simp only [code,dif_neg hp,dif_pos hq,Sum.inr_ne_inl] at he
  · have he' : fiberBiclique F B c p (index F B c p hp) = fiberBiclique F B c q (index F B c q hq) := by
      simpa only [code,dif_neg hp,dif_neg hq,Sum.inr.injEq] using he
    have hpi : index F B c p hp = t.x.2 := internal_unique F B c hp (index_internal F B c p hp) hip
    have hqi : index F B c q hq = t.x.2 := internal_unique F B c hq (index_internal F B c q hq) hiq
    have hij : t.x.2 = t.x'.2 := internal_unique F B c hp hip hjp
    rw [hpi,hqi] at he'
    have hadj : (right F).Adj (fiberBiclique F B c p t.x.2) (fiberBiclique F B c q t.x.2) := by
      refine ⟨⟨t.x.1,t.hx.1,t.hx.2⟩,⟨t.x'.1,?_,?_⟩⟩
      · change (t.x'.1,t.x.2) ∈ q.val.2
        simpa only [hij] using t.hx'.1
      · change (t.x'.1,t.x.2) ∈ p.val.1
        simpa only [hij] using t.hx'.2
    exact hadj.ne he'

include hc hB in
/-- Equality-of-label cross gluing with a finite fiber is excluded at the
second right stage, without a bound on the index graph's cardinality. -/
theorem second_right_cover [Finite S] [Countable C] :
    Erdos595Work.IsCountableUnionOfTriangleFree (right (right (H F B c))) := by
  apply right_cover_of_rainbow (right (H F B c)) (code F B c)
  intro p q r hpq hpr hqr
  exact ⟨code_ne F B c hc hB hpq hpr hqr,
    code_ne F B c hc hB hpr hpq hqr.symm,
    code_ne F B c hc hB hqr hpq.symm hpr.symm⟩

#print axioms uniform_of_two

namespace Prism
open Erdos595FiniteFiberOddBound

variable {J : Type} (D : SimpleGraph J)

/-- Swap the factors to identify the concrete prism bundle with cross-class gluing. -/
def swapHom : bundle Prism.fiber Prism.cross Prism.cross_symm D →g
    glue Prism.fiber D Prism.label :=
  ⟨Prod.swap,fun h => h⟩

/-- The concrete prism bundle is covered at its SECOND right stage for every
triangle-free index graph, including uncountably chromatic ones. -/
theorem second_right_cover (hD : D.CliqueFree 3) :
    Erdos595Work.IsCountableUnionOfTriangleFree
      (right (right (bundle Prism.fiber Prism.cross Prism.cross_symm D))) := by
  apply Erdos595Work.countable_union_of_hom
    (Erdos595RightFiber.rightHom (Erdos595RightFiber.rightHom (swapHom D)))
  apply Erdos595CrossClassSecondRight.second_right_cover Prism.fiber D Prism.label
  · intro a b hab he
    exact Prism.cross_independent a b he hab
  · exact hD

#print axioms second_right_cover
end Prism

#print axioms code_ne
#print axioms second_right_cover
end Erdos595CrossClassSecondRight
