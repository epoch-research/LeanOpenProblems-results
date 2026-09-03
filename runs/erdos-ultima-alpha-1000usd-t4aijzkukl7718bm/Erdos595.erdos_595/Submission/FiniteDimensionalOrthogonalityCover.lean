import Submission.Work
import Submission.CountableCodegreeColoring

/-!
Nonisotropic projective orthogonality in dimension at most four has a
countable triangle-free edge cover, over an arbitrary field.
-/

set_option autoImplicit false
open Set SimpleGraph Module
open scoped LinearAlgebra.Projectivization

namespace Erdos595FiniteDimensionalOrthogonality
universe u v
variable {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]

private lemma projective_eq_of_finrank_le_one (S : Submodule K E)
    (hS : finrank K S ≤ 1) (p q : ℙ K E) (hp : p.rep ∈ S) (hq : q.rep ∈ S) : p = q := by
  apply Projectivization.submodule_injective
  have eqS (r : ℙ K E) (hr : r.rep ∈ S) : r.submodule = S := by
    apply Submodule.eq_of_le_of_finrank_le
    · rw [r.submodule_eq]
      exact Submodule.span_le.mpr (by simpa using hr)
    · simpa only [r.finrank_submodule] using hS
  exact (eqS p hp).trans (eqS q hq).symm

omit [FiniteDimensional K E] in
private lemma orth_span_range (B : LinearMap.BilinForm K E) {I : Type*}
    (x : I → E) (z : E) (h : ∀ i, B (x i) z = 0) :
    z ∈ B.orthogonal (Submodule.span K (range x)) := by
  have hs : Submodule.span K (range x) ≤ LinearMap.ker (B.flip z) := by
    apply Submodule.span_le.mpr
    rintro w ⟨i,rfl⟩
    exact h i
  exact fun w hw => hs hw

abbrev Point (B : LinearMap.BilinForm K E) := {p : ℙ K E // B p.rep p.rep ≠ 0}

def graph (B : LinearMap.BilinForm K E) (hs : B.IsSymm) : SimpleGraph (Point B) where
  Adj p q := B p.val.rep q.val.rep = 0
  symm := fun p q hpq => (hs.eq q.val.rep p.val.rep).trans hpq
  loopless := fun p => p.property

variable (B : LinearMap.BilinForm K E) (hs : B.IsSymm) (hn : B.Nondegenerate)

omit [FiniteDimensional K E] in
private lemma three_independent (x a b : Point B)
    (hxa : (graph B hs).Adj x a) (hxb : (graph B hs).Adj x b) (hab : a ≠ b) :
    LinearIndependent K ![x.val.rep,a.val.rep,b.val.rep] := by
  apply linearIndependent_fin_cons.mpr
  constructor
  · have hp := (Projectivization.independent_pair_iff_ne a.val b.val).mpr
      (fun he => hab (Subtype.ext he))
    rw [Projectivization.independent_iff] at hp
    convert hp using 1
    ext i
    fin_cases i <;> rfl
  · intro hx
    have he : Submodule.span K (range ![a.val.rep,b.val.rep]) ≤ LinearMap.ker (B x.val.rep) := by
      apply Submodule.span_le.mpr
      rintro w ⟨i,rfl⟩
      fin_cases i
      · exact hxa
      · exact hxb
    exact x.property (he hx)

include hn in
/-- Every two distinct points in a neighborhood have at most one common
neighbor within that neighborhood. -/
theorem local_common_subsingleton (hd : finrank K E ≤ 4) (x : Point B)
    (a b : (graph B hs).neighborSet x) (hab : a ≠ b) :
    Set.Subsingleton (((graph B hs).induce ((graph B hs).neighborSet x)).commonNeighbors a b) := by
  intro y hy z hz
  let S : Submodule K E := Submodule.span K (range ![x.val.rep,a.val.val.rep,b.val.val.rep])
  have hi := three_independent B hs x a b a.property b.property
    (fun he => hab (Subtype.ext he))
  have hS : finrank K S = 3 := by
    simpa only [S,Fintype.card_fin] using finrank_span_eq_card hi
  have ho : finrank K (B.orthogonal S) ≤ 1 := by
    rw [B.finrank_orthogonal hn hs.isRefl S,hS]
    omega
  apply Subtype.ext
  apply Subtype.ext
  apply projective_eq_of_finrank_le_one (B.orthogonal S) ho
  · apply orth_span_range B _ y.val.val.rep
    intro i
    fin_cases i
    · exact y.property
    · exact hy.1
    · exact hy.2
  · apply orth_span_range B _ z.val.val.rep
    intro i
    fin_cases i
    · exact z.property
    · exact hz.1
    · exact hz.2

include hn in
/-- All neighborhoods are countably vertex-colorable. -/
theorem neighborhood_coloring (hd : finrank K E ≤ 4) (x : Point B) :
    Nonempty (((graph B hs).induce ((graph B hs).neighborSet x)).Coloring ℕ) := by
  apply Erdos595CountableCodegree.coloring_nat_of_countable_common_neighbors
  intro a b hab
  exact (local_common_subsingleton B hs hn hd x a b hab).countable

include hn in
/-- The projective graph is countably coverable, without any clique-free assumption. -/
theorem countable_cover (hd : finrank K E ≤ 4) :
    Erdos595Work.IsCountableUnionOfTriangleFree (graph B hs) := by
  classical
  let G := graph B hs
  let c := fun x => (neighborhood_coloring B hs hn hd x).some
  let f : Point B → Point B → ℕ := fun x y => if h : G.Adj x y then c x ⟨y,h⟩ else 0
  letI : LinearOrder (Point B) := IsWellOrder.linearOrder WellOrderingRel
  apply Erdos595Work.countable_union_of_earlier_neighbor_coloring G f
  intro x a b _ _ hxa hxb hab
  simpa only [f,dif_pos hxa,dif_pos hxb] using (c x).valid
    (show (G.induce (G.neighborSet x)).Adj ⟨a,hxa⟩ ⟨b,hxb⟩ from hab)

omit [FiniteDimensional K E] in
private lemma nonzero_of_nonisotropic (x : E) (hx : B x x ≠ 0) : x ≠ 0 := by
  intro he
  subst x
  simp at hx

omit [FiniteDimensional K E] in
private lemma nonisotropic_rep (x : E) (hx : B x x ≠ 0) :
    B (Projectivization.mk K x (nonzero_of_nonisotropic B x hx)).rep
      (Projectivization.mk K x (nonzero_of_nonisotropic B x hx)).rep ≠ 0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K x (nonzero_of_nonisotropic B x hx)
  rw [← ha]
  simpa only [Units.smul_def,LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.smul_right,smul_eq_mul,mul_ne_zero_iff] using
      (show (a : K) ≠ 0 ∧ (a : K) ≠ 0 ∧ B x x ≠ 0 from ⟨a.ne_zero,a.ne_zero,hx⟩)

include hs hn in
/-- Any nonisotropic orthogonal representation in dimension at most four
pulls back the countable cover. The original graph need not be induced. -/
theorem countable_cover_of_representation {V : Type*} (G : SimpleGraph V)
    (p : V → E) (hp : ∀ v, B (p v) (p v) ≠ 0)
    (he : ∀ {v w}, G.Adj v w → B (p v) (p w) = 0) (hd : finrank K E ≤ 4) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  let q : V → Point B := fun v => ⟨Projectivization.mk K (p v)
    (nonzero_of_nonisotropic B (p v) (hp v)),nonisotropic_rep B (p v) (hp v)⟩
  let f : G →g graph B hs :=
    { toFun := q
      map_rel' := by
        intro v w hvw
        obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K (p v)
          (nonzero_of_nonisotropic B (p v) (hp v))
        obtain ⟨b,hb⟩ := Projectivization.exists_smul_eq_mk_rep K (p w)
          (nonzero_of_nonisotropic B (p w) (hp w))
        change B (Projectivization.mk K (p v) _).rep (Projectivization.mk K (p w) _).rep = 0
        rw [← ha,← hb]
        simp only [Units.smul_def,LinearMap.BilinForm.smul_left,
          LinearMap.BilinForm.smul_right,he hvw,mul_zero] }
  exact Erdos595Work.countable_union_of_hom f (countable_cover B hs hn hd)

#print axioms countable_cover
#print axioms countable_cover_of_representation
end Erdos595FiniteDimensionalOrthogonality
