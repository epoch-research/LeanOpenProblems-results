import Submission.SmallParameterSource
import Submission.PrimitiveCollisionMass

/-! The complement of the two small-parameter regimes still contains a
primitive family of divergent reciprocal maximum-root mass. This concerns
per-collision mass before applying the divisor-avoiding source; it is not
a claim about collisions surviving inside that source. -/
namespace Erdos1206.SmallParameterResidualMass
open DefectCollisionCounting
open scoped Classical

def family (i : PrimitiveCollisionMass.Index) : Collision where
  a := PrimitiveCollisionMass.A (6*i.2.val+1) i.1.val
  b := PrimitiveCollisionMass.B (6*i.2.val+1) i.1.val
  c := PrimitiveCollisionMass.C (6*i.2.val+1) i.1.val
  d := PrimitiveCollisionMass.D (6*i.2.val+1) i.1.val
  hab := (PrimitiveCollisionMass.ordered (by omega : 0 < 6*i.2.val+1) i.1.val).2.1
  hbc := (PrimitiveCollisionMass.ordered (by omega : 0 < 6*i.2.val+1) i.1.val).2.2.1
  hcd := (PrimitiveCollisionMass.ordered (by omega : 0 < 6*i.2.val+1) i.1.val).2.2.2
  equation := PrimitiveCollisionMass.identity _ _

lemma family_injective : Function.Injective family := by
  intro i j he
  have ha := congrArg Collision.a he
  have hb := congrArg Collision.b he
  have hc := congrArg Collision.c he
  have hd := congrArg Collision.d he
  obtain ⟨ht,hp⟩ := PrimitiveCollisionMass.parameter_injective ha hb hc hd
  cases i with
  | mk p i =>
    cases j with
    | mk q j =>
      have hpq : p=q := Subtype.ext hp
      subst q
      have ht' : 6*i.val+1=6*j.val+1 := ht
      have hij : i=j := Fin.ext (by omega)
      subst j
      rfl

lemma family_primitive (i : PrimitiveCollisionMass.Index) :
    ConicHeightProduct.rootGcd (family i).a (family i).b (family i).c (family i).d=1 :=
  PrimitiveCollisionMass.index_gcd_one i

lemma family_gap (i : PrimitiveCollisionMass.Index) :
    (family i).smallGap=2*(6*i.2.val+1)*(7*(6*i.2.val+1)+2*i.1.val) := by
  have hh : (family i).d=(family i).c+
      2*(6*i.2.val+1)*(7*(6*i.2.val+1)+2*i.1.val) := by
    dsimp [family,PrimitiveCollisionMass.C,PrimitiveCollisionMass.D]
    ring
  change (family i).d-(family i).c=_
  omega

lemma family_defect (i : PrimitiveCollisionMass.Index) : (family i).defect=3*(family i).smallGap := by
  have hh : (family i).b+(family i).c=(family i).a+(family i).d+
      3*(2*(6*i.2.val+1)*(7*(6*i.2.val+1)+2*i.1.val)) := by
    dsimp [family,PrimitiveCollisionMass.A,PrimitiveCollisionMass.B,PrimitiveCollisionMass.C,PrimitiveCollisionMass.D]
    ring
  rw [family_gap]
  change (family i).b+(family i).c-((family i).a+(family i).d)=_
  omega

lemma family_height_lt_gap_cube (i : PrimitiveCollisionMass.Index) : (family i).d < (family i).smallGap^3 := by
  have hp := i.1.property.2
  have hp0 := i.1.property.1.pos
  have hg : 4*i.1.val≤(family i).smallGap := by
    rw [family_gap]
    have ht : 1≤6*i.2.val+1 := by omega
    nlinarith [Nat.mul_le_mul_right i.1.val ht]
  have hheight := PrimitiveCollisionMass.height_bound i
  change (family i).d≤134*i.1.val^2 at hheight
  have hp2 : 0 < i.1.val^2 := pow_pos hp0 2
  have hc : 134 < 64*i.1.val := by omega
  have hmul := Nat.mul_lt_mul_of_pos_right hc hp2
  have hpow := Nat.pow_le_pow_left hg 3
  calc
    (family i).d≤134*i.1.val^2 := hheight
    _  <  (4*i.1.val)^3 := by nlinarith only [hmul]
    _ ≤ (family i).smallGap^3 := hpow

lemma family_outside (i : PrimitiveCollisionMass.Index) :
    (family i).d < (family i).defect^32 ∧ (family i).d < (family i).smallGap^48 := by
  have hh := family_height_lt_gap_cube i
  have hgap := (family i).smallGap_pos
  have hk := (family i).defect_pos
  have hhk : (family i).smallGap≤(family i).defect := by rw [family_defect]; omega
  constructor
  · exact (hh.trans_le (Nat.pow_le_pow_left hhk 3)).trans_le
      (Nat.pow_le_pow_right hk (by decide : 3≤32))
  · exact hh.trans_le (Nat.pow_le_pow_right hgap (by decide : 3≤48))

def Residual (e : Collision) : Prop :=
  ConicHeightProduct.rootGcd e.a e.b e.c e.d=1 ∧
    e.d < e.defect^32 ∧ e.d < e.smallGap^48

/-- Primitive collisions outside both proved summability regimes still
have divergent reciprocal maximum-root mass. -/
theorem residual_reciprocals_not_summable :
    ¬ Summable (fun e : {e : Collision // Residual e} => (1:ℝ)/e.val.d) := by
  let f (i : PrimitiveCollisionMass.Index) : {e : Collision // Residual e} :=
    ⟨family i,family_primitive i,family_outside i⟩
  have hi : Function.Injective f := by
    intro i j he
    exact family_injective (congrArg Subtype.val he)
  intro hs
  have hh := hs.comp_injective hi
  exact PrimitiveCollisionMass.index_reciprocal_heights_not_summable hh

#print axioms family_outside
#print axioms residual_reciprocals_not_summable
end Erdos1206.SmallParameterResidualMass
