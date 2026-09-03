import Submission.RestrictedTupleCover

/-!
The restricted-family argument does not require finitely many coordinates
when only countably many ordered pair types occur on edges. This is a
restriction on possible constructions, not a settlement of Erdős 595.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595CountableRealizedTypes
open Erdos595Work Erdos595TupleType Erdos595RestrictedTuple

variable {V I A : Type*} [LinearOrder A]

abbrev TypeOf (I : Type*) := (Bool × I) → (Bool × I) → Prop

/-- Only actual edge types count; no condition is imposed on nonedge types. -/
def EdgeTypes (G : SimpleGraph V) (v : V → I → A) : Set (TypeOf I) :=
  {t | ∃ a b, G.Adj a b ∧ pairType (v a) (v b) = t}

/-- Coordinates may even be uncountable. The countability assumption is on
realized edge types, and the vertex family may be completely arbitrary. -/
theorem countable_cover (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (v : V → I → A) (hInv : RelativeInvariant G v)
    (hT : (EdgeTypes G v).Countable) : IsCountableUnionOfTriangleFree G := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  letI : Countable (EdgeTypes G v) := hT.to_subtype
  let col : V → V → Option ((EdgeTypes G v) × Bool) := fun a b =>
    if h : G.Adj a b then
      some (⟨pairType (v a) (v b),⟨a,b,h,rfl⟩⟩,decide (Later G v a b))
    else none
  have recover (a b : V) (h : G.Adj a b) :
      col a b = some (⟨pairType (v a) (v b),⟨a,b,h,rfl⟩⟩,decide (Later G v a b)) := by
    simp only [col,dif_pos h]
  have convert (a b c d : V) (hab : G.Adj a b) (hcd : G.Adj c d)
      (he : col a b = col c d) : code G v a b = code G v c d := by
    rw [recover a b hab,recover c d hcd] at he
    have hh := Option.some.inj he
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg Prod.fst hh)
    · change decide (Later G v a b) = decide (Later G v c d)
      exact congrArg Prod.snd hh
  apply Erdos595NegativeInner.cover_of_ordered_patterns G col
  intro a b c hablt hbclt hab hac hbc he
  exact code_valid G hG v hInv a b c hablt hbclt hab hac hbc
    ⟨convert a b a c hab hac he.1,convert a b b c hab hbc he.2⟩

/-- Equivalently, it is enough to bound all actual edge types by an explicitly
specified countable family. This includes any finite list of interlacing types. -/
theorem countable_cover_of_types (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (v : V → I → A) (hInv : RelativeInvariant G v)
    (T : Set (TypeOf I)) (hT : T.Countable)
    (hedge : ∀ a b, G.Adj a b → pairType (v a) (v b) ∈ T) :
    IsCountableUnionOfTriangleFree G := by
  apply countable_cover G hG v hInv (hT.mono ?_)
  rintro t ⟨a,b,hab,rfl⟩
  exact hedge a b hab

#print axioms countable_cover
#print axioms countable_cover_of_types
end Erdos595CountableRealizedTypes
