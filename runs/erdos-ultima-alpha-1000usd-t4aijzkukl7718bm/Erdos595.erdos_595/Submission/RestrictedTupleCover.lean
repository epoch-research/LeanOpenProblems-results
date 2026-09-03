import Submission.TupleTypeCover
import Submission.NegativeInner

/-!
Order-type covering for arbitrary RESTRICTED families of finite tuples.
The proof uses existing vertices in a four-cycle, not an extension of three
tuples to four in the full tuple space. This is auxiliary to Erdős 595.
-/

open SimpleGraph Set
namespace Erdos595RestrictedTuple
open Erdos595TupleType

variable {A I V : Type*} [LinearOrder A]

/-- A coordinate lying between two others has the same comparisons with a
fixed point whenever those two bounding coordinates have the same comparisons. -/
lemma middle_comparisons {a b c d : A} (hm : a ≤ b ↔ b ≤ c)
    (hl : a ≤ d ↔ c ≤ d) (hr : d ≤ a ↔ d ≤ c) :
    (b ≤ d ↔ a ≤ d) ∧ (d ≤ b ↔ d ≤ a) := by
  by_cases hab : a ≤ b
  · have hbc := hm.mp hab
    constructor
    · exact ⟨fun h => hab.trans h, fun h => hbc.trans (hl.mp h)⟩
    · exact ⟨fun h => hr.mpr (h.trans hbc), fun h => h.trans hab⟩
  · have hba : b ≤ a := le_of_not_ge hab
    have hcb : c ≤ b := le_of_not_ge (fun h => hab (hm.mpr h))
    constructor
    · exact ⟨fun h => hl.mpr (hcb.trans h), fun h => hba.trans h⟩
    · exact ⟨fun h => h.trans hba, fun h => (hr.mp h).trans hcb⟩

/-- An order-type-homogeneous three-edge path with a homogeneous shortcut
has a homogeneous second diagonal, on the EXISTING four tuples. -/
theorem four_cycle_second_diagonal (x₀ x₁ x₂ x₃ : I → A)
    (h₁ : pairType x₀ x₁ = pairType x₁ x₂)
    (h₂ : pairType x₀ x₁ = pairType x₂ x₃)
    (h₃ : pairType x₀ x₁ = pairType x₀ x₃) :
    pairType x₁ x₃ = pairType x₀ x₁ := by
  obtain ⟨h₁₀,h₁₁,h₁₂,h₁₃⟩ := pairType_eq_iff.mp h₁
  obtain ⟨h₂₀,h₂₁,h₂₂,h₂₃⟩ := pairType_eq_iff.mp h₂
  obtain ⟨h₃₀,h₃₁,h₃₂,h₃₃⟩ := pairType_eq_iff.mp h₃
  apply pairType_eq_iff.mpr
  refine ⟨fun i j => (h₁₀ i j).symm,?_,?_,fun i j => (h₃₃ i j).symm⟩
  · intro i j
    have hm := middle_comparisons (h₁₁ i i)
      ((h₃₁ i j).symm.trans (h₂₁ i j))
      ((h₃₂ j i).symm.trans (h₂₂ j i))
    exact hm.1.trans (h₃₁ i j).symm
  · intro i j
    have hm := middle_comparisons (h₁₁ j j)
      ((h₃₁ j i).symm.trans (h₂₁ j i))
      ((h₃₂ i j).symm.trans (h₂₂ i j))
    exact hm.2.trans (h₃₂ i j).symm

/-- Adjacency invariance only among the actual vertices, whose tuple labels
may lie in an arbitrary subset of the full tuple space. -/
def RelativeInvariant (G : SimpleGraph V) (v : V → I → A) : Prop :=
  ∀ a b c d, pairType (v a) (v b) = pairType (v c) (v d) →
    G.Adj a b → G.Adj c d

section Ordered
variable [LinearOrder V]

/-- A homogeneous triangle continuing an edge to a larger vertex. -/
def Later (G : SimpleGraph V) (v : V → I → A) (a b : V) : Prop :=
  ∃ c, b < c ∧ G.Adj a c ∧ G.Adj b c ∧
    pairType (v a) (v c) = pairType (v a) (v b) ∧
    pairType (v b) (v c) = pairType (v a) (v b)

noncomputable def code (G : SimpleGraph V) (v : V → I → A) (a b : V) :
    ((Bool × I) → (Bool × I) → Prop) × Bool := by
  classical
  exact (pairType (v a) (v b),decide (Later G v a b))

/-- Pair type together with one Boolean flag prevents monochromatic triangles.
This works even when the tuple labels form an arbitrary restricted family. -/
theorem code_valid (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (v : V → I → A) (hInv : RelativeInvariant G v)
    (a b c : V) (_hablt : a < b) (hbclt : b < c)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    ¬(code G v a b = code G v a c ∧ code G v a b = code G v b c) := by
  classical
  rintro ⟨he₁,he₂⟩
  have ht₁ : pairType (v a) (v b) = pairType (v a) (v c) := congrArg Prod.fst he₁
  have ht₂ : pairType (v a) (v b) = pairType (v b) (v c) := congrArg Prod.fst he₂
  have hlab : Later G v a b := ⟨c,hbclt,hac,hbc,ht₁.symm,ht₂.symm⟩
  have hflag : decide (Later G v a b) = decide (Later G v a c) := congrArg Prod.snd he₁
  have hlac : Later G v a c := by
    exact of_decide_eq_true (hflag.symm.trans (decide_eq_true hlab))
  obtain ⟨d,_,had,hcd,htad,htcd⟩ := hlac
  have htype : pairType (v b) (v d) = pairType (v a) (v b) :=
    four_cycle_second_diagonal (v a) (v b) (v c) (v d) ht₂
      (ht₁.trans htcd.symm) (ht₁.trans htad.symm)
  have hbd : G.Adj b d := hInv a b b d htype.symm hab
  exact Erdos595Work.no_adj_common_neighbors hG hab hac hbc had hbd hcd


/-- The ordered-pattern construction also gives an explicit finite palette
when the coordinate type I is finite: one comparison type and one Boolean. -/
theorem pattern_family (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (v : V → I → A) (hInv : RelativeInvariant G v) :
    ∃ H : (((Bool × I) → (Bool × I) → Prop) × Bool) → SimpleGraph V,
      (∀ t, (H t).CliqueFree 3) ∧ G = ⨆ t, H t := by
  classical
  let H : (((Bool × I) → (Bool × I) → Prop) × Bool) → SimpleGraph V := fun t =>
    { Adj := fun a b => G.Adj a b ∧ code G v (min a b) (max a b) = t
      symm := fun _ _ h => ⟨h.1.symm,by simpa only [min_comm,max_comm] using h.2⟩
      loopless := fun _ h => G.loopless _ h.1 }
  refine ⟨H,?_,?_⟩
  · intro t S hS
    let e := S.orderIsoOfFin hS.card_eq
    have hlt : ∀ i j : Fin 3, i < j → (e i).val < (e j).val :=
      fun i j hij => e.strictMono hij
    have hadj : ∀ i j : Fin 3, i ≠ j → (H t).Adj (e i).val (e j).val := by
      intro i j hij
      exact hS.isClique (e i).property (e j).property
        (fun he => hij (e.injective (Subtype.ext he)))
    have h01 := hadj 0 1 (by decide)
    have h02 := hadj 0 2 (by decide)
    have h12 := hadj 1 2 (by decide)
    have hc01 : code G v (e 0).val (e 1).val = t := by
      simpa only [min_eq_left (hlt 0 1 (by decide)).le,
        max_eq_right (hlt 0 1 (by decide)).le] using h01.2
    have hc02 : code G v (e 0).val (e 2).val = t := by
      simpa only [min_eq_left (hlt 0 2 (by decide)).le,
        max_eq_right (hlt 0 2 (by decide)).le] using h02.2
    have hc12 : code G v (e 1).val (e 2).val = t := by
      simpa only [min_eq_left (hlt 1 2 (by decide)).le,
        max_eq_right (hlt 1 2 (by decide)).le] using h12.2
    exact code_valid G hG v hInv _ _ _ (hlt 0 1 (by decide)) (hlt 1 2 (by decide))
      h01.1 h02.1 h12.1 ⟨hc01.trans hc02.symm,hc01.trans hc12.symm⟩
  · ext a b
    rw [SimpleGraph.iSup_adj]
    change G.Adj a b ↔ ∃ t, G.Adj a b ∧ code G v (min a b) (max a b) = t
    simp

end Ordered

/-- Every K4-free graph relatively order-type-invariant on a family of finite
tuples has a countable triangle-free edge cover. No closure, definability,
order invariance, or size assumption is imposed on the family itself. -/
theorem countable_cover [Finite I] (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (v : V → I → A) (hInv : RelativeInvariant G v) :
    Erdos595Work.IsCountableUnionOfTriangleFree G := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  exact Erdos595NegativeInner.cover_of_ordered_patterns G (code G v)
    (code_valid G hG v hInv)

/-- In particular, restrictions of an order-type-invariant ambient graph are
coverable as soon as the restriction, not necessarily the ambient graph, is K4-free. -/
theorem induced_countable_cover [Finite I] (G : SimpleGraph (I → A))
    (hInv : OrderTypeInvariant G) (S : Set (I → A)) (hS : (G.induce S).CliqueFree 4) :
    Erdos595Work.IsCountableUnionOfTriangleFree (G.induce S) := by
  apply countable_cover (G.induce S) hS Subtype.val
  intro a b c d ht hab
  exact hInv a b c d ht hab

#print axioms four_cycle_second_diagonal
#print axioms code_valid
#print axioms pattern_family
#print axioms countable_cover
#print axioms induced_countable_cover
end Erdos595RestrictedTuple
