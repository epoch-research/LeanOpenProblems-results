import Submission.ArcAdjoint
import Submission.NegativeInner

/-!
A structural obstruction to right-adjoint constructions: forbidding an ordered
alternating four-cycle in the base graph forces its biclique right adjoint to
have a countable triangle-free edge cover. This does not settle Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595NoAlternating
open Erdos595ArcAdjoint Erdos595Work

variable {V W K : Type*}

/-- The four cycle vertices, in their linear order, alternate between its sides. -/
def NoAlternating [LinearOrder V] (G : SimpleGraph V) : Prop :=
  ∀ a b c d, a < b → b < c → c < d →
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

/-- A label version, allowing distinct nonadjacent vertices to have equal labels. -/
def NoAlternatingLabel [LinearOrder K] (G : SimpleGraph V) (f : V → K) : Prop :=
  ∀ a b c d, f a < f b → f b < f c → f c < f d →
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

private def Later [LinearOrder K] (G : SimpleGraph V) (f : V → K) (a b : V) : Prop :=
  ∃ c, f b < f c ∧ G.Adj a c ∧ G.Adj b c

private def Earlier [LinearOrder K] (G : SimpleGraph V) (f : V → K) (a b : V) : Prop :=
  ∃ c, f c < f b ∧ G.Adj a c ∧ G.Adj b c

/-- The direction of the labels and two extension flags give a finite palette. -/
theorem cover_of_label [LinearOrder K] (G : SimpleGraph V) (f : V → K)
    (hne : ∀ a b, G.Adj a b → f a ≠ f b)
    (hG : NoAlternatingLabel G f) : IsCountableUnionOfTriangleFree G := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  let code (a b : V) : Bool × Bool × Bool :=
    (decide (f a < f b), decide (Later G f a b), decide (Earlier G f a b))
  apply Erdos595NegativeInner.cover_of_ordered_patterns G code
  intro a b c _ _ hab hac hbc he
  have hdir : (f a < f b) ↔ (f b < f c) := by
    have := congrArg Prod.fst he.2
    simpa only [code, decide_eq_decide] using this
  rcases lt_or_gt_of_ne (hne a b hab) with hlt | hgt
  · have hbc' := hdir.mp hlt
    have hflag : decide (Later G f a b) = decide (Later G f a c) :=
      congrArg (fun p => p.2.1) he.1
    have hl : Later G f a b := ⟨c,hbc',hac,hbc⟩
    have hl' : Later G f a c := by
      exact of_decide_eq_true (hflag.symm.trans (decide_eq_true hl))
    obtain ⟨d,hcd,had,hcd'⟩ := hl'
    exact hG a b c d hlt hbc' hcd hab hbc hcd' had.symm
  · have hcb : f c < f b := lt_of_le_of_ne
      (le_of_not_gt (fun h => (not_lt_of_gt hgt) (hdir.mpr h))) (hne b c hbc).symm
    have hflag : decide (Earlier G f a b) = decide (Earlier G f a c) :=
      congrArg (fun p => p.2.2) he.1
    have hl : Earlier G f a b := ⟨c,hcb,hac,hbc⟩
    have hl' : Earlier G f a c := by
      exact of_decide_eq_true (hflag.symm.trans (decide_eq_true hl))
    obtain ⟨d,hdc,had,hcd⟩ := hl'
    exact hG d c b a hdc hcb hgt hcd.symm hbc.symm hab.symm had

variable [LinearOrder V] (G : SimpleGraph V)

/-- Every point of the second side lies entirely before or after the first side. -/
def Inner (A B : Set V) : Prop :=
  ∀ b ∈ B, (∀ a ∈ A, b < a) ∨ (∀ a ∈ A, a < b)

lemma inner_or (hG : NoAlternating G) (p : Biclique G) :
    Inner p.1.1 p.1.2 ∨ Inner p.1.2 p.1.1 := by
  classical
  by_contra hn
  have h₁ : ¬Inner p.1.1 p.1.2 := fun h => hn (Or.inl h)
  have h₂ : ¬Inner p.1.2 p.1.1 := fun h => hn (Or.inr h)
  simp only [Inner, not_forall, not_or, not_lt, exists_prop] at h₁ h₂
  obtain ⟨b,hb,⟨a₀,ha₀,h₀⟩,a₁,ha₁,h₁⟩ := h₁
  obtain ⟨a,ha,⟨b₀,hb₀,k₀⟩,b₁,hb₁,k₁⟩ := h₂
  have hab : a ≠ b := (p.2 a ha b hb).ne
  have ha₀b : a₀ < b := lt_of_le_of_ne h₀ (p.2 a₀ ha₀ b hb).ne
  have hba₁ : b < a₁ := lt_of_le_of_ne h₁ (p.2 a₁ ha₁ b hb).ne.symm
  have hb₀a : b₀ < a := lt_of_le_of_ne k₀ (p.2 a ha b₀ hb₀).ne.symm
  have hab₁ : a < b₁ := lt_of_le_of_ne k₁ (p.2 a ha b₁ hb₁).ne
  rcases lt_or_gt_of_ne hab with h | h
  · exact hG b₀ a b a₁ hb₀a h hba₁ (p.2 a ha b₀ hb₀).symm
      (p.2 a ha b hb) (p.2 a₁ ha₁ b hb).symm (p.2 a₁ ha₁ b₀ hb₀)
  · exact hG a₀ b a b₁ ha₀b h hab₁ (p.2 a₀ ha₀ b hb)
      (p.2 a ha b hb).symm (p.2 a ha b₁ hb₁) (p.2 a₀ ha₀ b₁ hb₁).symm

/-- The strict lower cut of a side. Lower cuts are linearly ordered by inclusion. -/
def cut (A : Set V) : LowerSet V :=
  ⟨{x | ∀ a ∈ A, x < a}, fun _ _ hxy hx a ha => lt_of_le_of_lt hxy (hx a ha)⟩

lemma witness_right (p q : Biclique G) (hp : Inner p.1.1 p.1.2)
    (hpq : cut p.1.1 ≤ cut q.1.1) {x : V} (hxp : x ∈ p.1.2) (hxq : x ∈ q.1.1) :
    ∀ a ∈ p.1.1, a < x := by
  rcases hp x hxp with h | h
  · exact (lt_irrefl x ((hpq h) x hxq)).elim
  · exact h

lemma cut_ne (p q : Biclique G) (hp : Inner p.1.1 p.1.2)
    (hq : Inner q.1.1 q.1.2) (hpq : (right G).Adj p q) :
    cut p.1.1 ≠ cut q.1.1 := by
  intro he
  obtain ⟨x,hxp,hxq⟩ := hpq.1
  obtain ⟨y,hyq,hyp⟩ := hpq.2
  exact (lt_asymm (witness_right G p q hp he.le hxp hxq y hyp)
    (witness_right G q p hq he.symm.le hyq hyp x hxq))

/-- On the inner-left-side class, the lower cuts inherit the no-alternation rule. -/
lemma inner_no_alternating (hG : NoAlternating G)
    (p q r s : Biclique G)
    (hp : Inner p.1.1 p.1.2) (hq : Inner q.1.1 q.1.2) (hr : Inner r.1.1 r.1.2)
    (hpq : cut p.1.1 ≤ cut q.1.1) (hqr : cut q.1.1 ≤ cut r.1.1)
    (hrs : cut r.1.1 ≤ cut s.1.1)
    (hpq' : (right G).Adj p q) (hqr' : (right G).Adj q r)
    (hrs' : (right G).Adj r s) (hsp : (right G).Adj s p) : False := by
  obtain ⟨x,hxp,hxq⟩ := hpq'.1
  obtain ⟨y,hyq,hyr⟩ := hqr'.1
  obtain ⟨z,hzr,hzs⟩ := hrs'.1
  obtain ⟨w,hws,hwp⟩ := hsp.1
  exact hG w x y z
    (witness_right G p q hp hpq hxp hxq w hwp)
    (witness_right G q r hq hqr hyq hyr x hxq)
    (witness_right G r s hr hrs hzr hzs y hyr)
    (p.2 w hwp x hxp) (q.2 x hxq y hyq) (r.2 y hyr z hzr) (s.2 z hzs w hws)

/-- One class of the vertex partition is coverable. -/
theorem inner_cover (hG : NoAlternating G) :
    IsCountableUnionOfTriangleFree ((right G).induce {p | Inner p.1.1 p.1.2}) := by
  let H := (right G).induce {p | Inner p.1.1 p.1.2}
  apply cover_of_label H (fun p => cut p.1.1.1)
  · intro p q hpq
    exact cut_ne G p q p.2 q.2 hpq
  · intro p q r s hpq hqr hrs hpq' hqr' hrs' hsp
    exact inner_no_alternating G hG p q r s p.2 q.2 r.2 hpq.le hqr.le hrs.le
      hpq' hqr' hrs' hsp

def swap (p : Biclique G) : Biclique G :=
  ⟨(p.1.2,p.1.1), fun a ha b hb => (p.2 b hb a ha).symm⟩

lemma swap_adj {p q : Biclique G} (hpq : (right G).Adj p q) :
    (right G).Adj (swap G p) (swap G q) := by
  obtain ⟨x,hxp,hxq⟩ := hpq.1
  obtain ⟨y,hyq,hyp⟩ := hpq.2
  exact ⟨⟨y,hyp,hyq⟩,⟨x,hxq,hxp⟩⟩

/-- Orient each biclique so that its first side is an inner side. -/
noncomputable def orient (hG : NoAlternating G) (p : Biclique G) :
    {p : Biclique G // Inner p.1.1 p.1.2} := by
  classical
  exact if h : Inner p.1.1 p.1.2 then ⟨p,h⟩
    else ⟨swap G p, (inner_or G hG p).resolve_left h⟩

/-- The entire right adjoint is coverable, with no cardinality bound on the
linear order or the biclique sides. -/
theorem right_cover (hG : NoAlternating G) :
    IsCountableUnionOfTriangleFree (right G) := by
  classical
  let tag (p : Biclique G) : ℕ → Fin 2 :=
    fun _ => if Inner p.1.1 p.1.2 then 0 else 1
  apply countable_union_of_vertex_pieces (right G) tag
  intro i
  let F : vertexPiece (right G) tag i →g
      (right G).induce {p | Inner p.1.1 p.1.2} :=
    { toFun := orient G hG
      map_rel' := by
        intro p q hpq
        have he : tag p 0 = tag q 0 := congrFun (hpq.2.1.trans hpq.2.2.symm) 0
        have hiff : Inner p.1.1 p.1.2 ↔ Inner q.1.1 q.1.2 := by
          by_cases hp : Inner p.1.1 p.1.2 <;>
            by_cases hq : Inner q.1.1 q.1.2 <;> simp_all [tag]
        by_cases hp : Inner p.1.1 p.1.2
        · have hq := hiff.mp hp
          simpa only [orient, dif_pos hp, dif_pos hq] using hpq.1
        · have hq : ¬Inner q.1.1 q.1.2 := fun h => hp (hiff.mpr h)
          simpa only [orient, dif_neg hp, dif_neg hq] using swap_adj G hpq.1 }
  exact countable_union_of_hom F (inner_cover G hG)

omit [LinearOrder V] in
/-- Equal labels can be broken by a well-order: adjacency only uses distinct labels. -/
theorem right_cover_of_label [LinearOrder K] (f : V → K)
    (hne : ∀ a b, G.Adj a b → f a ≠ f b)
    (hG : NoAlternatingLabel G f) : IsCountableUnionOfTriangleFree (right G) := by
  classical
  let old : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  letI : LinearOrder V := old
  let e (v : V) : K ×ₗ V := toLex (f v,v)
  have he : Function.Injective e := by
    intro a b hab
    exact congrArg Prod.snd (toLex_inj.mp hab)
  let target : LinearOrder (K ×ₗ V) := inferInstance
  letI : LinearOrder V := @LinearOrder.lift' V (K ×ₗ V) target e he
  have hlt : ∀ a b : V, a < b → G.Adj a b → f a < f b := by
    intro a b hab hAdj
    have hh : @LT.lt (K ×ₗ V) target.toLT (e a) (e b) := hab
    have hor : f a < f b ∨ f a = f b ∧ @LT.lt V old.toLT a b :=
      (@Prod.Lex.lt_iff K V _ old.toLT (e a) (e b)).mp hh
    exact hor.elim id (fun h => (hne a b hAdj h.1).elim)
  apply right_cover G
  intro a b c d hab hbc hcd hab' hbc' hcd' hda
  exact hG a b c d (hlt a b hab hab') (hlt b c hbc hbc') (hlt c d hcd hcd')
    hab' hbc' hcd' hda

omit [LinearOrder V] in
/-- Base homomorphisms transport right-adjoint covers, by the adjunction. -/
theorem right_cover_of_base_hom {H : SimpleGraph W} (f : H →g G)
    (hG : IsCountableUnionOfTriangleFree (right G)) :
    IsCountableUnionOfTriangleFree (right H) := by
  let F : right H →g right G :=
    toRight (f.comp (fromRight (SimpleGraph.Hom.id : right H →g right H)))
  exact countable_union_of_hom F hG

#print axioms inner_cover
#print axioms right_cover
#print axioms right_cover_of_label
end Erdos595NoAlternating
