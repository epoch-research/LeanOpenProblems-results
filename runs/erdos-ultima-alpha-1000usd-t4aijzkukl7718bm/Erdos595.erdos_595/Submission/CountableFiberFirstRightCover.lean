import Submission.FiniteFiberUniversal

/-!
A countable-fiber graph over a triangle-free index graph has a countably
triangle-free-edge-covered first biclique right adjoint. Edges may stay
inside a fiber or project to an index edge; no fixed fiber template is needed.
This is an auxiliary exclusion, not a settlement of Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595CountableFiberFirstRight
open Erdos595ArcAdjoint Erdos595Work

variable {I S : Type*} (H : SimpleGraph (I × S)) (B : SimpleGraph I)
  (hproj : ∀ {x y}, H.Adj x y → x.1 = y.1 ∨ B.Adj x.1 y.1)
  (hB : B.CliqueFree 3)

abbrev P := Biclique H

def separated (p : P H) : Prop :=
  ∀ x ∈ p.val.1, ∀ y ∈ p.val.2, x.1 ≠ y.1

def leftSmall (p : P H) : Prop :=
  ∀ x ∈ p.val.1, ∀ y ∈ p.val.1, x.1 = y.1

def rightSmall (p : P H) : Prop :=
  ∀ x ∈ p.val.2, ∀ y ∈ p.val.2, x.1 = y.1

def leftCode (p : P H) : Set S := Prod.snd '' p.val.1

def rightCode (p : P H) : Set S := Prod.snd '' p.val.2

include hB in
private lemma no_triangle {a b c : I} (hab : B.Adj a b)
    (hac : B.Adj a c) (hbc : B.Adj b c) : False := by
  classical
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)

include hproj hB in
lemma separated_no_triangle {p q r : P H}
    (hp : separated H p) (hq : separated H q) (hr : separated H r)
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r)
    (hqr : (right H).Adj q r) : False := by
  obtain ⟨x,hxp,hxq⟩ := hpq.1
  obtain ⟨y,hyq,hyr⟩ := hqr.1
  obtain ⟨z,hzr,hzp⟩ := hpr.2
  exact no_triangle B hB
    ((hproj (q.property x hxq y hyq)).resolve_left (hq _ hxq _ hyq))
    ((hproj (p.property z hzp x hxp)).resolve_left (hp _ hzp _ hxp)).symm
    ((hproj (r.property y hyr z hzr)).resolve_left (hr _ hyr _ hzr))

private lemma left_transport {p q : P H} (hp : leftSmall H p)
    (he : leftCode H p = leftCode H q) {x y : I × S}
    (hx : x ∈ p.val.1) (hy : y ∈ q.val.1) (hxy : x.1 = y.1) :
    y ∈ p.val.1 := by
  have hy' : y.2 ∈ leftCode H p := he ▸ (show y.2 ∈ leftCode H q from ⟨y,hy,rfl⟩)
  obtain ⟨z,hz,hzy⟩ := hy'
  have hz' : z = y := Prod.ext ((hp z hz x hx).trans hxy) hzy
  exact hz' ▸ hz

include hproj hB in
lemma left_no_triangle {p q r : P H}
    (hp : leftSmall H p) (hq : leftSmall H q) (hr : leftSmall H r)
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r)
    (hqr : (right H).Adj q r)
    (heq : leftCode H p = leftCode H q) (her : leftCode H p = leftCode H r) : False := by
  obtain ⟨x,hxp,hxq⟩ := hpq.1
  obtain ⟨y,hyq,hyr⟩ := hqr.1
  obtain ⟨z,hzr,hzp⟩ := hpr.2
  have hzxn : z.1 ≠ x.1 := by
    intro he
    exact H.loopless x (p.property x (left_transport H hp heq hzp hxq he) x hxp)
  have hxyn : x.1 ≠ y.1 := by
    intro he
    exact H.loopless y (q.property y
      (left_transport H hq (heq.symm.trans her) hxq hyr he) y hyq)
  have hyzn : y.1 ≠ z.1 := by
    intro he
    exact H.loopless z (r.property z (left_transport H hr her.symm hyr hzp he) z hzr)
  exact no_triangle B hB
    ((hproj (q.property x hxq y hyq)).resolve_left hxyn)
    ((hproj (p.property z hzp x hxp)).resolve_left hzxn).symm
    ((hproj (r.property y hyr z hzr)).resolve_left hyzn)

def swap (p : P H) : P H :=
  ⟨(p.val.2,p.val.1),fun _ hx _ hy => (p.property _ hy _ hx).symm⟩

lemma swap_adj {p q : P H} (hpq : (right H).Adj p q) :
    (right H).Adj (swap H p) (swap H q) :=
  ⟨by obtain ⟨x,hx,hy⟩ := hpq.2; exact ⟨x,hy,hx⟩,
   by obtain ⟨x,hx,hy⟩ := hpq.1; exact ⟨x,hy,hx⟩⟩

include hproj hB in
lemma right_no_triangle {p q r : P H}
    (hp : rightSmall H p) (hq : rightSmall H q) (hr : rightSmall H r)
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r)
    (hqr : (right H).Adj q r)
    (heq : rightCode H p = rightCode H q) (her : rightCode H p = rightCode H r) : False :=
  left_no_triangle H B hproj hB (p := swap H p) (q := swap H q) (r := swap H r) hp hq hr
    (swap_adj H hpq) (swap_adj H hpr) (swap_adj H hqr) heq her

section Order
variable [LinearOrder I]

structure TwoSupport (p : P H) (i j : I) : Prop where
  increasing : i < j
  left : ∀ x ∈ p.val.1, x.1 = i ∨ x.1 = j
  right : ∀ x ∈ p.val.2, x.1 = i ∨ x.1 = j
  left_lo : ∃ s, (i,s) ∈ p.val.1
  left_hi : ∃ s, (j,s) ∈ p.val.1
  right_lo : ∃ s, (i,s) ∈ p.val.2
  right_hi : ∃ s, (j,s) ∈ p.val.2

include hproj hB in
lemma two_support {p : P H} (hs : ¬separated H p)
    (hl : ¬leftSmall H p) (hr : ¬rightSmall H p) :
    ∃ i j, TwoSupport H p i j := by
  classical
  simp only [separated, not_forall, not_not] at hs
  obtain ⟨x,hx,y,hy,hxy⟩ := hs
  have hl' : ∃ a ∈ p.val.1, a.1 ≠ x.1 := by
    by_contra hn
    push_neg at hn
    exact hl (fun a ha b hb => (hn a ha).trans (hn b hb).symm)
  have hr' : ∃ b ∈ p.val.2, b.1 ≠ x.1 := by
    by_contra hn
    push_neg at hn
    exact hr (fun a ha b hb => (hn a ha).trans (hn b hb).symm)
  obtain ⟨a,ha,hax⟩ := hl'
  obtain ⟨b,hb,hbx⟩ := hr'
  have different {c d : I × S} (hc : c ∈ p.val.1) (hd : d ∈ p.val.2)
      (hcx : c.1 ≠ x.1) (hdx : d.1 ≠ x.1) : c.1 = d.1 := by
    by_contra hcd
    have hxc : B.Adj x.1 c.1 := by
      have hh := (hproj (p.property c hc y hy)).resolve_left (fun h => hcx (h.trans hxy.symm))
      simpa only [← hxy] using hh.symm
    have hxd : B.Adj x.1 d.1 :=
      (hproj (p.property x hx d hd)).resolve_left hdx.symm
    exact no_triangle B hB hxc hxd ((hproj (p.property c hc d hd)).resolve_left hcd)
  have hab : a.1 = b.1 := different ha hb hax hbx
  have hL : ∀ c ∈ p.val.1, c.1 = x.1 ∨ c.1 = a.1 := by
    intro c hc
    by_cases hc' : c.1 = x.1
    · exact Or.inl hc'
    · exact Or.inr ((different hc hb hc' hbx).trans hab.symm)
  have hR : ∀ d ∈ p.val.2, d.1 = x.1 ∨ d.1 = a.1 := by
    intro d hd
    by_cases hd' : d.1 = x.1
    · exact Or.inl hd'
    · exact Or.inr (different ha hd hax hd').symm
  have hyl : (x.1,y.2) ∈ p.val.2 := by simpa only [hxy] using hy
  have hbh : (a.1,b.2) ∈ p.val.2 := by simpa only [hab] using hb
  rcases lt_or_gt_of_ne hax.symm with hh | hh
  · exact ⟨x.1,a.1,hh,hL,hR,⟨x.2,hx⟩,⟨a.2,ha⟩,⟨y.2,hyl⟩,⟨b.2,hbh⟩⟩
  · exact ⟨a.1,x.1,hh,(fun c hc => (hL c hc).symm),
      (fun d hd => (hR d hd).symm),⟨a.2,ha⟩,⟨x.2,hx⟩,⟨b.2,hbh⟩,⟨y.2,hyl⟩⟩

def twoCode (p : P H) (i j : I) : Set S × Set S :=
  ({s | (i,s) ∈ p.val.1},{s | (j,s) ∈ p.val.1})

lemma two_adj {p q : P H} {i j k l : I}
    (hp : TwoSupport H p i j) (hq : TwoSupport H q k l)
    (he : twoCode H p i j = twoCode H q k l)
    (hpq : (right H).Adj p q) : j = k ∨ l = i := by
  obtain ⟨x,hxp,hxq⟩ := hpq.1
  have hlo : ∀ s, ((i,s) ∈ p.val.1 ↔ (k,s) ∈ q.val.1) :=
    fun s => Set.ext_iff.mp (congrArg Prod.fst he) s
  have hhi : ∀ s, ((j,s) ∈ p.val.1 ↔ (l,s) ∈ q.val.1) :=
    fun s => Set.ext_iff.mp (congrArg Prod.snd he) s
  rcases hp.right x hxp with hxi | hxj <;> rcases hq.left x hxq with hxk | hxl
  · have hh : (i,x.2) ∈ p.val.1 := (hlo x.2).mpr (by simpa only [← hxk] using hxq)
    exact (H.loopless x (p.property x (by simpa only [← hxi] using hh) x hxp)).elim
  · exact Or.inr (hxl.symm.trans hxi)
  · exact Or.inl (hxj.symm.trans hxk)
  · have hh : (j,x.2) ∈ p.val.1 := (hhi x.2).mpr (by simpa only [← hxl] using hxq)
    exact (H.loopless x (p.property x (by simpa only [← hxj] using hh) x hxp)).elim

lemma two_no_triangle {p q r : P H} {i j k l m n : I}
    (hp : TwoSupport H p i j) (hq : TwoSupport H q k l)
    (hr : TwoSupport H r m n)
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r)
    (hqr : (right H).Adj q r)
    (heq : twoCode H p i j = twoCode H q k l)
    (her : twoCode H p i j = twoCode H r m n) : False := by
  classical
  let x : {p : I × I // p.1 < p.2} := ⟨(i,j),hp.increasing⟩
  let y : {p : I × I // p.1 < p.2} := ⟨(k,l),hq.increasing⟩
  let z : {p : I × I // p.1 < p.2} := ⟨(m,n),hr.increasing⟩
  have hxy : (orderedShiftGraph I).Adj x y := two_adj H hp hq heq hpq
  have hxz : (orderedShiftGraph I).Adj x z := two_adj H hp hr her hpr
  have hyz : (orderedShiftGraph I).Adj y z := two_adj H hq hr (heq.symm.trans her) hqr
  exact orderedShiftGraph_cliqueFree I _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)

inductive Shape (p : P H) where
  | sep (h : separated H p)
  | left (h : leftSmall H p)
  | right (h : rightSmall H p)
  | two (i j : I) (h : TwoSupport H p i j)

def Shape.code {p : P H} : Shape H p → Fin 4 × (Set S × Set S)
  | .sep _ => (0,(∅,∅))
  | .left _ => (1,(leftCode H p,∅))
  | .right _ => (2,(rightCode H p,∅))
  | .two i j _ => (3,twoCode H p i j)

include hproj hB in
noncomputable def shape (p : P H) : Shape H p := by
  classical
  by_cases hs : separated H p
  · exact .sep hs
  by_cases hl : leftSmall H p
  · exact .left hl
  by_cases hr : rightSmall H p
  · exact .right hr
  let ht := two_support H B hproj hB hs hl hr
  exact .two ht.choose ht.choose_spec.choose ht.choose_spec.choose_spec

include hproj hB in
lemma shape_no_triangle {p q r : P H} (sp : Shape H p) (sq : Shape H q) (sr : Shape H r)
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r) (hqr : (right H).Adj q r)
    (heq : sp.code H = sq.code H) (her : sp.code H = sr.code H) : False := by
  cases sp <;> cases sq <;> cases sr <;>
    simp only [Shape.code,Prod.mk.injEq,Fin.reduceEq,false_and,true_and] at heq her
  · exact separated_no_triangle H B hproj hB ‹_› ‹_› ‹_› hpq hpr hqr
  · exact left_no_triangle H B hproj hB ‹_› ‹_› ‹_› hpq hpr hqr heq.1 her.1
  · exact right_no_triangle H B hproj hB ‹_› ‹_› ‹_› hpq hpr hqr heq.1 her.1
  · exact two_no_triangle H ‹_› ‹_› ‹_› hpq hpr hqr heq her

end Order

abbrev Code (S : Type*) := Fin 4 × (Set S × Set S)
abbrev Index (S : Type*) := Fin 4 ⊕ (Bool × S)

def encode (c : Code S) : Set (Index S)
  | .inl t => t = c.1
  | .inr (false,s) => s ∈ c.2.1
  | .inr (true,s) => s ∈ c.2.2

lemma encode_injective : Function.Injective (encode (S := S)) := by
  intro c d he
  apply Prod.ext
  · have h := Set.ext_iff.mp he (Sum.inl c.1)
    exact h.mp rfl
  · apply Prod.ext
    · ext s
      exact Set.ext_iff.mp he (Sum.inr (false,s))
    · ext s
      exact Set.ext_iff.mp he (Sum.inr (true,s))

private theorem cover_of_countable_set_codes {V J : Type*} [Countable J]
    (G : SimpleGraph V) (f : V → Set J)
    (hf : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
      ¬(f a = f b ∧ f a = f c)) : IsCountableUnionOfTriangleFree G := by
  classical
  obtain ⟨e,he⟩ := exists_injective_nat J
  let g : V → ℕ → Fin 2 := fun v n => if ∃ j, e j = n ∧ j ∈ f v then 1 else 0
  have hg {a b} (hab : g a = g b) : f a = f b := by
    ext j
    have hh := congrFun hab (e j)
    simp only [g,he.eq_iff,exists_eq_left] at hh
    by_cases ha : j ∈ f a <;> by_cases hb : j ∈ f b <;> simp_all
  apply countable_union_of_triangle_free_fibers G g
  intro a b c hab hac hbc hh
  exact hf a b c hab hac hbc ⟨hg hh.1,hg hh.2⟩

include hproj hB in
/-- Countable fibers suffice; the quotient relation need only be triangle-free.
The resulting vertex codes have triangle-free fibers. -/
theorem first_right_cover [Countable S] : IsCountableUnionOfTriangleFree (right H) := by
  classical
  letI : LinearOrder I := IsWellOrder.linearOrder WellOrderingRel
  let c (p : P H) : Code S := (shape H B hproj hB p).code H
  apply cover_of_countable_set_codes (right H) (encode ∘ c)
  intro p q r hpq hpr hqr hh
  exact shape_no_triangle H B hproj hB
    (shape H B hproj hB p) (shape H B hproj hB q) (shape H B hproj hB r)
    hpq hpr hqr (encode_injective hh.1) (encode_injective hh.2)

section Bundle
open Erdos595FiniteFiberOddBound
universe u
variable {J T : Type u}

theorem bundle_first_right_cover [Countable T] (F : SimpleGraph T)
    (R : T → T → Prop) (hR : Symmetric R) (D : SimpleGraph J) (hD : D.CliqueFree 3) :
    IsCountableUnionOfTriangleFree (right (bundle F R hR D)) :=
  first_right_cover _ D (fun h => h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)) hD

/-- This closes the first stage of the universal two-three-coloring template. -/
theorem universal_first_right_cover (D : SimpleGraph J) (hD : D.CliqueFree 3) :
    IsCountableUnionOfTriangleFree
      (right (bundle Erdos595FiniteFiberUniversal.fiber Erdos595FiniteFiberUniversal.cross
        Erdos595FiniteFiberUniversal.cross_symm D)) :=
  bundle_first_right_cover _ _ _ D hD

end Bundle

#print axioms universal_first_right_cover
#print axioms bundle_first_right_cover
#print axioms first_right_cover
end Erdos595CountableFiberFirstRight
