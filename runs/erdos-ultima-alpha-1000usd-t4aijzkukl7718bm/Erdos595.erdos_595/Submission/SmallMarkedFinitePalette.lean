import Submission.SmallMarkedSecondRightCover
import Submission.FiniteFolkman

/-! A fixed finite palette for the small-marked second-right family.
This excludes a proposed universal representation; it does not settle Erdős 595. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open Set SimpleGraph
namespace Erdos595SmallMarkedFinitePalette
open Erdos595ArcAdjoint Erdos595FinitePalette
variable {V C D : Type*}

/-- The ordered-pattern construction preserves its palette. -/
theorem of_ordered_patterns [LinearOrder V] (G : SimpleGraph V) (code : V → V → C)
    (hc : ∀ a b c, a < b → b < c → G.Adj a b → G.Adj a c → G.Adj b c →
      ¬(code a b = code a c ∧ code a b = code b c)) : HasColoring G C := by
  classical
  let col : Sym2 V → C := Sym2.lift ⟨fun a b => code (min a b) (max a b), by
    intro a b; simp only [min_comm,max_comm]⟩
  let F : C → SimpleGraph V := fun k =>
    { Adj := fun a b => G.Adj a b ∧ col s(a,b) = k
      symm := fun _ _ h => ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
      loopless := fun _ h => h.1.ne rfl }
  have hF : ∀ k, (F k).CliqueFree 3 := by
    intro k T hT
    let f := T.orderIsoOfFin hT.card_eq
    have hlt : ∀ i j : Fin 3, i < j → (f i).val < (f j).val :=
      fun i j hij => f.strictMono hij
    have hadj : ∀ i j : Fin 3, i ≠ j → (F k).Adj (f i).val (f j).val := by
      intro i j hij
      exact hT.isClique (f i).property (f j).property
        (fun he => hij (f.injective (Subtype.ext he)))
    have h01 := hadj 0 1 (by decide)
    have h02 := hadj 0 2 (by decide)
    have h12 := hadj 1 2 (by decide)
    have h01' : code (f 0).val (f 1).val = k := by
      simpa only [col,Sym2.lift_mk,min_eq_left (hlt 0 1 (by decide)).le,
        max_eq_right (hlt 0 1 (by decide)).le] using h01.2
    have h02' : code (f 0).val (f 2).val = k := by
      simpa only [col,Sym2.lift_mk,min_eq_left (hlt 0 2 (by decide)).le,
        max_eq_right (hlt 0 2 (by decide)).le] using h02.2
    have h12' : code (f 1).val (f 2).val = k := by
      simpa only [col,Sym2.lift_mk,min_eq_left (hlt 1 2 (by decide)).le,
        max_eq_right (hlt 1 2 (by decide)).le] using h12.2
    exact hc _ _ _ (hlt 0 1 (by decide)) (hlt 1 2 (by decide))
      h01.1 h02.1 h12.1 ⟨h01'.trans h02'.symm,h01'.trans h12'.symm⟩
  refine ⟨col,?_⟩
  intro a b c hab hac hbc he
  exact hF (col s(a,b)) _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (F (col s(a,b))).Adj a b ∧ (F (col s(a,b))).Adj a c ∧
      (F (col s(a,b))).Adj b c from ⟨⟨hab,rfl⟩,⟨hac,he.1.symm⟩,⟨hbc,he.2.symm⟩⟩))

open Erdos595IndependentPairCover in
abbrev PairPalette := (Profile × Profile) × Option (Bool × Diagram)

open Erdos595IndependentPairCover in
theorem independent_pair (B : SimpleGraph V) (hB : B.CliqueFree 3) :
    HasColoring (RP B) PairPalette := by
  classical
  letI : LinearOrder (RV B) := IsWellOrder.linearOrder WellOrderingRel
  apply of_ordered_patterns (RP B) (color B)
  intro p q r _ _ hpq hpr hqr he
  have hpq' : profile B p = profile B q :=
    congrArg Prod.fst (congrArg Prod.fst he.2)
  have hqr' : profile B q = profile B r :=
    congrArg Prod.snd (congrArg Prod.fst he.1)
  have hpr' := hpq'.trans hqr'
  have hp := full_of_triangle_profile B hB p q r hpq hpr hqr hpq' hpr'
  have hq := full_of_profile B hpq' hp
  have hr := full_of_profile B hpr' hp
  have hk₁ := congrArg Prod.snd he.1
  have hk₂ := congrArg Prod.snd he.2
  rw [color_key B p q hp hq hpq,color_key B p r hp hr hpr] at hk₁
  rw [color_key B p q hp hq hpq,color_key B q r hq hr hqr] at hk₂
  exact key_valid B hB p q r hp hq hr hpq hpr hqr
    (Option.some.inj hk₁) (Option.some.inj hk₂)

open Erdos595RightCoverReduction in
theorem triangle_core (H : SimpleGraph V) (S : Set V)
    (hS : ∀ a b c, H.Adj a b → H.Adj a c → H.Adj b c → a ∈ S)
    (hJ : HasColoring (right (H.induce S)) C) :
    HasColoring (right H) (Option C) := by
  classical
  obtain ⟨col,hcol⟩ := hJ
  letI : LinearOrder (Biclique H) := IsWellOrder.linearOrder WellOrderingRel
  let tag (p q : Biclique H) : Option C :=
    if h : (right H).Adj p q then
      if h.1.choose ∈ S ∧ h.2.choose ∈ S then
        some (col s(restrict H S p,restrict H S q)) else none
    else none
  apply of_ordered_patterns (right H) tag
  intro p q r _ _ hpq hpr hqr he
  have x := hpq.1.choose_spec
  have y := hqr.1.choose_spec
  have z := hpr.2.choose_spec
  have x' := hpq.2.choose_spec
  have y' := hqr.2.choose_spec
  have z' := hpr.1.choose_spec
  have hxy := q.property _ x.2 _ y.1
  have hxz := (p.property _ z.2 _ x.1).symm
  have hyz := r.property _ y.2 _ z.1
  have hxy' := (q.property _ y'.2 _ x'.1).symm
  have hxz' := p.property _ x'.2 _ z'.1
  have hyz' := (r.property _ z'.2 _ y'.1).symm
  have hxS := hS _ _ _ hxy hxz hyz
  have hyS := hS _ _ _ hxy.symm hyz hxz
  have hzS := hS _ _ _ hxz.symm hyz.symm hxy
  have hxS' := hS _ _ _ hxy' hxz' hyz'
  have hyS' := hS _ _ _ hxy'.symm hyz' hxz'
  have hzS' := hS _ _ _ hxz'.symm hyz'.symm hxy'
  simp only [tag,dif_pos hpq,dif_pos hpr,dif_pos hqr,
    hxS,hxS',hyS,hyS',hzS,hzS',and_self,if_true,Option.some.injEq] at he
  exact hcol _ _ _ (restrict_adj H S hpq hxS hxS')
    (restrict_adj H S hpr hzS' hzS) (restrict_adj H S hqr hyS hyS') he

open Erdos595RightCoverReduction Erdos595RightProperTransversal in
theorem delete_colored (H : SimpleGraph V) (S : Set V) (c : (H.induce S).Coloring D)
    (hJ : HasColoring (right (H.induce Sᶜ)) C) :
    HasColoring (right H) ((Set D × Set D) × C) := by
  classical
  obtain ⟨col,hcol⟩ := hJ
  letI : LinearOrder (Biclique H) := IsWellOrder.linearOrder WellOrderingRel
  let tag (p q : Biclique H) :=
    ((code H S c p,code H S c q),col s(restrict H Sᶜ p,restrict H Sᶜ q))
  apply of_ordered_patterns (right H) tag
  intro p q r _ _ hpq hpr hqr he
  have hpq' : code H S c p = code H S c q :=
    congrArg Prod.fst (congrArg Prod.fst he.2)
  have hqr' : code H S c q = code H S c r :=
    congrArg Prod.snd (congrArg Prod.fst he.1)
  have edge {a b : Biclique H} (h : (right H).Adj a b)
      (hc : code H S c a = code H S c b) :
      (right (H.induce Sᶜ)).Adj (restrict H Sᶜ a) (restrict H Sᶜ b) := by
    apply restrict_adj H Sᶜ h
    · exact witness_outside H S c a b hc _ h.1.choose_spec.1 h.1.choose_spec.2
    · exact witness_outside H S c b a hc.symm _ h.2.choose_spec.1 h.2.choose_spec.2
  exact hcol _ _ _ (edge hpq hpq') (edge hpr (hpq'.trans hqr')) (edge hqr hqr')
    ⟨congrArg Prod.snd he.1,congrArg Prod.snd he.2⟩

abbrev Palette := ((Set Bool × Set Bool) × Option PairPalette)

open Erdos595SmallMarkedSecondRight in
theorem small_marked (H : SimpleGraph V) (m : V → Bool) (h : Conditions H m) :
    HasColoring (right (right H)) Palette := by
  classical
  apply delete_colored (right H) (Pure H m) (pureColor H m h)
  let J := (right H).induce (Pure H m)ᶜ
  let S : Set {p : P H // ¬Pure H m p} := {p | Good H m p.val}
  apply triangle_core J S
  · intro p q r hpq hpr hqr
    exact good_of_triangle H m h p.property hpq hpr hqr
  · let d (p : S) : Packet H m p.val.val := Classical.choice p.property
    let f : J.induce S →g Erdos595IndependentPair.graph (oldGraph H m) :=
      { toFun p := ((d p).pair,(d p).bit)
        map_rel' := fun {p q} hpq => packet_adj H m (d p) (d q) hpq }
    exact (independent_pair (oldGraph H m) (old_triangleFree H m h)).comap
      (Erdos595IndependentPair.rightMap f)

/-- The target carrier may have any size. Even finite K4-free sources cannot
all map through their second arc graphs into the small-marked class. -/
theorem finite_representation_failure :
    ∃ (A : Type) (_ : Finite A) (G : SimpleGraph A), G.CliqueFree 4 ∧
      ∀ (V : Type) (H : SimpleGraph V) (m : V → Bool),
        Erdos595SmallMarkedSecondRight.Conditions H m →
          ¬Nonempty (arcGraph (arcGraph G) →g H) := by
  classical
  obtain ⟨A,hA,G,hG,hbad⟩ := Erdos595FiniteFolkman.finite_folkman Palette
  refine ⟨A,hA,G,hG,?_⟩
  intro V H m h ⟨f⟩
  exact hbad ((small_marked H m h).comap (toRight (toRight f)))

#print axioms independent_pair
#print axioms small_marked
#print axioms finite_representation_failure
end Erdos595SmallMarkedFinitePalette
