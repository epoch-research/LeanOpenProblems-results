import Submission.IndependentPairCover
import Submission.RightCoverReduction
import Submission.MatchingBundleRightCover

/-! Independent triangle transversals with small independent neighborhoods
cannot yield a non-coverable second right adjoint. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open Set SimpleGraph
namespace Erdos595SmallMarkedSecondRight
open Erdos595ArcAdjoint Erdos595Work Erdos595MatchingBundle
variable {V : Type*} (H : SimpleGraph V) (m : V → Bool)

structure Conditions : Prop where
  independent : ∀ a b, m a = true → m b = true → ¬H.Adj a b
  hit : ∀ a b c, H.Adj a b → H.Adj a c → H.Adj b c →
    m a = true ∨ m b = true ∨ m c = true
  small : ∀ a b c, m a = true → H.Adj a b → H.Adj a c → H.Adj b c →
    ∀ x y z, H.Adj a x → H.Adj a y → H.Adj a z →
      ¬H.Adj x y → ¬H.Adj x z → ¬H.Adj y z → x = y ∨ x = z ∨ y = z

abbrev Old := {v : V // m v = false}
abbrev oldGraph : SimpleGraph (Old m) := H.induce {v | m v = false}
abbrev P := Biclique H

def side (p : P H) (s : Bool) : Set V := if s then p.val.2 else p.val.1

def PureSide (p : P H) (s : Bool) : Prop :=
  (side H p s).Nonempty ∧ ∀ a ∈ side H p s, m a = true

def Pure (p : P H) : Prop := ∃ s, PureSide H m p s

lemma cross (p : P H) (s : Bool) {a b : V}
    (ha : a ∈ side H p s) (hb : b ∈ side H p (!s)) : H.Adj a b := by
  cases s
  · exact p.property _ ha _ hb
  · exact (p.property _ hb _ ha).symm

variable (h : Conditions H m)

include h in
lemma pure_independent (p q : P H) (s : Bool)
    (hp : PureSide H m p s) (hq : PureSide H m q s) : ¬(right H).Adj p q := by
  intro hpq
  obtain ⟨a,ha⟩ := hp.1
  cases s
  · obtain ⟨b,hbp,hbq⟩ := hpq.1
    exact h.independent a b (hp.2 _ ha) (hq.2 _ hbq) (p.property _ ha _ hbp)
  · obtain ⟨b,hbq,hbp⟩ := hpq.2
    exact h.independent a b (hp.2 _ ha) (hq.2 _ hbq) (p.property _ hbp _ ha).symm

noncomputable def pureColor : ((right H).induce (Pure H m)).Coloring Bool := by
  classical
  exact SimpleGraph.Coloring.mk (fun p => p.property.choose) (by
    intro p q hpq he
    apply pure_independent H m h p.val q.val p.property.choose p.property.choose_spec
    · change p.property.choose = q.property.choose at he
      rw [he]
      exact q.property.choose_spec
    · exact hpq)

include h in
lemma old_triangleFree : (oldGraph H m).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
  rcases h.hit a.val b.val c.val hab hac hbc with he | he | he
  · simp only [a.property,Bool.false_eq_true] at he
  · simp only [b.property,Bool.false_eq_true] at he
  · simp only [c.property,Bool.false_eq_true] at he

/-- A biclique represented by one of its independent one- or two-point old sides. -/
structure Packet (p : P H) where
  bit : Bool
  pair : Erdos595IndependentPair.Pair (oldGraph H m)
  eq_side : side H p bit = {pair.val.1.val,pair.val.2.val}

def Good (p : P H) : Prop := Nonempty (Packet H m p)

lemma packet_mem {p : P H} (d : Packet H m p) {x : V} (hx : x ∈ side H p d.bit) :
    ∃ a ∈ Erdos595IndependentPair.support (oldGraph H m) d.pair, a.val = x := by
  rw [d.eq_side] at hx
  rcases Set.mem_insert_iff.mp hx with he | he
  · exact ⟨d.pair.val.1,by simp [Erdos595IndependentPair.support],he.symm⟩
  · exact ⟨d.pair.val.2,by simp [Erdos595IndependentPair.support],
      (Set.mem_singleton_iff.mp he).symm⟩

lemma packet_old_mem {p : P H} (d : Packet H m p) {a : Old m}
    (ha : a ∈ Erdos595IndependentPair.support (oldGraph H m) d.pair) :
    a.val ∈ side H p d.bit := by
  rw [d.eq_side]
  simp only [Erdos595IndependentPair.support,Set.mem_insert_iff,Set.mem_singleton_iff] at ha ⊢
  exact ha.imp (congrArg Subtype.val) (congrArg Subtype.val)

lemma packet_overlap {p q : P H} (d : Packet H m p) (e : Packet H m q) {x : V}
    (hx : x ∈ side H p d.bit) (hy : x ∈ side H q e.bit) :
    (Erdos595IndependentPair.support (oldGraph H m) d.pair ∩
      Erdos595IndependentPair.support (oldGraph H m) e.pair).Nonempty := by
  obtain ⟨a,ha,hea⟩ := packet_mem H m d hx
  obtain ⟨b,hb,heb⟩ := packet_mem H m e hy
  have he : a = b := Subtype.ext (hea.trans heb.symm)
  exact ⟨a,ha,he ▸ hb⟩

lemma packet_adj {p q : P H} (d : Packet H m p) (e : Packet H m q)
    (hpq : (right H).Adj p q) :
    (Erdos595IndependentPair.graph (oldGraph H m)).Adj (d.pair,d.bit) (e.pair,e.bit) := by
  have pd {a : Old m} (ha : a ∈ Erdos595IndependentPair.support (oldGraph H m) d.pair) :
      a.val ∈ side H p d.bit := packet_old_mem H m d ha
  have qe {a : Old m} (ha : a ∈ Erdos595IndependentPair.support (oldGraph H m) e.pair) :
      a.val ∈ side H q e.bit := packet_old_mem H m e ha
  cases hd : d.bit <;> cases he : e.bit
  · change Erdos595IndependentPair.Near (oldGraph H m) d.pair e.pair
    refine ⟨?_,?_⟩
    · obtain ⟨x,hxq,hxp⟩ := hpq.2
      obtain ⟨a,ha,rfl⟩ := packet_mem H m d (by simpa only [side,hd] using hxp)
      refine ⟨a,ha,fun b hb => ?_⟩
      exact (q.property _ (by simpa only [side,he] using qe hb) _ hxq).symm
    · obtain ⟨x,hxp,hxq⟩ := hpq.1
      obtain ⟨a,ha,rfl⟩ := packet_mem H m e (by simpa only [side,he] using hxq)
      refine ⟨a,ha,fun b hb => ?_⟩
      exact (p.property _ (by simpa only [side,hd] using pd hb) _ hxp).symm
  · change (Erdos595IndependentPair.support (oldGraph H m) d.pair ∩
      Erdos595IndependentPair.support (oldGraph H m) e.pair).Nonempty
    obtain ⟨x,hxq,hxp⟩ := hpq.2
    exact packet_overlap H m d e (by simpa only [side,hd] using hxp)
      (by simpa only [side,he] using hxq)
  · change (Erdos595IndependentPair.support (oldGraph H m) d.pair ∩
      Erdos595IndependentPair.support (oldGraph H m) e.pair).Nonempty
    obtain ⟨x,hxp,hxq⟩ := hpq.1
    exact packet_overlap H m d e (by simpa only [side,hd] using hxp)
      (by simpa only [side,he] using hxq)
  · change Erdos595IndependentPair.Near (oldGraph H m) d.pair e.pair
    refine ⟨?_,?_⟩
    · obtain ⟨x,hxp,hxq⟩ := hpq.1
      obtain ⟨a,ha,rfl⟩ := packet_mem H m d (by simpa only [side,hd] using hxp)
      refine ⟨a,ha,fun b hb => ?_⟩
      exact q.property _ hxq _ (by simpa only [side,he] using qe hb)
    · obtain ⟨x,hxq,hxp⟩ := hpq.2
      obtain ⟨a,ha,rfl⟩ := packet_mem H m e (by simpa only [side,he] using hxq)
      refine ⟨a,ha,fun b hb => ?_⟩
      exact p.property _ hxp _ (by simpa only [side,hd] using pd hb)


lemma side_nonempty {p q : P H} (hpq : (right H).Adj p q) (s : Bool) :
    (side H p s).Nonempty := by
  cases s
  · obtain ⟨x,_,hx⟩ := hpq.2
    exact ⟨x,hx⟩
  · obtain ⟨x,hx,_⟩ := hpq.1
    exact ⟨x,hx⟩

include h in
lemma marked_triangle_on_side {p q r : P H}
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r) (hqr : (right H).Adj q r) :
    ∃ s a, a ∈ side H p s ∧ m a = true ∧
      ∃ b c, H.Adj a b ∧ H.Adj a c ∧ H.Adj b c := by
  let t := six H hpq hpr hqr
  have ht := t.tri H
  have ht' := t.tri' H
  by_cases hx : m t.x = true
  · exact ⟨true,t.x,t.hx.1,hx,t.y,t.z,ht⟩
  by_cases hz : m t.z = true
  · exact ⟨false,t.z,t.hz.2,hz,t.x,t.y,ht.2.1.symm,ht.2.2.symm,ht.1⟩
  by_cases hx' : m t.x' = true
  · exact ⟨false,t.x',t.hx'.2,hx',t.y',t.z',ht'⟩
  by_cases hz' : m t.z' = true
  · exact ⟨true,t.z',t.hz'.1,hz',t.x',t.y',ht'.2.1.symm,ht'.2.2.symm,ht'.1⟩
  have hy : m t.y = true := by
    rcases h.hit _ _ _ ht.1 ht.2.1 ht.2.2 with hh | hh | hh
    · exact (hx hh).elim
    · exact hh
    · exact (hz hh).elim
  have hy' : m t.y' = true := by
    rcases h.hit _ _ _ ht'.1 ht'.2.1 ht'.2.2 with hh | hh | hh
    · exact (hx' hh).elim
    · exact hh
    · exact (hz' hh).elim
  exact (h.independent _ _ hy hy' (r.property _ t.hy.2 _ t.hy'.1)).elim

include h in
lemma old_opposite {p : P H} {s : Bool} {a x : V}
    (ha : a ∈ side H p s) (hma : m a = true) (hx : x ∈ side H p (!s)) : m x = false := by
  have hn : m x ≠ true := fun he => h.independent _ _ hma he (cross H p s ha hx)
  cases hm : m x <;> simp_all

include h in
lemma independent_opposite {p : P H} {s : Bool} {a : V}
    (ha : a ∈ side H p s) (hma : m a = true) (hp : ¬Pure H m p)
    {x y : V} (hx : x ∈ side H p (!s)) (hy : y ∈ side H p (!s)) : ¬H.Adj x y := by
  intro hxy
  have hmx := old_opposite H m h ha hma hx
  have hmy := old_opposite H m h ha hma hy
  apply hp
  refine ⟨s,⟨a,ha⟩,?_⟩
  intro z hz
  rcases h.hit z x y (cross H p s hz hx) (cross H p s hz hy) hxy with hmz | hmz | hmz
  · exact hmz
  · simp only [hmx,Bool.false_eq_true] at hmz
  · simp only [hmy,Bool.false_eq_true] at hmz

private lemma two_points {S : Set V} (hS : S.Nonempty)
    (h₂ : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x = y ∨ x = z ∨ y = z) :
    ∃ a ∈ S, ∃ b ∈ S, S = {a,b} := by
  classical
  obtain ⟨a,ha⟩ := hS
  by_cases hs : ∀ b ∈ S, b = a
  · refine ⟨a,ha,a,ha,?_⟩
    ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,or_self]
    exact ⟨fun hx => hs x hx,fun he => he ▸ ha⟩
  · push_neg at hs
    obtain ⟨b,hb,hba⟩ := hs
    refine ⟨a,ha,b,hb,?_⟩
    ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · intro hx
      rcases h₂ a ha b hb x hx with he | he | he
      · exact (hba he.symm).elim
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · rintro (rfl | rfl)
      · exact ha
      · exact hb

include h in
lemma good_of_triangle {p q r : P H} (hp : ¬Pure H m p)
    (hpq : (right H).Adj p q) (hpr : (right H).Adj p r) (hqr : (right H).Adj q r) :
    Good H m p := by
  obtain ⟨s,a,ha,hma,b,c,hab,hac,hbc⟩ := marked_triangle_on_side H m h hpq hpr hqr
  have h₂ : ∀ x ∈ side H p (!s), ∀ y ∈ side H p (!s), ∀ z ∈ side H p (!s),
      x = y ∨ x = z ∨ y = z := by
    intro x hx y hy z hz
    exact h.small a b c hma hab hac hbc x y z
      (cross H p s ha hx) (cross H p s ha hy) (cross H p s ha hz)
      (independent_opposite H m h ha hma hp hx hy)
      (independent_opposite H m h ha hma hp hx hz)
      (independent_opposite H m h ha hma hp hy hz)
  obtain ⟨u,hu,v,hv,he⟩ := two_points (side_nonempty H hpq (!s)) h₂
  let u' : Old m := ⟨u,old_opposite H m h ha hma hu⟩
  let v' : Old m := ⟨v,old_opposite H m h ha hma hv⟩
  exact ⟨⟨!s,⟨(u',v'),independent_opposite H m h ha hma hp hu hv⟩,he⟩⟩

include h in
/-- No cardinality bound is needed on the old triangle-free graph. -/
theorem second_right_cover : IsCountableUnionOfTriangleFree (right (right H)) := by
  classical
  apply Erdos595RightCoverReduction.delete_colored (right H) (Pure H m) (pureColor H m h)
  let J := (right H).induce (Pure H m)ᶜ
  let S : Set {p : P H // ¬Pure H m p} := {p | Good H m p.val}
  apply Erdos595RightCoverReduction.triangle_core J S
  · intro p q r hpq hpr hqr
    exact good_of_triangle H m h p.property hpq hpr hqr
  · let d (p : S) : Packet H m p.val.val := Classical.choice p.property
    let f : J.induce S →g Erdos595IndependentPair.graph (oldGraph H m) :=
      { toFun p := ((d p).pair,(d p).bit)
        map_rel' := fun {p q} hpq => packet_adj H m (d p) (d q) hpq }
    exact countable_union_of_hom (Erdos595IndependentPair.rightMap f)
      (Erdos595IndependentPairCover.countable_cover (oldGraph H m) (old_triangleFree H m h))

/-- Degree at most three implies the required bound on independent neighbors
at any marked vertex lying in a triangle. No matching condition is needed. -/
theorem conditions_of_degree_three
    (hi : ∀ a b, m a = true → m b = true → ¬H.Adj a b)
    (ht : ∀ a b c, H.Adj a b → H.Adj a c → H.Adj b c →
      m a = true ∨ m b = true ∨ m c = true)
    (hd : ∀ a, m a = true → ∀ b c d e,
      H.Adj a b → H.Adj a c → H.Adj a d → H.Adj a e →
      b = c ∨ b = d ∨ b = e ∨ c = d ∨ c = e ∨ d = e) : Conditions H m := by
  refine ⟨hi,ht,?_⟩
  intro a b c ha hab hac hbc x y z hax hay haz hxy hxz hyz
  by_cases exy : x = y
  · exact Or.inl exy
  by_cases exz : x = z
  · exact Or.inr (Or.inl exz)
  by_cases eyz : y = z
  · exact Or.inr (Or.inr eyz)
  have mem {v : V} (hav : H.Adj a v) : v = x ∨ v = y ∨ v = z := by
    rcases hd a ha x y z v hax hay haz hav with he | he | he | he | he | he
    · exact (exy he).elim
    · exact (exz he).elim
    · exact Or.inl he.symm
    · exact (eyz he).elim
    · exact Or.inr (Or.inl he.symm)
    · exact Or.inr (Or.inr he.symm)
  exfalso
  rcases mem hab with rfl | rfl | rfl <;>
    rcases mem hac with rfl | rfl | rfl <;>
    first | exact hbc.ne rfl | exact hxy hbc | exact hxz hbc | exact hyz hbc |
      exact hxy hbc.symm | exact hxz hbc.symm | exact hyz hbc.symm

/-- The second right adjoint of any graph with an independent degree-three
triangle transversal admits a countable triangle-free edge cover. -/
theorem second_right_cover_of_degree_three
    (hi : ∀ a b, m a = true → m b = true → ¬H.Adj a b)
    (ht : ∀ a b c, H.Adj a b → H.Adj a c → H.Adj b c →
      m a = true ∨ m b = true ∨ m c = true)
    (hd : ∀ a, m a = true → ∀ b c d e,
      H.Adj a b → H.Adj a c → H.Adj a d → H.Adj a e →
      b = c ∨ b = d ∨ b = e ∨ c = d ∨ c = e ∨ d = e) :
    IsCountableUnionOfTriangleFree (right (right H)) :=
  second_right_cover H m (conditions_of_degree_three H m hi ht hd)


#print axioms pureColor
#print axioms packet_adj
#print axioms good_of_triangle
#print axioms second_right_cover
#print axioms conditions_of_degree_three
#print axioms second_right_cover_of_degree_three
end Erdos595SmallMarkedSecondRight
