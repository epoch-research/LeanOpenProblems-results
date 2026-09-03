import Submission.PrivateTriangleBase
import Submission.RightFiberCover
import Submission.MatchingBundleRightCover
import Submission.RightThreeColor

/-! Structural reflection for private-triangle completion. Auxiliary work. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595PrivateTriangleRightReflection
open Erdos595ArcAdjoint Erdos595PrivateTriangleCompletion
open Erdos595MatchingBundle
variable {V : Type*} (H : SimpleGraph V)

abbrev K := graph H

def Both (p : Biclique (K H)) : Prop :=
  (Left (K H) p).Nonempty ∧ (Right (K H) p).Nonempty

def Private (u : Center H) (v : Vertex H) : Prop := ∃ t, v = .inr (u,t)
def HasPrivate (p : Biclique (K H)) (u : Center H) : Prop :=
  ∃ v, Private H u v ∧ (v ∈ Left (K H) p ∨ v ∈ Right (K H) p)

def localSet (u : Center H) : Set (Vertex H) :=
  {v | match v with
    | .inl a => a = u.val ∨ H.Adj u.val a
    | .inr w => w.1 = u}

lemma leaf_adj (u : Center H) (t : Bool) (v : Vertex H) :
    (K H).Adj (.inr (u,t)) v ↔ v = .inl u.val ∨ v = .inr (u,!t) := by
  cases v with
  | inl v => simp [K,graph,eq_comm]
  | inr w =>
    rcases w with ⟨z,s⟩
    cases t <;> cases s <;> simp [K,graph,eq_comm]

lemma neighbor_local (u : Center H) (t : Bool) {v : Vertex H}
    (h : (K H).Adj (.inr (u,t)) v) : v ∈ localSet H u := by
  rcases (leaf_adj H u t v).mp h with rfl | rfl
  · exact Or.inl rfl
  · exact rfl

lemma two_steps_local (u : Center H) (t : Bool) {v w : Vertex H}
    (hv : (K H).Adj (.inr (u,t)) v) (hw : (K H).Adj v w) : w ∈ localSet H u := by
  rcases (leaf_adj H u t v).mp hv with rfl | rfl
  · cases w with
    | inl w => exact Or.inr hw
    | inr w => exact Subtype.ext (show w.1.val = u.val from hw.symm)
  · exact neighbor_local H u (!t) hw

lemma all_local {p : Biclique (K H)} (hp : Both H p) {u : Center H}
    (hu : HasPrivate H p u) :
    Left (K H) p ⊆ localSet H u ∧ Right (K H) p ⊆ localSet H u := by
  obtain ⟨v,⟨t,rfl⟩,hv | hv⟩ := hu
  · obtain ⟨w,hw⟩ := hp.2
    exact ⟨fun a ha => two_steps_local H u t (p.property _ hv _ hw)
      (p.property _ ha _ hw).symm,
      fun b hb => neighbor_local H u t (p.property _ hv _ hb)⟩
  · obtain ⟨w,hw⟩ := hp.1
    exact ⟨fun a ha => neighbor_local H u t (p.property _ ha _ hv).symm,
      fun b hb => two_steps_local H u t (p.property _ hw _ hv).symm
        (p.property _ hw _ hb)⟩

lemma private_unique {p : Biclique (K H)} (hp : Both H p)
    {u z : Center H} (hu : HasPrivate H p u) (hz : HasPrivate H p z) : u = z := by
  obtain ⟨v,⟨t,rfl⟩,hv | hv⟩ := hz
  · exact ((all_local H hp hu).1 hv).symm
  · exact ((all_local H hp hu).2 hv).symm

/-- A triangle touching a neighbor of a private leaf is its private triangle. -/
lemma triangle_near_private (u : Center H) (t : Bool) {a b c : Vertex H}
    (ha : (K H).Adj (.inr (u,t)) a)
    (hab : (K H).Adj a b) (hac : (K H).Adj a c) (hbc : (K H).Adj b c) :
    (Private H u a ∨ Private H u b) ∧ (Private H u a ∨ Private H u c) ∧
      (Private H u b ∨ Private H u c) := by
  rcases (leaf_adj H u t a).mp ha with rfl | rfl
  · cases b with
    | inl b =>
      cases c with
      | inl c => exact (u.property b c hab hac hbc).elim
      | inr c =>
        have he : b = u.val := (show b = c.1.val from hbc).trans
          (show u.val = c.1.val from hac).symm
        exact (hab.ne (congrArg Sum.inl he.symm)).elim
    | inr b =>
      have hb : b.1 = u := Subtype.ext (show b.1.val = u.val from hab.symm)
      have hpb : Private H u (.inr b) := ⟨b.2,by cases b; simp_all⟩
      cases c with
      | inl c =>
        have he : u.val = c := (show u.val = b.1.val from hab).trans hbc
        exact (hac.ne (congrArg Sum.inl he)).elim
      | inr c =>
        have hc : c.1 = u := Subtype.ext (show c.1.val = u.val from hac.symm)
        have hpc : Private H u (.inr c) := ⟨c.2,by cases c; simp_all⟩
        exact ⟨Or.inr hpb,Or.inr hpc,Or.inl hpb⟩
  · have hpa : Private H u (.inr (u,!t)) := ⟨!t,rfl⟩
    refine ⟨Or.inl hpa,Or.inl hpa,?_⟩
    rcases (leaf_adj H u (!t) b).mp hab with rfl | rfl
    · rcases (leaf_adj H u (!t) c).mp hac with rfl | rfl
      · exact (hbc.ne rfl).elim
      · exact Or.inr ⟨_,rfl⟩
    · exact Or.inl ⟨_,rfl⟩

lemma private_propagates {p q r : Biclique (K H)}
    (s : Six (K H) p q r) {u : Center H} (hu : HasPrivate H p u) :
    HasPrivate H q u ∧ HasPrivate H r u := by
  have hs := s.tri (K H)
  have hh : (Private H u s.x ∨ Private H u s.y) ∧
      (Private H u s.y ∨ Private H u s.z) := by
    obtain ⟨v,⟨t,rfl⟩,hv | hv⟩ := hu
    · have ht := triangle_near_private H u t (p.property _ hv _ s.hx.1)
        hs.1 hs.2.1 hs.2.2
      exact ⟨ht.1,ht.2.2⟩
    · have ht := triangle_near_private H u t (p.property _ s.hz.2 _ hv).symm
        hs.2.1.symm hs.2.2.symm hs.1
      exact ⟨ht.2.2,ht.2.1.symm⟩
  constructor
  · rcases hh.1 with hx | hy
    · exact ⟨s.x,hx,Or.inl s.hx.2⟩
    · exact ⟨s.y,hy,Or.inr s.hy.1⟩
  · rcases hh.2 with hy | hz
    · exact ⟨s.y,hy,Or.inl s.hy.2⟩
    · exact ⟨s.z,hz,Or.inr s.hz.1⟩

noncomputable def kind (p : Biclique (K H)) : Option (Center H) := by
  classical
  exact if h : ∃ u, Both H p ∧ HasPrivate H p u then some h.choose else none

lemma kind_eq_some {p : Biclique (K H)} {u : Center H} :
    kind H p = some u ↔ Both H p ∧ HasPrivate H p u := by
  classical
  unfold kind
  split_ifs with h
  · constructor
    · intro he
      have heu := Option.some.inj he
      exact heu ▸ h.choose_spec
    · intro hu
      exact congrArg some (private_unique H hu.1 h.choose_spec.2 hu.2)
  · exact ⟨False.elim,fun hu => (h ⟨u,hu⟩).elim⟩

lemma both_of_adj {p q : Biclique (K H)} (h : (right (K H)).Adj p q) : Both H p :=
  ⟨⟨h.2.choose,h.2.choose_spec.2⟩,⟨h.1.choose,h.1.choose_spec.1⟩⟩

lemma kind_triangle : Erdos595TriangleFiber.TrianglesInFibers (right (K H)) (kind H) := by
  intro p q r hpq hpr hqr
  have bp := both_of_adj H hpq
  have bq := both_of_adj H hpq.symm
  have br := both_of_adj H hpr.symm
  have transfer {p q r : Biclique (K H)} {u : Center H}
      (hpq : (right (K H)).Adj p q) (hpr : (right (K H)).Adj p r)
      (hqr : (right (K H)).Adj q r) (hp : kind H p = some u) :
      kind H q = some u ∧ kind H r = some u := by
    have hh := private_propagates H (six (K H) hpq hpr hqr) ((kind_eq_some H).mp hp).2
    exact ⟨(kind_eq_some H).mpr ⟨both_of_adj H hpq.symm,hh.1⟩,
      (kind_eq_some H).mpr ⟨both_of_adj H hpr.symm,hh.2⟩⟩
  cases hp : kind H p with
  | some u =>
    have h := transfer hpq hpr hqr hp
    exact ⟨h.1.symm,h.2.symm⟩
  | none =>
    have hq : kind H q = none := by
      cases hq : kind H q with
      | none => rfl
      | some u =>
          have he := hp.symm.trans (transfer hpq.symm hqr hpr hq).1
          cases he
    have hr : kind H r = none := by
      cases hr : kind H r with
      | none => rfl
      | some u =>
          have he := hp.symm.trans (transfer hpr.symm hqr.symm hpq hr).1
          cases he
    exact ⟨hq.symm,hr.symm⟩

abbrev fiber (i : Option (Center H)) := (right (K H)).induce {p | kind H p = i}

def oldRestrict (p : Biclique (K H)) : Biclique H :=
  ⟨({v | Sum.inl v ∈ Left (K H) p},{v | Sum.inl v ∈ Right (K H) p}),
    fun _ ha _ hb => p.property _ ha _ hb⟩

lemma old_witness {p : Biclique (K H)} (hp : kind H p = none) (hb : Both H p)
    {v : Vertex H} (hv : v ∈ Left (K H) p ∨ v ∈ Right (K H) p) :
    ∃ a, v = Sum.inl a := by
  cases v with
  | inl a => exact ⟨a,rfl⟩
  | inr w =>
    have he := (kind_eq_some H).mpr ⟨hb,Sum.inr w,⟨w.2,rfl⟩,hv⟩
    rw [hp] at he
    cases he

def oldFiberHom : fiber H none →g right H where
  toFun p := oldRestrict H p.val
  map_rel' := by
    intro p q hpq
    have h : (right (K H)).Adj p.val q.val := hpq
    obtain ⟨a,ha⟩ := old_witness H p.property (both_of_adj H h) (Or.inr h.1.choose_spec.1)
    obtain ⟨b,hb⟩ := old_witness H p.property (both_of_adj H h) (Or.inl h.2.choose_spec.2)
    refine ⟨⟨a,?_,?_⟩,⟨b,?_,?_⟩⟩
    all_goals dsimp only [oldRestrict,Left,Right,Set.mem_setOf_eq]
    · exact ha ▸ h.1.choose_spec.1
    · exact ha ▸ h.1.choose_spec.2
    · exact hb ▸ h.2.choose_spec.1
    · exact hb ▸ h.2.choose_spec.2

abbrev Three := (⊤ : SimpleGraph (Fin 3))

private noncomputable def localCode (u : Center H) (v : Vertex H) : Fin 3 := by
  classical
  exact match v with
    | .inl a => if a = u.val then 0 else 1
    | .inr w => if w.2 then 2 else 1

noncomputable def localHom (u : Center H) : (K H).induce (localSet H u) →g Three where
  toFun v := localCode H u v.val
  map_rel' := by
    classical
    intro a b hab
    rcases a with ⟨a,ha⟩
    rcases b with ⟨b,hb⟩
    change localCode H u a ≠ localCode H u b
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        change a = u.val ∨ H.Adj u.val a at ha
        change b = u.val ∨ H.Adj u.val b at hb
        change H.Adj a b at hab
        rcases ha with rfl | ha
        · simp [localCode,hab.ne.symm]
        · rcases hb with rfl | hb
          · simp [localCode,hab.ne]
          · exact (u.property a b ha hb hab).elim
      | inr b =>
        change b.1 = u at hb
        change a = b.1.val at hab
        have he : a = u.val := hab.trans (congrArg Subtype.val hb)
        cases ht : b.2 <;> simp [localCode,he,ht]
    | inr a =>
      cases b with
      | inl b =>
        change a.1 = u at ha
        change a.1.val = b at hab
        have he : b = u.val := hab.symm.trans (congrArg Subtype.val ha)
        cases ht : a.2 <;> simp [localCode,he,ht]
      | inr b =>
        change a.1 = b.1 ∧ a.2 ≠ b.2 at hab
        cases ht : a.2 <;> cases hs : b.2 <;> simp_all [localCode]

def localRestrict (u : Center H) (p : Biclique (K H)) :
    Biclique ((K H).induce (localSet H u)) :=
  ⟨({v | v.val ∈ Left (K H) p},{v | v.val ∈ Right (K H) p}),
    fun _ ha _ hb => p.property _ ha _ hb⟩

def newFiberLocal (u : Center H) : fiber H (some u) →g right ((K H).induce (localSet H u)) where
  toFun p := localRestrict H u p.val
  map_rel' := by
    intro p q hpq
    have h : (right (K H)).Adj p.val q.val := hpq
    have hp := (kind_eq_some H).mp p.property
    have hs := all_local H hp.1 hp.2
    exact ⟨⟨⟨h.1.choose,hs.2 h.1.choose_spec.1⟩,h.1.choose_spec⟩,
      ⟨⟨h.2.choose,hs.1 h.2.choose_spec.2⟩,h.2.choose_spec⟩⟩

noncomputable def newFiberHom (u : Center H) : fiber H (some u) →g right Three :=
  (Erdos595RightFiber.rightHom (localHom H u)).comp (newFiberLocal H u)

open Erdos595Work Erdos595RightFiber

/-- The added fiber has a three-colorable SECOND right graph. -/
noncomputable def newSecondHom (u : Center H) : right (fiber H (some u)) →g Three :=
  Erdos595RightThree.hom.comp
    ((rightHom Erdos595RightThree.hom).comp (rightHom (newFiberHom H u)))

private theorem three_cover : IsCountableUnionOfTriangleFree Three :=
  countable_union_of_countable_common_neighbors Three (fun _ _ _ => Set.to_countable _)

/-- Private completion cannot create non-coverability at the second stage. -/
theorem second_cover (hH : IsCountableUnionOfTriangleFree (right (right H))) :
    IsCountableUnionOfTriangleFree (right (right (K H))) := by
  apply Erdos595RightFiber.cover_of_fibers (right (K H)) (kind H) (kind_triangle H)
  intro i
  cases i with
  | none => exact countable_union_of_hom (rightHom (oldFiberHom H)) hH
  | some u => exact countable_union_of_hom (newSecondHom H u) three_cover

/-- Coverability is preserved in both directions, without a K4 hypothesis. -/
theorem second_cover_iff :
    IsCountableUnionOfTriangleFree (right (right (K H))) ↔
      IsCountableUnionOfTriangleFree (right (right H)) := by
  constructor
  · exact countable_union_of_hom (rightHom (rightHom (oldEmbedding H).toHom))
  · exact second_cover H

private lemma cliqueFree_of_hom {X Y : Type*} {F : SimpleGraph X} {G : SimpleGraph Y}
    {n : ℕ} (f : F →g G) (hG : G.CliqueFree n) : F.CliqueFree n := by
  classical
  by_contra hn
  let g := f.comp (SimpleGraph.topEmbeddingOfNotCliqueFree hn).toHom
  let e : (⊤ : SimpleGraph (Fin n)) ↪g G :=
    { toFun := g
      inj' := g.injective_of_top_hom
      map_rel_iff' := by
        intro a b
        exact ⟨fun h he => h.ne (congrArg g he), fun h => g.map_adj h⟩ }
  exact SimpleGraph.not_cliqueFree_of_top_embedding e hG

/-- The same decomposition supplies a structural proof of K4 preservation,
independent of the large private-triangle SAT certificate. -/
theorem second_cliqueFree (hH : (right (right H)).CliqueFree 4) :
    (right (right (K H))).CliqueFree 4 := by
  apply Erdos595TriangleFiber.right_cliqueFree_of_fibers
    (right (K H)) (kind H) (kind_triangle H)
  intro i
  cases i with
  | none => exact cliqueFree_of_hom (rightHom (oldFiberHom H)) hH
  | some u =>
    exact cliqueFree_of_hom (newSecondHom H u)
      ((show Three.Colorable 3 from ⟨SimpleGraph.Hom.id⟩).cliqueFree (by decide))

theorem second_cliqueFree_iff :
    (right (right (K H))).CliqueFree 4 ↔ (right (right H)).CliqueFree 4 :=
  ⟨cliqueFree_of_hom (rightHom (rightHom (oldEmbedding H).toHom)),second_cliqueFree H⟩

#print axioms newSecondHom
#print axioms second_cover_iff
#print axioms second_cliqueFree_iff

#print axioms kind_triangle
#print axioms oldFiberHom
#print axioms newFiberHom

#print axioms private_propagates
end Erdos595PrivateTriangleRightReflection
