import Submission.InfiniteTriangleRamsey

/-!
An infinite-target ordered pair Ramsey theorem, by coding the existing
Erdős--Rado predecessor tree. The host is not claimed K4-free.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595InfinitePairRamsey
open Erdos595InfiniteTriangleRamsey

universe u
variable {V C T : Type u} [LinearOrder V] [WellFoundedLT V]
    (c : V → V → C)

abbrev TreeCode (T C : Type u) := Set T × Set (T × T) × Set (T × C)

noncomputable def treeCode (e : ∀ v, pred c v ↪ T) (v : V) : TreeCode T C :=
  (Set.range (e v),
    {ij | ∃ a b : pred c v, e v a = ij.1 ∧ e v b = ij.2 ∧ a.val < b.val},
    {ik | ∃ a : pred c v, e v a = ik.1 ∧ c a.val v = ik.2})

lemma treeCode_order (e : ∀ v, pred c v ↪ T) (v : V) (a b : pred c v) :
    (e v a,e v b) ∈ (treeCode c e v).2.1 ↔ a.val < b.val := by
  constructor
  · rintro ⟨x,y,hx,hy,hxy⟩
    simpa only [(e v).injective hx,(e v).injective hy] using hxy
  · exact fun h => ⟨a,b,rfl,rfl,h⟩

lemma treeCode_color (e : ∀ v, pred c v ↪ T) (v : V) (a : pred c v) (k : C) :
    (e v a,k) ∈ (treeCode c e v).2.2 ↔ c a.val v = k := by
  constructor
  · rintro ⟨x,hx,hc⟩
    simpa only [(e v).injective hx] using hc
  · exact fun h => ⟨a,rfl,h⟩

/-- Unlike the earlier finite-target code, the labels need not be colors. -/
theorem treeCode_injective (e : ∀ v, pred c v ↪ T) :
    Function.Injective (treeCode c e) := by
  classical
  intro v w he
  have hset : (treeCode c e v).1 = (treeCode c e w).1 := congrArg Prod.fst he
  have hrel : (treeCode c e v).2.1 = (treeCode c e w).2.1 :=
    congrArg (fun z => z.2.1) he
  have hcol : (treeCode c e v).2.2 = (treeCode c e w).2.2 :=
    congrArg (fun z => z.2.2) he
  have hex : ∀ a : pred c v, ∃ b : pred c w, e w b = e v a := by
    intro a
    have ha : e v a ∈ (treeCode c e v).1 := ⟨a,rfl⟩
    rw [hset] at ha
    exact ha
  choose f hf using hex
  have hsur : Function.Surjective f := by
    intro b
    have hb : e w b ∈ (treeCode c e w).1 := ⟨b,rfl⟩
    rw [← hset] at hb
    obtain ⟨a,ha⟩ := hb
    exact ⟨a,(e w).injective ((hf a).trans ha)⟩
  have hord : ∀ a b, (f a).val < (f b).val ↔ a.val < b.val := by
    intro a b
    rw [← treeCode_order c e w (f a) (f b),hf a,hf b,← hrel]
    exact treeCode_order c e v a b
  have hc : ∀ a, c (f a).val w = c a.val v := by
    intro a
    apply (treeCode_color c e w (f a) _).mp
    rw [hf a,← hcol]
    exact (treeCode_color c e v a _).mpr rfl
  have hid := paths_rigid c f hsur hord hc
  have hp : pred c v = pred c w := by
    ext a
    constructor
    · intro ha
      have hh : (f ⟨a,ha⟩).val = a := hid ⟨a,ha⟩
      exact hh ▸ (f ⟨a,ha⟩).property
    · intro ha
      obtain ⟨b,hb⟩ := hsur ⟨a,ha⟩
      have hh : b.val = a := (hid b).symm.trans (congrArg Subtype.val hb)
      exact hh ▸ b.property
  apply vertex_eq_of_pred_eq c hp
  intro a ha
  have hh := hc ⟨a,ha⟩
  rw [hid ⟨a,ha⟩] at hh
  exact hh.symm

/-- A large enough predecessor branch must contain any prescribed well order. -/
theorem exists_long_branch {A : Type u} [LinearOrder A] [WellFoundedLT A]
    (hV : ¬Nonempty (V ↪ TreeCode A C)) :
    ∃ v, Nonempty (A ↪o pred c v) := by
  classical
  by_contra hn
  have he : ∀ v, Nonempty (pred c v ↪ A) := by
    intro v
    rcases InitialSeg.total (fun x y : A => x < y)
      (fun x y : pred c v => x < y) with f | f
    · apply False.elim
      apply hn
      exact ⟨v,⟨OrderEmbedding.ofStrictMono f (fun _ _ h => f.map_rel_iff.mpr h)⟩⟩
    · exact ⟨f.toRelEmbedding.toEmbedding⟩
  let e := fun v => (he v).some
  exact hV ⟨⟨treeCode c e,treeCode_injective c e⟩⟩

/-- End-homogeneous pair sequences with an explicit size obstruction. -/
theorem end_homogeneous_of_noninjection (A C V : Type u)
    [LinearOrder A] [WellFoundedLT A] (hV : ¬Nonempty (V ↪ TreeCode A C)) :
    ∃ (_ : LinearOrder V) (_ : WellFoundedLT V),
      ∀ c : V → V → C, ∃ (f : A ↪o V) (d : A → C),
        ∀ a b, a < b → c (f a) (f b) = d a := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  letI : WellFoundedLT V := ⟨(inferInstance : IsWellOrder V WellOrderingRel).wf⟩
  refine ⟨inferInstance,inferInstance,?_⟩
  intro c
  obtain ⟨v,⟨f⟩⟩ := exists_long_branch c hV
  let g : A ↪o V := OrderEmbedding.ofStrictMono (fun a => (f a).val)
    (fun _ _ h => f.strictMono h)
  refine ⟨g,fun a => c (g a) v,?_⟩
  intro a b hab
  exact pred_agree c (f b).property
    (pred_chain c (f a).property (f b).property (f.strictMono hab))

/-- End-homogeneous pair sequences of arbitrary well-ordered length. -/
theorem end_homogeneous_host (A C : Type u) [LinearOrder A] [WellFoundedLT A] :
    ∃ (V : Type u) (_ : LinearOrder V) (_ : WellFoundedLT V),
      ∀ c : V → V → C, ∃ (f : A ↪o V) (d : A → C),
        ∀ a b, a < b → c (f a) (f b) = d a := by
  obtain ⟨o,w,h⟩ := end_homogeneous_of_noninjection A C (Set (TreeCode A C)) (by
    rintro ⟨e⟩
    exact Function.cantor_injective e e.injective)
  exact ⟨_,o,w,h⟩

/-- An order-theoretic pigeonhole bound, in an encoding form that does not
need cardinal arithmetic. -/
theorem order_pigeonhole {A X C : Type u} [LinearOrder A] [WellFoundedLT A]
    [LinearOrder X] [WellFoundedLT X] (c : X → C)
    (hX : ¬Nonempty (X ↪ A × C)) :
    ∃ (k : C) (e : A ↪o X), ∀ a, c (e a) = k := by
  classical
  by_contra hn
  have he : ∀ k, Nonempty ((c ⁻¹' {k}) ↪ A) := by
    intro k
    rcases InitialSeg.total (fun x y : A => x < y)
      (fun x y : c ⁻¹' {k} => x < y) with e | e
    · apply False.elim
      apply hn
      let f : A ↪o X := OrderEmbedding.ofStrictMono (fun a => (e a).val)
        (fun _ _ h => e.map_rel_iff.mpr h)
      exact ⟨k,f,fun a => (e a).property⟩
    · exact ⟨e.toRelEmbedding.toEmbedding⟩
  let e := fun k => (he k).some
  let f : X → A × C := fun x => (e (c x) ⟨x,rfl⟩,c x)
  have hf : Function.Injective f := by
    intro x y h
    have hc : c x = c y := congrArg Prod.snd h
    have hy : y ∈ c ⁻¹' {c x} := hc.symm
    have aux : ∀ (k : C) (hk : c y = k),
        e (c y) ⟨y,rfl⟩ = e k ⟨y,hk⟩ := by
      intro k hk
      subst k
      rfl
    have hi : e (c x) ⟨x,rfl⟩ = e (c x) ⟨y,hy⟩ :=
      (congrArg Prod.fst h).trans (aux (c x) hc.symm)
    exact congrArg Subtype.val ((e (c x)).injective hi)
  exact hX ⟨⟨f,hf⟩⟩

/-- Well-order a carrier larger than the pigeonhole code. -/
theorem pigeonhole_order (A C X : Type u) [LinearOrder A] [WellFoundedLT A]
    (hX : ¬Nonempty (X ↪ A × C)) :
    ∃ (_ : LinearOrder X) (_ : WellFoundedLT X),
      ∀ c : X → C, ∃ (k : C) (e : A ↪o X), ∀ a, c (e a) = k := by
  classical
  letI : LinearOrder X := IsWellOrder.linearOrder WellOrderingRel
  letI : WellFoundedLT X := ⟨(inferInstance : IsWellOrder X WellOrderingRel).wf⟩
  exact ⟨inferInstance,inferInstance,fun c => order_pigeonhole c hX⟩

theorem pair_ramsey_from_pigeonhole (A C X : Type u)
    [LinearOrder A] [WellFoundedLT A] [LinearOrder X] [WellFoundedLT X]
    (hX : ∀ c : X → C, ∃ (k : C) (e : A ↪o X), ∀ a, c (e a) = k) :
    ∃ (V : Type u) (_ : LinearOrder V) (_ : WellFoundedLT V),
      ∀ c : V → V → C, ∃ (f : A ↪o V) (k : C),
        ∀ a b, a < b → c (f a) (f b) = k := by
  obtain ⟨V,oV,wV,hV⟩ := end_homogeneous_host X C
  letI : LinearOrder V := oV
  letI : WellFoundedLT V := wV
  refine ⟨V,oV,wV,?_⟩
  intro c
  obtain ⟨f,d,hd⟩ := hV c
  obtain ⟨k,e,he⟩ := hX d
  exact ⟨e.trans f,k,fun a b hab => (hd _ _ (e.strictMono hab)).trans (he a)⟩

/-- Every ordered pair coloring has a monochromatic increasing copy of the
entire target well order, which may be uncountable. -/
theorem pair_ramsey_host (A C : Type u) [LinearOrder A] [WellFoundedLT A] :
    ∃ (V : Type u) (_ : LinearOrder V) (_ : WellFoundedLT V),
      ∀ c : V → V → C, ∃ (f : A ↪o V) (k : C),
        ∀ a b, a < b → c (f a) (f b) = k := by
  classical
  obtain ⟨oX,wX,hX⟩ := pigeonhole_order A C (Set (A × C)) (by
    rintro ⟨e⟩
    exact Function.cantor_injective e e.injective)
  exact @pair_ramsey_from_pigeonhole A C (Set (A × C)) _ _ oX wX hX

#print axioms treeCode_injective
#print axioms exists_long_branch
#print axioms end_homogeneous_host
#print axioms pair_ramsey_host
end Erdos595InfinitePairRamsey
