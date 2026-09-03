import Submission.FiniteBicliqueAdjoint
import Submission.TupleTypeCover

/-!
Transport of finite-parameter shift-square bicliques along finite partial
isomorphisms of dense linear orders. Auxiliary work for the candidate family.
-/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595ShiftTransport
open Erdos595MiddleCorner Erdos595FiniteBiclique

variable {A B I : Type*} [LinearOrder A] [LinearOrder B]

/-- A finite matching of tuples of the same weak order type is a finite
partial isomorphism of the underlying orders. -/
lemma partialIso_of_type [Finite I] (x : I → A) (y : I → B)
    (h : ∀ i j, (x i ≤ x j ↔ y i ≤ y j)) :
    ∃ f : Order.PartialIso A B, ∀ i, (x i,y i) ∈ f.1 := by
  classical
  letI := Fintype.ofFinite I
  have hc (i j : I) : cmp (x i) (x j) = cmp (y i) (y j) := by
    have hlt : x i < x j ↔ y i < y j := by
      simp only [lt_iff_le_not_ge, h i j, h j i]
    have hgt : x j < x i ↔ y j < y i := by
      simp only [lt_iff_le_not_ge, h i j, h j i]
    have heq : x i = x j ↔ y i = y j := by
      simp only [le_antisymm_iff, h i j, h j i]
    rcases lt_trichotomy (x i) (x j) with ht | ht | ht
    · exact (cmp_eq_lt_iff _ _).mpr ht |>.trans ((cmp_eq_lt_iff _ _).mpr (hlt.mp ht)).symm
    · exact (cmp_eq_eq_iff _ _).mpr ht |>.trans ((cmp_eq_eq_iff _ _).mpr (heq.mp ht)).symm
    · exact (cmp_eq_gt_iff _ _).mpr ht |>.trans ((cmp_eq_gt_iff _ _).mpr (hgt.mp ht)).symm
  let f : Order.PartialIso A B := ⟨Finset.univ.image (fun i => (x i,y i)), by
    intro p hp q hq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
    exact hc i j⟩
  exact ⟨f,fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

def coordinates (x : Triple A) : Fin 3 → A := ![x.a,x.b,x.c]

def encode (x : I → Triple A) : I × Fin 3 → A :=
  fun p => coordinates (x p.1) p.2

def Carries (f : Order.PartialIso A B) (x : Triple A) (y : Triple B) : Prop :=
  (x.a,y.a) ∈ f.1 ∧ (x.b,y.b) ∈ f.1 ∧ (x.c,y.c) ∈ f.1

lemma Carries.mono {f g : Order.PartialIso A B} (hfg : f ≤ g)
    {x : Triple A} {y : Triple B} (h : Carries f x y) : Carries g x y :=
  ⟨hfg h.1,hfg h.2.1,hfg h.2.2⟩

lemma carries_adj {f : Order.PartialIso A B} {x z : Triple A} {y w : Triple B}
    (hx : Carries f x y) (hz : Carries f z w) :
    (graph A).Adj x z ↔ (graph B).Adj y w := by
  have eqv {a c : A} {b d : B} (hab : (a,b) ∈ f.1) (hcd : (c,d) ∈ f.1) :
      a = c ↔ b = d := eq_iff_eq_of_cmp_eq_cmp (f.2 _ hab _ hcd)
  change ((x.b = z.a ∧ x.c = z.b) ∨ x.c = z.a) ∨
      ((z.b = x.a ∧ z.c = x.b) ∨ z.c = x.a) ↔
    ((y.b = w.a ∧ y.c = w.b) ∨ y.c = w.a) ∨
      ((w.b = y.a ∧ w.c = y.b) ∨ w.c = y.a)
  rw [eqv hx.2.1 hz.1, eqv hx.2.2 hz.2.1, eqv hx.2.2 hz.1,
    eqv hz.2.1 hx.1, eqv hz.2.2 hx.2.1, eqv hz.2.2 hx.1]

lemma extendTripleLeft [DenselyOrdered B] [NoMinOrder B] [NoMaxOrder B] [Nonempty B]
    (f : Order.PartialIso A B) (x : Triple A) :
    ∃ (g : Order.PartialIso A B) (y : Triple B), f ≤ g ∧ Carries g x y := by
  obtain ⟨f₁,⟨a,ha⟩,h₁⟩ := (Order.PartialIso.definedAtLeft B x.a).isCofinal f
  obtain ⟨f₂,⟨b,hb⟩,h₂⟩ := (Order.PartialIso.definedAtLeft B x.b).isCofinal f₁
  obtain ⟨f₃,⟨c,hc⟩,h₃⟩ := (Order.PartialIso.definedAtLeft B x.c).isCofinal f₂
  have ha' : (x.a,a) ∈ f₃.1 := h₃ (h₂ ha)
  have hb' : (x.b,b) ∈ f₃.1 := h₃ hb
  have hab : a < b := (lt_iff_lt_of_cmp_eq_cmp (f₃.2 _ ha' _ hb')).mp x.ab
  have hbc : b < c := (lt_iff_lt_of_cmp_eq_cmp (f₃.2 _ hb' _ hc)).mp x.bc
  exact ⟨f₃, ⟨a,b,c,hab,hbc⟩, h₁.trans (h₂.trans h₃), ha', hb', hc⟩

lemma extendTripleRight [DenselyOrdered A] [NoMinOrder A] [NoMaxOrder A] [Nonempty A]
    (f : Order.PartialIso A B) (y : Triple B) :
    ∃ (g : Order.PartialIso A B) (x : Triple A), f ≤ g ∧ Carries g x y := by
  obtain ⟨f₁,⟨a,ha⟩,h₁⟩ := (Order.PartialIso.definedAtRight A y.a).isCofinal f
  obtain ⟨f₂,⟨b,hb⟩,h₂⟩ := (Order.PartialIso.definedAtRight A y.b).isCofinal f₁
  obtain ⟨f₃,⟨c,hc⟩,h₃⟩ := (Order.PartialIso.definedAtRight A y.c).isCofinal f₂
  have ha' : (a,y.a) ∈ f₃.1 := h₃ (h₂ ha)
  have hb' : (b,y.b) ∈ f₃.1 := h₃ hb
  have hab : a < b := (lt_iff_lt_of_cmp_eq_cmp (f₃.2 _ ha' _ hb')).mpr y.ab
  have hbc : b < c := (lt_iff_lt_of_cmp_eq_cmp (f₃.2 _ hb' _ hc)).mpr y.bc
  exact ⟨f₃, ⟨a,b,c,hab,hbc⟩, h₁.trans (h₂.trans h₃), ha', hb', hc⟩

def familyCommon (x : I → Triple A) (w : Triple A) : Prop :=
  ∀ i, (graph A).Adj (x i) w

def familyDouble (x : I → Triple A) (w : Triple A) : Prop :=
  ∀ z, familyCommon x z → (graph A).Adj z w

lemma familyCommon_transport (f : Order.PartialIso A B)
    {x : I → Triple A} {y : I → Triple B} {v : Triple A} {w : Triple B}
    (h : ∀ i, Carries f (x i) (y i)) (hv : Carries f v w) :
    familyCommon x v ↔ familyCommon y w :=
  forall_congr' fun i => carries_adj (h i) hv

variable [DenselyOrdered A] [NoMinOrder A] [NoMaxOrder A] [Nonempty A]
  [DenselyOrdered B] [NoMinOrder B] [NoMaxOrder B] [Nonempty B]

lemma familyDouble_transport (f : Order.PartialIso A B)
    {x : I → Triple A} {y : I → Triple B} {v : Triple A} {w : Triple B}
    (h : ∀ i, Carries f (x i) (y i)) (hv : Carries f v w) :
    familyDouble x v ↔ familyDouble y w := by
  constructor
  · intro hp z hz
    obtain ⟨g,t,hfg,ht⟩ := extendTripleRight f z
    have htt : familyCommon x t :=
      (familyCommon_transport g (fun i => (h i).mono hfg) ht).mpr hz
    exact (carries_adj ht (hv.mono hfg)).mp (hp t htt)
  · intro hp z hz
    obtain ⟨g,t,hfg,ht⟩ := extendTripleLeft f z
    have htt : familyCommon y t :=
      (familyCommon_transport g (fun i => (h i).mono hfg) ht).mp hz
    exact (carries_adj ht (hv.mono hfg)).mpr (hp t htt)

def familyAdj (x y : I → Triple A) : Prop :=
  (∃ v, familyDouble x v ∧ familyCommon y v) ∧
  (∃ v, familyDouble y v ∧ familyCommon x v)

lemma familyAdj_transport (f : Order.PartialIso A B)
    {x z : I → Triple A} {y w : I → Triple B}
    (hx : ∀ i, Carries f (x i) (y i)) (hz : ∀ i, Carries f (z i) (w i)) :
    familyAdj x z ↔ familyAdj y w := by
  have forward {x z : I → Triple A} {y w : I → Triple B}
      (hx : ∀ i, Carries f (x i) (y i)) (hz : ∀ i, Carries f (z i) (w i)) :
      (∃ v, familyDouble x v ∧ familyCommon z v) →
        ∃ v, familyDouble y v ∧ familyCommon w v := by
    rintro ⟨v,hv,hv'⟩
    obtain ⟨g,t,hfg,ht⟩ := extendTripleLeft f v
    exact ⟨t, (familyDouble_transport g (fun i => (hx i).mono hfg) ht).mp hv,
      (familyCommon_transport g (fun i => (hz i).mono hfg) ht).mp hv'⟩
  have backward {x z : I → Triple A} {y w : I → Triple B}
      (hx : ∀ i, Carries f (x i) (y i)) (hz : ∀ i, Carries f (z i) (w i)) :
      (∃ v, familyDouble y v ∧ familyCommon w v) →
        ∃ v, familyDouble x v ∧ familyCommon z v := by
    rintro ⟨v,hv,hv'⟩
    obtain ⟨g,t,hfg,ht⟩ := extendTripleRight f v
    exact ⟨t, (familyDouble_transport g (fun i => (hx i).mono hfg) ht).mpr hv,
      (familyCommon_transport g (fun i => (hz i).mono hfg) ht).mpr hv'⟩
  exact ⟨fun h => ⟨forward hx hz h.1, forward hz hx h.2⟩,
    fun h => ⟨backward hx hz h.1, backward hz hx h.2⟩⟩

/-- Matching pair order types of finite families produce a finite partial
isomorphism carrying both families. -/
lemma partialIso_of_pairType [Finite I] {x z : I → Triple A} {y w : I → Triple B}
    (h : ∀ p q : Bool × (I × Fin 3),
      Erdos595TupleType.pairType (encode x) (encode z) p q ↔
      Erdos595TupleType.pairType (encode y) (encode w) p q) :
    ∃ f : Order.PartialIso A B, (∀ i, Carries f (x i) (y i)) ∧
      ∀ i, Carries f (z i) (w i) := by
  let v : Bool × (I × Fin 3) → A :=
    fun p => if p.1 then encode z p.2 else encode x p.2
  let u : Bool × (I × Fin 3) → B :=
    fun p => if p.1 then encode w p.2 else encode y p.2
  obtain ⟨f,hf⟩ := partialIso_of_type v u h
  refine ⟨f,fun i => ?_,fun i => ?_⟩
  · exact ⟨by simpa [v,u,encode,coordinates] using hf (false,(i,0)),
      by simpa [v,u,encode,coordinates] using hf (false,(i,1)),
      by simpa [v,u,encode,coordinates] using hf (false,(i,2))⟩
  · exact ⟨by simpa [v,u,encode,coordinates] using hf (true,(i,0)),
      by simpa [v,u,encode,coordinates] using hf (true,(i,1)),
      by simpa [v,u,encode,coordinates] using hf (true,(i,2))⟩

lemma familyAdj_of_pairType [Finite I] {x z : I → Triple A} {y w : I → Triple B}
    (h : ∀ p q : Bool × (I × Fin 3),
      Erdos595TupleType.pairType (encode x) (encode z) p q ↔
      Erdos595TupleType.pairType (encode y) (encode w) p q) :
    familyAdj x z ↔ familyAdj y w := by
  obtain ⟨f,hx,hz⟩ := partialIso_of_pairType h
  exact familyAdj_transport f hx hz

#print axioms partialIso_of_type
#print axioms partialIso_of_pairType
#print axioms familyAdj_of_pairType
#print axioms extendTripleLeft
#print axioms extendTripleRight
#print axioms familyDouble_transport
#print axioms familyAdj_transport
end Erdos595ShiftTransport
