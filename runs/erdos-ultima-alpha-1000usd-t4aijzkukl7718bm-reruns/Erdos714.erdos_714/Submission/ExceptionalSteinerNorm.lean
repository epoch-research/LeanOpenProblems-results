import Submission.ExceptionalQuinticCounts

/-!
The exceptional characteristic-three quintics define an actual Steiner
quasigroup. Its norm-weighted graph has the critical host counts, but no
freeness theorem is asserted. This is not a proof of Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714ExceptionalSteiner
open Erdos714ExceptionalCounts
variable {E K : Type*} [Field E] [Field K] [CharP E 3] [CharP K 3]

/-- Three distinct roots of one member of the exceptional quintic family. -/
def Triple (u v w : E) : Prop :=
  u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ ∃ a b : E,
    u ∈ roots a b ∧ v ∈ roots a b ∧ w ∈ roots a b

omit [CharP E 3] in
lemma triple_swap {u v w : E} (h : Triple u v w) : Triple v u w := by
  obtain ⟨huv,huw,hvw,a,b,hu,hv,hw⟩ := h
  exact ⟨huv.symm,hvw,huw,a,b,hv,hu,hw⟩

omit [CharP E 3] in
lemma triple_rotate {u v w : E} (h : Triple u v w) : Triple u w v := by
  obtain ⟨huv,huw,hvw,a,b,hu,hv,hw⟩ := h
  exact ⟨huw,huv,hvw.symm,a,b,hu,hw,hv⟩

lemma third_unique (hns : ¬IsSquare (-1:E)) {u v w z : E}
    (hw : Triple u v w) (hz : Triple u v z) : w=z := by
  obtain ⟨huv,huw,hvw,a,b,hu,hv,hw⟩ := hw
  obtain ⟨_,huz,hvz,c,d,hu',hv',hz⟩ := hz
  obtain ⟨rfl,rfl⟩ := parameters_unique a b c d u v huv hu hv hu' hv'
  by_contra hwz
  have hb := Erdos714Exceptional.finite_root_bound a b hns {u,v,w,z} (by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (mem_roots _ _ _).mp hu
    · exact (mem_roots _ _ _).mp hv
    · exact (mem_roots _ _ _).mp hw
    · exact (mem_roots _ _ _).mp hz)
  have hc : ({u,v,w,z} : Finset E).card=4 := by simp [huv,huw,huz,hvw,hvz,hwz]
  omega

lemma triple_map (f : E →+* K) {u v w : E} (h : Triple u v w) :
    Triple (f u) (f v) (f w) := by
  obtain ⟨huv,huw,hvw,a,b,hu,hv,hw⟩ := h
  have hr (x : E) (hx : x ∈ roots a b) : f x ∈ roots (f a) (f b) := by
    rw [mem_roots] at hx ⊢
    simpa only [map_add,map_mul,map_pow,map_zero] using congrArg f hx
  exact ⟨f.injective.ne huv,f.injective.ne huw,f.injective.ne hvw,
    f a,f b,hr u hu,hr v hv,hr w hw⟩

variable [Finite E]

lemma third_exists (hns : ¬IsSquare (-1:E)) (u v : E) (huv : u ≠ v) :
    ∃ w, Triple u v w := by
  obtain ⟨a,b,hu,hv⟩ := two_root_parameters u v huv
  obtain ⟨w,hwu,hwv,hw⟩ := third_root a b u v huv
    ((mem_roots _ _ _).mp hu) ((mem_roots _ _ _).mp hv) hns
  exact ⟨w,huv,hwu.symm,hwv.symm,a,b,hu,hv,(mem_roots _ _ _).mpr hw⟩

def star (hns : ¬IsSquare (-1:E)) (u v : E) : E :=
  if h : u=v then u else Classical.choose (third_exists hns u v h)

@[simp] lemma star_self (hns : ¬IsSquare (-1:E)) (u : E) : star hns u u=u := by
  simp [star]

lemma star_triple (hns : ¬IsSquare (-1:E)) {u v : E} (huv : u ≠ v) :
    Triple u v (star hns u v) := by
  simpa only [star,dif_neg huv] using Classical.choose_spec (third_exists hns u v huv)

lemma star_eq_of_triple (hns : ¬IsSquare (-1:E)) {u v w : E}
    (h : Triple u v w) : star hns u v=w :=
  third_unique hns (star_triple hns h.1) h

lemma star_comm (hns : ¬IsSquare (-1:E)) (u v : E) : star hns u v=star hns v u := by
  by_cases h : u=v
  · subst v; rfl
  · exact star_eq_of_triple hns (triple_swap (star_triple hns (Ne.symm h)))

lemma star_involutive (hns : ¬IsSquare (-1:E)) (u : E) :
    Function.Involutive (star hns u) := by
  intro v
  by_cases h : u=v
  · subst v; simp
  · exact star_eq_of_triple hns (triple_rotate (star_triple hns h))

def starEquiv (hns : ¬IsSquare (-1:E)) (u : E) : E ≃ E :=
  (star_involutive hns u).toPerm

lemma star_map [Finite K] (f : E →+* K) (hE : ¬IsSquare (-1:E))
    (hK : ¬IsSquare (-1:K)) (u v : E) : f (star hE u v)=star hK (f u) (f v) := by
  by_cases h : u=v
  · subst v; simp
  · exact (star_eq_of_triple hK (triple_map f (star_triple hE h))).symm

section Norm
variable {F : Type*} [Field F] [Algebra F E] [FiniteDimensional F E]

/-- Multiplicative weights on the actual quasigroup kernel, not on u+v. -/
def graph (hns : ¬IsSquare (-1:E)) : SimpleGraph ((E × Fˣ) ⊕ (E × Fˣ)) where
  Adj x y := match x,y with
    | .inl x,.inr y => Algebra.norm F (star hns x.1 y.1)=(x.2:F)*(y.2:F)
    | .inr y,.inl x => Algebra.norm F (star hns x.1 y.1)=(x.2:F)*(y.2:F)
    | _,_ => False
  symm := by intro x y; cases x <;> cases y <;> exact id
  loopless := by intro x; cases x <;> exact not_false

def relationNeighbors (hns : ¬IsSquare (-1:E)) (x : E × Fˣ) :
    {y : E × Fˣ // Algebra.norm F (star hns x.1 y.1)=(x.2:F)*(y.2:F)} ≃
      {z : E // z ≠ 0} where
  toFun y := ⟨star hns x.1 y.val.1,by
    intro hz
    have hh := y.property
    rw [hz,Algebra.norm_zero] at hh
    exact mul_ne_zero x.2.ne_zero y.val.2.ne_zero hh.symm⟩
  invFun z := ⟨(star hns x.1 z.val,
    Units.mk0 (Algebra.norm F z.val/(x.2:F))
      (div_ne_zero (Algebra.norm_ne_zero_iff.mpr z.property) x.2.ne_zero)),by
    change Algebra.norm F (star hns x.1 (star hns x.1 z.val))=
      (x.2:F)*(Algebra.norm F z.val/(x.2:F))
    rw [star_involutive hns x.1]
    exact (mul_div_cancel₀ _ x.2.ne_zero).symm⟩
  left_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · exact star_involutive hns x.1 y.val.1
    · apply Units.ext
      change Algebra.norm F (star hns x.1 y.val.1)/(x.2:F)=(y.val.2:F)
      rw [y.property]
      exact mul_div_cancel_left₀ _ x.2.ne_zero
  right_inv z := Subtype.ext (star_involutive hns x.1 z.val)

def leftNeighbors (hns : ¬IsSquare (-1:E)) (x : E × Fˣ) :
    (graph hns).neighborSet (.inl x) ≃ {z : E // z ≠ 0} :=
  (show (graph hns).neighborSet (.inl x) ≃
    {y : E × Fˣ // Algebra.norm F (star hns x.1 y.1)=(x.2:F)*(y.2:F)} from
    { toFun := fun y => match y with
        | ⟨.inl _,h⟩ => False.elim h
        | ⟨.inr y,h⟩ => ⟨y,h⟩
      invFun := fun y => ⟨.inr y.val,y.property⟩
      left_inv := by
        rintro ⟨y,h⟩
        cases y with
        | inl y => exact False.elim h
        | inr y => rfl
      right_inv := fun y => rfl }).trans (relationNeighbors hns x)

def rightNeighbors (hns : ¬IsSquare (-1:E)) (x : E × Fˣ) :
    (graph hns).neighborSet (.inr x) ≃ {z : E // z ≠ 0} :=
  (show (graph hns).neighborSet (.inr x) ≃
    {y : E × Fˣ // Algebra.norm F (star hns x.1 y.1)=(x.2:F)*(y.2:F)} from
    { toFun := fun y => match y with
        | ⟨.inr _,h⟩ => False.elim h
        | ⟨.inl y,h⟩ => ⟨y,by
            change Algebra.norm F (star hns y.1 x.1)=(y.2:F)*(x.2:F) at h
            simpa only [star_comm hns y.1 x.1,mul_comm (y.2:F)] using h⟩
      invFun := fun y => ⟨.inl y.val,by
        simpa only [star_comm hns x.1 y.val.1,mul_comm (x.2:F)] using y.property⟩
      left_inv := by
        rintro ⟨y,h⟩
        cases y with
        | inr y => exact False.elim h
        | inl y => rfl
      right_inv := fun y => rfl }).trans (relationNeighbors hns x)

variable [Fintype F] [Fintype E]

theorem degree (hns : ¬IsSquare (-1:E)) (v : (E × Fˣ) ⊕ (E × Fˣ)) :
    (graph hns).degree v=Fintype.card E-1 := by
  rw [←card_neighborSet_eq_degree]
  cases v with
  | inl x =>
    rw [Fintype.card_congr (leftNeighbors hns x),Fintype.card_subtype_compl]
    simp
  | inr x =>
    rw [Fintype.card_congr (rightNeighbors hns x),Fintype.card_subtype_compl]
    simp

omit [Field E] [CharP E 3] [Finite E] [Algebra F E] [FiniteDimensional F E] in
lemma vertex_count : Fintype.card ((E × Fˣ) ⊕ (E × Fˣ))=
    2*Fintype.card E*(Fintype.card F-1) := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_units]
  ring

theorem edge_count (hns : ¬IsSquare (-1:E)) :
    (graph (F := F) hns).edgeFinset.card=
      Fintype.card E*(Fintype.card F-1)*(Fintype.card E-1) := by
  have h := (graph (F := F) hns).sum_degrees_eq_twice_card_edges
  simp only [degree,Finset.sum_const,Finset.card_univ,smul_eq_mul,vertex_count] at h
  nlinarith only [h]

end Norm
#print axioms third_unique
#print axioms third_exists
#print axioms star_comm
#print axioms star_involutive
#print axioms star_map
#print axioms relationNeighbors
#print axioms degree
#print axioms edge_count
end Erdos714ExceptionalSteiner
