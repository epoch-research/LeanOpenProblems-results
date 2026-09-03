import Submission.ContactKernel
import Submission.PathKernelPartitions
import Submission.MaximumTriplePatterns

/-! Junction extraction from arbitrary cycle families. This gives a genuine
finite kernel for every family with at least two contacts per piece. It does
not assert a classification of those kernels or a general linear bound. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.CycleSegments
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {V K : Type*} [Fintype V] [Fintype K] {G : SimpleGraph V}

/-- A vertex lying on two different members of a set family. -/
def Junction (B : K → Set V) := {x : V // ∃ i j, i ≠ j ∧ x ∈ B i ∧ x ∈ B j}

def LocalJunction (B : K → Set V) (i : K) := {w : Junction B // w.val ∈ B i}

noncomputable instance junctionFintype (B : K → Set V) : Fintype (Junction B) := by
  unfold Junction
  infer_instance
noncomputable instance localJunctionFintype (B : K → Set V) (i : K) :
    Fintype (LocalJunction B i) := by
  unfold LocalJunction
  infer_instance

lemma junction_mem_iff (B : K → Set V) (i : K) (x : V) (hx : x ∈ B i) :
    (∃ a b, a ≠ b ∧ x ∈ B a ∧ x ∈ B b) ↔ ∃ j, j ≠ i ∧ x ∈ B j := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    by_cases hai : a = i
    · subst a
      exact ⟨b,hab.symm,hb⟩
    · exact ⟨a,hai,ha⟩
  · rintro ⟨j,hj,hxj⟩
    exact ⟨i,j,hj.symm,hx,hxj⟩

noncomputable def localJunctionEquiv (B : K → Set V) (i : K) :
    LocalJunction B i ≃ {x : V // x ∈ B i ∧ ∃ j, j ≠ i ∧ x ∈ B j} where
  toFun w := ⟨w.val.val,w.property,(junction_mem_iff B i _ w.property).mp w.val.property⟩
  invFun x := ⟨⟨x.val,(junction_mem_iff B i _ x.property.1).mpr x.property.2⟩,x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Number all the contact vertices on each cycle, retaining their common
identity in the global junction type. No cyclic ordering is presumed here. -/
lemma exists_junction_layout (root : K → V) (C : ∀ i, G.Walk (root i) (root i))
    (hcontacts : ∀ i, 2 ≤ Fintype.card (LocalJunction (fun j => {x | x ∈ (C j).support}) i)) :
    ∃ m : K → ℕ, ∃ place : ∀ i, Fin (m i+2) → Junction (fun j => {x | x ∈ (C j).support}),
      (∀ i, Function.Injective (place i)) ∧
      ContactLayout (fun i => m i+2) place Subtype.val root C := by
  let B : K → Set V := fun j => {x | x ∈ (C j).support}
  let m : K → ℕ := fun i => Fintype.card (LocalJunction B i) - 2
  have hm (i : K) : Fintype.card (LocalJunction B i) = m i+2 :=
    (Nat.sub_add_cancel (hcontacts i)).symm
  let e (i : K) : LocalJunction B i ≃ Fin (m i+2) := Fintype.equivFinOfCardEq (hm i)
  let place (i : K) (x : Fin (m i+2)) : Junction B := ((e i).symm x).val
  refine ⟨m,place,?_,?_⟩
  · intro i x y hxy
    exact (e i).symm.injective (Subtype.ext hxy)
  · refine ⟨Subtype.val_injective,?_,?_⟩
    · intro i w
      constructor
      · intro hw
        refine ⟨e i ⟨w,hw⟩,?_⟩
        exact congrArg Subtype.val ((e i).symm_apply_apply ⟨w,hw⟩)
      · rintro ⟨x,rfl⟩
        exact ((e i).symm x).property
    · intro i j hij x hxi hxj
      exact ⟨⟨x,i,j,hij,hxi,hxj⟩,rfl⟩

lemma exists_junction_kernel (root : K → V) (C : ∀ i, G.Walk (root i) (root i))
    (hC : ∀ i, (C i).IsCycle)
    (hd : ∀ i j, i ≠ j → (C i).edges.Disjoint (C j).edges)
    (hcover : ∀ x y, G.Adj x y → ∃ i, s(x,y) ∈ (C i).edges)
    (hcontacts : ∀ i, 2 ≤ Fintype.card (LocalJunction (fun j => {x | x ∈ (C j).support}) i)) :
    ∃ m : K → ℕ, ∃ place : ∀ i, Fin (m i+2) → Junction (fun j => {x | x ∈ (C j).support}),
    ∃ o : ∀ i, Marked.Order (m i),
    ∃ F : PathSubstitution.Family (Σ i, Fin (m i+2))
        (Junction (fun j => {x | x ∈ (C j).support})) G,
      (∀ i, Function.Injective (place i)) ∧
      ContactLayout (fun i => m i+2) place Subtype.val root C ∧
      F.vertex = Subtype.val ∧
      F.src = (fun j => place j.1 j.2) ∧
      F.dst = (fun j => place j.1 (Marked.nextFin (m j.1) (o j.1) j.2)) ∧
      (∀ i e, e ∈ (C i).edges ↔ ∃ j, e ∈ (F.path ⟨i,j⟩).edges) ∧
      (∀ x y, G.Adj x y → ∃ j, s(x,y) ∈ (F.path j).edges) := by
  obtain ⟨m,place,hplace,L⟩ := exists_junction_layout root C hcontacts
  obtain ⟨o,F,hF,hsrc,hdst,hpiece,hcov⟩ := L.exists_ordered_family m place hplace
    Subtype.val root C hC hd hcover
  exact ⟨m,place,o,F,hplace,L,hF,hsrc,hdst,hpiece,hcov⟩

#print axioms exists_junction_kernel
end Erdos184Work.CycleSegments
