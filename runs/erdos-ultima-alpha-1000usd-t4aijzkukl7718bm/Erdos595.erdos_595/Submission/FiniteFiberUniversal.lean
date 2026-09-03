import Submission.FiniteFiberOddBound
import Submission.RightFiberCover

/-!
Every two-three-coloring fiber template maps to one universal nine-point
fiber template. The induced maps persist through every finite right tower.
No non-coverability claim for the universal template is made here.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FiniteFiberUniversal
open Erdos595FiniteFiberOddBound Erdos595HigherConeOddBound Erdos595ArcAdjoint
universe u

abbrev Nine := ULift.{u} (Fin 3 × Fin 3)

def fiber : SimpleGraph Nine where
  Adj a b := a.down.1 ≠ b.down.1 ∧ a.down.2 ≠ b.down.2
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.1 rfl

/-- The maximal symmetric cross relation allowed by the two coordinate colorings. -/
def cross (a b : Nine) : Prop := a.down.1 ≠ b.down.2 ∧ a.down.2 ≠ b.down.1

lemma cross_symm : Symmetric cross := fun _ _ h => ⟨h.2.symm,h.1.symm⟩

def template : Template fiber cross :=
  ⟨SimpleGraph.Coloring.mk (fun a => a.down.1) (fun h => h.1),
    SimpleGraph.Coloring.mk (fun a => a.down.2) (fun h => h.2),fun _ _ h => h.1⟩

variable {I S : Type u} (F : SimpleGraph S) (P : S → S → Prop)
    (hP : Symmetric P) (t : Template F P) (B : SimpleGraph I)

/-- Every fiber, finite or infinite, folds through the pair of its two colors. -/
def fold : bundle F P hP B →g bundle fiber cross cross_symm B where
  toFun x := (x.1,ULift.up (t.c₀ x.2,t.c₁ x.2))
  map_rel' := by
    intro x y hxy
    rcases hxy with ⟨he,hxy⟩ | ⟨hB,hxy⟩
    · exact Or.inl ⟨he,t.c₀.valid hxy,t.c₁.valid hxy⟩
    · exact Or.inr ⟨hB,t.cross _ _ hxy,(t.cross _ _ (hP hxy)).symm⟩

/-- Functoriality at every finite right-adjoint stage. -/
noncomputable def iterRightHom (n : ℕ) {p q : Packed.{u}} (f : Hom p q) :
    Hom ((rightP^[n]) p) ((rightP^[n]) q) := by
  induction n with
  | zero => exact f
  | succ n ih =>
    rw [Function.iterate_succ_apply' rightP,Function.iterate_succ_apply' rightP]
    exact Erdos595RightFiber.rightHom ih

include t in
/-- A covering theorem for the nine-point template would cover every template
with two compatible proper three-colorings at the same right stage. -/
theorem cover_of_universal (n : ℕ)
    (h : Erdos595Work.IsCountableUnionOfTriangleFree
      (((rightP^[n]) ⟨I × Nine,bundle fiber cross cross_symm B⟩).2)) :
    Erdos595Work.IsCountableUnionOfTriangleFree
      (((rightP^[n]) ⟨I × S,bundle F P hP B⟩).2) :=
  Erdos595Work.countable_union_of_hom
    (iterRightHom n (p := ⟨I × S,bundle F P hP B⟩)
      (q := ⟨I × Nine,bundle fiber cross cross_symm B⟩) (fold F P hP t B)) h

include t in
/-- Conversely, a genuine obstruction anywhere in this template class
would already be an obstruction for the nine-point template. -/
theorem universal_no_cover (n : ℕ)
    (h : ¬Erdos595Work.IsCountableUnionOfTriangleFree
      (((rightP^[n]) ⟨I × S,bundle F P hP B⟩).2)) :
    ¬Erdos595Work.IsCountableUnionOfTriangleFree
      (((rightP^[n]) ⟨I × Nine,bundle fiber cross cross_symm B⟩).2) :=
  fun hh => h (cover_of_universal F P hP t B n hh)

/-- The universal template obeys the same verified finite odd-walk bound. -/
theorem universal_cliqueFree (n : ℕ) (hB : NoShortOdd B (bound.{u} n)) :
    (((rightP^[n]) ⟨I × Nine,bundle fiber cross cross_symm B⟩).2).CliqueFree 4 :=
  Erdos595FiniteFiberOddBound.cliqueFree n fiber cross cross_symm template B hB

/-- At stage zero there is always a cover when the index graph is triangle-free. -/
theorem base_cover (hB : B.CliqueFree 3) :
    Erdos595Work.IsCountableUnionOfTriangleFree (bundle fiber cross cross_symm B) := by
  classical
  obtain ⟨e,he⟩ := exists_injective_nat Nine
  let bits : Nine → ℕ → Fin 2 := fun a n => if e a = n then 1 else 0
  have hbits : Function.Injective bits := by
    intro a b hab
    apply he
    have h := congrFun hab (e a)
    by_contra hn
    simp [bits,Ne.symm hn] at h
  apply Erdos595Work.countable_union_of_triangle_free_fibers _ (fun x => bits x.2)
  intro a b d hab had hbd hh
  have hab' : a.2 = b.2 := hbits hh.1
  have had' : a.2 = d.2 := hbits hh.2
  have edge {x y : I × Nine} (he : x.2 = y.2)
      (h : (bundle fiber cross cross_symm B).Adj x y) : B.Adj x.1 y.1 := by
    rcases h with h | h
    · exact (h.2.ne he).elim
    · exact h.1
  exact hB _ (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨edge hab' hab,edge had' had,edge (hab'.symm.trans had') hbd⟩)

abbrev offDiagonal : Nine := ⟨(0,1)⟩
abbrev diagonal : Nine := ⟨(2,2)⟩

/-- Every index edge occurs as one side of an explicit mixed-fiber triangle. -/
lemma mixed_triangle {i j : I} (hij : B.Adj i j) :
    (bundle fiber cross cross_symm B).Adj (i,offDiagonal) (j,offDiagonal) ∧
    (bundle fiber cross cross_symm B).Adj (i,offDiagonal) (i,diagonal) ∧
    (bundle fiber cross cross_symm B).Adj (j,offDiagonal) (i,diagonal) := by
  refine ⟨Or.inr ⟨hij,by simp [cross,offDiagonal]⟩,
    Or.inl ⟨rfl,by simp [fiber,offDiagonal,diagonal]⟩,
    Or.inr ⟨hij.symm,by simp [cross,offDiagonal,diagonal]⟩⟩

/-- A rainbow-on-triangles vertex label of the universal base properly colors
B. This is stronger than an edge cover, and must not be used as its converse. -/
theorem rainbow_transfer {D : Type*} (c : I × Nine → D)
    (hc : ∀ x y z, (bundle fiber cross cross_symm B).Adj x y →
      (bundle fiber cross cross_symm B).Adj x z →
      (bundle fiber cross cross_symm B).Adj y z → c x ≠ c y) :
    Nonempty (B.Coloring D) := by
  refine ⟨SimpleGraph.Coloring.mk (fun i => c (i,offDiagonal)) ?_⟩
  intro i j hij
  have ht := mixed_triangle B hij
  exact hc _ _ _ ht.1 ht.2.1 ht.2.2

#print axioms base_cover
#print axioms mixed_triangle
#print axioms rainbow_transfer

#print axioms fold
#print axioms iterRightHom
#print axioms cover_of_universal
#print axioms universal_no_cover
#print axioms universal_cliqueFree
end Erdos595FiniteFiberUniversal
