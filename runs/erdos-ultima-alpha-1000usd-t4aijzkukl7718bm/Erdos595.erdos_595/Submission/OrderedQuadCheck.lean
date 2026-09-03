import Submission.ArcAdjoint

/-!
An ordered four-subset base and a K4-free biclique right adjoint.
This auxiliary construction does not establish countable non-coverability.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open SimpleGraph Set
namespace Erdos595OrderedQuadRight
open Erdos595ArcAdjoint
variable {A : Type*} [LinearOrder A]
abbrev Quad (A : Type*) := Fin 4 → A

def AB (x y : Quad A) : Prop :=
  x 1 = y 2 ∧ x 2 = y 3 ∧ y 0 < x 0 ∧ x 0 < y 1 ∧ y 1 < x 1 ∧ x 1 < x 2 ∧ x 2 < x 3

def AC (x y : Quad A) : Prop :=
  x 0 = y 1 ∧ x 3 = y 3 ∧ y 0 < x 0 ∧ x 0 < y 2 ∧ y 2 < x 1 ∧ x 1 < x 2 ∧ x 2 < x 3

def BC (x y : Quad A) : Prop :=
  x 0 = y 0 ∧ x 1 = y 2 ∧ x 0 < y 1 ∧ y 1 < x 1 ∧ x 1 < x 2 ∧ x 2 < x 3 ∧ x 3 < y 3

def Adj (x y : Quad A) : Prop :=
  AB x y ∨ AC x y ∨ AB y x ∨ BC x y ∨ AC y x ∨ BC y x

lemma adj_symm {x y : Quad A} (h : Adj x y) : Adj y x := by
  unfold Adj at *
  tauto

lemma adj_irrefl (x : Quad A) : ¬Adj x x := by
  intro h
  rcases h with h | h | h | h | h | h <;>
    simp only [AB,AC,BC] at h <;> obtain ⟨_,_,_,_,_,_,_⟩ := h <;> order

def graph (A : Type*) [LinearOrder A] : SimpleGraph (Quad A) where
  Adj := Adj
  symm := fun _ _ => adj_symm
  loopless := adj_irrefl

def Tri (x y z : Quad A) : Prop :=
  x 0 = z 1 ∧ x 1 = y 2 ∧ x 2 = y 3 ∧ x 3 = z 3 ∧ y 0 = z 0 ∧ y 1 = z 2 ∧ y 0 < x 0 ∧ x 0 < y 1 ∧ y 1 < x 1 ∧ x 1 < x 2 ∧ x 2 < x 3

def TriOptions (x y z : Quad A) : Prop :=
  Tri x y z ∨ Tri x z y ∨ Tri y x z ∨ Tri z x y ∨ Tri y z x ∨ Tri z y x

theorem triangle_options {x y z : Quad A} (hxy : Adj x y)
    (hxz : Adj x z) (hyz : Adj y z) : TriOptions x y z := by
  rcases hxy with hxy | hxy | hxy | hxy | hxy | hxy
  · rcases hxz with hxz | hxz | hxz | hxz | hxz | hxz
    · rcases hyz with hyz | hyz | hyz | hyz | hyz | hyz
      · simp only [AB,AC,BC] at hxy hxz hyz
        rcases hxy with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        rcases hxz with ⟨j1,j2,j3,j4,j5,j6,j7⟩
        rcases hyz with ⟨k1,k2,k3,k4,k5,k6,k7⟩
        exfalso
        order
      · simp only [AB,AC,BC] at hxy hxz hyz
        rcases hxy with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        rcases hxz with ⟨j1,j2,j3,j4,j5,j6,j7⟩
        rcases hyz with ⟨k1,k2,k3,k4,k5,k6,k7⟩
        exfalso
        order
      · simp only [AB,AC,BC] at hxy hxz hyz
        rcases hxy with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        rcases hxz with ⟨j1,j2,j3,j4,j5,j6,j7⟩
        rcases hyz with ⟨k1,k2,k3,k4,k5,k6,k7⟩
        exfalso
        order
      · simp only [AB,AC,BC] at hxy hxz hyz
        rcases hxy with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        rcases hxz with ⟨j1,j2,j3,j4,j5,j6,j7⟩
        rcases hyz with ⟨k1,k2,k3,k4,k5,k6,k7⟩
        exfalso
        order
      · simp only [AB,AC,BC] at hxy hxz hyz
        rcases hxy with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        rcases hxz with ⟨j1,j2,j3,j4,j5,j6,j7⟩
        rcases hyz with ⟨k1,k2,k3,k4,k5,k6,k7⟩
        exfalso
        order
      · simp only [AB,AC,BC] at hxy hxz hyz
        rcases hxy with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        rcases hxz with ⟨j1,j2,j3,j4,j5,j6,j7⟩
        rcases hyz with ⟨k1,k2,k3,k4,k5,k6,k7⟩
        exfalso
        order
    · rcases hyz with hyz | hyz | hyz | hyz | hyz | hyz
      · simp only [AB,AC,BC] at hxy hxz hyz
        rcases hxy with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        rcases hxz with ⟨j1,j2,j3,j4,j5,j6,j7⟩
        rcases hyz with ⟨k1,k2,k3,k4,k5,k6,k7⟩
        exfalso
        order
      · simp only [AB,AC,BC] at hxy hxz hyz
        rcases hxy with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        rcases hxz with ⟨j1,j2,j3,j4,j5,j6,j7⟩
        rcases hyz with ⟨k1,k2,k3,k4,k5,k6,k7⟩
        exfalso
        order
      · simp only [AB,AC,BC] at hxy hxz hyz
        rcases hxy with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        rcases hxz with ⟨j1,j2,j3,j4,j5,j6,j7⟩
        rcases hyz with ⟨k1,k2,k3,k4,k5,k6,k7⟩
        exfalso
        order
      · simp only [AB,AC,BC] at hxy hxz hyz
        rcases hxy with ⟨h1,h2,h3,h4,h5,h6,h7⟩
        rcases hxz with ⟨j1,j2,j3,j4,j5,j6,j7⟩
        rcases hyz with ⟨k1,k2,k3,k4,k5,k6,k7⟩
        apply Or.inl (show Tri x y z from ?_)
        unfold Tri
        repeat' constructor <;> (first | assumption | order | trace_state)
