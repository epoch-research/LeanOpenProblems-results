import Submission.BoundedIncreasingPath
import Submission.NegativeInner

/-!
Finite ranks on homogeneous triangle extensions give triangle-free edge
covers. Auxiliary criteria, not a settlement of Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set
open Erdos595BoundedPath Erdos595Work
namespace Erdos595FanCover
variable {V C : Type*} [LinearOrder V] [Countable C]

def Extend (G : SimpleGraph V) (col : V → V → C) (t : C)
    (p q : V × V) : Prop :=
  p.1 = q.1 ∧ p.1 < p.2 ∧ p.2 < q.2 ∧
    G.Adj p.1 p.2 ∧ G.Adj p.1 q.2 ∧ G.Adj p.2 q.2 ∧
    col p.1 p.2 = t ∧ col p.1 q.2 = t ∧ col p.2 q.2 = t

/-- A type-dependent finite bound on increasing homogeneous fans gives a
countable triangle-free cover. With a finite type palette and uniform bound,
the construction is itself finite. -/
theorem cover_of_bounded_fans (G : SimpleGraph V) (col : V → V → C)
    (N : C → ℕ)
    (hn : ∀ t p q, ¬Chain (Extend G col t) (N t) p q) :
    IsCountableUnionOfTriangleFree G := by
  classical
  choose rank hrank using fun t => finite_rank (Extend G col t) (N t) (hn t)
  let code (a b : V) : C × ℕ := (col a b,(rank (col a b) (a,b)).val)
  apply Erdos595NegativeInner.cover_of_ordered_patterns G code
  intro a b c hab hbc aab aac abc he
  have ht : col a b = col a c := congrArg Prod.fst he.1
  have hu : col a b = col b c := congrArg Prod.fst he.2
  have hh : (rank (col a b) (a,b)).val = (rank (col a c) (a,c)).val :=
    congrArg Prod.snd he.1
  rw [← ht] at hh
  exact (hrank (col a b) (a,b) (a,c) ⟨rfl,hab,hbc,aab,aac,abc,rfl,ht.symm,hu.symm⟩).ne
    (Fin.ext hh)

#print axioms cover_of_bounded_fans
end Erdos595FanCover
