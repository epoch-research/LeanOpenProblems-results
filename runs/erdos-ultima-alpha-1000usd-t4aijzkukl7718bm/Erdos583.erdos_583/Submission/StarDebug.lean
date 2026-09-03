import Submission.Work
open SimpleGraph
open scoped Classical
namespace Test
structure Arm {V : Type*} (G : SimpleGraph V) (x : V) where
 finish : V
 walk : G.Walk x finish
 isPath : walk.IsPath
noncomputable def half {V : Type*} {G : SimpleGraph V} {a b : V} (P : G.Walk a b) (hp : P.IsPath) (x : V) (d : Bool) : Arm G x :=
 if hx : x ∈ P.support then
  if d then ⟨a,(P.takeUntil x hx).reverse,(hp.takeUntil hx).reverse⟩
  else ⟨b,P.dropUntil x hx,hp.dropUntil hx⟩
 else ⟨x,.nil,by simp⟩
example {V : Type*} {G : SimpleGraph V} {a b : V} (P : G.Walk a b) (hp : P.IsPath) (x : V) (d : Bool)
 (hx : x ∉ P.support) : (half P hp x d).walk.Nil := by
 unfold half
 rw [dif_neg hx]
 simp
end Test
