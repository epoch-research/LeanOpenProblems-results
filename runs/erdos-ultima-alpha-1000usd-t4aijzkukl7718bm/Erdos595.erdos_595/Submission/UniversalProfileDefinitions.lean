import Submission.FiniteFiberUniversal

/-! The finite witness diagram for two complementary biclique-triangle profiles. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595UniversalProfile
open Erdos595FiniteFiberUniversal Erdos595FiniteFiberOddBound Erdos595ArcAdjoint
universe u
variable {I : Type u} (B : SimpleGraph I)

abbrev H := bundle fiber cross cross_symm B

def coord (c : Fin 9) : Nine.{u} :=
  ⟨(⟨c.val / 3,by omega⟩,⟨c.val % 3,Nat.mod_lt _ (by decide)⟩)⟩

lemma coord_injective : Function.Injective coord.{u} := by
  intro a b he
  have h₁ := congrArg (fun x : Nine => x.down.1.val) he
  have h₂ := congrArg (fun x : Nine => x.down.2.val) he
  simp only [coord] at h₁ h₂
  apply Fin.ext
  omega

lemma coord_surjective : Function.Surjective coord.{u} := by
  rintro ⟨a,b⟩
  refine ⟨⟨3*a.val+b.val,by omega⟩,?_⟩
  apply ULift.ext
  apply Prod.ext <;> apply Fin.ext <;> dsimp only [coord] <;> omega

def cls : Fin 6 → Fin 2 := ![0,0,1,0,1,1]
def source : Fin 12 → Fin 6 := ![0,0,1,1,2,2,3,3,4,4,5,5]
def target : Fin 12 → Fin 6 := ![1,2,0,2,0,1,4,5,3,5,3,4]

def rep (p : Fin 6) (s : Fin 2) (c : Fin 9) : Fin 120 :=
  ⟨18*p.val+9*s.val+c.val,by omega⟩

def wit (w : Fin 12) : Fin 120 := ⟨108+w.val,by omega⟩

def active (mark : Fin 2 → Fin 2 → Fin 9 → Prop) (n : Fin 120) : Prop :=
  if h : n.val < 108 then
    mark (cls ⟨n.val/18,by omega⟩) ⟨(n.val%18)/9,by omega⟩ ⟨n.val%9,Nat.mod_lt _ (by decide)⟩
  else True

def LeftSlot (p : Fin 6) (n : Fin 120) : Prop :=
  if h : n.val < 108 then n.val/18 = p.val ∧ n.val%18 < 9
  else target ⟨n.val-108,by omega⟩ = p

def RightSlot (p : Fin 6) (n : Fin 120) : Prop :=
  if h : n.val < 108 then n.val/18 = p.val ∧ 9 ≤ n.val%18
  else source ⟨n.val-108,by omega⟩ = p

instance (p : Fin 6) (n : Fin 120) : Decidable (LeftSlot p n) := by
  unfold LeftSlot
  infer_instance
instance (p : Fin 6) (n : Fin 120) : Decidable (RightSlot p n) := by
  unfold RightSlot
  infer_instance

structure Conditions (z : Fin 120 → I × Nine.{u}) (mark : Fin 2 → Fin 2 → Fin 9 → Prop) : Prop where
  fixed : ∀ p s c, (z (rep p s c)).2 = coord c
  edge : ∀ p a b, LeftSlot p a → RightSlot p b → active mark a → active mark b → (H B).Adj (z a) (z b)
  witness_source : ∀ w c, (z (wit w)).2 = coord c → mark (cls (source w)) 1 c
  witness_target : ∀ w c, (z (wit w)).2 = coord c → mark (cls (target w)) 0 c

variable (z : Fin 120 → I × Nine.{u})

lemma projected {a b : Fin 120} (hab : (H B).Adj (z a) (z b)) :
    (z a).1 = (z b).1 ∨ B.Adj (z a).1 (z b).1 :=
  hab.imp And.left And.left

lemma only_equal {a b : Fin 120} {i j : Fin 9}
    (hab : (H B).Adj (z a) (z b)) (ha : (z a).2 = coord i) (hb : (z b).2 = coord j)
    (hP : ¬cross (coord.{u} i) (coord.{u} j)) : (z a).1 = (z b).1 := by
  rcases hab with h | h
  · exact h.1
  · exact (hP (by simpa only [ha,hb] using h.2)).elim

lemma only_cross {a b : Fin 120} {i j : Fin 9}
    (hab : (H B).Adj (z a) (z b)) (ha : (z a).2 = coord i) (hb : (z b).2 = coord j)
    (hF : ¬fiber.Adj (coord.{u} i) (coord.{u} j)) : B.Adj (z a).1 (z b).1 := by
  rcases hab with h | h
  · exact (hF (by simpa only [ha,hb] using h.2)).elim
  · exact h.1

lemma impossible {a b : Fin 120} {i j : Fin 9}
    (hab : (H B).Adj (z a) (z b)) (ha : (z a).2 = coord i) (hb : (z b).2 = coord j)
    (hF : ¬fiber.Adj (coord.{u} i) (coord.{u} j)) (hP : ¬cross (coord.{u} i) (coord.{u} j)) : False := by
  rcases hab with h | h
  · exact hF (by simpa only [ha,hb] using h.2)
  · exact hP (by simpa only [ha,hb] using h.2)

end Erdos595UniversalProfile
