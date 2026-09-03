import Submission.OriginLineLiftExplore

/-! Representation-peak propagation through the concrete line recoloring.
The regenerated upper cap does not make an unchanged iteration harmless:
every two steps can double an inherited self-representation count. -/
namespace Erdos66LineRecoloringPeaks
open Erdos66GraphRowAssembly Erdos66LineRecoloring Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 2600000
variable {G F : Type*} [AddCommGroup G] [DecidableEq G]
  [Field F] [Fintype F] [DecidableEq F]

lemma row_mixed_dominates (B C : F → Finset G) (f h : F → F) (x y : F) (z : G) :
    pairCount (B x) (C y) z ≤
      pairCount (rowAssembly B f) (rowAssembly C h) (z,(x+y,f x+h y)) := by
  rw [rowAssembly_mixed_pairCount]
  have hh := Finset.single_le_sum (f := fun u : F ↦
    if f u+h (x+y-u)=f x+h y then pairCount (B u) (C (x+y-u)) z else 0)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)
  simpa only [add_sub_cancel_left,if_pos rfl] using hh

lemma row_self_dominates_twice (B : F → Finset G) (f : F → F) (x y : F)
    (hxy : x≠y) (z : G) :
    2*pairCount (B x) (B y) z ≤
      pairCount (rowAssembly B f) (rowAssembly B f) (z,(x+y,f x+f y)) := by
  rw [rowAssembly_mixed_pairCount]
  let w : F → ℕ := fun u ↦
    if f u+f (x+y-u)=f x+f y then pairCount (B u) (B (x+y-u)) z else 0
  have hx : w x=pairCount (B x) (B y) z := by simp [w]
  have hy : w y=pairCount (B x) (B y) z := by
    simp only [w,add_sub_cancel_right,add_comm (f y) (f x),ite_true,pairCount_comm (B y)]
  have hs : ∑ u∈({x,y} : Finset F), w u ≤ ∑ u : F, w u :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Finset.sum_pair hxy,hx,hy] at hs
  change _ ≤ ∑ u : F, w u
  omega

def oldRow (α v u : F) : F := (v-u)/α

def oldPoint (τ α v u : F) : F×F :=
  (oldRow α v u,recolorGraph τ α v (oldRow α v u))

omit [Fintype F] [DecidableEq F] in
lemma label_oldRow (α v u : F) (hα : α≠0) : v-α*oldRow α v u=u := by
  unfold oldRow
  field_simp
  ring

omit [Fintype F] [DecidableEq F] in
lemma oldRow_injective (α v : F) (hα : α≠0) : Function.Injective (oldRow α v) := by
  intro u w he
  have hh := congrArg (fun x ↦ v-α*x) he
  simpa only [label_oldRow α v _ hα] using hh

/-- Any old mixed count survives in ANY prescribed pair of new colors,
with an explicitly given new high target. -/
theorem recolored_mixed_dominates (A : F → Finset G) (τ α : F) (hα : α≠0)
    (u t v w : F) (z : G) :
    pairCount (A u) (A t) z ≤
      pairCount (recolored A τ α v) (recolored A τ α w)
        (z,oldPoint τ α v u+oldPoint τ α w t) := by
  have hh := row_mixed_dominates (fun x ↦ A (v-α*x)) (fun y ↦ A (w-α*y))
    (recolorGraph τ α v) (recolorGraph τ α w) (oldRow α v u) (oldRow α w t) z
  simpa only [label_oldRow α v u hα,label_oldRow α w t hα,recolored,oldPoint,Prod.mk_add_mk] using hh

/-- A count between distinct old labels contributes twice to a new
same-color count, because both ordered orientations occur. -/
theorem recolored_self_dominates_twice (A : F → Finset G) (τ α : F) (hα : α≠0)
    (u t : F) (hut : u≠t) (v : F) (z : G) :
    2*pairCount (A u) (A t) z ≤
      pairCount (recolored A τ α v) (recolored A τ α v)
        (z,oldPoint τ α v u+oldPoint τ α v t) := by
  have hh := row_self_dominates_twice (fun x ↦ A (v-α*x)) (recolorGraph τ α v)
    (oldRow α v u) (oldRow α v t) (fun he ↦ hut (oldRow_injective α v hα he)) z
  simpa only [label_oldRow α v u hα,label_oldRow α v t hα,recolored,oldPoint,Prod.mk_add_mk] using hh

/-- The doubled old self-count appears after two steps, in every chosen
final color. This lower bound does not assume disjointness, flatness, or
any upper cap on the input. -/
theorem two_step_self_amplification (A : F → Finset G) (τ α σ β : F)
    (hα : α≠0) (hβ : β≠0) (u v : F) (z : G) :
    ∃ z' : (G×(F×F))×(F×F),
      2*pairCount (A u) (A u) z ≤
        pairCount (recolored (recolored A τ α) σ β v)
          (recolored (recolored A τ α) σ β v) z' := by
  let z₁ := (z,oldPoint τ α 0 u+oldPoint τ α 1 u)
  refine ⟨(z₁,oldPoint σ β v 0+oldPoint σ β v 1),?_⟩
  have hfirst := recolored_mixed_dominates A τ α hα u u 0 1 z
  have hsecond := recolored_self_dominates_twice (recolored A τ α) σ β hβ 0 1 zero_ne_one v z₁
  exact (Nat.mul_le_mul_left 2 hfirst).trans hsecond

end Erdos66LineRecoloringPeaks
