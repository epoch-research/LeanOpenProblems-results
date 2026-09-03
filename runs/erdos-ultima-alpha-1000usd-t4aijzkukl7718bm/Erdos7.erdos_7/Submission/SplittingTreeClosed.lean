import Submission.SplittingTreeCover
import Submission.DownwardDivisorAssignment

/-! Divisor closure can be imposed on a splitting-tree certificate without
altering its splitting skeleton or increasing its leaf labels. -/
namespace Erdos7SplittingTreeClosed
open Erdos7SplittingTreeCover
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Replace leaf labels, keeping every split and every child position. -/
def relabel : (T : Tree) → (T.Leaf → ℕ) → Tree
  | .leaf _, f => .leaf (f ())
  | .split q c, f => .split q (fun r => relabel (c r) (fun k => f ⟨r,k⟩))

def leafEquiv : (T : Tree) → (f : T.Leaf → ℕ) → (relabel T f).Leaf ≃ T.Leaf
  | .leaf _, _ => Equiv.refl Unit
  | .split _ c, f => Equiv.sigmaCongrRight (fun r => leafEquiv (c r) (fun k => f ⟨r,k⟩))

lemma modulus_relabel (T : Tree) (f : T.Leaf → ℕ) (k : (relabel T f).Leaf) :
    (relabel T f).modulus k=f (leafEquiv T f k) := by
  induction T with
  | leaf d => cases k; rfl
  | split q c ih =>
      rcases k with ⟨r,k⟩
      exact ih r (fun k => f ⟨r,k⟩) k

lemma residue_relabel (T : Tree) (f : T.Leaf → ℕ) (m : ℕ) (a : ℤ)
    (k : (relabel T f).Leaf) :
    (relabel T f).residue m a k=T.residue m a (leafEquiv T f k) := by
  induction T generalizing m a with
  | leaf d => rfl
  | split q c ih =>
      rcases k with ⟨r,k⟩
      exact ih r (fun k => f ⟨r,k⟩) (m*q) (a+(m : ℤ)*r.val) k

lemma valid_relabel (T : Tree) (f : T.Leaf → ℕ) (m : ℕ) (hT : T.Valid m)
    (hf : ∀ k, 1 < f k ∧ f k ∣ T.modulus k) : (relabel T f).Valid m := by
  induction T generalizing m with
  | leaf d => exact ⟨(hf ()).1,(hf ()).2.trans hT.2⟩
  | split q c ih =>
      exact ⟨hT.1,fun r => ih r (fun k => f ⟨r,k⟩) (m*q) (hT.2 r) (fun k => hf ⟨r,k⟩)⟩

/-- Every valid injectively labelled splitting tree has a relabelling with a
divisor-closed image. The same leaf positions and the same residues are used. -/
theorem exists_closed_relabel (T : Tree) (m : ℕ) (hT : T.Valid m)
    (hinj : Function.Injective T.modulus) :
    ∃ f : T.Leaf → ℕ,
      (∀ k, 1 < f k ∧ f k ∣ T.modulus k) ∧
      (relabel T f).Valid m ∧ Function.Injective (relabel T f).modulus ∧
      (∀ k d, 1 < d → d ∣ (relabel T f).modulus k →
        ∃ l, (relabel T f).modulus l=d) := by
  obtain ⟨f,hfi,hf,_,hc⟩ :=
    Erdos7DownwardDivisorAssignment.exists_closed T.modulus hinj (T.nontrivial m hT)
  refine ⟨f,hf,valid_relabel T f m hT hf,?_,?_⟩
  · intro k l hkl
    apply (leafEquiv T f).injective
    apply hfi
    simpa only [modulus_relabel] using hkl
  · intro k d hd hdk
    rw [modulus_relabel] at hdk
    obtain ⟨l,hl⟩ := hc (leafEquiv T f k) d hd hdk
    refine ⟨(leafEquiv T f).symm l,?_⟩
    simpa only [modulus_relabel,Equiv.apply_symm_apply] using hl

#print axioms exists_closed_relabel
#print axioms residue_relabel
#print axioms valid_relabel
end Erdos7SplittingTreeClosed
