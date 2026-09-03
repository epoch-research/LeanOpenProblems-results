import Submission.DivisorRepair

/-! A finite certificate format for actual splitting-and-enlargement covers.
The odd-cover theorem below is conditional on a valid tree with injective
odd leaf moduli. No such odd witness is asserted. -/
namespace Erdos7SplittingTreeCover
set_option autoImplicit false
set_option maxHeartbeats 2000000

inductive Tree : Type where
  | leaf (d : ℕ) : Tree
  | split (q : ℕ) (children : Fin q → Tree) : Tree

namespace Tree

def Leaf : Tree → Type
  | .leaf _ => Unit
  | .split q children => (r : Fin q) × Leaf (children r)

def leafFintype : (T : Tree) → Fintype T.Leaf
  | .leaf _ => inferInstanceAs (Fintype Unit)
  | .split q children => by
      change Fintype ((r : Fin q) × Leaf (children r))
      letI : ∀ r, Fintype (Leaf (children r)) := fun r => leafFintype (children r)
      infer_instance

instance (T : Tree) : Fintype T.Leaf := leafFintype T

def leafDecidableEq : (T : Tree) → DecidableEq T.Leaf
  | .leaf _ => inferInstanceAs (DecidableEq Unit)
  | .split q children => by
      change DecidableEq ((r : Fin q) × Leaf (children r))
      letI : ∀ r, DecidableEq (Leaf (children r)) := fun r => leafDecidableEq (children r)
      infer_instance

instance (T : Tree) : DecidableEq T.Leaf := leafDecidableEq T

def modulus : (T : Tree) → T.Leaf → ℕ
  | .leaf d, _ => d
  | .split _ children, ⟨r,k⟩ => modulus (children r) k

def residue : (T : Tree) → ℕ → ℤ → T.Leaf → ℤ
  | .leaf _, _, a, _ => a
  | .split q children, m, a, ⟨r,k⟩ =>
      residue (children r) (m*q) (a+(m : ℤ)*r.val) k

/-- Leaves can enlarge their current congruence class only to a nontrivial
positive divisor modulus; every split has a positive number of children. -/
def Valid : Tree → ℕ → Prop
  | .leaf d, m => 1 < d ∧ d ∣ m
  | .split q children, m => 0 < q ∧ ∀ r, Valid (children r) (m*q)

def validDecidable : (T : Tree) → (m : ℕ) → Decidable (T.Valid m)
  | .leaf d, m => inferInstanceAs (Decidable (1 < d ∧ d ∣ m))
  | .split q children, m => by
      change Decidable (0 < q ∧ ∀ r, Valid (children r) (m*q))
      letI : ∀ r, Decidable (Valid (children r) (m*q)) := fun r => validDecidable (children r) (m*q)
      infer_instance

instance (T : Tree) (m : ℕ) : Decidable (T.Valid m) := validDecidable T m

theorem nontrivial (T : Tree) (m : ℕ) (hT : T.Valid m) :
    ∀ k : T.Leaf, 1 < T.modulus k := by
  induction T generalizing m with
  | leaf d => exact fun _ => hT.1
  | split q children ih =>
      rintro ⟨r,k⟩
      exact ih r (m*q) (hT.2 r) k

/-- A valid tree covers every integer in its starting congruence class. -/
theorem covers (T : Tree) (m : ℕ) (a : ℤ) (hT : T.Valid m)
    (x : ℤ) (hx : (m : ℤ) ∣ x-a) :
    ∃ k : T.Leaf, (T.modulus k : ℤ) ∣ x-T.residue m a k := by
  induction T generalizing m a with
  | leaf d =>
      refine ⟨(), ?_⟩
      exact (show (d : ℤ) ∣ m by exact_mod_cast hT.2).trans hx
  | split q children ih =>
      obtain ⟨r,hr⟩ := Erdos7DivisorRepair.split_class m q hT.1 a x hx
      obtain ⟨k,hk⟩ := ih r (m*q) (a+(m : ℤ)*r.val) (hT.2 r) hr
      exact ⟨⟨r,k⟩,hk⟩

/-- A successful odd tree certificate proves precisely the original
existential conjecture, rather than just a finite sampled covering. -/
theorem odd_strict_cover (T : Tree) (hT : T.Valid 1)
    (hinj : Function.Injective T.modulus) (hodd : ∀ k, Odd (T.modulus k)) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  apply Erdos7Reduction.arithmetic_formulation.mpr
  refine ⟨T.Leaf, inferInstance, T.modulus, T.residue 1 0, hinj, ?_, ?_⟩
  · intro k
    exact ⟨T.nontrivial 1 hT k,hodd k⟩
  · intro x
    exact T.covers 1 0 hT x (by simp)

end Tree

/-- An even-period positive control, NOT an odd covering witness. -/
def control : Tree := .split 2 ![
  .leaf 2,
  .split 3 ![.leaf 3, .leaf 6, .split 2 ![.leaf 4, .leaf 12]]]

lemma control_valid : control.Valid 1 := by decide +kernel
lemma control_injective : Function.Injective control.modulus := by decide +kernel
lemma control_covers : ∀ x : ℤ, ∃ k : control.Leaf,
    (control.modulus k : ℤ) ∣ x-control.residue 1 0 k := by
  intro x
  exact control.covers 1 0 control_valid x (by simp)

#print axioms Tree.odd_strict_cover
#print axioms control_valid
#print axioms control_injective
#print axioms control_covers
end Erdos7SplittingTreeCover
