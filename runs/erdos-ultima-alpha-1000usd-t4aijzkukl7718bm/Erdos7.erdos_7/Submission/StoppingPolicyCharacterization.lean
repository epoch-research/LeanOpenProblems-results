import Submission.StoppingPrefixClosure

/-! Exact characterization of the full stopping-prefix closure: its terminal
obstruction is equivalent to nonexistence of a safe predictable policy. -/
namespace Erdos7StoppingPolicyCharacterization
open Erdos7StoppingDigitRestriction Erdos7StoppingPrefixClosure
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma node_eq_iff {E : ℕ} {R : Type*} (x y : Fin E → R) (t : Fin E) :
    node x t = node y t ↔ Agree t.val x y := by
  constructor
  · intro h j hj
    have hh := eq_of_heq (Sigma.mk.inj h).2
    exact congrFun hh ⟨j.val,hj⟩
  · exact node_agree x y t

/-- The prefixes reached before or at the policy's deletion. -/
def Reached {E : ℕ} {R : Type*} (T : (Fin E → R) → Fin E) : Set (Node E R) :=
  {u | ∃ x, node x u.1 = u ∧ u.1.val ≤ (T x).val}

lemma reached_node_iff {E : ℕ} {R : Type*} (T : (Fin E → R) → Fin E)
    (hT : Predictable T) (x : Fin E → R) (t : Fin E) :
    node x t ∈ Reached T ↔ t.val ≤ (T x).val := by
  constructor
  · rintro ⟨y,hnode,hy⟩
    by_contra! ht
    have ha : Agree t.val x y := ((node_eq_iff y x t).mp hnode).symm
    have hty := hT x y (ha.mono ht.le)
    change t.val ≤ (T y).val at hy
    rw [hty] at hy
    omega
  · intro ht
    exact ⟨x,rfl,ht⟩

def Safe {E : ℕ} {R : Type*}
    (Block : Set (Node E R) → Node E R → R → Prop)
    (T : (Fin E → R) → Fin E) (V : (Fin E → R) → R) : Prop :=
  ∀ x, ¬ Block (Reached T) (node x (T x)) (V x)

section Closure
variable {E : ℕ} {R : Type*} [Nonempty R] (hE : 0 < E)
    (Block : Set (Node E R) → Node E R → R → Prop)
    (hmono : ∀ {B C : Set (Node E R)}, B ⊆ C →
      ∀ {u r}, Block B u r → Block C u r)
    (T : (Fin E → R) → Fin E) (V : (Fin E → R) → R)
    (hT : Predictable T) (hSafe : Safe Block T V)

include hT hSafe in
theorem reached_closed : Closed hE Block (Reached T) := by
  classical
  constructor
  · let x : Fin E → R := fun _ => Classical.arbitrary R
    rw [← node_zero hE x]
    exact (reached_node_iff T hT x _).mpr (Nat.zero_le _)
  · intro x t ht hx hr
    have hle := (reached_node_iff T hT x t).mp hx
    have hne : t.val ≠ (T x).val := by
      intro heq
      have heq' : t = T x := Fin.ext heq
      exact hSafe x (by simpa only [heq'] using hr (V x))
    exact (reached_node_iff T hT x _).mpr (by change t.val+1 ≤ (T x).val; omega)

include hT hSafe in
theorem reached_nonterminal : ¬ Terminal hE Block (Reached T) := by
  rintro ⟨x,hx,hr⟩
  have hle := (reached_node_iff T hT x _).mp hx
  change E-1 ≤ (T x).val at hle
  have ht : (⟨E-1,by omega⟩ : Fin E) = T x := by
    apply Fin.ext
    have := (T x).isLt
    change E-1 = (T x).val
    omega
  exact hSafe x (by simpa only [ht] using hr (V x))

include hmono in
/-- This is an equivalence, not just a sufficient pruning rule. -/
theorem safe_policy_iff_nonterminal :
    (∃ T : (Fin E → R) → Fin E, ∃ V : (Fin E → R) → R,
      Predictable T ∧ PredictableValue T V ∧ Safe Block T V) ↔
    ¬ Terminal hE Block (Frozen hE Block) := by
  constructor
  · rintro ⟨T,V,hT,hV,hSafe⟩ ht
    have hc := reached_closed hE Block T V hT hSafe
    exact reached_nonterminal hE Block T V hT hSafe
      (terminal_mono hE Block hmono (frozen_le hE Block hc) ht)
  · intro hn
    obtain ⟨T,V,hT,hV,hreach,hfree⟩ := policy_of_frozen_nonterminal hE Block hmono hn
    have hsub : Reached T ⊆ Frozen hE Block := by
      rintro u ⟨x,hnode,ht⟩
      rw [←hnode]
      exact hreach x u.1 ht
    exact ⟨T,V,hT,hV,fun x hx => hfree x (hmono hsub hx)⟩
end Closure

#print axioms reached_node_iff
#print axioms reached_closed
#print axioms reached_nonterminal
#print axioms safe_policy_iff_nonterminal
end Erdos7StoppingPolicyCharacterization
