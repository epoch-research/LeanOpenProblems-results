import FormalConjecturesUtil

/-!
The alternating-edge labels used for the second directed arc theorem do
not have its no-three property at the third arc stage. A finite K4-free
source (the diamond) and target K3 suffice. This is not a disproof of
Erdős 595, but rules out this precise attempted extension.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open SimpleGraph Set
namespace Erdos595ThirdArcFailure

private def table : Fin 256 → Fin 3 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 2, 0, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 2, 0, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 2, 1, 2, 0, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def label (a b c d : Fin 4) : Fin 3 :=
  table ⟨a.val * 64 + b.val * 16 + c.val * 4 + d.val, by omega⟩

theorem label_step : ∀ a b c d e : Fin 4,
    a ≠ b → b ≠ c → c ≠ d → d ≠ e →
      label a b c d ≠ label b c d e := by decide +kernel

theorem label_alternating : ∀ a b : Fin 4, a < b →
    label a b a b = 0 ∧ label b a b a = 1 := by decide +kernel

def diamond : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b ∧ ¬(a = 0 ∧ b = 3) ∧ ¬(a = 3 ∧ b = 0)
  symm := by intro a b h; exact ⟨h.1.symm, by tauto, by tauto⟩
  loopless := by intro a h; exact h.1 rfl

instance : DecidableRel diamond.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem diamond_cliqueFree : diamond.CliqueFree 4 := by
  unfold SimpleGraph.CliqueFree
  simp only [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]
  decide +kernel

def tag (a b : Fin 4) : Fin 3 × Fin 3 :=
  (label a b a b, label b a b a)

/-- Three consecutive edges in a K4-free source have identical alternating
labels, although overlap is mapped properly into the K4-free target K3. -/
theorem same_tag_three :
    diamond.Adj 0 1 ∧ diamond.Adj 1 2 ∧ diamond.Adj 2 3 ∧
    tag 0 1 = tag 1 2 ∧ tag 1 2 = tag 2 3 := by decide +kernel

theorem target_cliqueFree : (⊤ : SimpleGraph (Fin 3)).CliqueFree 4 := by
  unfold SimpleGraph.CliqueFree
  simp only [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff]
  decide +kernel

#print axioms label_step
#print axioms label_alternating
#print axioms diamond_cliqueFree
#print axioms same_tag_three
end Erdos595ThirdArcFailure
