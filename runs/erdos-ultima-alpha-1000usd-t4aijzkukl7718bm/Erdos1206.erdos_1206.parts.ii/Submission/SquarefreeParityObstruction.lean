import FormalConjecturesUtil

/-!
An obstruction to an odd-parity sufficient condition for cube-Sidon coloring.
It does not obstruct ordinary two-coloring or settle the density conjecture.
-/

namespace Erdos1206.SquarefreeParityObstruction

/-- The source used in this obstruction. -/
def source : Set ℕ := {n | Squarefree n ∧ Nat.Coprime n 6}

lemma source_witnesses :
    1115 ∈ source ∧ 15773 ∈ source ∧ 27541 ∈ source ∧
    29167 ∈ source ∧ 33167 ∈ source ∧ 38569 ∈ source := by
  norm_num only [source, Set.mem_setOf_eq, Nat.squarefree_iff_minSqFac, Nat.Coprime]
  decide +kernel

lemma three_differences :
    (27541 : ℕ)^3-1115^3 = 20888646305546 ∧
    (29167 : ℕ)^3-15773^3 = 20888646305546 ∧
    (38569 : ℕ)^3-33167^3 = 20888646305546 := by
  norm_num

private lemma parity_triangle (a b c d e f : ZMod 2)
    (h₁ : a+b+c+d=1) (h₂ : b+d+e+f=1) (h₃ : a+c+e+f=1) : False := by
  have h : 2*(a+b+c+d+e+f)=(3 : ZMod 2) := by
    linear_combination h₁+h₂+h₃
  have htwo : (2 : ZMod 2)=0 := by decide
  rw [htwo, zero_mul] at h
  exact (by decide : (0 : ZMod 2) ≠ 3) h

/-- Even without assuming multiplicativity, no Boolean coloring has odd
parity on every strict cube collision in the squarefree, coprime-to-six source.
The weaker requirement of merely being nonmonochromatic is not excluded. -/
theorem no_odd_parity_coloring :
    ¬ ∃ c : ℕ → ZMod 2, ∀ a b d e : ℕ,
      a ∈ source → b ∈ source → d ∈ source → e ∈ source →
      a < b → b < d → d < e → a^3+e^3=b^3+d^3 →
      c a+c b+c d+c e=1 := by
  rintro ⟨c,hc⟩
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := source_witnesses
  have he₁ := hc 1115 15773 27541 29167 h₁ h₂ h₃ h₄
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he₂ := hc 15773 29167 33167 38569 h₂ h₄ h₅ h₆
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he₃ := hc 1115 27541 33167 38569 h₁ h₃ h₅ h₆
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact parity_triangle _ _ _ _ _ _ he₁ he₂ he₃

#print axioms source_witnesses
#print axioms three_differences
#print axioms no_odd_parity_coloring

end Erdos1206.SquarefreeParityObstruction
