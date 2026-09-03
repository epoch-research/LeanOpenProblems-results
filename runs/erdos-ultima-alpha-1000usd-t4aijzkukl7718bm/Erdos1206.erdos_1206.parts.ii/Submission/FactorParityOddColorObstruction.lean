import FormalConjecturesUtil

/-!
An obstruction to an odd-parity refinement after separating the squarefree
integers by factor-count parity. It does not obstruct ordinary proper coloring
and does not settle the positive-density cube-Sidon conjecture.
-/
namespace Erdos1206.FactorParityOddColorObstruction

/-- On squarefree numbers, distinct and multiplicity factor counts agree. -/
def source (r : ℕ) : Set ℕ :=
  {n | Squarefree n ∧ n.primeFactors.card % 2 = r}

private lemma witnesses :
    4062 ∈ source 1 ∧ 9058 ∈ source 1 ∧ 12002 ∈ source 1 ∧
    13398 ∈ source 1 ∧ 31171 ∈ source 1 ∧ 31731 ∈ source 1 ∧
    20310 ∈ source 0 ∧ 45290 ∈ source 0 ∧ 60010 ∈ source 0 ∧
    66990 ∈ source 0 ∧ 155855 ∈ source 0 ∧ 158655 ∈ source 0 := by
  norm_num only [source, Set.mem_setOf_eq, Nat.squarefree_iff_minSqFac]
  decide +kernel

private lemma parity_triangle (a b c d e f : ZMod 2)
    (h₁ : a+b+c+d=1) (h₂ : a+c+e+f=1) (h₃ : b+d+e+f=1) : False := by
  have h : 2*(a+b+c+d+e+f)=(3 : ZMod 2) := by
    linear_combination h₁+h₂+h₃
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_mul] at h
  exact (by decide : (0 : ZMod 2) ≠ 3) h

/-- Neither factor-count parity class admits a Boolean coloring with odd
color sum on every strict cube collision. Nonmonochromatic coloring is a
weaker condition and is not excluded by this theorem. -/
theorem no_odd_parity_refinement (r : ℕ) (hr : r < 2) :
    ¬ ∃ c : ℕ → ZMod 2, ∀ a b d e : ℕ,
      a ∈ source r → b ∈ source r → d ∈ source r → e ∈ source r →
      a < b → b < d → d < e → a^3+e^3=b^3+d^3 →
      c a+c b+c d+c e=1 := by
  rintro ⟨c,hc⟩
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,k₁,k₂,k₃,k₄,k₅,k₆⟩ := witnesses
  interval_cases r
  · have he₁ := hc 20310 45290 60010 66990 k₁ k₂ k₃ k₄
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he₂ := hc 20310 60010 155855 158655 k₁ k₃ k₅ k₆
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he₃ := hc 45290 66990 155855 158655 k₂ k₄ k₅ k₆
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact parity_triangle _ _ _ _ _ _ he₁ he₂ he₃
  · have he₁ := hc 4062 9058 12002 13398 h₁ h₂ h₃ h₄
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he₂ := hc 4062 12002 31171 31731 h₁ h₃ h₅ h₆
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have he₃ := hc 9058 13398 31171 31731 h₂ h₄ h₅ h₆
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact parity_triangle _ _ _ _ _ _ he₁ he₂ he₃

#print axioms no_odd_parity_refinement
end Erdos1206.FactorParityOddColorObstruction
