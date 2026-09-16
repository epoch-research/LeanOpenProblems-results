import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma M_eq (p : ℕ) (hp5 : 5 ≤ p) :
  let n := p * p - 2 * p
  let c := (p - 1) * (p - 3) / 2
  let M := c * p + 1
  2 * M = (p - 2) * (n - 1) := by
  intro n c M
  have heven : Even ((p - 1) * (p - 3)) := by
    obtain ⟨k, hk⟩ : ∃ k, p - 1 = 2 * k := ⟨(p - 1) / 2, by omega⟩
    rw [hk]
    exact even_two_mul _
  have hc : 2 * c = (p - 1) * (p - 3) := by
    dsimp [c]
    omega
  have H : 2 * M = (p - 2) * (n - 1) := by
    zify [show 2 * p ≤ p * p by nlinarith, show 1 ≤ p * p - 2 * p by nlinarith, show 3 ≤ p by omega, show 1 ≤ p by omega, show 2 ≤ p by omega]
    push_cast
    dsimp [M, n]
    have hz : (2 : ℤ) * (c : ℤ) = (p - 1) * (p - 3) := by
      exact_mod_cast hc
    linarith [hz]
  exact H
