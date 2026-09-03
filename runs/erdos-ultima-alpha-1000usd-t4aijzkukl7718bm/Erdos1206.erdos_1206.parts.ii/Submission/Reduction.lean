import FormalConjecturesUtil

/-! Verified auxiliary results. These do not settle `erdos_1206.parts.ii`. -/

namespace Erdos1206

lemma infinite_of_lowerDensity_pos {A : Set ℕ} (hA : 0 < A.lowerDensity) : A.Infinite := by
  by_contra h
  have hfinite : A.Finite := Set.not_infinite.mp h
  have hzero := Nat.hasDensity_zero_of_finite hfinite
  have hlim : A.lowerDensity = 0 := hzero.liminf_eq
  simpa [hlim] using hA

lemma existence_reduction :
    (∃ A : Set ℕ, A.Infinite ∧ 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A)) ↔
    (∃ A : Set ℕ, 0 < A.lowerDensity ∧
      IsSidon ((fun a : ℕ => a ^ 3) '' A)) := by
  constructor
  · rintro ⟨A, _, hd, hs⟩
    exact ⟨A, hd, hs⟩
  · rintro ⟨A, hd, hs⟩
    exact ⟨A, infinite_of_lowerDensity_pos hd, hd, hs⟩

end Erdos1206
