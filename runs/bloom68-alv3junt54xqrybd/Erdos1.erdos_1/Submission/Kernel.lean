import Submission.Basic

/-! Interfaces for the integral cyclic code and its adjustable period. -/

namespace ErdosDSS

/-- The local integral ternary-kernel property, before the final efficiency
and external coprimality choices. -/
structure CyclicKernel (q m B : ℕ) where
  b : Fin m → ℕ
  q_pos : 0 < q
  B_pos : 0 < B
  B_odd : Odd B
  small : ∀ i, 0 < b i ∧ b i < B
  kernel : ∀ e : Fin m → ℤ, Ternary e →
    (B : ℤ) ∣ signedSum b e →
    e = 0 ∨ charge e = (q : ℤ) ∨ charge e = -(q : ℤ)

/-- Changing one timeout-root coefficient supplies an arithmetic progression
of odd cyclic periods, without changing the ternary-kernel restriction. -/
structure AdjustableKernel (q : ℕ) where
  m : ℕ
  h : ℕ
  B : ℕ
  h_le_m : h ≤ m
  height : q ≤ h
  data : ∀ u : ℕ, CyclicKernel q m (B + u * 2 ^ (m - h))
  efficiency : 24 * B ≤ 17 * 2 ^ m

/-- The sole combinatorial existence theorem needed from the stopped-tree
construction.  This definition does not assert the theorem. -/
def TreeSupply : Prop :=
  ∀ q : ℕ, Even q → 2 ≤ q → Nonempty (AdjustableKernel q)

end ErdosDSS
