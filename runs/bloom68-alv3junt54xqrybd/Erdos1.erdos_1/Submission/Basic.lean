import FormalConjecturesUtil

/-! Shared interfaces for the distinct-subset-sum counterexample construction. -/

namespace ErdosDSS

open scoped BigOperators

/-- Integral coefficients in the three-element alphabet. -/
def Ternary {ι : Type*} (e : ι → ℤ) : Prop :=
  ∀ i, -1 ≤ e i ∧ e i ≤ 1

/-- A signed sum of an indexed row of natural numbers. -/
def signedSum {ι : Type*} [Fintype ι] (a : ι → ℕ) (e : ι → ℤ) : ℤ :=
  ∑ i, e i * (a i : ℤ)

/-- A signed sum of an integral row. -/
def intSum {ι : Type*} [Fintype ι] (a e : ι → ℤ) : ℤ :=
  ∑ i, e i * a i

/-- The ordinary coefficient sum. -/
def charge {ι : Type*} [Fintype ι] (e : ι → ℤ) : ℤ := ∑ i, e i

/-- A finite cyclic code with only zero or opposite prescribed charges in
its ternary kernel.  The period is also coprime to an external odd modulus. -/
structure CyclicCode (q P : ℕ) where
  m : ℕ
  B : ℕ
  b : Fin m → ℕ
  q_pos : 0 < q
  B_pos : 0 < B
  B_odd : Odd B
  small : ∀ i, 0 < b i ∧ b i < B
  kernel : ∀ e : Fin m → ℤ, Ternary e →
    (B : ℤ) ∣ signedSum b e →
    e = 0 ∨ charge e = (q : ℤ) ∨ charge e = -(q : ℤ)
  efficiency : 48 * B ≤ 35 * 2 ^ m
  residue : Nat.ModEq P B 1

/-- A positive indexed row with controlled nonzero returns modulo its
period.  Zero returns are rigid, and its period/cardinality ratio is at
most three quarters. -/
structure ReturnBlock (q P : ℕ) where
  n : ℕ
  p : ℕ
  a : Fin n → ℕ
  q_pos : 0 < q
  p_pos : 0 < p
  p_odd : Odd p
  small : ∀ i, 0 < a i ∧ a i < p
  returns : ∀ e : Fin n → ℤ, Ternary e → ∀ k : ℤ,
    signedSum a e = k * (p : ℤ) →
    (e = 0 ∧ k = 0) ∨ k = (q : ℤ) ∨ k = -(q : ℤ)
  efficiency : 4 * p ≤ 3 * 2 ^ n
  residue : Nat.ModEq P p 1

/-- The interface supplied by the cyclic-code construction. -/
def CodeSupply : Prop :=
  ∀ P : ℕ, 0 < P → Odd P → ∀ K : ℕ,
    ∃ q : ℕ, K < q ∧ Nonempty (CyclicCode q P)

/-- The interface supplied by the periodic lift. -/
def BlockSupply : Prop :=
  ∀ P : ℕ, 0 < P → Odd P → ∀ K : ℕ,
    ∃ q : ℕ, K < q ∧ Nonempty (ReturnBlock q P)

end ErdosDSS
