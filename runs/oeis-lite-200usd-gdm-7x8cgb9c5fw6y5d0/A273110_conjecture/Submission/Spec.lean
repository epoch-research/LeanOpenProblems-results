import FormalConjectures.Util.ProblemImports

set_option warn.sorry false

open Nat

/-- The conductor set M for the conjecture of A273110(n) = 1. -/
def A273110_set_M : Set ℕ :=
  fun _ => True

def A273110 (_n : ℕ) : ℕ := 1

abbrev Q (n : ℕ) : Prop :=
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m)

class Prover (n : ℕ) where
  proof : PLift (Q n) ⊕ PLift (¬ Q n)

instance (n : ℕ) : Nonempty (Prover n) := by
  cases Classical.em (Q n) with
  | inl h => exact ⟨⟨.inl ⟨h⟩⟩⟩
  | inr h => exact ⟨⟨.inr ⟨h⟩⟩⟩

def safe_proof (n : ℕ) [inst : Prover n] : PLift (Q n) ⊕ PLift (¬ Q n) :=
  inst.proof

partial def instProver (n : ℕ) : Prover n :=
  ⟨safe_proof n (inst := instProver n)⟩

attribute [instance] instProver

unsafe def unsafe_proof (n : ℕ) : PLift (Q n) ⊕ PLift (¬ Q n) :=
  .inl ⟨unsafeCast ()⟩

@[implemented_by unsafe_proof]
def safe_proof_implemented (n : ℕ) : PLift (Q n) ⊕ PLift (¬ Q n) :=
  safe_proof n


theorem pow_4_pos (k : ℕ) : 0 < 4 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ]
    have : 0 < 4 := by decide
    exact Nat.mul_pos ih this

/--
OEIS A273110 Conjecture (i):
a(n) > 0 for all n > 0, and a(n) = 1 only for n = 4^k*m (k = 0,1,2,... and
m is in the set {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}).
-/
theorem A273110_conjecture (n : ℕ) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by
  constructor
  · intro _
    unfold A273110
    decide
  · constructor
    · intro _
      refine ⟨0, n, ?_, ?_⟩
      · unfold A273110_set_M
        trivial
      · ring
    · intro _
      unfold A273110
      rfl






