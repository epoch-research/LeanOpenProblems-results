import FormalConjectures.Util.ProblemImports


set_option linter.unusedVariables false

open Nat

/--
A365179: $a(1) = 2$; for $n \ge 2$, $a(n) = p^6$ if $p \equiv 2 \pmod 3$, $a(n) = p^7$ if $p = 3$ or $p \equiv 1 \pmod 3$, where $p = \text{prime}(n)$.
-/
noncomputable def A365179 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 =>
    let p : ℕ := Nat.nth Nat.Prime (k.succ)
    if p % 3 = 2 then
      p ^ 6
    else
      p ^ 7

/-- The $n$-th prime number, where $\text{prime}(1)=2$. -/
noncomputable def prime_of_index (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- The property that a natural number $m$ is the order of the automorphism group
of a finite, non-trivial group, and $m$ is a positive power of $p$. -/
def is_possible_aut_order_power (p m : ℕ) : Prop :=
  (∃ (k : ℕ) (hk : 0 < k), m = p ^ k) ∧
  (∃ (G : Type) (inst_group : Group G) (inst_fintype : Fintype G) (inst_aut_fintype : Fintype (MulAut G)),
    1 < Fintype.card G ∧ Fintype.card (MulAut G) = m)

/--
Conjecture 1: a(n) is the smallest nontrivial power of p such that there exists a finite nontrivial group whose automorphism group is of order a(n).
-/
theorem A365179_conjecture_1 (n : ℕ) (hn : 2 ≤ n) :
  let p := prime_of_index n;
  is_possible_aut_order_power p (A365179 n) ∧
  ∀ m' : ℕ, (is_possible_aut_order_power p m') → (A365179 n) ≤ m' := by
  dsimp only
  constructor
  · constructor
    · -- Prove ∃ k, 0 < k ∧ A365179 n = p^k
      rcases n with _ | _ | k
      · contradiction
      · contradiction
      · dsimp [prime_of_index, A365179]
        by_cases h : Nat.nth Nat.Prime (k + 1) % 3 = 2
        · rw [if_pos h]
          refine ⟨6, by decide, rfl⟩
        · rw [if_neg h]
          refine ⟨7, by decide, rfl⟩
    · -- Prove ∃ G ..., ...
      sorry
  · sorry



