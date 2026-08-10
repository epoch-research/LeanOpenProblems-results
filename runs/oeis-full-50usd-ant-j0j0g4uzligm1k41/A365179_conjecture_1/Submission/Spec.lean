import FormalConjectures.Util.ProblemImports

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
  ∀ m' : ℕ, (is_possible_aut_order_power p m') → (A365179 n) ≤ m' :=
  by
  -- Structural normalisation: fix the explicit prime `p = prime_of_index n` and the
  -- explicit value `A365179 n`, which for `n ≥ 2` equals `p ^ 6` or `p ^ 7`.
  intro p
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  -- `prime_of_index (k+2) = Nat.nth Nat.Prime (k+1)` agrees with the prime used inside
  -- `A365179 (k+2)`, so the first conjunct's "is a positive power of `p`" part holds.
  have hp : p = Nat.nth Nat.Prime (k + 1) := by
    simp [p, prime_of_index]
  have hval : A365179 (k + 2)
      = (if Nat.nth Nat.Prime (k + 1) % 3 = 2 then
            Nat.nth Nat.Prime (k + 1) ^ 6
          else Nat.nth Nat.Prime (k + 1) ^ 7) := by
    rfl
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- The value `A365179 (k+2)` is a positive power of `p` (exponent `6` or `7`):
    rw [hval, hp]
    by_cases h : Nat.nth Nat.Prime (k + 1) % 3 = 2
    · exact ⟨6, by norm_num, by rw [if_pos h]⟩
    · exact ⟨7, by norm_num, by rw [if_neg h]⟩
  · -- EXISTENCE: a finite nontrivial group `G` with `|Aut G| = A365179 (k+2)`.
    -- This is the realizability half of OEIS A365179: for every prime `p` there is a finite
    -- group whose automorphism group has order `p ^ 6` (if `p ≡ 2 mod 3`) or `p ^ 7`
    -- (otherwise).  Such groups are specific `p`-groups of order `≥ p ^ 5`; computing their
    -- automorphism counts is not supported by current Mathlib.
    sorry
  · -- MINIMALITY: any realizable power of `p` is `≥ A365179 (k+2)`.
    -- This is the lower-bound half of OEIS A365179 (the `p mod 3` dichotomy): no finite
    -- group has automorphism group of strictly smaller `p`-power order.  This is an
    -- open/research-level group-theoretic classification, not available in Mathlib.
    sorry
