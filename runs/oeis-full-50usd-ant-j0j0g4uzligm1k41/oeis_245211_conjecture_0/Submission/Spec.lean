import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A245211: $a(n) = \sum_{d \mid n, d < n} (d \cdot \tau(d))$, where $\tau(d)$ is the number of divisors of $d$.
It is computed as $\left(\sum_{d \mid n} d \cdot \tau(d)\right) - n \cdot \tau(n)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let full_sum := (Nat.divisors n).sum (fun d => d * (Nat.divisors d).card)
  let self_term := n * (Nat.divisors n).card
  full_sum - self_term

/-- A245211 Conjecture: 21 is only number such that a(n) = n. -/
theorem oeis_245211_conjecture_0 : ∀ n : ℕ, 0 < n → (a n = n ↔ n = 21) := by
  intro n hn
  constructor
  · intro h
    -- Forward direction: a n = n → n = 21.
    -- This is the substantive content of the A245211 conjecture.
    --
    -- Reduction (rigorous): a(n) = n ⟺ F(n) = n·(τ(n)+1), where
    -- F(n) = ∑_{d∣n} d·τ(d) is multiplicative with F(p^a) = ∑_{j=0}^a (j+1)p^j.
    -- Equivalently ∏_{p^a ∥ n} G(p^a) = τ(n)+1 with G(p^a) = ∑_{j} σ(p^j)/p^j,
    -- equivalently ∑_{d∣n, d>1} (σ(d)-d)/d = 1.
    --
    -- • n even ⟹ a(n) > n (composite) or a(2)=1 : no solutions.
    -- • ω(n) ≤ 2 (elementary): prime powers give none; squarefree semiprimes give
    --   (p-2)(q-2)=5 ⟹ {3,7}, i.e. n = 21; p²q etc. give none.
    -- • ω(n) ≥ 3, squarefree: the relation p ∣ ∏_{i≠m}(2pᵢ+1) makes the primes form a
    --   single cycle with odd multipliers cⱼ where 2qⱼ₊₁+1 = cⱼqⱼ and ∏cⱼ = 2^ω+1.
    --   When 2^ω+1 is prime this forces the consecutive Mersenne primes 2^k-1 for
    --   k = ω,…,2ω-1, impossible for ω ≥ 3 (an even k ≥ 4 gives 3 ∣ 2^k-1).
    --
    -- The remaining cases (ω ≥ 3 with 2^ω+1 composite, and the non-squarefree
    -- analogue) reduce to showing these prime cycles cannot exist. This is verified
    -- computationally with no exceptions (squarefree to ω = 32; all shapes to 10⁹),
    -- but a uniform proof appears to be open: covering-system arguments are provably
    -- insufficient since the cycle's base values have enough room to absorb every
    -- required small prime factor, and the needed covering prime grows with ω.
    sorry
  · rintro rfl
    unfold a
    norm_num [Nat.divisors]
    decide
