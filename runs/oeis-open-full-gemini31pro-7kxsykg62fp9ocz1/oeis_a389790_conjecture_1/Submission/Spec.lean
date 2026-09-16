import FormalConjectures.Util.ProblemImports
open Classical
open Nat

/-- The smallest prime strictly greater than $r$. Defined non-computably using the set infimum. -/
noncomputable def next_prime (r : ℕ) : ℕ :=
  -- Nat.sInf finds the minimum element in a set of natural numbers.
  -- The set of primes greater than r is non-empty by Euclid's theorem.
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

/-- $r + r'$, where $r'$ is the next prime after $r$. -/
noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

/--
A389790: Number of ways to write $2n$ as $p + p' + q + q'$, where $p$ and $q$ are primes with $p \le q$, and $r'$ is the first prime greater than $r$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  -- The finset range is taken from the original user code.
  let R := Finset.range n

  Finset.card $ Finset.filter (fun ⟨p, q⟩ =>
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

/-- OEIS A389790 Conjecture: a(n) > 0 for all n >= 474.
This is an analog of Goldbach's conjecture. It has been verified for n <= 2*10^5. -/
theorem oeis_a389790_conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := sorry

lemma sInf_eval {r p : ℕ} (hp : Nat.Prime p) (hr : r < p) (h_none : ∀ q, r < q → q < p → ¬Nat.Prime q) : next_prime r = p := by
  have h_mem : p ∈ {k : ℕ | Nat.Prime k ∧ r < k} := ⟨hp, hr⟩
  have h_nonempty : {k : ℕ | Nat.Prime k ∧ r < k}.Nonempty := ⟨p, h_mem⟩
  have h_sInf_mem : next_prime r ∈ {k : ℕ | Nat.Prime k ∧ r < k} := Nat.sInf_mem h_nonempty
  have h_le : next_prime r ≤ p := Nat.sInf_le h_mem
  have h_not_lt : ¬(next_prime r < p) := by
    intro hlt
    exact h_none (next_prime r) h_sInf_mem.2 hlt h_sInf_mem.1
  omega

lemma S_sum_eval {r p : ℕ} (hp : Nat.Prime p) (hr : r < p) (h_none : ∀ q, r < q → q < p → ¬Nat.Prime q) : S_sum r = r + p := by
  unfold S_sum
  rw [sInf_eval hp hr h_none]

theorem pos_filter (n p q : ℕ) (hp_lt : p < n) (hq_lt : q < n) (hp_prime : Nat.Prime p) (hq_prime : Nat.Prime q) (hpq : p ≤ q) (hsum : S_sum p + S_sum q = 2 * n) : 0 < a n := by
  have H : (p, q) ∈ Finset.filter (fun x : ℕ × ℕ => Nat.Prime x.1 ∧ Nat.Prime x.2 ∧ x.1 ≤ x.2 ∧ S_sum x.1 + S_sum x.2 = 2 * n) (Finset.range n ×ˢ Finset.range n) := by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨hp_lt, hq_lt⟩, hp_prime, hq_prime, hpq, hsum⟩
  unfold a
  dsimp
  exact Finset.card_pos.mpr ⟨(p, q), H⟩

theorem oeis_a389790_conjecture_1.disproof : ¬ (type_of% @oeis_a389790_conjecture_1) := by
  sorry
