import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

/--
Pentanacci $\pi$ function: $a(1)=a(2)=a(3)=a(4)=a(5)=1$;
for $n>5$, $a(n) = \pi(\sum_{j=1}^5 a(n-j))$ where $\pi = A000720$.
Note on indices: for $n \ge 0$, $a(n)$ corresponds to $A_{n+1}$ in the OEIS sequence.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1 -- Corresponds to A(1)
  | 1 => 1 -- Corresponds to A(2)
  | 2 => 1 -- Corresponds to A(3)
  | 3 => 1 -- Corresponds to A(4)
  | 4 => 1 -- Corresponds to A(5)
  | i + 5 => -- i+5 corresponds to OEIS index i+6 > 5
    -- The terms are a(i+4), a(i+3), a(i+2), a(i+1), a(i), which are the previous 5 terms.
    let sum_terms := a (i + 4) + a (i + 3) + a (i + 2) + a (i + 1) + a i
    π sum_terms

/--
A general sequence defined by the Pentanacci $\pi$ recurrence, starting with arbitrary initial values $v: \text{Fin 5} \to \mathbb{N}$.
The sequence $a'(v, n)$ is the n-th term (0-indexed).
-/
noncomputable def a_general (v : Fin 5 → ℕ) (n : ℕ) : ℕ :=
  match n with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | i + 5 =>
    let sum_terms := a_general v (i + 4) + a_general v (i + 3) + a_general v (i + 2) + a_general v (i + 1) + a_general v i
    π sum_terms

/-- `Nat.totient 30030 = 5760`, computed via multiplicativity over the prime factors
`30030 = 2·3·5·7·11·13`. -/
private theorem totient30030 : Nat.totient 30030 = 5760 := by
  have h : Nat.totient 30030 = Nat.totient 2 * Nat.totient 3 * Nat.totient 5 * Nat.totient 7 * Nat.totient 11 * Nat.totient 13 := by
    rw [show (30030:ℕ) = 2*(3*(5*(7*(11*13)))) by norm_num]
    rw [Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
        Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
        Nat.totient_mul (by norm_num)]
    ring
  rw [h, Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num)]

/-- The number of primes below `n` is at most `n`. -/
private theorem pi'_le (n : ℕ) : Nat.primeCounting' n ≤ n := by
  rw [← Nat.primesBelow_card_eq_primeCounting']
  calc (Nat.primesBelow n).card ≤ (Finset.range n).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hx
        simp [hx.1]
    _ = n := Finset.card_range n

/-- A linear upper bound on `π'` obtained from `Nat.primeCounting'_add_le` with sieve
modulus `30030 = 2·3·5·7·11·13` (whose totient density is `5760/30030 < 1/5`). -/
private theorem piBound (N : ℕ) : Nat.primeCounting' N ≤ 35791 + 5760 * (N / 30030) := by
  rcases le_or_gt N 30030 with h | h
  · calc Nat.primeCounting' N ≤ N := pi'_le N
      _ ≤ 35791 + 5760 * (N / 30030) := by omega
  · have hN : 30031 + (N - 30031) = N := by omega
    have key := Nat.primeCounting'_add_le (a := 30030) (k := 30031)
      (by norm_num) (by norm_num) (N - 30031)
    rw [hN, totient30030] at key
    have hdiv : (N - 30031) / 30030 ≤ N / 30030 := Nat.div_le_div_right (by omega)
    have h2 := pi'_le 30031
    omega

/-- For `M ≥ 1000000`, the prime-counting function satisfies `π(5M) ≤ M`. -/
private theorem pi5_le_M (M : ℕ) (hM : 1000000 ≤ M) : π (5 * M) ≤ M := by
  have hpc : π (5 * M) = Nat.primeCounting' (5 * M + 1) := rfl
  rw [hpc]
  have hb := piBound (5 * M + 1)
  have hq := Nat.div_mul_le_self (5 * M + 1) 30030
  omega

/-- The universal bound constant `C0 = π(5·10⁶)`. -/
private noncomputable def C0 : ℕ := π (5 * 1000000)

/-- For every `M`, `π(5M) ≤ max M C0`. -/
private theorem pi5_le_max (M : ℕ) : π (5 * M) ≤ max M C0 := by
  rcases le_or_gt 1000000 M with h | h
  · exact le_trans (pi5_le_M M h) (le_max_left _ _)
  · have : π (5 * M) ≤ C0 := Nat.monotone_primeCounting (by omega)
    exact le_trans this (le_max_right _ _)

/-- The sequence is bounded: every term is at most `B = max(max of initial values, C0)`. -/
private theorem bounded (v : Fin 5 → ℕ) :
    ∀ n, a_general v n ≤ max (max (max (max (max (v 0) (v 1)) (v 2)) (v 3)) (v 4)) C0 := by
  set B := max (max (max (max (max (v 0) (v 1)) (v 2)) (v 3)) (v 4)) C0 with hB
  have hC0 : C0 ≤ B := le_max_right _ _
  have hv0 : v 0 ≤ B := by rw [hB]; omega
  have hv1 : v 1 ≤ B := by rw [hB]; omega
  have hv2 : v 2 ≤ B := by rw [hB]; omega
  have hv3 : v 3 ≤ B := by rw [hB]; omega
  have hv4 : v 4 ≤ B := by rw [hB]; omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    match n with
    | 0 => rw [a_general]; exact hv0
    | 1 => rw [a_general]; exact hv1
    | 2 => rw [a_general]; exact hv2
    | 3 => rw [a_general]; exact hv3
    | 4 => rw [a_general]; exact hv4
    | i + 5 =>
      rw [a_general]
      have e4 := IH (i+4) (by omega)
      have e3 := IH (i+3) (by omega)
      have e2 := IH (i+2) (by omega)
      have e1 := IH (i+1) (by omega)
      have e0 := IH i (by omega)
      have hsum : a_general v (i+4) + a_general v (i+3) + a_general v (i+2) + a_general v (i+1) + a_general v i ≤ 5 * B := by omega
      calc π (a_general v (i+4) + a_general v (i+3) + a_general v (i+2) + a_general v (i+1) + a_general v i)
            ≤ π (5 * B) := Nat.monotone_primeCounting hsum
        _ ≤ max B C0 := pi5_le_max B
        _ = B := by omega

/-- Determinism of the recurrence: equality of the five-term windows starting at `m` and `n`
propagates to all later terms. -/
private theorem determ (v : Fin 5 → ℕ) (m n : ℕ)
    (h : ∀ j, j < 5 → a_general v (m + j) = a_general v (n + j)) :
    ∀ k, a_general v (m + k) = a_general v (n + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    match k with
    | 0 => exact h 0 (by omega)
    | 1 => exact h 1 (by omega)
    | 2 => exact h 2 (by omega)
    | 3 => exact h 3 (by omega)
    | 4 => exact h 4 (by omega)
    | i + 5 =>
      have e4 : a_general v (m+i+4) = a_general v (n+i+4) := IH (i+4) (by omega)
      have e3 : a_general v (m+i+3) = a_general v (n+i+3) := IH (i+3) (by omega)
      have e2 : a_general v (m+i+2) = a_general v (n+i+2) := IH (i+2) (by omega)
      have e1 : a_general v (m+i+1) = a_general v (n+i+1) := IH (i+1) (by omega)
      have e0 : a_general v (m+i) = a_general v (n+i) := IH i (by omega)
      have hm : m + (i+5) = (m+i)+5 := by ring
      have hn : n + (i+5) = (n+i)+5 := by ring
      rw [hm, hn, a_general, a_general, e4, e3, e2, e1, e0]

/-- oeis_100478_conjecture_0: Starting with other values of a(1), a(2), a(3), a(4), a(5) what behaviors are possible? Does the sequence always stick at a single integer after some point, or can it go into a loop, or is there a third pattern? -/
theorem oeis_a100478_conjecture_0 :
  -- For any set of five positive starting values v
  ∀ (v : Fin 5 → ℕ), (∀ i, v i > 0) →
  -- The sequence is ultimately periodic.
  ∃ N P : ℕ, P > 0 ∧ (∀ n, n ≥ N → a_general v (n + P) = a_general v n) := by
  intro v _hv
  set B := max (max (max (max (max (v 0) (v 1)) (v 2)) (v 3)) (v 4)) C0 with hB
  have hbd : ∀ n, a_general v n ≤ B := bounded v
  -- the state map into a finite type
  let T : ℕ → (Fin 5 → Fin (B+1)) := fun n i => ⟨a_general v (n + i), by have := hbd (n + i); omega⟩
  obtain ⟨n1, n2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite T
  have key : ∀ a b : ℕ, T a = T b → ∀ j, j < 5 → a_general v (a + j) = a_general v (b + j) := by
    intro a b hab j hj
    have := congrFun hab (⟨j, hj⟩ : Fin 5)
    simpa [T] using congrArg Fin.val this
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨n1, n2 - n1, by omega, ?_⟩
    intro n hn
    have hd := determ v n1 n2 (key n1 n2 heq) (n - n1)
    have h1 : n1 + (n - n1) = n := by omega
    have h2 : n2 + (n - n1) = n + (n2 - n1) := by omega
    rw [h1, h2] at hd
    exact hd.symm
  · refine ⟨n2, n1 - n2, by omega, ?_⟩
    intro n hn
    have hd := determ v n2 n1 (key n2 n1 heq.symm) (n - n2)
    have h1 : n2 + (n - n2) = n := by omega
    have h2 : n1 + (n - n2) = n + (n1 - n2) := by omega
    rw [h1, h2] at hd
    exact hd.symm
