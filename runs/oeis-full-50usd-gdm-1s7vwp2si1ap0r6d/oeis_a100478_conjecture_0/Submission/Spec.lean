import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 5000

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

theorem pi_5X_le_X (X : ℕ) (hX : X ≥ 175000) : π (5 * X) ≤ X := by
  have hX_ge : 5 * X + 1 ≥ 30031 := by omega
  let n := 5 * X - 30030
  have hn_eq : 5 * X + 1 = 30031 + n := by omega
  have h_le : π' (30031 + n) ≤ π' 30031 + Nat.totient 30030 * (n / 30030 + 1) := by
    apply Nat.primeCounting'_add_le
    · decide
    · decide
  have ht_30030 : Nat.totient 30030 = 5760 := by
    have hc1 : Nat.Coprime 10 3003 := by decide
    have h1 : Nat.totient 30030 = Nat.totient 10 * Nat.totient 3003 := by
      have : 30030 = 10 * 3003 := by rfl
      rw [this]
      exact Nat.totient_mul hc1
    have hc2 : Nat.Coprime 21 143 := by decide
    have h2 : Nat.totient 3003 = Nat.totient 21 * Nat.totient 143 := by
      have : 3003 = 21 * 143 := by rfl
      rw [this]
      exact Nat.totient_mul hc2
    have ht10 : Nat.totient 10 = 4 := by decide
    have ht21 : Nat.totient 21 = 12 := by decide
    have ht143 : Nat.totient 143 = 120 := by decide
    rw [h1, h2, ht10, ht21, ht143]
  have ht_30031 : Nat.primeCounting' 30031 ≤ 7075 := by
    have h1 : Nat.primeCounting' (211 + 29820) ≤ Nat.primeCounting' 211 + Nat.totient 210 * (29820 / 210 + 1) := by
      apply Nat.primeCounting'_add_le
      · decide
      · decide
    have ht : Nat.totient 210 = 48 := by decide
    have hc : Nat.primeCounting' 211 ≤ 211 := by apply Nat.count_le
    have heq : 211 + 29820 = 30031 := by rfl
    rw [heq] at h1
    rw [ht] at h1
    omega
  have h_div : (5 * X - 30030) / 30030 + 1 = (5 * X) / 30030 := by omega
  have h_π : π (5 * X) = π' (30031 + n) := by
    rw [Nat.primeCounting, hn_eq]
  rw [h_π]
  have h_n_div : n / 30030 + 1 = (5 * X) / 30030 := h_div
  rw [ht_30030, h_n_div] at h_le
  have h_le_2 : π' (30031 + n) ≤ 7075 + 5760 * ((5 * X) / 30030) := by omega
  omega

def B (v : Fin 5 → ℕ) : ℕ := 175000 + v 0 + v 1 + v 2 + v 3 + v 4

theorem a_general_le (v : Fin 5 → ℕ) (n : ℕ) : a_general v n ≤ B v := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | _ | _ | _ | i
    · have : a_general v 0 = v 0 := rfl
      rw [this]
      unfold B
      omega
    · have : a_general v 1 = v 1 := rfl
      rw [this]
      unfold B
      omega
    · have : a_general v 2 = v 2 := rfl
      rw [this]
      unfold B
      omega
    · have : a_general v 3 = v 3 := rfl
      rw [this]
      unfold B
      omega
    · have : a_general v 4 = v 4 := rfl
      rw [this]
      unfold B
      omega
    · have h_eq : a_general v (i + 5) = π (a_general v (i + 4) + a_general v (i + 3) + a_general v (i + 2) + a_general v (i + 1) + a_general v i) := rfl
      rw [h_eq]
      have ih0 : a_general v i ≤ B v := by
        apply ih i
        omega
      have ih1 : a_general v (i + 1) ≤ B v := by
        apply ih (i + 1)
        omega
      have ih2 : a_general v (i + 2) ≤ B v := by
        apply ih (i + 2)
        omega
      have ih3 : a_general v (i + 3) ≤ B v := by
        apply ih (i + 3)
        omega
      have ih4 : a_general v (i + 4) ≤ B v := by
        apply ih (i + 4)
        omega
      have h_sum : a_general v (i + 4) + a_general v (i + 3) + a_general v (i + 2) + a_general v (i + 1) + a_general v i ≤ 5 * B v := by
        omega
      have h_π_le : π (a_general v (i + 4) + a_general v (i + 3) + a_general v (i + 2) + a_general v (i + 1) + a_general v i) ≤ π (5 * B v) := by
        exact Nat.monotone_primeCounting h_sum
      have h_B_le : π (5 * B v) ≤ B v := by
        apply pi_5X_le_X
        unfold B
        omega
      omega

theorem duplicate_test {S : Type*} [Fintype S] (f : ℕ → S) : ∃ a b, a < b ∧ f a = f b := by
  have h_not : ¬ Function.Injective f := not_injective_infinite_finite f
  by_contra! hc
  apply h_not
  intro x y h_eq
  rcases lt_trichotomy x y with h | h | h
  · have := hc x y h
    contradiction
  · exact h
  · have := hc y x h
    have : f y = f x := h_eq.symm
    contradiction

abbrev State (v : Fin 5 → ℕ) := Fin 5 → Fin (B v + 1)

noncomputable def S_seq (v : Fin 5 → ℕ) (n : ℕ) : State v :=
  fun j => ⟨a_general v (n + j.val), by
    have := a_general_le v (n + j.val)
    omega⟩

theorem a_general_periodic (v : Fin 5 → ℕ) (N P : ℕ) (h_fun : ∀ j : Fin 5, a_general v (N + P + j.val) = a_general v (N + j.val)) (n : ℕ) :
  a_general v (N + P + n) = a_general v (N + n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases lt_or_ge n 5 with hn5 | hn5
    · -- n < 5
      let j : Fin 5 := ⟨n, hn5⟩
      have h1 : N + P + n = N + P + j.val := rfl
      have h2 : N + n = N + j.val := rfl
      rw [h1, h2]
      exact h_fun j
    · -- n ≥ 5
      let i := n - 5
      have hn_eq : n = i + 5 := by omega
      rw [hn_eq]
      have h1 : N + P + (i + 5) = (N + P + i) + 5 := by omega
      have h2 : N + (i + 5) = (N + i) + 5 := by omega
      rw [h1, h2]
      have hu1 : a_general v ((N + P + i) + 5) = π (a_general v (N + P + i + 4) + a_general v (N + P + i + 3) + a_general v (N + P + i + 2) + a_general v (N + P + i + 1) + a_general v (N + P + i)) := rfl
      have hu2 : a_general v ((N + i) + 5) = π (a_general v (N + i + 4) + a_general v (N + i + 3) + a_general v (N + i + 2) + a_general v (N + i + 1) + a_general v (N + i)) := rfl
      rw [hu1, hu2]
      have ih4 : a_general v (N + P + i + 4) = a_general v (N + i + 4) := by
        have h_eq : N + P + i + 4 = N + P + (i + 4) := by omega
        have h_eq2 : N + i + 4 = N + (i + 4) := by omega
        rw [h_eq, h_eq2]
        apply ih (i + 4) (by omega)
      have ih3 : a_general v (N + P + i + 3) = a_general v (N + i + 3) := by
        have h_eq : N + P + i + 3 = N + P + (i + 3) := by omega
        have h_eq2 : N + i + 3 = N + (i + 3) := by omega
        rw [h_eq, h_eq2]
        apply ih (i + 3) (by omega)
      have ih2 : a_general v (N + P + i + 2) = a_general v (N + i + 2) := by
        have h_eq : N + P + i + 2 = N + P + (i + 2) := by omega
        have h_eq2 : N + i + 2 = N + (i + 2) := by omega
        rw [h_eq, h_eq2]
        apply ih (i + 2) (by omega)
      have ih1 : a_general v (N + P + i + 1) = a_general v (N + i + 1) := by
        have h_eq : N + P + i + 1 = N + P + (i + 1) := by omega
        have h_eq2 : N + i + 1 = N + (i + 1) := by omega
        rw [h_eq, h_eq2]
        apply ih (i + 1) (by omega)
      have ih0 : a_general v (N + P + i) = a_general v (N + i) := by
        have h_eq : N + P + i = N + P + i := by omega
        have h_eq2 : N + i = N + i := by omega
        rw [h_eq, h_eq2]
        apply ih i (by omega)
      rw [ih4, ih3, ih2, ih1, ih0]

/-- oeis_100478_conjecture_0: Starting with other values of a(1), a(2), a(3), a(4), a(5) what behaviors are possible? Does the sequence always stick at a single integer after some point, or can it go into a loop, or is there a third pattern? -/
theorem oeis_a100478_conjecture_0 :
  -- For any set of five positive starting values v
  ∀ (v : Fin 5 → ℕ), (∀ i, v i > 0) →
  -- The sequence is ultimately periodic.
  ∃ N P : ℕ, P > 0 ∧ (∀ n, n ≥ N → a_general v (n + P) = a_general v n) := by
  intro v hv
  have h_dup := duplicate_test (S_seq v)
  rcases h_dup with ⟨N, b, h_lt, h_eq⟩
  let P := b - N
  have hP_pos : P > 0 := by omega
  use N, P
  refine ⟨hP_pos, ?_⟩
  dsimp only [P]
  have h_seq : S_seq v (N + (b - N)) = S_seq v N := by
    have : N + (b - N) = b := by omega
    rw [this]
    exact h_eq.symm
  have h_fun : ∀ j : Fin 5, a_general v (N + (b - N) + j.val) = a_general v (N + j.val) := by
    intro j
    have h_seq_j := congr_fun h_seq j
    exact congr_arg Fin.val h_seq_j
  intro n hn
  let k := n - N
  have hn_eq : n = N + k := by omega
  have hP_eq : n + (b - N) = N + (b - N) + k := by omega
  rw [hP_eq, hn_eq]
  exact a_general_periodic v N (b - N) h_fun k
